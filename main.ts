// Driftline — a momentum paper-trading bot for the pump.fun bonding-curve replay.
//
// Idea: new curves that have survived their first few hundred slots and are now
// drawing steady, accelerating buy flow from many wallets tend to keep drifting up
// for a while. Buy small at first, add only while the drift continues, and leave
// quickly on a stop, a trailing stop, a fade in flow, or old age. A few tiny probe
// round trips keep the run over the guardrail bar (20 coins) even in a dead tape.
//
// Deterministic by construction: no clock, no randomness, no environment reads.
// Every decision is a pure function of the batches the harness has delivered, and
// iteration is only over insertion-ordered maps fed by that same stream.

import { runBot, type Batch, type BotState, type OrderInput, type Pubkey } from './vendor/makefun-bot.ts';

const LAMPORTS = 1_000_000_000;

// --- entry gate -------------------------------------------------------------
const ENTRY_WINDOW = 40; // slots of tape the entry signal looks at
const MIN_AGE = 400; // slots since CreateEvent before a curve may be bought
const MIN_REAL_SOL = 2; // real SOL on the curve at entry
const MAX_REAL_SOL = 50;
const MIN_NET_INFLOW_SOL = 0.8; // buys minus sells over the window, in SOL
const MIN_BUY_TRADES = 3;
const MIN_BUYERS = 4; // distinct wallets buying in the window
const MIN_RISE = 0.04; // price now vs window start, minus 1
const MAX_RISE = 1.2; // skip curves that already ran too far in one window
const NEAR_HIGH = 0.92; // price now must sit at least this close to the window high
const MAX_TOP_BUYER_SHARE = 0.8; // largest single buyer's share of window buy SOL

// --- sizing -----------------------------------------------------------------
const FIRST_BUY_SOL = 0.1;
const ADD_BUY_SOL = 0.2;
const MAX_STAKE_SOL = 1.0; // most SOL ever put into one coin
const MIN_BUY_SOL = 0.01;
const MAX_MAIN_POSITIONS = 5;
const MAX_EXPOSURE_SOL = 6;
const BUY_SLIPPAGE_BPS = 1500;

// --- exits ------------------------------------------------------------------
const STOP_LOSS = 0.12; // sell when value falls this far under cost
const TRAIL_DROP = 0.15; // sell when value falls this far under its peak
const TRAIL_ARM = 0.08; // trailing stop arms once value reaches cost * (1 + this)
const FADE_WINDOW = 15; // slots
const FADE_NET_SOL = -0.3; // exit when net flow over the fade window is worse than this
const BIG_SELL_SOL = 3; // exit on any single recorded sell of at least this
const MAX_HOLD_SLOTS = 600;
const HOLD_IF_UP = 0.2; // the hold limit does not apply while up at least this much
const COOLDOWN_SLOTS = 200; // wait after an exit before the same curve may re-enter
const MAX_ENTRIES_PER_COIN = 2;

// --- guardrail probes -------------------------------------------------------
const TARGET_COINS = 25;
const TARGET_FILLS = 200;
const PACE_SECONDS = 14_400;
const PROBE_SOL = 0.01;
const MAX_PROBES = 1;

// Curve fee on every trade (95 protocol + 30 creator bps) plus tx fees.
const CURVE_FEE = 0.0125;

interface TapeTrade {
  slot: number;
  buy: boolean;
  sol: number;
  user: string;
  price: number;
}

interface Tape {
  created: number | null;
  trades: TapeTrade[];
  entries: number;
  lastExit: number;
}

interface OpenPosition {
  openedSlot: number;
  peakValueSol: number;
  investedSol: number;
  leaving: boolean;
  everFilled: boolean;
  lastBuyPrice: number;
  lastValueSol: number;
}

const tapes = new Map<Pubkey, Tape>();
const open = new Map<Pubkey, OpenPosition>();
const probes = new Map<Pubkey, boolean>(); // mint -> true once its probe buy has landed
let ownFills = 0;
const ownCoins = new Set<Pubkey>();
let firstBlockTime: number | null = null;
let lastBlockTime: number | null = null;

function tapeFor(mint: Pubkey): Tape {
  let t = tapes.get(mint);
  if (t === undefined) {
    t = { created: null, trades: [], entries: 0, lastExit: -1e12 };
    tapes.set(mint, t);
  }
  return t;
}

function priceOf(virtualQuote: bigint, virtualToken: bigint): number {
  return Number(virtualQuote) / Number(virtualToken);
}

/** Net SOL (buys minus sells) recorded on a tape over the last `slots` slots. */
function netFlow(t: Tape, now: number, slots: number): number {
  let net = 0;
  for (let i = t.trades.length - 1; i >= 0; i--) {
    const tr = t.trades[i]!;
    if (tr.slot <= now - slots) break;
    net += tr.buy ? tr.sol : -tr.sol;
  }
  return net;
}

/**
 * The entry test: a curve old enough, liquid enough, with several distinct buyers
 * pushing net SOL in, the price climbing but not vertical, sitting near its recent
 * high, and the inflow accelerating (the newer half of the window beats the older).
 */
function entryOk(t: Tape, now: number, realSol: number): boolean {
  if (realSol < MIN_REAL_SOL || realSol > MAX_REAL_SOL) return false;
  if (t.created === null || now - t.created < MIN_AGE) return false;
  const from = now - ENTRY_WINDOW;
  const mid = now - ENTRY_WINDOW / 2;
  let buySol = 0;
  let sellSol = 0;
  let buyCount = 0;
  let netOld = 0;
  let netNew = 0;
  let startPrice = -1;
  let high = 0;
  let last = 0;
  const buyers = new Map<string, number>();
  for (const tr of t.trades) {
    if (tr.slot <= from) {
      startPrice = tr.price;
      continue;
    }
    if (startPrice < 0) startPrice = tr.price;
    const signed = tr.buy ? tr.sol : -tr.sol;
    if (tr.slot <= mid) netOld += signed;
    else netNew += signed;
    if (tr.buy) {
      buySol += tr.sol;
      buyCount++;
      buyers.set(tr.user, (buyers.get(tr.user) ?? 0) + tr.sol);
    } else {
      sellSol += tr.sol;
    }
    if (tr.price > high) high = tr.price;
    last = tr.price;
  }
  if (buyCount < MIN_BUY_TRADES || buyers.size < MIN_BUYERS) return false;
  if (buySol - sellSol < MIN_NET_INFLOW_SOL) return false;
  if (startPrice <= 0) return false;
  const rise = last / startPrice - 1;
  if (rise < MIN_RISE || rise > MAX_RISE) return false;
  if (last < high * NEAR_HIGH) return false;
  if (netNew <= 0 || netNew < netOld) return false;
  let top = 0;
  for (const v of buyers.values()) if (v > top) top = v;
  if (top > MAX_TOP_BUYER_SHARE * buySol) return false;
  return true;
}

/** Current close value of a holding in SOL, curve fee and one tx fee deducted. */
function closeValueSol(
  tokens: number,
  virtualQuote: number,
  virtualToken: number,
  txFeeSol: number,
): number {
  const gross = (tokens * virtualQuote) / (virtualToken + tokens) / LAMPORTS;
  return gross * (1 - CURVE_FEE) - txFeeSol;
}

await runBot({
  onBatch(state: BotState, batch: Batch): OrderInput[] {
    const now = batch.slot;
    const bigSellers = new Set<Pubkey>();
    const touched = new Set<Pubkey>();

    for (const f of batch.fills) {
      if (f.status === 'filled' && !f.client_id.startsWith('_')) {
        ownFills++;
        ownCoins.add(f.mint);
      }
    }
    for (const e of batch.events) {
      if (e.block_time !== null) {
        if (firstBlockTime === null) firstBlockTime = e.block_time;
        if (lastBlockTime === null || e.block_time > lastBlockTime) lastBlockTime = e.block_time;
      }
      if (e.event === 'CreateEvent') {
        tapeFor(e.mint).created = e.slot;
      } else if (e.event === 'TradeEvent') {
        const t = tapeFor(e.mint);
        t.trades.push({
          slot: e.slot,
          buy: e.is_buy,
          sol: Number(e.sol_amount) / LAMPORTS,
          user: e.user,
          price: priceOf(BigInt(e.virtual_quote_reserves), BigInt(e.virtual_token_reserves)),
        });
        touched.add(e.mint);
        if (!e.is_buy && Number(e.sol_amount) / LAMPORTS >= BIG_SELL_SOL) bigSellers.add(e.mint);
      }
    }
    // Prune tape history older than any window we read.
    const keepSlots = Math.max(ENTRY_WINDOW, FADE_WINDOW) + 5;
    for (const mint of touched) {
      const t = tapes.get(mint)!;
      let cut = 0;
      while (cut < t.trades.length && t.trades[cut]!.slot <= now - keepSlots) cut++;
      if (cut > 0) t.trades.splice(0, cut);
    }

    const marks = new Map(batch.marks.map((m) => [m.mint, m] as const));
    const pendingByMint = new Map<Pubkey, number>();
    for (const po of state.pending.values()) {
      pendingByMint.set(po.order.mint, (pendingByMint.get(po.order.mint) ?? 0) + 1);
    }

    const orders: OrderInput[] = [];
    const cap = state.hello.caps.max_orders_per_batch;
    const txSol = Number(state.txFeeLamports()) / LAMPORTS;

    // --- exits first: stop, trailing stop, fade, big sell, old age. ----------
    for (const [mint, pos] of open) {
      const held = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (held === undefined) {
        if (!pendingByMint.has(mint)) {
          open.delete(mint);
          const t = tapeFor(mint);
          if (pos.everFilled) t.lastExit = now;
          else t.entries--;
        }
        continue;
      }
      pos.everFilled = true;
      if (curve === undefined || curve.complete) continue;
      const mk = marks.get(mint);
      const vq = mk ? Number(mk.virtual_quote_reserves) : Number(curve.virtual_quote_reserves);
      const vt = mk ? Number(mk.virtual_token_reserves) : Number(curve.virtual_token_reserves);
      const tokens = Number(held.token_amount);
      const value = closeValueSol(tokens, vq, vt, txSol);
      const cost = Number(held.cost_lamports) / LAMPORTS;
      if (value > pos.peakValueSol) pos.peakValueSol = value;
      pos.lastValueSol = value;
      let leave = pos.leaving;
      if (!leave && value < cost * (1 - STOP_LOSS)) leave = true;
      if (!leave && pos.peakValueSol >= cost * (1 + TRAIL_ARM) && value < pos.peakValueSol * (1 - TRAIL_DROP)) leave = true;
      if (!leave && netFlow(tapeFor(mint), now, FADE_WINDOW) < FADE_NET_SOL) leave = true;
      if (!leave && bigSellers.has(mint)) leave = true;
      if (!leave && now - pos.openedSlot > MAX_HOLD_SLOTS && value < cost * (1 + HOLD_IF_UP)) leave = true;
      if (!leave) continue;
      pos.leaving = true;
      let sellFlying = false;
      for (const po of state.pending.values()) {
        if (po.order.mint === mint && po.order.side === 'sell') sellFlying = true;
      }
      if (sellFlying) continue;
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: held.token_amount, max_slippage_bps: 10_000 });
    }

    // --- probe round trips: sell the probe whole once its buy has landed. ----
    for (const [mint, selling] of probes) {
      const held = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (held === undefined) {
        if (!pendingByMint.has(mint)) probes.delete(mint);
        continue;
      }
      if (curve === undefined || curve.complete || pendingByMint.has(mint)) continue;
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: held.token_amount, max_slippage_bps: 10_000 });
      if (!selling) probes.set(mint, true);
    }

    // --- entries and pyramid adds. -------------------------------------------
    let freeSol = Number(state.freeCashLamports()) / LAMPORTS;
    let slotsLeft = state.hello.caps.max_open_positions - state.committedPositionCount();
    let mainLeft = MAX_MAIN_POSITIONS - open.size;
    let exposureSol = 0;
    for (const [mint, pos] of open) {
      exposureSol += Math.max(pos.investedSol, Number(state.positions.get(mint)?.cost_lamports ?? 0n) / LAMPORTS);
    }
    for (const mint of touched) {
      if (orders.length >= cap) break;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      if (pendingByMint.has(mint) || probes.has(mint)) continue;
      const t = tapes.get(mint)!;
      const pos = open.get(mint);
      const price = priceOf(curve.virtual_quote_reserves, curve.virtual_token_reserves);
      const realSol = Number(curve.real_quote_reserves) / LAMPORTS;
      let want: number;
      if (pos === undefined) {
        if (slotsLeft <= 0 || mainLeft <= 0) continue;
        if (t.entries >= MAX_ENTRIES_PER_COIN || now - t.lastExit < COOLDOWN_SLOTS) continue;
        if (!entryOk(t, now, realSol)) continue;
        want = Math.min(FIRST_BUY_SOL, MAX_STAKE_SOL);
      } else {
        // Add only into strength: price stepped up from the last buy, position
        // up, flow still in. A 5% step keeps adds off flat tops.
        if (pos.leaving || !pos.everFilled || pos.investedSol >= MAX_STAKE_SOL - MIN_BUY_SOL) continue;
        const held = state.positions.get(mint);
        if (held === undefined) continue;
        if (price < pos.lastBuyPrice * 1.05) continue;
        if (pos.lastValueSol < Number(held.cost_lamports) / LAMPORTS) continue;
        if (netFlow(t, now, ENTRY_WINDOW) < MIN_NET_INFLOW_SOL) continue;
        if (realSol > MAX_REAL_SOL) continue;
        want = Math.min(ADD_BUY_SOL, MAX_STAKE_SOL - pos.investedSol);
      }
      const capSol = Math.floor(Number(state.maxBuyLamports(mint))) / LAMPORTS;
      let amount = Math.min(capSol, want, MAX_EXPOSURE_SOL - exposureSol);
      if (amount > freeSol - txSol) amount = freeSol - txSol;
      if (amount < MIN_BUY_SOL) continue;
      orders.push({ side: 'buy', mint, quote_lamports: BigInt(Math.floor(amount * LAMPORTS)), max_slippage_bps: BUY_SLIPPAGE_BPS });
      freeSol -= amount + txSol;
      exposureSol += amount;
      if (pos === undefined) {
        open.set(mint, {
          openedSlot: now,
          peakValueSol: 0,
          investedSol: amount,
          leaving: false,
          everFilled: false,
          lastBuyPrice: price,
          lastValueSol: 0,
        });
        t.entries++;
        slotsLeft--;
        mainLeft--;
      } else {
        pos.investedSol += amount;
        pos.lastBuyPrice = price;
      }
    }

    // --- guardrail pacing: open a probe when fills or coins lag the pace. ----
    if (probes.size < MAX_PROBES && slotsLeft > 0 && firstBlockTime !== null && lastBlockTime !== null) {
      const pace = Math.min(1, (lastBlockTime - firstBlockTime) / PACE_SECONDS);
      const needCoins = ownCoins.size < Math.ceil(TARGET_COINS * pace);
      const needFills = ownFills < Math.ceil(TARGET_FILLS * pace);
      if (needCoins || needFills) {
        const minReal = (PROBE_SOL * 10_000) / state.hello.caps.max_order_bps_of_real_reserve;
        for (const mint of touched) {
          if (orders.length >= cap || probes.size >= MAX_PROBES) break;
          if (open.has(mint) || probes.has(mint) || pendingByMint.has(mint) || state.positions.has(mint)) continue;
          if (needCoins && !needFills && ownCoins.has(mint)) continue;
          const curve = state.curves.get(mint);
          if (curve === undefined || curve.complete) continue;
          if (Number(curve.real_quote_reserves) / LAMPORTS < minReal * 1.5) continue;
          if (freeSol < PROBE_SOL + 2 * txSol) break;
          orders.push({ side: 'buy', mint, quote_lamports: BigInt(Math.floor(PROBE_SOL * LAMPORTS)), max_slippage_bps: BUY_SLIPPAGE_BPS });
          probes.set(mint, false);
          freeSol -= PROBE_SOL + txSol;
        }
      }
    }
    return orders;
  },
});
