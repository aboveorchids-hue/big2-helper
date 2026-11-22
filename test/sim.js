// Simulated games through the live tracker: readings made from a known game (with the reader's usual troubles: counts not
// read, a single read wrong or not at all, the table moving, PASS signs over counts), fed in as the page would, and checked
// against the truth at every one of your turns. Run: node test/sim.js [games] [seed]
"use strict";
const B = require("../engine.js"), ST = require("../state.js"), LV = require("../live.js"), M = require("../models.js"), SW = require("../swap.js");

const N = +(process.argv[2] || 40), SEED = +(process.argv[3] || 7), SHOWS = process.env.SHOWS !== "0", ONE_UNREAD = process.env.ONE === "1";
// SWAP=1: a swap game (每局先換 0～3 張), with the swap's buttons read as play buttons now and then, and cards taken out
// of your row while choosing
const SWAP = process.env.SWAP === "1";
let a = SEED >>> 0;
const rnd = () => { a = (a + 0x6d2b79f5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
const SK = [null, "right", "top", "left"];

function deal() {
  const d = Array.from({ length: 52 }, (_, i) => i);
  for (let i = 51; i > 0; i--) { const j = Math.floor(rnd() * (i + 1)); [d[i], d[j]] = [d[j], d[i]]; }
  const hands = [0, 1, 2, 3].map((q) => B.fromIds(d.slice(q * 13, q * 13 + 13)));
  const cur = hands.findIndex((h) => B.has(h, 0));
  return B.newGame(hands, cur);
}
// the cards of yours the game lights up: those in some play that beats the one on the table
function litOf(g) {
  const ids = B.toIds(g.hand[0]);
  if (g.last.type === B.T_PASS) return ids.map(() => true);
  const on = new Set();
  for (const c of ST.combosOf(g.hand[0], false)) if (B.beats(c, g.last)) for (const x of B.toIds(c.set)) on.add(x);
  return ids.map((x) => on.has(x));
}
// what the reader would give for this moment; trouble: how unlucky the reading is
function reading(g, pile, opt) {
  const ids = B.toIds(g.hand[0]), myTurn = g.cur === 0 && g.winner < 0;
  const seats = {};
  for (let q = 1; q <= 3; q++) {
    const pass = !!(g.passed >> q & 1) && g.last.type !== B.T_PASS;
    const unread = rnd() < 0.08 || (opt.busy && q === opt.who) || (ONE_UNREAD && B.count(g.hand[q]) === 1);
    seats[SK[q]] = { count: unread ? null : B.count(g.hand[q]), p: unread ? 0 : 0.97, pass, gold: 0, ps: 0 };
  }
  const p = { n: pile ? pile.ids.length : 0, busy: false, displays: [] };
  if (pile && pile.ids.length === 1) {
    const u = rnd();
    if (u < 0.75) { p.cards = pile.ids.slice(); p.sure = true; }
    else if (u < 0.85) { p.cards = [(pile.ids[0] + 4) % 52]; p.sure = false; }   // read wrong, and not sure of it
  }
  if (pile && pile.ids.length > 1 && rnd() < 0.08) p.n = pile.ids.length === 2 ? 5 : 2;   // the size misjudged now and then
  if (opt.busy) {
    const d = { seat: opt.who, area: 9000 };
    if (opt.disp && opt.disp.length === 1 && rnd() < 0.7) { d.card = opt.disp[0]; d.sure = true; }
    p.displays.push(d);
  }
  const lit = myTurn ? litOf(g) : ids.map(() => rnd() < 0.5);
  const shows = opt.busy && opt.who && opt.disp && SHOWS && rnd() < 0.9 ? [{ seat: opt.who, cards: opt.disp.slice(), sure: true }] : [];
  return { hand: { cards: ids, sure: ids.map(() => true), lit, geoOk: true, n: ids.length, why: "" }, seats, pile: p, shows, myTurn, raised: false };
}

const tally = { games: 0, turns: 0, leadOk: 0, ownerOk: 0, sizeOk: 0, singleKnown: 0, singleTot: 0, singleWrong: 0, advIllegal: 0, advPassWhenLead: 0,
  countOk: 0, countTot: 0, playedWrong: 0, oppSingles: 0, oppSinglesSeen: 0, misses: [] };
const sameSet = (x, y) => B.sameSet(x.set, y.set);
let clock = 0;
for (let gi = 0; gi < N; gi++) {
  let g = deal();
  const live = LV.create();
  let pile = null, steps = 0;
  let feed = (r) => { clock += 700; return live.process(r, clock); };
  // a few settled readings of the table as it is
  const settle = (k) => { let last = null; for (let i = 0; i < k; i++) last = feed(reading(g, pile, {})); return last; };
  if (SWAP) {
    live.setSwapMode(true);
    g.cur = 1;   // nobody's turn yet
    let starts = 0;
    const feed0 = feed;
    feed = (r) => { const st = feed0(r); if (st && st.swapStart) starts++; return st; };
    // now and then a card of the row dealt is misread the same way every time
    const H0true = g.hand[0];
    let mis = null;
    if (rnd() < 0.2) { const ids = B.toIds(H0true), out = B.toIds(B.minus(B.fromIds([...Array(52).keys()]), H0true)); mis = [ids[Math.floor(rnd() * 13)], out[Math.floor(rnd() * out.length)]]; }
    const dealt = (r) => { if (mis) { const ids = r.hand.cards.map((c) => (c === mis[0] ? mis[1] : c)).sort((x, y) => x - y); r.hand = Object.assign({}, r.hand, { cards: ids }); } return r; };
    for (let i = 0; i < 3; i++) feed(dealt(reading(g, pile, {})));
    const sw = live.swapInfo();
    if (!sw || sw.phase !== "choose") tally.misses.push(`g${gi}: swap not started`);
    // the swap: you swap what the advice's quick model would (or nothing now and then), the others their loose singles
    const H0 = g.hand[0], mine = rnd() < 0.25 ? [] : SW.autoSwap(H0);
    if (live.S.swap) live.setSwapAdvice(live.S.swap.hand0, mine);
    // the others swap their loose singles (or nothing, now and then)
    const T = { hands: [null, g.hand[1], g.hand[2], g.hand[3]], gave: [null], seed: Math.floor(rnd() * 4294967296) };
    for (let q = 1; q <= 3; q++) T.gave.push(rnd() < 0.3 ? [] : SW.autoSwap(g.hand[q]));
    if (rnd() < 0.1) { T.gave = [null, [], [], []]; }
    const nobody = !mine.length && T.gave.every((x) => !x || !x.length);
    // choosing: buttons on screen (read as yours), now and then a count misread once
    for (let i = 0; i < 4; i++) {
      const r = dealt(reading(g, null, {}));
      if (rnd() < 0.6) r.myTurn = true;
      if (rnd() < 0.08) { const k = SK[1 + Math.floor(rnd() * 3)]; r.seats[k] = Object.assign({}, r.seats[k], { count: 12, p: 0.9 }); }
      feed(r);
    }
    // the chosen cards leave every row (not all seats at the same moment), then come back shuffled
    const away = (r, part) => {
      if (mine.length) { const ids = r.hand.cards.filter((c) => !mine.includes(c)); r.hand = Object.assign({}, r.hand, { cards: ids, sure: ids.map(() => true), lit: ids.map(() => true), n: ids.length }); }
      for (let q = 1; q <= 3; q++) if (T.gave[q].length && r.seats[SK[q]].count != null && (!part || q !== 1)) r.seats[SK[q]] = Object.assign({}, r.seats[SK[q]], { count: 13 - T.gave[q].length });
      return r;
    };
    if (!nobody) { feed(away(dealt(reading(g, null, {})), true)); for (let i = 0; i < 4; i++) feed(away(dealt(reading(g, null, {})), false)); }
    const hands = SW.afterSwap(H0, mine, T);
    g = B.newGame(hands, hands.findIndex((h) => B.has(h, 0)));
    tally.swaps = (tally.swaps || 0) + 1;
    // the cards just got are not read surely at first, now and then
    const fresh = B.toIds(B.minus(g.hand[0], H0));
    if (fresh.length && rnd() < 0.4) for (let i = 0; i < 2; i++) { const r = reading(g, null, {}); r.hand = Object.assign({}, r.hand, { sure: r.hand.cards.map((c) => !fresh.includes(c)) }); feed(r); }
    settle(4);
    if (starts !== 1) tally.misses.push(`g${gi}: swap advice started ${starts} times`);
    const got = B.toIds(B.minus(g.hand[0], H0));
    const w = live.S.swap;
    if (mis) tally.misreadDeals = (tally.misreadDeals || 0) + 1;
    else if (got.length ? !(w && w.got && w.got.slice().sort().join() === got.slice().sort().join()) : !!(w && w.got)) tally.misses.push(`g${gi}: swap read as ${w && w.got} truth ${got}`);
    else tally.swapOk = (tally.swapOk || 0) + 1;
    if (live.S.events.some((e) => e.k === "play" || e.k === "count")) tally.misses.push(`g${gi}: a play recorded during the swap`);
    if (!B.sameSet(B.fromIds(live.S.my), g.hand[0])) tally.misses.push(`g${gi}: hand after the swap wrong`);
    // you hold ♣3 and swapped but your row came back the same: wait out the swap
    if (live.S.events.length && live.S.events.some((e) => e.k === "count" || e.k === "play")) tally.misses.push(`g${gi}: plays recorded during the swap: ${JSON.stringify(live.S.events)}`);
    if ([1, 2, 3].some((q) => live.S.counts[q] !== 13)) tally.misses.push(`g${gi}: counts after the swap ${live.S.counts}`);
    if (g.cur === 0 && !live.S.round) { tally[nobody ? "waitedNobody" : "waited"] = (tally[nobody ? "waitedNobody" : "waited"] || 0) + 1; clock += 12000; settle(3); }
  } else settle(3);
  while (g.winner < 0 && steps++ < 200) {
    const p = g.cur;
    let move;
    if (p === 0) {
      const st = live.S;
      if (st.round) {
        tally.turns++;
        const R = st.round, lead = g.last.type === B.T_PASS;
        if (R.lead === lead) tally.leadOk++; else tally.misses.push(`g${gi}: lead ${R.lead} truth ${lead}`);
        if (!lead && R.top) {
          if (R.top.s === g.lastP) tally.ownerOk++; else tally.misses.push(`g${gi}: owner ${R.top.s} truth ${g.lastP}`);
          const n = B.count(g.last.set);
          if (R.top.n === n) tally.sizeOk++;
          if (n === 1) { tally.singleTot++; if (R.top.c) { tally.singleKnown++; if (R.top.c[0] !== B.toIds(g.last.set)[0]) tally.singleWrong++; } }
        }
        for (let q = 1; q <= 3; q++) { tally.countTot++; if (st.counts[q] === B.count(g.hand[q])) tally.countOk++; }
        for (const c of st.played) if (!B.has(g.played, c)) tally.playedWrong++;
        const adv = live.advise({ W: M.W, nDet: 12, maxCand: 4 });
        if (adv) {
          const L = B.genLegal(g, 0);
          if (adv.risky) tally.risky = (tally.risky || 0) + 1;
          if (adv.card.type === B.T_PASS) { if (lead) tally.advPassWhenLead++; else move = B.PASS(); }
          else if (!L.some((c) => sameSet(c, adv.card))) { tally.advIllegal++; tally.misses.push(`g${gi}: advice ${B.toIds(adv.card.set).map(B.name).join(" ")} not legal over ${B.toIds(g.last.set).map(B.name).join(" ")}`); }
          else move = adv.card;
        }
      } else tally.misses.push(`g${gi}: no round at your turn`);
    }
    if (!move) move = B.choose(g, p, { type: B.P_SMART });
    if (move.type !== B.T_PASS && p !== 0) { tally.oppSingles += B.count(move.set) === 1 ? 1 : 0; }
    B.applyMove(g, move);
    if (move.type !== B.T_PASS) pile = { ids: B.toIds(move.set) };
    // the play shown large for a moment, then the table settles
    if (move.type !== B.T_PASS) for (let i = 0; i < 2; i++) feed(reading(g, pile, { busy: true, who: p, disp: B.toIds(move.set) }));
    settle(g.cur === 0 ? 5 : 2);
  }
  // singles of the others the tracker knew by the end
  for (const c of live.S.played) if (B.has(g.played, c)) tally.oppSinglesSeen += 0;
  tally.games++;
}
const pct = (x, y) => (y ? (100 * x / y).toFixed(1) + "%" : "-");
console.log(`games ${tally.games}, your turns ${tally.turns}`);
console.log(`lead right ${pct(tally.leadOk, tally.turns)}, owner right ${pct(tally.ownerOk, tally.turns - (tally.turns - tally.ownerOk - tally.misses.filter((m) => m.includes("owner")).length))}`);
console.log(`play to beat: owner ${tally.ownerOk}, size right ${tally.sizeOk}; singles known ${pct(tally.singleKnown, tally.singleTot)} (wrong ${tally.singleWrong})`);
console.log(`counts right ${pct(tally.countOk, tally.countTot)}, cards wrongly marked played ${tally.playedWrong}`);
console.log(`risky ${tally.risky || 0}; advice not legal ${tally.advIllegal}, PASS when you lead ${tally.advPassWhenLead}`);
if (SWAP) console.log(`swaps read right ${tally.swapOk || 0}/${tally.swaps - (tally.misreadDeals || 0)} (+${tally.misreadDeals || 0} with a card of the row dealt misread); you lead first and had to wait out the swap ${tally.waited || 0} (nobody swapped: ${tally.waitedNobody || 0})`);
if (tally.misses.length) console.log(tally.misses.slice(0, 15).join("\n"));
