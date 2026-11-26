// Strength test: whole games with you (seat 0) played by one strategy against three opponents of a given kind, on the
// same deals for every strategy (each deal four times, you getting each of the four hands once), so the strategies are
// compared on exactly the same cards. Points as the game scores them (with the house's 15 %).
// Run: node test/match.js <deals> <opponents> <strategy> [strategy ...]
//   opponents: smart | s | mix | noisy | greedy | pimc (see oppPolicy below)
//   strategy:  smart | s | pimc, with options after a colon (see heroMove below), e.g. pimc:deals=600,cand=8
//              s:wf=<weights.json> plays the weighted-feature player with other weights; swap=none|auto|advice in swap
//              games; any other name is played by the advice function in --adv=<file> (its `advise`, given the options)
// Env: SEED (first deal), JOBS (processes, default the number of cores), SWAP=1 (each deal starts with a swap)
// Prints each strategy's points per game (± standard error over deals), how often it goes out first and how often it loses
// 20 points or more, and, from the second on, the differences from the first on the same deals (points, going out first).
"use strict";
const path = require("path");
const { fork } = require("child_process");
const os = require("os");
const B = require("../engine.js"), M = require("../models.js");
const SW = require("../swap.js");

const RNG = (seed) => B.rng32(seed >>> 0);
function dealHands(seed) {
  const r = RNG(seed), d = Array.from({ length: 52 }, (_, i) => i);
  for (let i = 51; i > 0; i--) { const j = r.below(i + 1); const t = d[i]; d[i] = d[j]; d[j] = t; }
  return [0, 1, 2, 3].map((q) => B.fromIds(d.slice(q * 13, q * 13 + 13)));
}

// ---- opponents ----
// smart: the rule-based player the advice's simulations assume for the others
// s: the weighted-feature player (the advice's model of your own later plays)
// mix: each opponent seat smart or s, fixed for the deal
// noisy: s, but a quarter of the time a random one of its top few choices (a human who is not always sharp)
// greedy: plays the smallest play that beats the table, leads its lowest card (a beginner)
// pimc: a small version of the advice itself (60 deals, 6 plays compared): a strong, careful player
function oppPolicy(kind, seat, dealSeed) {
  const r = RNG((dealSeed * 7919 + seat * 104729) >>> 0);
  if (kind === "smart") return { type: B.P_SMART };
  if (kind === "s") return { type: B.P_S, w: M.W };
  if (kind === "mix") return r.below(2) ? { type: B.P_S, w: M.W } : { type: B.P_SMART };
  if (kind === "noisy") return { custom: "noisy", r };
  if (kind === "greedy") return { custom: "greedy" };
  if (kind === "pimc") return { custom: "pimc", r };
  throw new Error("opponents? " + kind);
}
function scoreS(g, p, m, steps0, U) { const f = B.featuresOf(g, p, m, steps0, U); let v = 0; for (let k = 0; k < f.length; k++) v += M.W[k] * f[k]; return v; }
function customMove(g, p, pol) {
  const L = B.genLegal(g, p);
  if (!L.length) return B.PASS();
  for (const c of L) if (B.isEmpty(B.minus(g.hand[p], c.set))) return c;
  if (pol.custom === "pimc") {
    if (L.length === 1 && g.last.type === B.T_PASS) return L[0];
    return B.choosePIMC(g, p, L, { type: B.P_PIMC, nDet: 60, maxCand: 6, rollType: B.P_S, w: M.W, seed: pol.r.next(), ev: true }).card;
  }
  if (pol.custom === "greedy") {
    const lead = g.last.type === B.T_PASS;
    const C = L.filter((c) => !B.isBomb(c.type) || lead);
    if (!C.length) return B.PASS();
    if (lead) { const lo = B.lowest(g.hand[p]); const s = C.filter((c) => B.has(c.set, lo)); return (s.find((c) => c.type === B.T_SINGLE) || s[0] || C[0]); }
    return C.reduce((a, b) => (b.key < a.key ? b : a));
  }
  // noisy
  const C = B.candidates(g, p, L);
  if (g.last.type !== B.T_PASS) C.push(B.PASS());
  const H = g.hand[p], U = B.unseenOf(H, g.played), steps0 = B.splitHand(H).steps;
  const sc = C.map((c) => [scoreS(g, p, c, steps0, U), c]).sort((a, b) => b[0] - a[0]);
  if (pol.r.below(4) === 0 && sc.length > 1) return sc[pol.r.below(Math.min(3, sc.length))][1];
  return sc[0][1];
}
function oppMove(g, p, pol) { return pol.custom ? customMove(g, p, pol) : B.choose(g, p, pol); }

// ---- you ----
// smart / s: as above. pimc: the advice (B.choosePIMC) with deals (most), min (fewest), cand (plays compared), z (drop a
// play this many standard errors behind), aim (pts | win), bonus (兼顧: the points plus this many more for going out
// first), loose (1: 散牌優先, B.looseChoice; 2: without its danger rule); `fixed=1` plays exactly `deals` deals with every play.
function parseHero(spec) {
  const [name, rest] = spec.split(":");
  const o = { name, spec };
  if (rest) for (const kv of rest.split(",")) { const [k, v] = kv.split("="); o[k] = isNaN(+v) ? v : +v; }
  return o;
}
let ADV = null;   // an alternative advice function (to compare a changed engine), set by --adv=<file>
function heroMove(g, h, seed, info) {
  const p = 0;
  if (h.name === "smart") return B.choose(g, p, { type: B.P_SMART });
  if (h.name === "s") return B.choose(g, p, { type: B.P_S, w: h.wf ? require(h.wf) : M.W });
  const L = B.genLegal(g, p);
  if (!L.length) return B.PASS();
  const outs = L.filter((c) => B.isEmpty(B.minus(g.hand[p], c.set)));
  if (outs.length) return outs.reduce((a, b) => (B.winnerMult(b) > B.winnerMult(a) ? b : a));
  if (L.length === 1 && g.last.type === B.T_PASS) return L[0];
  // rule: 只顯示最大牌's own advice (B.ruleChoice), no simulation
  if (h.name === "rule") return B.ruleChoice(g, p, L).card;
  const adapt = h.fixed ? null : { z: h.z || 2.5, min: h.min || 200, max: h.deals || 1500, batch: 100, budget: 1e9 };
  const pol = { type: B.P_PIMC, nDet: h.deals || 200, adapt, maxCand: h.cand || 8, rollType: B.P_S, w: M.W, seed, ev: (h.aim || "pts") === "pts", winBonus: h.bonus || 0 };
  if (h.name === "pimc") {
    // loose=1: 散牌優先 (B.looseChoice narrows the plays, the simulation picks among them)
    if (h.loose) { const lz = B.looseChoice(g, p, L, { danger: h.loose !== 2 }); if (lz.L.length) { if (lz.L.length === 1 && lz.noPass) return lz.L[0]; const r = B.choosePIMC(g, p, lz.L, Object.assign({}, pol, { noPass: lz.noPass })); info.deals += r.deals || 0; info.dec++; return r.card; } if (g.last.type !== B.T_PASS) return B.PASS(); }
    // keep=1: 神幣優先 as on the page, only plays that split nothing up (B.keepPlays)
    if (h.keep && !B.anyLow(g, p, h.free == null ? 5 : h.free)) { const K = B.keepPlays(g.hand[p], L, !!h.two); if (!K.length) return B.PASS(); if (K.length === 1 && g.last.type === B.T_PASS) return K[0]; const r = B.choosePIMC(g, p, K, pol); info.deals += r.deals || 0; info.dec++; return h.close != null ? B.preferKeep(g.hand[p], r.stats, r.card, h.close) : r.card; }
    // close=N: (with keep) a play that splits something up only when nothing that keeps the hand whole is within N points
    if (h.keep && h.close != null) { const r = B.choosePIMC(g, p, L, pol); info.deals += r.deals || 0; info.dec++; return B.preferKeep(g.hand[p], r.stats, r.card, h.close); }
    const r = B.choosePIMC(g, p, L, pol); info.deals += r.deals || 0; info.dec++; return r.card;
  }
  if (ADV) { const r = ADV(g, p, L, Object.assign({}, pol, h), info); return r; }
  throw new Error("strategy? " + h.spec);
}

// one game: the deal's hands rotated so you get hand `rot`; returns { pts, win, left, info }
function playGame(dealSeed, rot, hero, oppKind, swapPlan) {
  let hands = dealHands(dealSeed);
  hands = [0, 1, 2, 3].map((q) => hands[(q + rot) & 3]);
  const pols = [null, 1, 2, 3].map((q) => (q ? oppPolicy(oppKind, q, dealSeed * 4 + rot) : null));
  if (swapPlan) hands = swapPlan(hands, dealSeed, rot);
  const g = B.newGame(hands, hands.findIndex((h) => B.has(h, 0)));
  const info = { deals: 0, dec: 0 };
  // what everyone did, for advice functions (--adv) that read the others' plays: who, what, the play it was on, how many
  // cards they had, and whether the rule of playing your top single held them (the next one to play had one card)
  g.log = [];
  let k = 0;
  while (g.winner < 0 && k++ < 400) {
    const p = g.cur;
    const m = p === 0 ? heroMove(g, hero, (dealSeed * 131 + rot * 17 + k * 7) >>> 0, info) : oppMove(g, p, pols[p]);
    g.log.push({ p, m, last: g.last, n: B.count(g.hand[p]), top: B.dingDa(g, p) });
    B.applyMove(g, m);
  }
  return { pts: B.pointsFor(g, 0), win: g.winner === 0 ? 1 : 0, left: B.count(g.hand[0]), info };
}

// ---- workers ----
function runRange(job) {
  if (job.adv) ADV = require(path.resolve(job.adv)).advise;
  const heroes = job.heroes.map(parseHero), out = heroes.map(() => []);
  let swapPlans = null;
  if (job.swap) swapPlans = heroes.map((h) => makeSwapPlan(h));
  for (let d = job.from; d < job.to; d++) {
    const seed = (job.seed + d * 2654435761) >>> 0;
    for (let rot = 0; rot < 4; rot++) heroes.forEach((h, i) => { const r = playGame(seed, rot, h, job.opp, swapPlans && swapPlans[i]); out[i].push([r.pts, r.win, r.info.deals, r.info.dec]); });
  }
  return out;
}
// the swap at the start of a deal: you swap as the strategy says (hero option swap=none|auto|advice), the others their
// loose low singles
function makeSwapPlan(h) {
  return (hands, dealSeed, rot) => {
    const r = RNG((dealSeed * 31 + rot) >>> 0);
    const T = { hands: [null, hands[1], hands[2], hands[3]], gave: [null], seed: r.next() };
    for (let q = 1; q <= 3; q++) T.gave.push(SW.autoSwap(hands[q]));
    let mine = [];
    const how = h.swap || "none";
    if (how === "auto") mine = SW.autoSwap(hands[0]);
    else if (how === "advice") { const a = SW.advise(B.toIds(hands[0]), { W: M.W, budget: 1e9, aim: h.aim === "win" ? "win" : "pts", seed: (dealSeed ^ rot) >>> 0 }); mine = a.best.gave; }
    return SW.afterSwap(hands[0], mine, T);
  };
}
if (require.main !== module) {
  // (used as a module)
} else if (process.argv[2] === "--worker") {
  process.on("message", (job) => { process.send(runRange(job)); process.exit(0); });
} else {
  const args = process.argv.slice(2).filter((a) => !a.startsWith("--"));
  const adv = (process.argv.find((a) => a.startsWith("--adv=")) || "").slice(6) || null;
  const deals = +(args[0] || 50), opp = args[1] || "smart", heroes = args.slice(2);
  if (!heroes.length) heroes.push("s", "pimc");
  const seed = +(process.env.SEED || 1), jobs = +(process.env.JOBS || os.cpus().length), swap = process.env.SWAP === "1";
  const t0 = Date.now();
  const per = Math.ceil(deals / jobs), parts = [];
  for (let j = 0; j < jobs; j++) {
    const from = j * per, to = Math.min(deals, from + per);
    if (from >= to) continue;
    parts.push(new Promise((res, rej) => {
      const w = fork(__filename, ["--worker"]);
      w.on("message", res); w.on("error", rej);
      w.send({ from, to, seed, opp, heroes, adv, swap });
    }));
  }
  Promise.all(parts).then((rs) => {
    const all = heroes.map((h, i) => [].concat(...rs.map((r) => r[i])));
    const n = all[0].length;
    const mean = (a) => a.reduce((s, x) => s + x, 0) / a.length;
    const sd = (a) => { const m = mean(a); return Math.sqrt(a.reduce((s, x) => s + (x - m) * (x - m), 0) / Math.max(1, a.length - 1)); };
    console.log(`${deals} deals x 4 seats = ${n} games, opponents ${opp}${swap ? ", swap games" : ""}, ${((Date.now() - t0) / 1000).toFixed(0)} s`);
    // per deal (the four rotations together), for paired differences
    const perDeal = (a) => { const o = []; for (let i = 0; i < a.length; i += 4) o.push((a[i] + a[i + 1] + a[i + 2] + a[i + 3]) / 4); return o; };
    const deal0 = perDeal(all[0].map((x) => x[0])), win0 = perDeal(all[0].map((x) => x[1]));
    heroes.forEach((h, i) => {
      const pts = all[i].map((x) => x[0]), win = all[i].map((x) => x[1]);
      const dec = all[i].reduce((s, x) => s + x[3], 0), dl = all[i].reduce((s, x) => s + x[2], 0);
      const big = pts.map((x) => (x <= -20 ? 1 : 0));
      let line = `${h.padEnd(28)} pts/game ${mean(pts).toFixed(2).padStart(6)} ± ${(sd(perDeal(pts)) / Math.sqrt(n / 4)).toFixed(2)}   win ${(100 * mean(win)).toFixed(1)}%   lose 20+ ${(100 * mean(big)).toFixed(1)}%`;
      if (dec) line += `   deals/decision ${(dl / dec).toFixed(0)}`;
      if (i > 0) {
        const d = perDeal(pts).map((x, k) => x - deal0[k]);
        const dw = perDeal(win).map((x, k) => x - win0[k]);
        line += `   vs ${heroes[0]}: ${mean(d) >= 0 ? "+" : ""}${mean(d).toFixed(2)} ± ${(sd(d) / Math.sqrt(d.length)).toFixed(2)} pts, ${mean(dw) >= 0 ? "+" : ""}${(100 * mean(dw)).toFixed(1)} ± ${(100 * sd(dw) / Math.sqrt(dw.length)).toFixed(1)}% win`;
      }
      console.log(line);
    });
  });
}
module.exports = { playGame, dealHands, oppPolicy, oppMove, parseHero };
