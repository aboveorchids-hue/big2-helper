// 換牌局：一開始每家可以換 0～3 張。換出的牌和別家換出的牌洗在一起，每家再隨機拿回和換出一樣多的牌（可能拿回自己的）。
// Which cards to swap: every way of swapping 0 to 3 of your cards is first rated quickly by how your hand splits after
// a random refill; the best few (and not swapping) are then played out in full many times, with the others' hands dealt
// at random from the cards you don't hold and the others swapping their own loose low singles, and the one that wins
// you the most points on average is the advice (the same aim as the play advice).
(function (root) {
  "use strict";
  const B = root.Big2 || (typeof require !== "undefined" ? require("./engine.js") : null);

  // what the others swap: their loose singles from 3 to 10 (not in a pair or a five-card play), lowest first, up to 3
  function autoSwap(H) {
    const pieces = B.splitPieces(H, B.splitHand(H));
    return pieces.filter((c) => c.type === B.T_SINGLE && (c.key >> 2) <= 7).map((c) => c.key).sort((a, b) => a - b).slice(0, 3);
  }
  // every way of choosing 0 to k of the cards
  function choices(ids, k) {
    const out = [[]];
    const n = ids.length;
    for (let a = 0; a < n; a++) {
      out.push([ids[a]]);
      if (k >= 2) for (let b = a + 1; b < n; b++) {
        out.push([ids[a], ids[b]]);
        if (k >= 3) for (let c = b + 1; c < n; c++) out.push([ids[a], ids[b], ids[c]]);
      }
    }
    return out;
  }
  function hashIds(ids) { let h = 0x811c9dc5; for (const c of ids) { h ^= c + 1; h = Math.imul(h, 16777619) >>> 0; } return h >>> 0; }
  // quick rating of a hand: fewer plays to empty it, stronger pieces, and the 2s and As that take back the lead
  const quick = (H) => { const s = B.splitHand(H); let hi = 0; for (const r of [11, 12]) for (let b = 0; b < 4; b++) if (H[r] >> b & 1) hi += r === 12 ? 300 : 100; return -s.steps * 1000 - s.weak + hi; };

  // one possible table: the others' hands, what each of them swaps, and the order the pooled cards come back in
  function sampleTable(unseen, rnd) {
    const d = unseen.slice();
    for (let i = d.length - 1; i > 0; i--) { const j = rnd.below(i + 1); const t = d[i]; d[i] = d[j]; d[j] = t; }
    const hands = [null], gave = [null];
    for (let q = 1; q <= 3; q++) { const h = B.fromIds(d.slice((q - 1) * 13, q * 13)); hands.push(h); gave.push(autoSwap(h)); }
    return { hands, gave, seed: rnd.next() };
  }
  // the four hands after the swap, you giving `mine`
  function afterSwap(H, mine, T) {
    const pool = mine.concat(T.gave[1], T.gave[2], T.gave[3]);
    const r = B.rng32(T.seed);
    for (let i = pool.length - 1; i > 0; i--) { const j = r.below(i + 1); const t = pool[i]; pool[i] = pool[j]; pool[j] = t; }
    let k = 0;
    const take = (h, out, n) => { const o = B.minus(h, B.fromIds(out)); for (let i = 0; i < n; i++) { const c = pool[k++]; o[c >> 2] |= 1 << (c & 3); } return o; };
    const hands = [take(H, mine, mine.length)];
    for (let q = 1; q <= 3; q++) hands.push(take(T.hands[q], T.gave[q], T.gave[q].length));
    return hands;
  }

  // the advice for a hand of 13 (card ids): { best, list: [{ gave, pts, wins, n }] best first, ms }
  // opts: keep (choices played out), nQuick (refills per choice in the quick rating), stages ([games so far, choices kept
  //       after]), W (the strategy weights for your own play in the games), budget (ms to stop at, roughly), aim ("pts" |
  //       "win")
  function advise(myIds, opts) {
    opts = opts || {};
    const t0 = Date.now();
    const my = myIds.slice().sort((a, b) => a - b);
    if (my.length !== 13) return null;
    const H = B.fromIds(my), unseen = B.toIds(B.unseenOf(H, B.empty()));
    const rnd = B.rng32(opts.seed != null ? opts.seed : hashIds(my));
    const nQuick = opts.nQuick || 32, keep = opts.keep || 16, budget = opts.budget || 3000;
    // 1. quick rating of all 378 choices: how well your hand splits after the refill
    const QT = []; for (let i = 0; i < nQuick; i++) QT.push(sampleTable(unseen, rnd));
    const all = choices(my, 3).map((gave) => {
      let v = 0;
      for (const T of QT) v += quick(afterSwap(H, gave, T)[0]);
      return { gave, v: v / nQuick };
    });
    all.sort((a, b) => b.v - a.v);
    const short = all.slice(0, keep);
    const must = [[], autoSwap(H)];
    for (const m of must) if (!short.some((x) => x.gave.join() === m.join())) short.push(all.find((x) => x.gave.join() === m.join()));
    // 2. full games for the short list, the same tables for every choice; the weaker half is dropped twice on the way
    // (not swapping is always played out, to compare with)
    const pol = [{ type: B.P_S, w: opts.W || (root.B2_MODELS && root.B2_MODELS.W) }, { type: B.P_SMART }, { type: B.P_SMART }, { type: B.P_SMART }];
    if (!pol[0].w) pol[0] = { type: B.P_SMART };
    const res = short.map((x) => ({ gave: x.gave, pts: 0, wins: 0, n: 0, out: false }));
    // the aim: points on average (opts.aim "pts", the default) or how often you go out first ("win")
    const win = opts.aim === "win";
    const val = (x) => (win ? x.wins : x.pts) / Math.max(1, x.n), valAvg = (x) => (win ? x.wins / Math.max(1, x.n) : x.pts);
    const stages = opts.stages || [[100, 6], [400, 3], [1000, 0]];
    let d = 0;
    for (const [upTo, keepNext] of stages) {
      for (; d < upTo; d++) {
        if (d >= 60 && Date.now() - t0 > budget) break;
        const T = sampleTable(unseen, rnd);
        for (const x of res) {
          if (x.out) continue;
          const hands = afterSwap(H, x.gave, T);
          let cur = 0; for (let q = 0; q < 4; q++) if (B.has(hands[q], 0)) cur = q;
          const g = B.newGame(hands, cur);
          B.playOut(g, pol);
          x.pts += B.pointsFor(g, 0); if (g.winner === 0) x.wins++; x.n++;
        }
      }
      if (!keepNext || d < upTo) break;
      const alive = res.filter((x) => !x.out).sort((a, b) => val(b) - val(a));
      alive.forEach((x, i) => { if (i >= keepNext && x.gave.length) x.out = true; });
    }
    for (const x of res) x.pts /= Math.max(1, x.n);
    // the choices played out longest first (their averages are the surest), best first among them; ties: fewer cards
    res.sort((a, b) => b.n - a.n || valAvg(b) - valAvg(a) || a.gave.length - b.gave.length);
    return { best: res[0], list: res, none: res.find((x) => !x.gave.length), ms: Date.now() - t0 };
  }

  const api = { advise, autoSwap, choices, afterSwap, sampleTable };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  else root.B2Swap = api;
})(typeof self !== "undefined" ? self : this);
