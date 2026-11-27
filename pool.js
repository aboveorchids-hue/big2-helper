// The play advice's simulation spread over several threads (worker.js), so it runs on more of the iPad's cores and the
// page keeps reading the screen meanwhile. Same work as Big2.choosePIMC: the same plays compared on the same random
// deals for each, the same dropping of plays clearly behind (pol.adapt: z, min, max, budget) and the same pick; the
// deals are only cut into rounds, each round shared among the threads. A round is sized to take about ROUND_MS, so
// plays are dropped and the time limit looked at about that often.
(function (root) {
  "use strict";
  const ROUND_MS = 150;

  function create(n, url) {
    const workers = [];
    for (let i = 0; i < n; i++) workers.push(new Worker(url));
    let seq = 0, gen = 0;
    const waiting = new Map();
    for (const w of workers) {
      w.onmessage = (e) => { const f = waiting.get(e.data.id); if (f) { waiting.delete(e.data.id); f(e.data); } };
      w.onerror = (e) => { for (const [id, f] of waiting) { waiting.delete(id); f({ id, err: e.message || "worker error" }); } };
    }
    const ask = (w, msg) => new Promise((res, rej) => {
      const id = ++seq;
      waiting.set(id, (d) => (d.err ? rej(new Error(d.err)) : res(d.r)));
      w.postMessage(Object.assign({ id }, msg));
    });

    // the advice for plays C (from Big2.pimcSetup; pref its weighted player's pick), as Big2.choosePIMC returns it, or
    // null when cancelled (a newer piece of advice was asked for)
    async function run(g, p, C, pref, pol) {
      const my = ++gen;
      const A = pol.adapt, nMax = A ? A.max : pol.nDet;
      const vals = C.map(() => []), wins = C.map(() => 0), pts = C.map(() => 0), alive = C.map(() => true);
      const X = pol.ev ? pol.winBonus || 0 : 0;
      const n = (i) => vals[i].length;
      const mean = (i) => (pol.ev ? pts[i] + X * wins[i] : wins[i]) / Math.max(1, n(i));
      const t0 = Date.now();
      let done = 0, round = 0, size = workers.length * 4;
      const base = (pol.seed >>> 0) || 1;
      while (done < nMax) {
        if (my !== gen) return null;
        // this round's deals, shared among the threads (no more than are left, and at least `min` before dropping any)
        const want = Math.min(nMax - done, Math.max(size, A && done < A.min ? Math.min(A.min - done, size * 4) : 0));
        const share = workers.map((w, i) => Math.floor(want / workers.length) + (i < want % workers.length ? 1 : 0)).filter((k) => k > 0);
        const r0 = Date.now();
        const outs = await Promise.all(share.map((k, i) => ask(workers[i], { g, p, C, pol, seed: (base + round * 7919 + i * 104729) >>> 0, count: k, alive })));
        if (my !== gen) return null;
        for (const o of outs) for (let i = 0; i < C.length; i++) if (alive[i]) { for (const v of o.vals[i]) vals[i].push(v); wins[i] += o.wins[i]; pts[i] += o.pts[i]; }
        done += want; round++;
        const ms = Math.max(1, Date.now() - r0);
        size = Math.max(workers.length, Math.min(4000, Math.round(want * ROUND_MS / ms)));
        if (!A) continue;
        if (done >= A.min) {
          let b = -1;
          for (let i = 0; i < C.length; i++) if (alive[i] && (b < 0 || mean(i) > mean(b))) b = i;
          for (let i = 0; i < C.length; i++) {
            if (!alive[i] || i === b) continue;
            const m = n(i);   // (both still in: played on the same deals)
            let s1 = 0, s2 = 0;
            for (let j = 0; j < m; j++) { const dd = vals[b][j] - vals[i][j]; s1 += dd; s2 += dd * dd; }
            const md = s1 / m, se = Math.sqrt(Math.max(1e-12, s2 / m - md * md) / m);
            if (md > A.z * se) alive[i] = false;
          }
          if (alive.filter(Boolean).length === 1 || Date.now() - t0 > A.budget) break;
        }
      }
      const B = root.Big2;
      let bi = -1;
      for (let i = 0; i < C.length; i++) if (alive[i] && (bi < 0 || mean(i) > mean(bi))) bi = i;
      for (let i = 0; i < C.length; i++) if (alive[i] && mean(i) === mean(bi) && B.sameCombo(C[i], pref)) { bi = i; break; }
      return { card: C[bi], stats: C.map((c, i) => ({ card: c, wins: wins[i], pts: pts[i] / Math.max(1, n(i)), n: n(i), out: !alive[i] })), pref, ms: Date.now() - t0, deals: Math.max(...C.map((c, i) => n(i))), threads: workers.length };
    }
    const cancel = () => { gen++; };
    const close = () => { for (const w of workers) w.terminate(); };
    return { run, cancel, close, size: workers.length };
  }

  // how many threads: one fewer than the cores the browser reports (the page needs one), 1 to 8
  const threads = () => Math.max(1, Math.min(8, ((root.navigator && root.navigator.hardwareConcurrency) || 4) - 1));
  root.B2Pool = { create, threads };
})(typeof self !== "undefined" ? self : this);
