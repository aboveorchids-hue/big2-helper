// 大老二 engine for the page: rules, hand splitting, opponents' model and the strategy.
// A port of the C++ simulator (big2.h / bots.h): same move order, same arithmetic, so it picks exactly the same plays.
// Cards: id = rank*4 + suit; rank 0..12 = 3 4 5 6 7 8 9 10 J Q K A 2; suit 0..3 = ♣ ♦ ♥ ♠.
// A set of cards is an array of 13 nibbles (bit s of entry r = card r*4+s).
(function (root) {
  "use strict";
  const T_PASS = 0, T_SINGLE = 1, T_PAIR = 2, T_STRAIGHT = 3, T_FULL = 4, T_QUADS = 5, T_SF = 6, T_DRAGON = 7;
  const TNAME = ["PASS", "單張", "一對", "順子", "葫蘆", "鐵支", "同花順", "一條龍"];
  const PC4 = [0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4];
  const CTZ4 = [4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0];
  const MSB4 = [-1, 0, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3];
  const WINR = [], WINTOP = [];
  WINR[0] = [11, 12, 0, 1, 2]; WINR[9] = [12, 0, 1, 2, 3]; WINTOP[0] = WINTOP[9] = 12;
  for (let o = 1; o <= 8; o++) { WINR[o] = [o - 1, o, o + 1, o + 2, o + 3]; WINTOP[o] = o + 3; }
  const RANKS = ["3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K", "A", "2"];
  const SUITS = ["♣", "♦", "♥", "♠"];
  const name = (c) => SUITS[c & 3] + RANKS[c >> 2];

  // ---- card sets ----
  const empty = () => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
  const fromIds = (ids) => { const s = empty(); for (const c of ids) s[c >> 2] |= 1 << (c & 3); return s; };
  const toIds = (s) => { const o = []; for (let r = 0; r < 13; r++) for (let b = 0; b < 4; b++) if (s[r] >> b & 1) o.push(r * 4 + b); return o; };
  const count = (s) => { let n = 0; for (let r = 0; r < 13; r++) n += PC4[s[r]]; return n; };
  const lowest = (s) => { for (let r = 0; r < 13; r++) if (s[r]) return r * 4 + CTZ4[s[r]]; return -1; };
  const highest = (s) => { for (let r = 12; r >= 0; r--) if (s[r]) return r * 4 + MSB4[s[r]]; return -1; };
  const minus = (a, b) => { const o = new Array(13); for (let r = 0; r < 13; r++) o[r] = a[r] & ~b[r]; return o; };
  const isEmpty = (s) => { for (let r = 0; r < 13; r++) if (s[r]) return false; return true; };
  const sameSet = (a, b) => { for (let r = 0; r < 13; r++) if (a[r] !== b[r]) return false; return true; };
  const cmpSet = (a, b) => { for (let r = 12; r >= 0; r--) if (a[r] !== b[r]) return a[r] > b[r] ? 1 : -1; return 0; };   // as 52-bit numbers
  const has = (s, c) => (s[c >> 2] >> (c & 3) & 1) === 1;
  const unseenOf = (hand, played) => { const o = new Array(13); for (let r = 0; r < 13; r++) o[r] = 15 & ~hand[r] & ~played[r]; return o; };

  const mk = (set, type, key) => ({ set, type, key });
  const PASS = () => ({ set: empty(), type: T_PASS, key: 0 });
  const isBomb = (t) => t === T_QUADS || t === T_SF;
  function beats(c, last) {
    if (last.type === T_PASS) return true;
    if (c.type === T_DRAGON) return last.type !== T_DRAGON || c.key > last.key;
    if (last.type === T_DRAGON) return false;
    if (c.type === T_SF) return last.type !== T_SF || c.key > last.key;
    if (last.type === T_SF) return false;
    if (c.type === T_QUADS) return last.type !== T_QUADS || c.key > last.key;
    if (last.type === T_QUADS) return false;
    return c.type === last.type && c.key > last.key;
  }

  // ---- move generation (same order as the C++) ----
  function bitsOf(m) { const o = []; for (let b = 0; b < 4; b++) if (m >> b & 1) o.push(b); return o; }
  // (above: only what could beat a single or pair with this key; the same order as all of them filtered)
  function genSingles(H, out, above = -1) { for (let r = Math.max(0, above >> 2); r < 13; r++) for (let b = 0; b < 4; b++) if (H[r] >> b & 1 && r * 4 + b > above) { const s = empty(); s[r] = 1 << b; out.push(mk(s, T_SINGLE, r * 4 + b)); } }
  function genPairs(H, out, above = -1) {
    for (let r = Math.max(0, above >> 2); r < 13; r++) {
      const m = H[r];
      if (PC4[m] < 2) continue;
      const bs = bitsOf(m);
      for (let i = 0; i < bs.length; i++) for (let j = i + 1; j < bs.length; j++) { const s = empty(); s[r] = (1 << bs[i]) | (1 << bs[j]); out.push(mk(s, T_PAIR, r * 4 + bs[j])); }
    }
  }
  function genStraights(H, out, wantPlain, wantSF) {
    for (let o = 0; o < 10; o++) {
      const R = WINR[o];
      let ok = true;
      for (let i = 0; i < 5; i++) if (!H[R[i]]) { ok = false; break; }
      if (!ok) continue;
      if (!wantPlain) {
        // (only the straight flushes: one per suit present in all five ranks, in suit order as below)
        const both = H[R[0]] & H[R[1]] & H[R[2]] & H[R[3]] & H[R[4]];
        if (wantSF) for (let a = 0; a < 4; a++) if (both >> a & 1) { const s = empty(); for (let i = 0; i < 5; i++) s[R[i]] = 1 << a; out.push(mk(s, T_SF, o * 4 + a)); }
        continue;
      }
      const B = R.map((r) => bitsOf(H[r]));
      for (const a of B[0]) for (const b of B[1]) for (const c of B[2]) for (const d of B[3]) for (const e of B[4]) {
        const su = [a, b, c, d, e];
        const s = empty();
        for (let i = 0; i < 5; i++) s[R[i]] |= 1 << su[i];
        const flush = b === a && c === a && d === a && e === a;
        const topSuit = CTZ4[s[WINTOP[o]]];
        if (flush) { if (wantSF) out.push(mk(s, T_SF, o * 4 + a)); }
        else if (wantPlain) out.push(mk(s, T_STRAIGHT, o * 4 + topSuit));
      }
    }
  }
  function genFulls(H, out) {
    for (let t = 0; t < 13; t++) {
      const mt = H[t], nt = PC4[mt];
      if (nt < 3) continue;
      const trips = [];
      if (nt === 3) trips.push(mt);
      else for (const b of bitsOf(mt)) trips.push(mt & ~(1 << b));
      for (let p = 0; p < 13; p++) {
        if (p === t) continue;
        const mp = H[p];
        if (PC4[mp] < 2) continue;
        const bs = bitsOf(mp);
        for (let i = 0; i < bs.length; i++) for (let j = i + 1; j < bs.length; j++) {
          const pr = (1 << bs[i]) | (1 << bs[j]);
          for (const tr of trips) { const s = empty(); s[t] = tr; s[p] = pr; out.push(mk(s, T_FULL, t)); }
        }
      }
    }
  }
  function genQuads(H, out) {
    for (let q = 0; q < 13; q++) {
      if (H[q] !== 15) continue;
      for (let r = 0; r < 13; r++) { if (r === q) continue; for (const b of bitsOf(H[r])) { const s = empty(); s[q] = 15; s[r] = 1 << b; out.push(mk(s, T_QUADS, q)); } }
    }
  }
  function isDragonHand(H) { if (count(H) !== 13) return false; for (let r = 0; r < 13; r++) if (!H[r]) return false; return true; }
  function genDragon(H, out) {
    if (!isDragonHand(H)) return;
    const s0 = CTZ4[H[0]];
    let same = true;
    for (let r = 0; r < 13; r++) if (H[r] !== 1 << s0) same = false;
    out.push(mk(H.slice(), T_DRAGON, same ? 1 : 0));
  }

  // ---- game ----
  // g = {hand: [4 sets], played: set, last: combo, lastP, passed (bit mask), cur, first, winner, finalPlay}
  function newGame(hands, cur) { return { hand: hands.map((h) => h.slice()), played: empty(), last: PASS(), lastP: -1, passed: 0, cur, first: true, winner: -1, finalPlay: null, nplays: 0 }; }
  function copyGame(g) { return { hand: g.hand.map((h) => h.slice()), played: g.played.slice(), last: g.last, lastP: g.lastP, passed: g.passed, cur: g.cur, first: g.first, winner: g.winner, finalPlay: g.finalPlay, nplays: g.nplays }; }
  function nextActor(g, p) { for (let k = 1; k <= 3; k++) { const q = (p + k) & 3; if (!(g.passed >> q & 1)) return q; } return p; }
  function dingDa(g, p) { const q = nextActor(g, p); return q !== p && count(g.hand[q]) === 1; }
  function genLegal(g, p) {
    const H = g.hand[p], lt = g.last.type;
    let out = [];
    if (lt === T_PASS) { genSingles(H, out); genPairs(H, out); genStraights(H, out, true, true); genFulls(H, out); genQuads(H, out); genDragon(H, out); }
    else {
      if (lt === T_SINGLE) genSingles(H, out, g.last.key);
      else if (lt === T_PAIR) genPairs(H, out, g.last.key);
      else if (lt === T_STRAIGHT) genStraights(H, out, true, false);
      else if (lt === T_FULL) genFulls(H, out);
      if (lt !== T_DRAGON) { genQuads(H, out); genStraights(H, out, false, true); }
      genDragon(H, out);
      out = out.filter((c) => beats(c, g.last));
    }
    if (g.first) out = out.filter((c) => c.set[0] & 1);
    if (dingDa(g, p)) { const top = highest(H); out = out.filter((c) => c.type !== T_SINGLE || c.key === top); }
    return out;
  }
  function applyMove(g, c) {
    const p = g.cur;
    if (c.type === T_PASS) g.passed |= 1 << p;
    else {
      const h = g.hand[p];
      for (let r = 0; r < 13; r++) { h[r] &= ~c.set[r]; g.played[r] |= c.set[r]; }
      g.last = c; g.lastP = p; g.first = false; g.nplays++;
      if (isEmpty(h)) { g.winner = p; g.finalPlay = c; return; }
    }
    for (let k = 1; k <= 4; k++) {
      const q = (p + k) & 3;
      if (q === g.lastP) { g.last = PASS(); g.passed = 0; g.cur = q; return; }
      if (!(g.passed >> q & 1)) { g.cur = q; return; }
    }
  }

  // ---- scoring (算分方式) ----
  function loserPoints(h) {
    const n = count(h);
    if (!n) return 0;
    let m = 1;
    if (n >= 10) m *= 2;
    m *= 1 << PC4[h[12]];
    const quad = empty();
    for (let r = 0; r < 13; r++) if (h[r] === 15) { m *= 2; quad[r] = 15; }
    const rest = minus(h, quad);
    for (let s = 0; s < 4; s++) for (let o = 9; o >= 0; o--) {
      let ok = true;
      for (let i = 0; i < 5; i++) if (!(rest[WINR[o][i]] >> s & 1)) { ok = false; break; }
      if (ok) { m *= 2; for (let i = 0; i < 5; i++) rest[WINR[o][i]] &= ~(1 << s); }
    }
    return n * m;
  }
  function winnerMult(c) {
    if (!c) return 1;
    if (c.type === T_DRAGON || c.type === T_QUADS) return 2;
    if (c.type === T_SF) return c.set[12] ? 4 : 2;
    if (c.type === T_SINGLE && (c.key >> 2) === 12) return 2;
    if (c.type === T_PAIR && (c.key >> 2) === 12) return 2;
    if (c.type === T_STRAIGHT && Math.floor(c.key / 4) === 9) return 2;
    if (c.type === T_FULL && c.key === 12) return 2;
    return 1;
  }

  // your points at the end of a hand: the winner takes each loser's points times the winner's last-play multiplier, less
  // the house's 15 %; a loser pays their own
  const RAKE = 0.85;
  function pointsFor(g, p) {
    if (g.winner < 0) return 0;
    const m = winnerMult(g.finalPlay);
    if (g.winner === p) { let s = 0; for (let q = 0; q < 4; q++) if (q !== p) s += loserPoints(g.hand[q]); return RAKE * s * m; }
    return -loserPoints(g.hand[p]) * m;
  }

  // ---- rank-level hand splitting ----
  const countsOf = (H) => H.map((m) => PC4[m]);
  function psSteps(c) { let s = 0; for (let r = 0; r < 13; r++) s += (c[r] >> 1) + (c[r] & 1); return s; }
  function psWeak(c) { let w = 0; for (let r = 0; r < 13; r++) w += ((c[r] >> 1) + (c[r] & 1)) * 3 * (12 - r); return w; }
  // (no2: no full house made with a pair of 2s, for keepPlays: three of a kind whose only pair is the 2s is no combo)
  function listFives(c, no2) {
    const out = [];
    for (let o = 0; o < 10; o++) { let ok = true; for (let i = 0; i < 5; i++) if (!c[WINR[o][i]]) { ok = false; break; } if (ok) out.push([0, o, 0]); }
    for (let t = 0; t < 13; t++) if (c[t] >= 3) for (let p = 0; p < 13; p++) if (p !== t && c[p] >= 2 && !(no2 && p === 12)) out.push([1, t, p]);
    for (let q = 0; q < 13; q++) if (c[q] === 4) {
      let k = -1;
      for (let r = 0; r < 13; r++) if (r !== q && (c[r] & 1)) { k = r; break; }
      if (k < 0) for (let r = 0; r < 13; r++) if (r !== q && c[r]) { k = r; break; }
      if (k >= 0) out.push([2, q, k]);
    }
    return out;
  }
  function fiveApply(c, f, sg) {
    if (f[0] === 0) for (let i = 0; i < 5; i++) c[WINR[f[1]][i]] += sg;
    else if (f[0] === 1) { c[f[1]] += 3 * sg; c[f[2]] += 2 * sg; }
    else { c[f[1]] += 4 * sg; c[f[2]] += sg; }
  }
  const fiveWeak = (f) => (f[0] === 0 ? 4 * (9 - f[1]) : f[0] === 1 ? 3 * (12 - f[1]) : 0);
  const better = (s1, w1, s2, w2) => s1 < s2 || (s1 === s2 && w1 < w2);
  function splitCounts(c0, no2) {
    const c = c0.slice();
    const best = { steps: psSteps(c), weak: psWeak(c), f: [] };
    const A = listFives(c, no2);
    for (const a of A) {
      fiveApply(c, a, -1);
      const s1 = 1 + psSteps(c), w1 = fiveWeak(a) + psWeak(c);
      if (better(s1, w1, best.steps, best.weak)) { best.steps = s1; best.weak = w1; best.f = [a]; }
      const B = listFives(c, no2);
      for (const b of B) {
        fiveApply(c, b, -1);
        const s2 = 2 + psSteps(c), w2 = fiveWeak(a) + fiveWeak(b) + psWeak(c);
        if (better(s2, w2, best.steps, best.weak)) { best.steps = s2; best.weak = w2; best.f = [a, b]; }
        fiveApply(c, b, +1);
      }
      fiveApply(c, a, +1);
    }
    return best;
  }
  // (within one piece of advice the same hands come up again and again in the simulated games: each is split once)
  let SPLIT = null;
  function splitAfter(H, set) {
    if (!SPLIT) return splitHand(minus(H, set));
    let key = 0;
    for (let r = 12; r >= 0; r--) key = key * 5 + PC4[H[r] & ~set[r]];
    let s = SPLIT.get(key);
    if (s === undefined) { s = splitCounts(countsOf(minus(H, set))); if (SPLIT.size < 300000) SPLIT.set(key, s); }
    return s;
  }
  // fn() with the cache on (the advice turns it on for its simulations; it is let go afterwards)
  function withSplitCache(fn) {
    if (SPLIT) return fn();
    SPLIT = new Map();
    try { return fn(); } finally { SPLIT = null; }
  }
  function splitHand(H) {
    if (!SPLIT) return splitCounts(countsOf(H));
    let key = 0;
    for (let r = 12; r >= 0; r--) key = key * 5 + PC4[H[r]];
    let s = SPLIT.get(key);
    if (s === undefined) { s = splitCounts(countsOf(H)); if (SPLIT.size < 300000) SPLIT.set(key, s); }
    return s;
  }

  // ---- could another player beat combo c? (union of unseen cards; bombs ignored) ----
  function beatableBy(c, U) {
    switch (c.type) {
      case T_SINGLE: { const h = highest(U); return h >= 0 && h > c.key; }
      case T_PAIR:
        for (let r = c.key >> 2; r < 13; r++) {
          const m = U[r];
          if (PC4[m] < 2) continue;
          if (r > (c.key >> 2)) return true;
          if (r * 4 + MSB4[m] > c.key) return true;
        }
        return false;
      case T_STRAIGHT: {
        const o0 = Math.floor(c.key / 4);
        for (let o = o0; o < 10; o++) {
          let ok = true;
          for (let i = 0; i < 5; i++) if (!U[WINR[o][i]]) { ok = false; break; }
          if (!ok) continue;
          if (o > o0) return true;
          if (WINTOP[o] * 4 + MSB4[U[WINTOP[o]]] > WINTOP[o] * 4 + (c.key % 4)) return true;
        }
        return false;
      }
      case T_FULL:
        for (let t = c.key + 1; t < 13; t++) if (PC4[U[t]] >= 3) for (let p = 0; p < 13; p++) if (p !== t && PC4[U[p]] >= 2) return true;
        return false;
      case T_QUADS:
        for (let q = c.key + 1; q < 13; q++) if (U[q] === 15) return true;
        return false;
      default: return false;
    }
  }

  // ---- split pieces as card combos ----
  function pieceSingle(H, r) { const s = empty(); const b = CTZ4[H[r]]; s[r] = 1 << b; return mk(s, T_SINGLE, r * 4 + b); }
  function piecePair(H, r) { const m = H[r]; const a = CTZ4[m]; const b = CTZ4[m & ~(1 << a)]; const s = empty(); s[r] = (1 << a) | (1 << b); return mk(s, T_PAIR, r * 4 + b); }
  function pieceFive(H, f) {
    if (f[0] === 0) {
      const s = empty();
      for (let i = 0; i < 5; i++) { const r = WINR[f[1]][i]; s[r] = 1 << CTZ4[H[r]]; }
      let su = -1, flush = true;
      for (let r = 0; r < 13; r++) if (s[r]) { const b = CTZ4[s[r]]; if (su < 0) su = b; else if (b !== su) flush = false; }
      return flush ? mk(s, T_SF, f[1] * 4 + su) : mk(s, T_STRAIGHT, f[1] * 4 + CTZ4[s[WINTOP[f[1]]]]);
    }
    if (f[0] === 1) {
      let t = H[f[1]], p = H[f[2]];
      if (PC4[t] === 4) t &= ~(1 << MSB4[t]);
      while (PC4[p] > 2) p &= ~(1 << MSB4[p]);
      const s = empty(); s[f[1]] = t; s[f[2]] = p;
      return mk(s, T_FULL, f[1]);
    }
    const s = empty(); s[f[1]] = 15; s[f[2]] = 1 << CTZ4[H[f[2]]];
    return mk(s, T_QUADS, f[1]);
  }
  function splitPieces(H, sp) {
    const out = [];
    let rest = H.slice();
    for (const f of sp.f) { const c = pieceFive(rest, f); out.push(c); rest = minus(rest, c.set); }
    for (let r = 0; r < 13; r++) {
      let m = rest[r];
      while (PC4[m] >= 2) { const tmp = empty(); tmp[r] = m; const c = piecePair(tmp, r); out.push(c); m &= ~c.set[r]; }
      if (m) { const tmp = empty(); tmp[r] = m; out.push(pieceSingle(tmp, r)); }
    }
    return out;
  }
  // how many pieces of the split (splitPieces) another player could beat (beatableBy), without making the pieces
  function nonCtrlOf(H, sp, U) {
    let n = 0, rest = H;
    if (sp.f.length) {
      rest = H.slice();
      for (const f of sp.f) { const c = pieceFive(rest, f); if (beatableBy(c, U)) n++; for (let r = 0; r < 13; r++) rest[r] &= ~c.set[r]; }
    }
    const hU = highest(U);
    for (let r = 0; r < 13; r++) {
      let m = rest[r];
      while (PC4[m] >= 2) {
        const a = CTZ4[m], b = CTZ4[m & ~(1 << a)], key = r * 4 + b;
        for (let r2 = r; r2 < 13; r2++) {
          const u = U[r2];
          if (PC4[u] < 2) continue;
          if (r2 > r || r2 * 4 + MSB4[u] > key) { n++; break; }
        }
        m &= ~((1 << a) | (1 << b));
      }
      if (m && hU >= 0 && hU > r * 4 + CTZ4[m]) n++;
    }
    return n;
  }
  function staticStrength(c) {
    switch (c.type) {
      case T_SINGLE: return c.key / 51.0;
      case T_PAIR: return (c.key >> 2) / 12.0;
      case T_STRAIGHT: return Math.floor(c.key / 4) / 9.0;
      case T_FULL: return c.key / 12.0;
      default: return 1.0;
    }
  }

  // ---- policies ----
  const minOpp = (g, p) => { let m = 99; for (let q = 0; q < 4; q++) if (q !== p) m = Math.min(m, count(g.hand[q])); return m; };
  const sameCombo = (a, b) => a.type === b.type && sameSet(a.set, b.set);

  // could hand h beat play `last` with one of the same kind (mode 2: without the rest of h taking more plays)
  function couldBeat(h, last, mode) {
    if (mode !== 2) return beatableBy(last, h);
    const L = [], lt = last.type;
    if (lt === T_SINGLE) genSingles(h, L); else if (lt === T_PAIR) genPairs(h, L);
    else if (lt === T_STRAIGHT) genStraights(h, L, true, false); else if (lt === T_FULL) genFulls(h, L);
    else return false;
    let steps = -1;
    for (const c of L) {
      if (!beats(c, last)) continue;
      if (steps < 0) steps = splitHand(h).steps;
      if (1 + splitHand(minus(h, c.set)).steps <= steps) return true;
    }
    return false;
  }
  function chooseSmart(g, p, L) {
    const H = g.hand[p];
    const lead = g.last.type === T_PASS;
    const mo = minOpp(g, p);
    const nextN = count(g.hand[nextActor(g, p)]);
    const s = splitHand(H);
    const U = unseenOf(H, g.played);
    if (lead) {
      const P = splitPieces(H, s);
      const top = dingDa(g, p) ? highest(H) : -1;
      const legalLead = (c) => (!g.first || (c.set[0] & 1)) && (top < 0 || c.type !== T_SINGLE || c.key === top);
      let bi = -1, bv = 1e9;
      for (let i = 0; i < P.length; i++) {
        if (!legalLead(P[i])) continue;
        let v = staticStrength(P[i]) - 0.01 * count(P[i].set);
        if (!beatableBy(P[i], U)) v += 2.0;
        if (mo <= 2 && P[i].type === T_SINGLE) v += 1.0;
        if (mo === 1 && P[i].type === T_SINGLE) v += 1.0;
        if (v < bv) { bv = v; bi = i; }
      }
      if (P.length <= 2) {
        for (let i = 0; i < P.length; i++) if (!beatableBy(P[i], U) && legalLead(P[i])) return P[i];
      }
      if (bi >= 0) return P[bi];
      let best = -1, bs = 99, bw = 1 << 30;
      for (let j = 0; j < L.length; j++) {
        const s2 = splitAfter(H, L[j].set);
        if (s2.steps < bs || (s2.steps === bs && s2.weak < bw)) { bs = s2.steps; bw = s2.weak; best = j; }
      }
      return L[best];
    }
    let bi = -1;
    for (let i = 0; i < L.length; i++) {
      if (L[i].type !== g.last.type) continue;
      const s2 = splitAfter(H, L[i].set);
      if (s2.steps > s.steps - 1) continue;
      if (bi < 0 || L[i].key < L[bi].key) bi = i;
    }
    const danger = mo <= 2 || count(g.hand[g.lastP]) <= 2 || nextN <= 1;
    if (bi >= 0) {
      const control = !beatableBy(L[bi], U);
      if (L[bi].set[12] && s.steps > 3 && !danger) return PASS();
      if (control && s.steps > 4 && !danger && L[bi].type === T_SINGLE && (L[bi].key >> 2) >= 11) return PASS();
      return L[bi];
    }
    if (danger) {
      let bj = -1;
      for (let i = 0; i < L.length; i++) if (L[i].type === g.last.type && (bj < 0 || L[i].key < L[bj].key)) bj = i;
      if (bj >= 0) return L[bj];
      for (let i = 0; i < L.length; i++) if (isBomb(L[i].type)) return L[i];
    }
    return PASS();
  }

  // weighted features of a candidate play (our strategy); order of FNAMES matches the C++
  const FNAMES = ["steps", "weak", "nonCtrl", "pass", "shed", "mStrength", "mControl", "m2s", "bomb", "pass_x_danger", "pass_x_opp1",
    "leadSingle_x_danger", "leadSingle_x_opp1", "nonCtrl_x_danger", "steps_x_late", "breaks", "lead5", "leadPair", "keepTop", "mControl_x_lead"];
  const NF = FNAMES.length;
  function featuresOf(g, p, m, steps0, U) {
    const f = new Array(NF).fill(0);
    const H = g.hand[p];
    const pass = m.type === T_PASS, lead = g.last.type === T_PASS;
    const H2 = pass ? H : minus(H, m.set);
    const s2 = splitHand(H2);
    const nonCtrl = nonCtrlOf(H2, s2, U);
    const mo = minOpp(g, p);
    const danger = mo <= 2 ? 1 : 0, mo1 = mo === 1 ? 1 : 0;
    const late = Math.max(0, 8 - count(H)) / 8.0;
    f[0] = s2.steps; f[1] = s2.weak / 36.0; f[2] = nonCtrl; f[13] = nonCtrl * danger; f[14] = s2.steps * late;
    const hH2 = highest(H2), hU = highest(U);
    f[18] = (hH2 >= 0 && hU >= 0) ? (hH2 > hU ? 1 : 0) : 0;
    if (pass) { f[3] = 1; f[9] = danger; f[10] = mo1; return f; }
    f[4] = count(m.set);
    f[5] = staticStrength(m);
    const ctrl = !beatableBy(m, U);
    f[6] = ctrl ? 1 : 0;
    f[7] = PC4[m.set[12]];
    f[8] = isBomb(m.type) ? 1 : 0;
    f[15] = Math.max(0, s2.steps - (steps0 - 1));
    if (lead) {
      f[19] = ctrl ? 1 : 0;
      if (m.type === T_SINGLE) { f[11] = danger; f[12] = mo1; }
      if (count(m.set) === 5) f[16] = 1;
      if (m.type === T_PAIR) f[17] = 1;
    }
    return f;
  }
  function candidates(g, p, L) {
    const C = [], seen = new Map();
    const H = g.hand[p];
    for (const m of L) {
      let sig = 0;
      for (let r = 12; r >= 0; r--) sig = sig * 5 + PC4[m.set[r]];
      sig = sig * 8 + m.type;
      if (!seen.has(sig)) { seen.set(sig, C.length); C.push(m); continue; }
      const at = seen.get(sig), o = C[at];
      const cmp = cmpSet(minus(H, m.set), minus(H, o.set));
      if (cmp > 0 || (cmp === 0 && m.key < o.key)) C[at] = m;
    }
    return C;
  }
  function chooseS(g, p, L, w) {
    const C = candidates(g, p, L);
    if (g.last.type !== T_PASS) C.push(PASS());
    const H = g.hand[p];
    const U = unseenOf(H, g.played);
    const steps0 = splitHand(H).steps;
    let bv = -1e18, bi = 0;
    for (let i = 0; i < C.length; i++) {
      const f = featuresOf(g, p, C[i], steps0, U);
      let v = 0;
      for (let k = 0; k < NF; k++) v += w[k] * f[k];
      if (v > bv + 1e-12) { bv = v; bi = i; }
    }
    return C[bi];
  }

  // mulberry32 (same numbers as the C++ Rng32)
  function rng32(seed) {
    let a = seed >>> 0;
    const next = () => { a = (a + 0x6D2B79F5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return (t ^ (t >>> 14)) >>> 0; };
    return { next, below: (n) => Math.floor(next() * n / 4294967296) };
  }

  const P_SIMPLE = 0, P_SMART = 1, P_S = 4, P_PIMC = 5, P_NEST = 6;
  const sizeOf = (c) => (c.type === T_SINGLE ? 1 : c.type === T_PAIR ? 2 : c.type === T_DRAGON ? 13 : c.type === T_PASS ? 0 : 5);
  function choose(g, p, pol) {
    const L = genLegal(g, p);
    if (!L.length) return PASS();
    const nH = count(g.hand[p]);
    if (nH <= 5 || nH === 13) for (const c of L) if (sizeOf(c) === nH) return c;
    if (L.length === 1 && g.last.type === T_PASS) return L[0];
    if (pol.type === P_S) return chooseS(g, p, L, pol.w);
    if (pol.type === P_PIMC) return choosePIMC(g, p, L, pol).card;
    // P_NEST: your own later plays in a simulated game, each worked out by a small simulation of its own (pol.nest:
    // deals, cand) for the first pol.left of them, by the weighted player after that
    if (pol.type === P_NEST) {
      if (pol.left > 0) {
        pol.left--;
        const N = pol.nest;
        return choosePIMC(g, p, L, { type: P_PIMC, nDet: N.deals, maxCand: N.cand, rollType: P_S, w: pol.w, seed: pol.rnd.next(), ev: pol.ev }).card;
      }
      return chooseS(g, p, L, pol.w);
    }
    return chooseSmart(g, p, L);
  }
  function playOut(g, pols) { for (let k = 0; k < 400 && g.winner < 0; k++) applyMove(g, choose(g, g.cur, pols[g.cur])); }

  // Monte Carlo over the unseen cards: for each candidate, how often do I go out first?
  function choosePIMC(g, p, L, pol) { return withSplitCache(() => choosePIMC1(g, p, L, pol)); }
  // the plays to compare (pol.maxCand of them at most: those leaving the fewest plays, PASS and one keeping your 獨大
  // cards) and the weighted player's own pick; single: nothing to compare
  function pimcSetup(g, p, L, pol) {
    let C = candidates(g, p, L);
    if (g.last.type !== T_PASS && !pol.noPass) C.push(PASS());
    const rp = pol.nest ? { type: P_NEST, w: pol.w, nest: pol.nest, left: 0, ev: pol.ev !== false } : { type: pol.rollType, w: pol.w };
    if (C.length === 1) return { C, pref: C[0], single: true };
    const pref = choose(g, p, pol.nest ? { type: P_S, w: pol.w } : rp);
    if (pol.maxCand > 0 && C.length > pol.maxCand) {
      const H = g.hand[p];
      const sc = C.map((c, i) => {
        let v;
        if (c.type === T_PASS) v = -1;
        else { const s2 = splitHand(minus(H, c.set)); v = -s2.steps * 1000 - s2.weak; }
        if (sameCombo(c, pref)) v = 1e9;
        return [v, i];
      });
      sc.sort((a, b) => b[0] - a[0] || a[1] - b[1]);
      const K = [];
      let hasPass = false;
      for (let i = 0; i < pol.maxCand; i++) { K.push(C[sc[i][1]]); if (C[sc[i][1]].type === T_PASS) hasPass = true; }
      if (g.last.type !== T_PASS && !hasPass) K.push(PASS());
      // and the best of the rest by the same order that keeps your 獨大 cards: a play nobody could beat is not it, nor
      // one that takes a card from a piece of the split nobody could beat
      const U0 = unseenOf(H, g.played), boss = splitPieces(H, splitHand(H)).filter((x) => !beatableBy(x, U0));
      const keepsBoss = (c) => c.type !== T_PASS && beatableBy(c, U0) && !boss.some((x) => x.set.some((m, r) => m & c.set[r]));
      if (!K.some(keepsBoss)) for (let i = pol.maxCand; i < sc.length; i++) if (keepsBoss(C[sc[i][1]])) { K.push(C[sc[i][1]]); break; }
      C = K;
    }
    return { C, pref };
  }
  // one deal at a time for plays C from position g (p to play): the unseen cards dealt at random (with pol.passes, see
  // below), each play still in (alive) played out on it; out[i] = { w, s } (went out first, points) or null
  function pimcDealer(g, p, C, pol, rnd) {
    const rp = pol.nest ? { type: P_NEST, w: pol.w, nest: pol.nest, left: 0, ev: pol.ev !== false, rnd } : { type: pol.rollType, w: pol.w };
    const pols = [0, 1, 2, 3].map((q) => (q === p ? rp : { type: P_SMART }));
    const unseen = toIds(unseenOf(g.hand[p], g.played)), cnt = g.hand.map(count);
    // pol.passes [{ q, last }]: the others' passes so far, each on the play it did not beat; a deal giving q a hand that
    // could have beaten it (pol.passMode 2: without splitting anything up) counts pol.passW times as likely (dealt
    // again, up to 30 times, unless kept by that chance)
    const PS = pol.passes && pol.passes.length && pol.passW != null && pol.passW < 1 ? pol.passes : null;
    return (alive) => {
      let base;
      for (let tries = 0; tries < 30; tries++) {
        const deck = unseen.slice();
        for (let i = deck.length - 1; i > 0; i--) { const j = rnd.below(i + 1); const t = deck[i]; deck[i] = deck[j]; deck[j] = t; }
        base = copyGame(g);
        let k = 0;
        for (let q = 0; q < 4; q++) if (q !== p) { const h = empty(); for (let i = 0; i < cnt[q]; i++) { const c = deck[k++]; h[c >> 2] |= 1 << (c & 3); } base.hand[q] = h; }
        if (!PS) break;
        let w = 1;
        for (const x of PS) if (cnt[x.q] && couldBeat(base.hand[x.q], x.last, pol.passMode)) w *= pol.passW;
        if (w >= 1 || rnd.next() / 4294967296 < w) break;
      }
      const out = new Array(C.length).fill(null);
      for (let i = 0; i < C.length; i++) {
        if (!alive[i]) continue;
        const x = copyGame(base);
        applyMove(x, C[i]);
        if (pol.nest) rp.left = pol.nest.depth || 1;
        playOut(x, pols);
        out[i] = { w: x.winner === p ? 1 : 0, s: pointsFor(x, p) };
      }
      return out;
    };
  }
  // `count` deals for plays C (those with alive[i]), from seed: for each play its results deal by deal (vals: the points,
  // or with pol.ev false whether it went out first; + pol.winBonus per win), wins and points in all (several of these
  // run side by side on other threads, see pool.js)
  function pimcRun(g, p, C, pol, seed, count, alive) {
    return withSplitCache(() => {
      const deal = pimcDealer(g, p, C, pol, rng32(seed >>> 0)), X = pol.ev ? pol.winBonus || 0 : 0;
      const vals = C.map(() => []), wins = C.map(() => 0), pts = C.map(() => 0);
      for (let d = 0; d < count; d++) {
        const out = deal(alive);
        for (let i = 0; i < C.length; i++) if (out[i]) { wins[i] += out[i].w; pts[i] += out[i].s; vals[i].push(pol.ev ? out[i].s + X * out[i].w : out[i].w); }
      }
      return { vals, wins, pts };
    });
  }
  function choosePIMC1(g, p, L, pol) {
    const su = pimcSetup(g, p, L, pol);
    let C = su.C;
    const pref = su.pref;
    if (su.single) return { card: C[0], stats: [{ card: C[0], wins: 0, n: 0 }], pref: C[0] };
    const wins = new Array(C.length).fill(0), pts = new Array(C.length).fill(0), n = new Array(C.length).fill(0), alive = C.map(() => true);
    const rnd = rng32(pol.seed >>> 0);
    const deal = pimcDealer(g, p, C, pol, rnd);
    // pol.adapt { z, min, max, batch, budget }: deals in batches; from `min` deals on, a play falls out once it is behind
    // the leader by more than z standard errors of the difference on the same deals; stop when one is left, at `max`
    // deals, or after `budget` ms. Else exactly pol.nDet deals for every play.
    const A = pol.adapt, nMax = A ? A.max : pol.nDet;
    const V = A ? C.map(() => new Float32Array(nMax)) : null;
    // the aim: going out first (pol.ev false), or the points (pol.ev), with pol.winBonus more points counted for going
    // out first (兼顧: when the points are close, the play that goes out first more often)
    const X = pol.ev ? pol.winBonus || 0 : 0;
    const mean = (i) => (pol.ev ? pts[i] + X * wins[i] : wins[i]) / Math.max(1, n[i]);
    const t0 = Date.now();
    for (let d = 0; d < nMax; d++) {
      const out = deal(alive);
      for (let i = 0; i < C.length; i++) {
        if (!out[i]) continue;
        const w = out[i].w, s = out[i].s;
        wins[i] += w; pts[i] += s;
        if (V) V[i][n[i]] = pol.ev ? s + X * w : w;
        n[i]++;
      }
      if (A && (d + 1) % A.batch === 0 && d + 1 >= A.min) {
        let b = -1;
        for (let i = 0; i < C.length; i++) if (alive[i] && (b < 0 || mean(i) > mean(b))) b = i;
        for (let i = 0; i < C.length; i++) {
          if (!alive[i] || i === b) continue;
          const m = n[i];   // (both still in: played on the same deals)
          let s1 = 0, s2 = 0;
          for (let j = 0; j < m; j++) { const dd = V[b][j] - V[i][j]; s1 += dd; s2 += dd * dd; }
          const md = s1 / m, se = Math.sqrt(Math.max(1e-12, s2 / m - md * md) / m);
          if (md > A.z * se) alive[i] = false;
        }
        if (alive.filter(Boolean).length === 1 || Date.now() - t0 > A.budget) break;
      }
    }
    // the aim: how often you go out first, or (pol.ev) the points you win or lose on average (+ pol.winBonus per win)
    let bi = -1;
    for (let i = 0; i < C.length; i++) if (alive[i] && (bi < 0 || mean(i) > mean(bi))) bi = i;
    for (let i = 0; i < C.length; i++) if (alive[i] && mean(i) === mean(bi) && sameCombo(C[i], pref)) { bi = i; break; }
    return { card: C[bi], stats: C.map((c, i) => ({ card: c, wins: wins[i], pts: pts[i] / Math.max(1, n[i]), n: n[i], out: !alive[i] })), pref, ms: Date.now() - t0, deals: Math.max(...n) };
  }

  // ---- 散牌優先: which plays to choose from (the simulation then picks among them) ----
  // Danger: another seat could go out in at most three plays (its count made of 1, 2 and 5-card plays, say 10 = 5+5
  // or 11 = a 2 + 5 + 5), each size to be found among the cards not seen, and when it takes two or three plays one of
  // them a play you cannot beat (獨大 in that seat's hand, so it keeps the lead). In danger: the plays with a 2 first,
  // else those shedding the most cards, and no PASS while you can play. Otherwise, with a play to beat (not your lead):
  // only your hand's leftover singles (散牌) on a single, only whole pieces of your best split on a pair or 5-card play,
  // or PASS; your combinations stay whole for when you have the lead. Your lead: every play.
  // opt.danger false: no danger rule. Returns { L, danger: [seats], noPass }.
  // 只顯示最大牌's own advice, without simulating: the hand split into the fewest plays (splitHand); leading, the smallest
  // of the split's plays with the most cards; on someone's play, the smallest play that beats it without the rest of
  // the hand taking more plays than before (else PASS)
  // the plays of L after which the rest of hand H still takes no more plays than before (splitHand): nothing split up
  // (神幣優先 keeps to them unless someone is down to `free` cards or fewer: then anything goes)
  const anyLow = (g, p, free) => [0, 1, 2, 3].some((q) => q !== p && count(g.hand[q]) > 0 && count(g.hand[q]) <= free);
  // (two: a play with a 2 in it is always allowed)
  // (a full house whose pair is the 2s does not count as a combo: its three of a kind is a pair and a single)
  const keepSteps = (H) => splitCounts(countsOf(H), true).steps;
  function keepPlays(H, L, two) {
    const steps = keepSteps(H);
    return L.filter((c) => c.type !== T_PASS && ((two && c.set[12]) || 1 + keepSteps(minus(H, c.set)) <= steps));
  }
  // 神幣優先: the simulation's pick (card, over its stats) swapped for a play that splits nothing up (keepPlays without
  // the 2s; PASS counts) when that one is within `close` points a game of it
  function preferKeep(H, stats, card, close) {
    const keeps = (c) => c.type === T_PASS || keepPlays(H, [c], false).length > 0;
    if (keeps(card)) return card;
    const top = stats.find((x) => x.card === card);
    if (!top) return card;
    const ok = stats.filter((x) => x.n > 0 && keeps(x.card) && x.pts >= top.pts - close);
    return ok.length ? ok.reduce((a, b) => (b.pts > a.pts ? b : a)).card : card;
  }
  function ruleChoice(g, p, L) {
    const H = g.hand[p], sp = splitHand(H), pieces = splitPieces(H, sp);
    const small = (list) => (list.length ? list.reduce((a, b) => (beats(a, b) ? b : a)) : null);
    const plays = L.filter((c) => c.type !== T_PASS);
    let card = null;
    if (g.last.type === T_PASS) {
      const ok = pieces.map((x) => plays.find((c) => sameCombo(c, x))).filter(Boolean);
      const most = Math.max(0, ...ok.map(sizeOf));
      card = small(ok.filter((c) => sizeOf(c) === most)) || small(plays);
    } else {
      card = small(keepPlays(H, plays, false));
    }
    return { card: card || PASS(), pieces, steps: sp.steps };
  }
  function looseChoice(g, p, L, opt) {
    opt = opt || {};
    const H = g.hand[p], U = unseenOf(H, g.played);
    const lead = g.last.type === T_PASS;
    const best = (list) => (list.length ? list.reduce((a, b) => (beats(b, a) ? b : a)) : null);
    const of = (gen) => { const o = []; gen(o); return o; };
    const Uplays = { 1: of((o) => genSingles(U, o)), 2: of((o) => genPairs(U, o)), 5: of((o) => { genStraights(U, o, true, true); genFulls(U, o); genQuads(U, o); }) };
    const Hplays = { 1: of((o) => genSingles(H, o)), 2: of((o) => genPairs(H, o)), 5: of((o) => { genStraights(H, o, true, true); genFulls(H, o); genQuads(H, o); }) };
    const bombs = of((o) => { genQuads(H, o); genStraights(H, o, false, true); });
    const boss = { 1: false, 2: false, 5: false };
    for (const n of [1, 2, 5]) { const u = best(Uplays[n]); boss[n] = !!u && !Hplays[n].concat(bombs).some((c) => beats(c, u)); }
    // the ways to make n cards of at most three plays
    const ways = [];
    for (const a of [1, 2, 5]) { ways.push([a]); for (const b of [1, 2, 5]) { if (b < a) continue; ways.push([a, b]); for (const c of [1, 2, 5]) if (c >= b) ways.push([a, b, c]); } }
    const danger = [];
    if (opt.danger !== false) for (let q = 0; q < 4; q++) {
      if (q === p) continue;
      const n = count(g.hand[q]);
      if (n && ways.some((w) => w.reduce((x, y) => x + y, 0) === n && w.every((k) => Uplays[k].length) && (w.length === 1 || w.some((k) => boss[k])))) danger.push(q);
    }
    if (danger.length) {
      const with2 = L.filter((c) => c.set[12]);
      if (with2.length) return { L: with2, danger, noPass: true };
      const most = Math.max(...L.map((c) => count(c.set)));
      return { L: L.filter((c) => count(c.set) === most), danger, noPass: true };
    }
    if (lead) return { L, danger, noPass: false };
    const pieces = splitPieces(H, splitHand(H));
    const isPiece = (c) => pieces.some((x) => x.type === c.type && sameSet(x.set, c.set));
    return { L: L.filter((c) => isPiece(c)), danger, noPass: false };
  }

  const api = { T_PASS, T_SINGLE, T_PAIR, T_STRAIGHT, T_FULL, T_QUADS, T_SF, T_DRAGON, TNAME, RANKS, SUITS, name, WINR, WINTOP,
    empty, fromIds, toIds, count, lowest, highest, minus, isEmpty, sameSet, has, unseenOf, beats, PASS, isBomb,
    genLegal, applyMove, newGame, copyGame, nextActor, dingDa, loserPoints, winnerMult, pointsFor, splitHand, splitPieces, beatableBy,
    chooseSmart, chooseS, choosePIMC, pimcSetup, pimcRun, looseChoice, ruleChoice, keepPlays, anyLow, preferKeep, couldBeat, choose, playOut, candidates, featuresOf, FNAMES, rng32, P_SMART, P_S, P_PIMC, sameCombo, staticStrength,
    genSingles, genPairs, genStraights, genFulls, genQuads, genDragon, splitCounts, cmpSet, withSplitCache };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  else root.Big2 = api;
})(typeof self !== "undefined" ? self : this);
