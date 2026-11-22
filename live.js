// 大老二小助手：把一張張讀到的畫面變成牌局。
// Readings come in every second or so (B2Read.readShot on a frame of the shared screen). A reading is used once two in a
// row agree and nothing is moving on the table, and only when it shows something new; the game so far is kept by
// B2State.apply (the same tracker as the screenshot version, told that it is reading live). At your turn the advice is
// worked out from it: the cards still unseen, every seat's count, and the play to beat.
(function (root) {
  "use strict";
  const B = root.Big2 || (typeof require !== "undefined" ? require("./engine.js") : null);
  const ST = root.B2State || (typeof require !== "undefined" ? require("./state.js") : null);
  const DISP_MS = 9000;          // a single read off the large display counts for this long
  const BUSY_MS = 4000;          // the table counts as moving for at most this long (then it is read anyway)
  const ODD_N = 4;               // a hand that does not fit the one before is taken after this many readings agree on it
  const WAIT_N = 1;              // at your turn, readings to wait for every count to be read (1: none, the plays shown large say who played)

  const sameList = (a, b) => a.length === b.length && a.every((c, i) => c === b[i]);
  // two readings of the same moment of the game (a count not read, or a single on the table not read surely, in one of
  // them matches anything)
  function agree(a, b) {
    if (!a || !b || !a.ok || !b.ok) return false;
    if (!sameList(a.guess, b.guess) || a.myTurn !== b.myTurn) return false;
    for (let q = 1; q <= 3; q++) {
      if (a.pass[q] !== b.pass[q]) return false;
      if (a.counts[q] != null && b.counts[q] != null && a.counts[q] !== b.counts[q]) return false;
    }
    if (a.pile.n !== b.pile.n) return false;
    if (a.pile.sure && b.pile.sure && a.pile.card !== b.pile.card) return false;
    return true;
  }
  // does reading a show anything the last reading used did not? At your turn only what decides the advice counts
  // (your cards, the counts, the PASS signs), so the advice does not change while you look at it.
  function news(a, b) {
    if (!b) return true;
    if (!sameList(a.guess, b.guess) || a.myTurn !== b.myTurn) return true;
    for (let q = 1; q <= 3; q++) {
      if (a.pass[q] !== b.pass[q]) return true;
      if (a.counts[q] != null && a.counts[q] !== b.counts[q]) return true;
    }
    if (a.myTurn) return false;
    if (a.pile.n !== b.pile.n) return true;
    if (a.pile.sure && a.pile.card !== (b.pile.sure ? b.pile.card : null)) return true;
    return false;
  }
  // the table is moving: a play shown large with nothing readable on the pile yet
  const busyOf = (r) => !!(r && r.pile && r.pile.busy);

  function create() {
    const L = { S: ST.blank(), ring: [], lastO: null, waitCount: 0, seen: [], shows: [], handT: null, disp: [null, null, null, null], busySince: 0, odd: null, swapMode: false };

    function noteDisplays(r, now) {
      const ds = (r && r.pile && r.pile.displays) || [];
      for (const d of ds) {
        if (!(d.seat >= 1 && d.seat <= 3)) continue;
        L.disp[d.seat] = d.card != null && d.sure ? { card: d.card, at: now } : null;
      }
    }
    function dispFor(now) {
      const o = [null, null, null, null];
      for (let q = 1; q <= 3; q++) if (L.disp[q] && now - L.disp[q].at < DISP_MS) o[q] = L.disp[q].card;
      return o;
    }

    // ---------- singles on the table ----------
    // A single read surely on the table is a played card, whatever else is still moving (a new card often shows clearly
    // for only a moment before the next one covers it). It is matched to a play of one card seen as a count going down,
    // in the order both came and close in time (the count can be hidden for a moment by the card shown large).
    const MATCH_BEFORE = 6000, MATCH_AFTER = 3000;
    const mine = () => { const m = new Set(L.S.my || []); for (const e of L.S.events) if (e.k === "play") for (const c of e.c) m.add(c); return m; };
    function noteSingle(r, now) {
      const p = r && r.pile, c = p && p.n === 1 && p.sure && p.cards && p.cards.length === 1 ? p.cards[0] : null;
      if (c == null || L.seen.some((x) => x.card === c) || mine().has(c)) return;
      L.seen.push({ card: c, at: now, used: false, show: L.shows.some((x) => x.cards.includes(c)) });
      if (!L.S.played.includes(c)) L.S.played.push(c);
      match(now);
    }
    // plays shown large at a seat: who played which cards (each is seen in a reading or two; kept once)
    const SHOW_SAME = 2500, SHOW_PAIR = 3500;
    function noteShows(r, now) {
      const my = mine();
      for (const sh of (r && r.shows) || []) {
        if (!sh.sure || !ST.classify(sh.cards) || sh.cards.some((c) => my.has(c))) continue;
        const key = sh.seat + ":" + sh.cards.slice().sort((a, b) => a - b).join(",");
        // the same play seen again (or read a little differently a moment later)
        if (L.shows.some((x) => x.key === key || (x.seat === sh.seat && now - x.at < SHOW_SAME && x.cards.length === sh.cards.length && x.cards.filter((c) => sh.cards.includes(c)).length * 2 >= sh.cards.length))) continue;
        L.shows.push({ key, seat: sh.seat, cards: sh.cards.slice(), at: now, used: false });
        for (const c of sh.cards) if (!L.S.played.includes(c)) L.S.played.push(c);
        // a single seen on the table too is the same card
        for (const x of L.seen) if (sh.cards.includes(x.card)) x.show = true;
      }
      match(now);
    }
    function match(now) {
      const S = L.S, my = mine();
      // first the plays shown large: a count going down by as many cards at the same seat, close in time. A play shown
      // large with no count seen going down (the badge hidden, or not readable at one card left) counts by itself: the
      // seat's count goes down by it now, so the badge read later shows nothing new.
      for (const x of L.shows) {
        if (x.used) continue;
        const e = S.events.find((y) => y.k === "count" && y.s === x.seat && y.n === x.cards.length && !y.byShow && y.t != null && Math.abs(y.t - x.at) <= SHOW_PAIR);
        if (e) {
          if (e.c) for (const c of e.c) { const z = L.seen.find((w) => w.card === c); if (z && !x.cards.includes(c)) z.used = false; }
          e.c = x.cards.slice(); e.byShow = true; x.used = true;
          for (const c of x.cards) { const z = L.seen.find((w) => w.card === c); if (z) z.used = true; }
        } else if (now != null && S.my && S.counts[x.seat] >= x.cards.length) {
          S.counts[x.seat] -= x.cards.length; S.countAt[x.seat] = S.shots;
          S.events.push({ k: "count", s: x.seat, n: x.cards.length, c: x.cards.slice(), at: S.shots, t: x.at, byShow: true, fromShow: true, pend: true });
          x.used = true;
        }
      }
      for (const x of L.seen) if (my.has(x.card)) x.used = true;
      let cycle = 0, last = -Infinity;
      const drops = [];
      for (const e of S.events) {
        if (e.k === "turn" || e.k === "play") cycle++;
        if (e.k === "count" && e.n === 1) { if (e.c) { const x = L.seen.find((y) => y.card === e.c[0]); if (x && x.at > last) last = x.at; } else if (e.t != null) drops.push({ e, cycle }); }
      }
      drops.sort((a, b) => a.e.t - b.e.t || a.cycle - b.cycle || a.e.s - b.e.s);
      for (const d of drops) {
        const x = L.seen.find((y) => !y.used && !y.show && y.at >= last && y.at >= d.e.t - MATCH_BEFORE && y.at <= d.e.t + MATCH_AFTER);
        if (!x) continue;
        d.e.c = [x.card]; x.used = true; last = x.at;
        if (!S.played.includes(x.card)) S.played.push(x.card);
      }
    }

    // ---------- 換牌局 ----------
    // In a swap game every deal starts with each seat swapping 0 to 3 cards. Until the first play of the deal the swap is
    // open: your row changing by up to 3 cards is the swap (not a new deal), cards taken out of your row while choosing
    // are not a play, and play buttons on screen belong to the swap, except when you hold ♣3 (you lead first) and the swap
    // is over: your row has changed, there was nothing to swap, or SWAP_WAIT has passed.
    const SWAP_WAIT = 12000;
    const playsSeen = (S) => S.events.some((e) => e.k === "play" || e.k === "count") || L.shows.length > 0;
    const swapOpen = () => { const S = L.S; return !!(L.swapMode && S.swap && S.my && !playsSeen(S)); };
    function swapHold(now) {
      const S = L.S, w = S.swap;
      if (!swapOpen()) return false;
      if (!S.my.includes(0)) return true;
      return !w.got && !(w.adv && !w.adv.length) && now - w.t0 < SWAP_WAIT;
    }
    // the swap as it stands: { phase: "choose" | "done", hand0, gave, got, adv } while it is open, else null
    function swapInfo() {
      if (!swapOpen()) return null;
      const w = L.S.swap;
      return { phase: w.got ? "done" : "choose", hand0: w.hand0.slice(), gave: w.gave, got: w.got, adv: w.adv, t0: w.t0 };
    }
    // the swap of a deal just dealt: 13 cards each and nothing played yet (also when swap games are turned on then)
    function startSwap(now) {
      const S = L.S;
      if (!L.swapMode || !S.my || S.my.length !== 13 || playsSeen(S) || ![1, 2, 3].every((q) => S.counts[q] === 13)) return false;
      L.S = Object.assign({}, S, { swap: { hand0: S.my.slice(), t0: now, adv: null, gave: null, got: null } });
      return true;
    }
    // the advice the page gave for the swap (cards to swap; [] to keep them all)
    function setSwapAdvice(hand0, ids) {
      const w = L.S.swap;
      if (w && sameList(w.hand0, hand0)) L.S = Object.assign({}, L.S, { swap: Object.assign({}, w, { adv: ids.slice() }) });
    }

    // one reading; returns { status, why?, turn?, notes?, swapStart?, swapDone? }
    // status: applied | same | settling | busy | unread | odd | err | swapping
    function process(r, now) {
      now = now == null ? Date.now() : now;
      noteDisplays(r, now);
      noteShows(r, now);
      noteSingle(r, now);
      // during the swap, buttons on screen are the swap's
      const hold = !!(r && r.myTurn && swapHold(now));
      if (hold) r = Object.assign({}, r, { myTurn: false, noPlay: false });
      // the game says nothing of yours beats the table: its message covers your row, which is the row you had (and
      // none of it lit)
      if (r && r.noPlay && r.myTurn && L.S.my && !r.raised) r = Object.assign({}, r, { hand: { cards: L.S.my.slice(), sure: L.S.my.map(() => true), lit: L.S.my.map(() => false), geoOk: true, n: L.S.my.length, why: "" } });
      let o = ST.observe(r);
      // your row found but some of its cards hidden (say, by the game's message over it) while it still has as many cards
      // as you had: the cards you had
      if (!o.ok && r && r.hand && r.hand.cards && !r.raised && L.S.my && r.hand.n === L.S.my.length && r.hand.geoOk) {
        const h = r.hand, r2 = Object.assign({}, r, { hand: Object.assign({}, h, { cards: L.S.my.slice(), sure: L.S.my.map(() => true), lit: h.lit && h.lit.length === L.S.my.length ? h.lit : L.S.my.map(() => true) }) });
        const o2 = ST.observe(r2);
        if (o2.ok) { r = r2; o = o2; }
      }
      if (!o.ok) { L.ring = []; return { status: "unread", why: o.why, raised: !!(r && r.raised), hold }; }
      // choosing what to swap: cards taken out of your row are not played (nobody has played yet)
      if (swapOpen() && !L.S.swap.got && !o.myTurn && o.guess.length < 13 && o.guess.length >= 10 && o.guess.every((c) => L.S.swap.hand0.includes(c))
          && [1, 2, 3].every((q) => o.counts[q] == null || o.counts[q] === 13) && !L.S.events.some((e) => e.k === "turn")) return { status: "swapping", hold };
      // when your hand was last seen as it was (your play, when it comes, is after that)
      if (L.S.my && sameList(o.guess, L.S.my)) L.handT = now;
      if (busyOf(r)) {
        if (!L.busySince) L.busySince = now;
        if (now - L.busySince < BUSY_MS) { L.ring = []; return { status: "busy" }; }
      } else L.busySince = 0;
      // settled: the same reading came up before among the last few (one odd reading in between does not matter)
      // the first reading of your turn with your hand as it was: used at once (the play to beat is known by then from
      // what was shown large and the counts); everything else waits for a second reading that agrees
      const quick = o.myTurn && !L.S.round && L.S.my && sameList(o.guess, L.S.my) && L.lastO && !L.lastO.myTurn;
      const stable = quick || L.ring.some((p) => agree(o, p));
      L.ring.push(o); if (L.ring.length > 4) L.ring.shift();
      if (!stable) return { status: "settling", hold };
      if (!news(o, L.lastO)) return { status: "same", turn: !!L.S.round, hold };
      // your turn with someone's count not read (and no PASS sign over it): wait a reading or two for it, since it says
      // who played last
      if (o.myTurn && [1, 2, 3].some((q) => o.counts[q] == null && !o.pass[q]) && ++L.waitCount < WAIT_N) return { status: "settling", why: "等看清楚各家張數" };
      L.waitCount = 0;
      // a hand that does not fit the cards you had: a misreading, unless it keeps coming back (a new hand of 13 is fine)
      if (L.S.my && o.guess.length !== 13 && !ST.align(L.S.my, L.S.guess, o.guess, o.sure)) {
        const k = o.guess.join(",");
        L.odd = L.odd && L.odd.k === k ? { k, n: L.odd.n + 1 } : { k, n: 1 };
        if (L.odd.n < ODD_N) return { status: "odd", why: "手牌和之前的對不起來" };
      }
      L.odd = null;
      // the swap: your row of 13 now differs from the one dealt by up to 3 cards (back to the one dealt: an earlier
      // misreading)
      let swapDone = null;
      if (swapOpen() && o.guess.length === 13 && o.sure.every(Boolean) && !sameList(o.guess, L.S.my)) {
        const w = L.S.swap, got = o.guess.filter((c) => !w.hand0.includes(c));
        if (got.length <= 3) {
          const gave = w.hand0.filter((c) => !o.guess.includes(c));
          L.S = Object.assign({}, L.S, { my: o.guess.slice(), hand0: o.guess.slice(), guess: [], swap: Object.assign({}, w, got.length ? { gave, got, at: now } : { gave: null, got: null }) });
          if (got.length) swapDone = { gave, got };
        }
      }
      const deal0 = L.S.deal;
      const newest = L.seen.length ? L.seen[L.seen.length - 1] : null;
      const recent = newest && !newest.used && now - newest.at < 6000 ? newest.card : null;
      const lastShow = L.shows.length ? L.shows[L.shows.length - 1] : null;
      const show = lastShow && !lastShow.used && now - lastShow.at < MATCH_BEFORE ? { seat: lastShow.seat, cards: lastShow.cards } : null;
      const out = ST.apply(L.S, r, { live: true, disp: dispFor(now), recent, show, handT: L.handT });
      if (out.err) return { status: "err", why: out.err };
      const S = out.S;
      // a display that was used up (that seat's count went down) is forgotten
      for (const e of S.events) if (e.at === S.shots && e.k === "count") { L.disp[e.s] = null; if (e.t == null) e.t = now; }
      L.S = S; L.lastO = o;
      if (S.deal !== deal0) { L.seen = []; L.shows = []; }
      // the singles seen so far are played cards; match them to the plays
      for (const x of L.seen) if (!S.played.includes(x.card) && !(S.my || []).includes(x.card)) S.played.push(x.card);
      for (const x of L.shows) for (const c of x.cards) if (!S.played.includes(c) && !(S.my || []).includes(c)) S.played.push(c);
      match(now);
      // a swap game: a deal just dealt (13 cards each, nothing played) starts its swap
      const swapStart = !S.swap && startSwap(now);
      return { status: "applied", turn: !!S.round, notes: out.notes, swapStart, swapDone, hold };
    }

    // ---------- the advice ----------
    function hash(str) { let h = 0x811c9dc5; for (let i = 0; i < str.length; i++) { h ^= str.charCodeAt(i); h = Math.imul(h, 16777619) >>> 0; } return h >>> 0; }
    const recKey = () => { const S = L.S; return JSON.stringify([S.deal, S.shots, S.my, S.counts, S.played, S.round]); };
    // the turn as it matters for the advice: your hand, and leading or the play to beat
    const turnKey = () => { const S = L.S, R = S.round; return R ? JSON.stringify([S.deal, S.my, R.lead, R.top && [R.top.s, R.top.n, R.top.c, R.top.eff]]) : null; };
    // the same position always gives the same advice (the random deals start from the position, not the moment)
    const posSeed = () => { const S = L.S; return hash(JSON.stringify([turnKey(), S.counts, B.toIds(B.fromIds(S.played)), S.round && S.round.passed])); };
    // the plays you can make: what beats the play on the table, using only cards the game has lit up. An unread play on
    // the table could be any of the plays that light up your cards this way: what beats the strongest of them is sure to
    // be allowed; only if nothing does, what beats the weakest (the advice then says it may not be enough).
    function legal(g, R, lit) {
      const vs = (t) => { const g2 = B.copyGame(g); g2.last = { type: t.type, key: t.key, set: B.empty() }; return B.genLegal(g2, 0); };
      const on = !R.lead && lit && lit.length === L.S.my.length ? new Set(L.S.my.filter((c, i) => lit[i])) : null;
      const litOnly = (A) => (on ? A.filter((c) => B.toIds(c.set).every((x) => on.has(x))) : A);
      if (on && !on.size) return { L: [], byLit: true };
      let A = B.genLegal(g, 0), risky = false;
      if (!R.lead && R.top && !R.top.c && R.top.hi) {
        A = litOnly(vs(R.top.hi));
        if (!A.length && R.top.lo) { A = litOnly(vs(R.top.lo)); risky = A.length > 0; }
        return { L: A, byLit: !!on, risky };
      }
      const Af = litOnly(A);
      return Af.length ? { L: Af, byLit: Af.length < A.length } : { L: A, byLit: false };
    }
    function advise(opts) {
      opts = opts || {};
      const S = L.S, R = S.round, g = ST.position(S);
      if (!g || !R) return null;
      const { L: Lg, byLit, risky } = legal(g, R, S.view && S.view.lit);
      if (!Lg.length) return { kind: "none", card: B.PASS(), g, byLit };
      // going out now: with the play that doubles the others' payment if there is one
      const outs = Lg.filter((c) => B.isEmpty(B.minus(g.hand[0], c.set)));
      if (outs.length) return { kind: "finish", card: outs.reduce((a, b) => (B.winnerMult(b) > B.winnerMult(a) ? b : a)), g, risky };
      if (Lg.length === 1 && g.last.type === B.T_PASS) return { kind: "forced", card: Lg[0], g };
      const W = opts.W || (root.B2_MODELS && root.B2_MODELS.W);
      const ev = opts.ev !== false;
      const r = B.choosePIMC(g, 0, Lg, { type: B.P_PIMC, nDet: opts.nDet || 200, maxCand: opts.maxCand || 8, rollType: B.P_S, w: W, seed: posSeed(), ev });
      const stats = r.stats.filter((x) => x.n > 0).sort((a, b) => (ev ? b.pts - a.pts : b.wins - a.wins));
      return { kind: stats.length > 1 ? "sim" : "only", card: r.card, stats, g, byLit, ev, risky: risky && r.card.type !== B.T_PASS };
    }

    function reset() { L.S = ST.blank(); L.ring = []; L.lastO = null; L.waitCount = 0; L.seen = []; L.shows = []; L.disp = [null, null, null, null]; L.busySince = 0; L.odd = null; }
    function restore(S) { if (S && S.v === 2) { L.S = S; L.lastO = null; L.ring = []; } }
    const setSwapMode = (on) => { L.swapMode = !!on; };
    return { process, advise, reset, restore, recKey, turnKey, setSwapMode, swapInfo, setSwapAdvice, startSwap, get S() { return L.S; } };
  }

  const api = { create, agree, news };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  else root.B2Live = api;
})(typeof self !== "undefined" ? self : this);
