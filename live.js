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
  const PLAY_WAIT = 6000;        // cards gone from your row that make no hand: taken only after they stay gone this long
  const RESYNC_GAP = 20000;      // a row that does not fit is put right within the deal only this soon after the last reading
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
    const L = { S: ST.blank(), ring: [], lastO: null, waitCount: 0, seen: [], shows: [], handT: null, disp: [null, null, null, null], busySince: 0, odd: null, swapMode: false, bad: [], lastApplied: null };

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
        L.shows.push({ key, seat: sh.seat, cards: sh.cards.slice(), at: now, used: false, marks: sh.marks || null });
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
      // A count at the same seat going down close in time by a different number of cards is the same play. Shown large
      // as fewer cards: read short there (a rank mark lost); the count says how many cards it was, the cards read are
      // part of it, and the play shown large is not used (it would count the play twice). Shown large as more cards (a
      // whole play of 2 or 5 read surely is hard to get by mistake): the count was seen part way, or was not a play;
      // the play shown large stands, the count going down by it.
      for (const x of L.shows) {
        if (x.used) continue;
        const near = (y) => y.k === "count" && y.s === x.seat && !y.byShow && y.t != null && Math.abs(y.t - x.at) <= SHOW_PAIR;
        const e = S.events.find((y) => near(y) && y.n === x.cards.length);
        const odd = e ? null : S.events.find((y) => near(y) && y.n !== x.cards.length);
        if (e) {
          if (e.c) for (const c of e.c) { const z = L.seen.find((w) => w.card === c); if (z && !x.cards.includes(c)) z.used = false; }
          e.c = x.cards.slice(); e.byShow = true; x.used = true;
          for (const c of x.cards) { const z = L.seen.find((w) => w.card === c); if (z) z.used = true; }
        } else if (odd && x.cards.length < odd.n) {
          x.used = true; x.odd = true;
          if (!odd.c) odd.part = x.cards.slice();
          L.bad.push({ seat: x.seat, cards: x.cards.slice(), n: odd.n, marks: x.marks });
        } else if (odd && S.counts[x.seat] >= x.cards.length - odd.n) {
          if (odd.c) for (const c of odd.c) { const z = L.seen.find((w) => w.card === c); if (z && !x.cards.includes(c)) z.used = false; }
          S.counts[x.seat] -= x.cards.length - odd.n; S.countAt[x.seat] = S.shots;
          odd.n = x.cards.length; odd.c = x.cards.slice(); odd.byShow = true; x.used = true;
          for (const c of x.cards) { const z = L.seen.find((w) => w.card === c); if (z) z.used = true; }
          L.bad.push({ seat: x.seat, cards: x.cards.slice(), n: x.cards.length, long: true, marks: x.marks });
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
    // In a swap game every deal starts with each seat swapping 0 to 3 cards: the cards chosen leave the rows (yours gets
    // shorter, the others' counts go down by up to 3), are shuffled together and dealt back. While the swap is on, what
    // moves on screen is the swap, not plays: readings go to the tracker as if nothing moved (your row as it was, every
    // count 13), and play buttons on screen are the swap's unless you hold ♣3 (you lead first). Your row of 13 changing
    // by up to 3 cards is your swap, not a new deal. The swap is over once everything is back to 13 after something
    // moved, or a play is shown large, a count goes down by more than 3, your turn comes for real, or nothing has moved
    // for SWAP_QUIET (nobody swapped), something moved but never came back for SWAP_STUCK (it was a play), or SWAP_MAX.
    const SWAP_WAIT = 12000, SWAP_QUIET = 30000, SWAP_STUCK = 20000, SWAP_MAX = 45000;
    const SKEY = [null, "right", "top", "left"];
    const playsSeen = (S) => S.events.some((e) => e.k === "play" || e.k === "count") || L.shows.length > 0;
    const swapOpen = () => { const S = L.S; return !!(L.swapMode && S.swap && !S.swap.closed && S.my && !S.events.some((e) => e.k === "play" || e.k === "count")); };
    const patchSwap = (p) => { L.S = Object.assign({}, L.S, { swap: Object.assign({}, L.S.swap, p) }); };
    function swapHold(now) {
      const S = L.S, w = S.swap;
      if (!swapOpen()) return false;
      if (!S.my.includes(0)) return true;
      // you lead first: the buttons are yours once the swap is over (it closes the swap), or when nothing has moved for a
      // while (nobody swapping; the game's swap takes about this long)
      return w.moved ? now - w.t0 < SWAP_MAX : now - w.t0 < SWAP_WAIT;
    }
    function closeSwap(why, now) { patchSwap({ closed: true, why, end: now }); return `換牌結束（${why}）`; }
    // a reading during the swap: the swap over, or the reading as if nothing moved; returns { r, note }
    function swapFilter(r, now) {
      if (!swapOpen() || !r || !r.hand || !r.hand.cards || r.raised) return { r, note: null };
      const w = L.S.swap, my = L.S.my, row = r.hand.cards;
      const seat = (q) => r.seats && r.seats[SKEY[q]];
      const cnt = (q) => { const x = seat(q); return x && x.count != null && x.p >= 0.55 && !(x.pass && q !== 2) ? x.count : null; };
      const counts = [null, cnt(1), cnt(2), cnt(3)];
      const short = row.length >= 10 && row.length < 13 && (row.every((c) => w.hand0.includes(c)) || row.every((c) => my.includes(c)));
      const down = [1, 2, 3].filter((q) => counts[q] != null && counts[q] >= 10 && counts[q] < 13);
      let why = null;
      if (L.shows.some((x) => x.at >= w.t0)) why = "有人出牌了";
      else if (counts.some((c) => c != null && c < 10)) why = "有人出牌了";
      else if (r.myTurn) why = "輪到你了";
      else if (w.moved && row.length === 13 && !down.length && [1, 2, 3].some((q) => counts[q] === 13) && w.backAt && now - w.backAt < 3000) why = "各家都回到 13 張";
      else if (!w.moved && now - w.t0 > SWAP_QUIET) why = "沒有人換牌";
      else if (w.moved && !short && down.length && now - w.movedAt > SWAP_STUCK) why = "張數變少後沒有回來，是出牌";
      else if (now - w.t0 > SWAP_MAX) why = "等太久了";
      if (why) {
        // your row back at 13 and changed by up to 3 cards: your swap (before the reading goes on as usual)
        if (row.length === 13 && !sameList(row, my)) {
          const d = swapDiff(w, row);
          if (d && d.got.length) { L.S = Object.assign({}, L.S, { my: row.slice(), hand0: row.slice(), guess: row.filter((c, i) => !r.hand.sure[i]) }); patchSwap({ gave: d.gave, got: d.got, done: true, at: now }); L.swapDone = d; }
        }
        return { r, note: closeSwap(why, now) };
      }
      // (everything back at 13: once more and the swap is over)
      if (!short && !down.length) { if (w.moved && row.length === 13) patchSwap({ backAt: now }); return { r, note: null }; }
      // (something seen moving the same way twice in a row: one odd reading of a count is not the swap)
      let note = null;
      const mv = { row: short ? row.length : 0, c: counts.map((c, q) => (q && c != null && c < 13 ? c : 0)) };
      const pm = w.mv && now - w.moveAt < 3000 ? w.mv : null;
      const same = pm && ((mv.row && mv.row === pm.row) || [1, 2, 3].some((q) => mv.c[q] && mv.c[q] === pm.c[q]));
      patchSwap({ mv, moveAt: now, backAt: 0 });
      if (!w.moved && same) { patchSwap({ moved: true, movedAt: now }); note = `換牌中：${short ? `你的牌列剩 ${row.length} 張` : ""}${short && down.length ? "，" : ""}${down.map((q) => `${["", "下家", "對家", "上家"][q]} ${counts[q]} 張`).join("、")}（不當成出牌）`; }
      const seats = Object.assign({}, r.seats);
      for (const q of down) seats[SKEY[q]] = Object.assign({}, seats[SKEY[q]], { count: 13, p: 0.97 });
      const hand = short ? { cards: my.slice(), sure: my.map(() => true), lit: my.map(() => true), geoOk: true, n: my.length, why: "" } : r.hand;
      return { r: Object.assign({}, r, { seats, hand }), note };
    }
    // the swap as it stands: { phase: "choose" | "done", hand0, gave, got, adv } while it is on, else null
    // (done with gave/got null: your row changed by more than 3 cards, which cards went where is not known)
    function swapInfo() {
      if (!swapOpen()) return null;
      const w = L.S.swap;
      return { phase: w.done ? "done" : "choose", hand0: w.hand0.slice(), gave: w.gave, got: w.got, adv: w.adv, t0: w.t0 };
    }
    // the cards you swapped out and got, from the row dealt and the row now
    function swapDiff(w, my) {
      const got = my.filter((c) => !w.hand0.includes(c)), gave = w.hand0.filter((c) => !my.includes(c));
      return got.length <= 3 && gave.length === got.length ? { gave, got } : null;
    }
    // the swap of a deal just dealt: 13 cards each and nothing played yet (also when swap games are turned on then)
    function startSwap(now) {
      const S = L.S;
      if (!L.swapMode || !S.my || S.my.length !== 13 || playsSeen(S) || ![1, 2, 3].every((q) => S.counts[q] === 13)) return false;
      L.S = Object.assign({}, S, { swap: { hand0: S.my.slice(), t0: now, adv: null, gave: null, got: null, done: false, moved: false, closed: false } });
      return true;
    }
    // the advice the page gave for the swap (cards to swap; [] to keep them all)
    function setSwapAdvice(hand0, ids) {
      const w = L.S.swap;
      if (w && sameList(w.hand0, hand0)) L.S = Object.assign({}, L.S, { swap: Object.assign({}, w, { adv: ids.slice() }) });
    }

    // one reading; returns { status, why?, turn?, notes?, swapStart?, swapDone? }
    // status: applied | same | settling | busy | unread | odd | err | swapping
    // a reading; returns its status, with `bad`: the plays shown large that were read as more or fewer cards than their
    // owner put down (seat, cards read, how many it was, where the marks were read), for the log
    function process(r, now) {
      L.bad = [];
      const st = process1(r, now);
      for (const e of L.S.events) if (e.fixed && !e.told) {
        e.told = true;
        const x = L.shows.find((y) => y.seat === e.s && y.at === e.t);
        if (x) x.odd = true;
        L.bad.push({ seat: e.s, cards: (e.part || []).slice(), n: e.n, marks: x ? x.marks : null });
      }
      if (L.bad.length) st.bad = L.bad;
      return st;
    }
    function process1(r, now) {
      now = now == null ? Date.now() : now;
      noteDisplays(r, now);
      noteShows(r, now);
      // (cards in the middle during the swap are not plays)
      if (!swapOpen()) noteSingle(r, now);
      // during the swap, buttons on screen are the swap's, and what moves is the swap
      const hold = !!(r && r.myTurn && swapHold(now));
      if (hold) r = Object.assign({}, r, { myTurn: false, noPlay: false });
      L.swapDone = null;
      const sf = swapFilter(r, now);
      r = sf.r;
      const swapNote = sf.note;
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
      if (!o.ok) { L.ring = []; return { status: "unread", why: o.why, raised: !!(r && r.raised), hold, swapNote, swapDone: L.swapDone }; }
      // when your hand was last seen as it was (your play, when it comes, is after that)
      if (L.S.my && sameList(o.guess, L.S.my)) L.handT = now;
      if (busyOf(r)) {
        if (!L.busySince) L.busySince = now;
        if (now - L.busySince < BUSY_MS) { L.ring = []; return { status: "busy", swapNote, swapDone: L.swapDone }; }
      } else L.busySince = 0;
      // settled: the same reading came up before among the last few (one odd reading in between does not matter)
      // the first reading of your turn with your hand as it was: used at once (the play to beat is known by then from
      // what was shown large and the counts); everything else waits for a second reading that agrees
      const quick = o.myTurn && !L.S.round && L.S.my && sameList(o.guess, L.S.my) && L.lastO && !L.lastO.myTurn;
      const stable = quick || L.ring.some((p) => agree(o, p));
      L.ring.push(o); if (L.ring.length > 4) L.ring.shift();
      if (!stable) return { status: "settling", hold, swapNote, swapDone: L.swapDone };
      if (!news(o, L.lastO)) return { status: "same", turn: !!L.S.round, hold, swapNote, swapDone: L.swapDone };
      // your turn with someone's count not read (and no PASS sign over it): wait a reading or two for it, since it says
      // who played last
      if (o.myTurn && [1, 2, 3].some((q) => o.counts[q] == null && !o.pass[q]) && ++L.waitCount < WAIT_N) return { status: "settling", why: "等看清楚各家張數" };
      L.waitCount = 0;
      // a hand that does not fit the cards you had: a misreading, unless it keeps coming back (a new hand of 13 is fine).
      // One that fits, but what left it is not one play (1, 2 or 5 cards making a hand): cards of your row hidden for a
      // moment (your play shown large, a card moving, the end of the deal), not played; taken only once it has stayed
      // like that for PLAY_WAIT (your plays while this page was in the background).
      // You play only on your turn, so cards leaving your row with no turn of yours seen since your last play are held
      // the same way.
      if (L.S.my && o.guess.length !== 13) {
        const al = ST.align(L.S.my, L.S.guess, o.guess, o.sure);
        let lastPlay = -1, lastTurn = -1;
        L.S.events.forEach((e, i) => { if (e.k === "play") lastPlay = i; else if (e.k === "turn") lastTurn = i; });
        const why = !al ? "手牌和之前的對不起來"
          : al.gone.length && !ST.classify(al.gone) ? `手牌少了 ${al.gone.length} 張，湊不成一手牌：先當作有牌被擋住`
          : al.gone.length && lastTurn < lastPlay ? `手牌少了 ${al.gone.length} 張，但你出牌後還沒輪到你：先當作有牌被擋住` : null;
        if (why) {
          const k = (al ? "p" : "a") + o.guess.join(",");
          L.odd = L.odd && L.odd.k === k ? { k, n: L.odd.n + 1, t: L.odd.t } : { k, n: 1, t: now };
          if (!al ? L.odd.n < ODD_N : now - L.odd.t < PLAY_WAIT) return { status: "odd", why, swapNote, swapDone: L.swapDone };
        }
      }
      L.odd = null;
      // the swap: your row of 13 now differs from the one dealt by up to 3 cards (cards not read surely count as read;
      // a later reading puts them right). Back to the one dealt: an earlier misreading.
      let swapDone = L.swapDone;
      const open0 = swapOpen() ? L.S.swap : null;
      const prev = L.S;
      if (open0 && o.guess.length === 13 && !sameList(o.guess, L.S.my)) {
        const d = swapDiff(open0, o.guess);
        if (d) {
          const guess = o.guess.filter((c, i) => !o.sure[i]);
          L.S = Object.assign({}, L.S, { my: o.guess.slice(), hand0: o.guess.slice(), guess, swap: Object.assign({}, open0, d.got.length ? { gave: d.gave, got: d.got, done: true, at: now } : { gave: null, got: null, done: false }) });
          // (the reading as given to the tracker: your row as it is now)
          if (d.got.length && !(open0.done && open0.got && sameList(open0.got, d.got))) swapDone = d;
        }
      }
      const deal0 = L.S.deal;
      const newest = L.seen.length ? L.seen[L.seen.length - 1] : null;
      const recent = newest && !newest.used && now - newest.at < 6000 ? newest.card : null;
      const lastShow = L.shows.length ? L.shows[L.shows.length - 1] : null;
      const show = lastShow && !lastShow.used && now - lastShow.at < MATCH_BEFORE ? { seat: lastShow.seat, cards: lastShow.cards } : null;
      const resync = L.lastApplied != null && now - L.lastApplied < RESYNC_GAP;
      const out = ST.apply(L.S, r, { live: true, now, resync, disp: dispFor(now), recent, show, handT: L.handT });
      if (out.err) return { status: "err", why: out.err };
      const S = out.S;
      // a display that was used up (that seat's count went down) is forgotten
      for (const e of S.events) if (e.at === S.shots && e.k === "count") { L.disp[e.s] = null; if (e.t == null) e.t = now; }
      L.S = S; L.lastO = o;
      if (S.deal !== deal0) { L.seen = []; L.shows = []; }
      // a whole new row of 13 while the swap is open (nothing played since the deal): the row after the swap, read
      // differently from the one dealt, not another deal (unless the swap advice was not out yet: then the row dealt
      // was misread, and the swap starts over from this one)
      const w0 = prev.swap;
      if (S.deal !== deal0 && L.swapMode && w0 && w0.adv && now - w0.t0 < 90000 && S.my.length === 13 && !prev.events.some((e) => e.k === "play" || e.k === "count")) {
        const d = swapDiff(w0, S.my);
        S.swap = Object.assign({}, w0, d && d.got.length ? { gave: d.gave, got: d.got, done: true, at: now } : { gave: null, got: null, done: true, at: now });
        swapDone = d && d.got.length ? d : { gave: null, got: null };
        out.notes = (out.notes || []).filter((x) => x !== "新的一局").concat("換牌後的手牌和發牌時差超過 3 張，照現在的手牌算");
      }
      // while nothing is played yet, what was swapped follows your row as read now
      if (S.swap && S.swap.done && S.swap.got && !playsSeen(S) && S.my.length === 13) { const d = swapDiff(S.swap, S.my); if (d && d.got.length) { S.swap.gave = d.gave; S.swap.got = d.got; } }
      // the singles seen so far are played cards; match them to the plays
      for (const x of L.seen) if (!S.played.includes(x.card) && !(S.my || []).includes(x.card)) S.played.push(x.card);
      for (const x of L.shows) for (const c of x.cards) if (!S.played.includes(c) && !(S.my || []).includes(c)) S.played.push(c);
      match(now);
      // a swap game: a deal just dealt (13 cards each, nothing played) starts its swap
      const swapStart = !S.swap && startSwap(now);
      L.lastApplied = now;
      return { status: "applied", turn: !!S.round, notes: out.notes, swapStart, swapDone, hold, swapNote };
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
      // 保證出完: your hand splits into plays nobody can beat and at most one other; played in that order you go out
      // first whatever the others hold (no simulating needed)
      const lock = B.lockPlan(g, 0, Lg);
      if (lock) return { kind: "lock", card: lock.plan[0], plan: lock.plan, mult: lock.mult, g, byLit, risky: risky && lock.plan[0].type !== B.T_PASS };
      const W = opts.W || (root.B2_MODELS && root.B2_MODELS.W);
      // the aim: points (ev), going out first (ev false), or points with opts.winBonus more for going out first (兼顧)
      const ev = opts.ev !== false, winBonus = ev ? opts.winBonus || 0 : 0;
      const r = B.choosePIMC(g, 0, Lg, { type: B.P_PIMC, nDet: opts.nDet || 200, adapt: opts.adapt || null, maxCand: opts.maxCand || 8, rollType: B.P_S, w: W, seed: posSeed(), ev, winBonus });
      // the play chosen first, then the others by the aim (each over the deals it was played on)
      const val = (x) => (ev ? x.pts + winBonus * x.wins / x.n : x.wins / x.n);
      const stats = r.stats.filter((x) => x.n > 0).sort((a, b) => (a.card === r.card ? -1 : b.card === r.card ? 1 : val(b) - val(a)));
      return { kind: stats.length > 1 ? "sim" : "only", card: r.card, stats, g, byLit, ev, winBonus, risky: risky && r.card.type !== B.T_PASS, ms: r.ms, deals: r.deals };
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
