// 大老二: the game so far, put together from screenshots (what B2Read.readShot reads), and the position for the advice.
// Seats: 0 = you, 1 = 下家 (right), 2 = 對家 (top), 3 = 上家 (left); play goes 0 → 1 → 2 → 3 → 0.
(function (root) {
  "use strict";
  const B = root.Big2 || (typeof require !== "undefined" ? require("./engine.js") : null);
  const SEAT = ["你", "下家", "對家", "上家"];
  const SKEY = [null, "right", "top", "left"];
  const COUNT_P = 0.85;          // a badge read less surely than this counts as not read
  const MAX_UNSURE = 4;          // more unclear cards than this in your row: the screenshot is not used

  const sortIds = (a) => a.slice().sort((x, y) => x - y);
  const clone = (o) => JSON.parse(JSON.stringify(o));
  function classify(ids) {
    const set = B.fromIds(ids), out = [], n = ids.length;
    if (n === 1) B.genSingles(set, out);
    else if (n === 2) B.genPairs(set, out);
    else if (n === 5) { B.genStraights(set, out, true, true); B.genFulls(set, out); B.genQuads(set, out); }
    else if (n === 13) B.genDragon(set, out);
    return out.find((c) => B.sameSet(c.set, set)) || null;
  }

  // ---------- one screenshot, in plain terms ----------
  function observe(r) {
    const h = (r && r.hand) || {}, o = { ok: false, why: "", hand: null, guess: null, sure: null, lit: null, counts: [null, null, null, null], craw: [null, null, null, null], cp: [0, 0, 0, 0], pass: [false, false, false, false], pile: { n: null, card: null, sure: false }, myTurn: !!(r && r.myTurn), unsure: 0 };
    if (!h.cards) { o.why = h.why || "沒找到手牌"; return o; }
    if (r.raised) { o.why = "手牌有牌被選起來（黃框）：先在遊戲裡按「重選」再截圖"; return o; }
    const unsure = h.sure.filter((s) => !s).length;
    if (!h.geoOk) { o.why = "手牌沒讀清楚（" + (h.why || "排列看不清") + "）"; return o; }
    if (unsure > MAX_UNSURE) { o.why = `手牌有 ${unsure} 張看不清`; return o; }
    o.guess = tidy(h.cards, h.sure); o.sure = h.sure.slice(); o.lit = h.lit.slice(); o.unsure = unsure;
    if (!o.guess) { o.why = "手牌沒讀清楚（看不清的牌排不進去）"; return o; }
    if (r.seats) for (let q = 1; q <= 3; q++) {
      const s = r.seats[SKEY[q]];
      if (!s) continue;
      if (s.count != null && s.p >= COUNT_P) o.counts[q] = s.count;
      o.craw[q] = s.count != null ? s.count : null;
      o.cp[q] = s.p || 0;
      o.pass[q] = !!s.pass;
      // 上家's and 下家's PASS sign sits right over their count: what shows through is not their count
      if (o.pass[q] && q !== 2) { o.counts[q] = null; o.craw[q] = null; o.cp[q] = 0; }
    }
    const p = r.pile || {};
    if (!p.busy && p.n != null) {
      o.pile.n = p.n;
      if (p.n === 1 && p.cards && p.cards.length === 1) { o.pile.card = p.cards[0]; o.pile.sure = !!p.sure; }
    }
    o.ok = true;
    return o;
  }

  // an unclear card (say, its suit hidden by the game's message) stands in as a real card that keeps the row in the
  // game's order and is not used twice: the guess when it fits, else one of the same rank, else any that fits
  function tidy(guess, sure) {
    const out = guess.slice(), used = new Set(guess.filter((c, i) => sure[i]));
    for (let i = 0; i < out.length; i++) {
      if (sure[i]) continue;
      const lo = i > 0 ? out[i - 1] : -1;
      let hi = 52; for (let j = i + 1; j < out.length; j++) if (sure[j]) { hi = out[j]; break; }
      let c = out[i];
      const fits = (x) => x > lo && x < hi && !used.has(x);
      if (!(c >= 0 && fits(c))) {
        let pick = -1;
        if (c >= 0) for (let s = 0; s < 4 && pick < 0; s++) if (fits((c & ~3) | s)) pick = (c & ~3) | s;
        if (pick < 0) for (let x = lo + 1; x < hi; x++) if (!used.has(x)) { pick = x; break; }
        if (pick < 0) return null;
        c = pick;
      }
      out[i] = c; used.add(c);
    }
    return out;
  }
  // your row only loses cards during a hand: line the new reading up with the cards you had (both in the game's order).
  // An unclear card on either side matches whatever stands there. Gives the row now, which of its cards are still
  // guesses, and the cards that left.
  function align(prev, prevGuess, guess, sure) {
    const n = prev.length, m = guess.length, pg = new Set(prevGuess || []);
    if (m > n) return null;
    const fits = (i, j) => !sure[j] || pg.has(prev[i]) || prev[i] === guess[j];
    const ok = [];   // ok[i][j]: reading j.. fits into prev i..
    for (let i = 0; i <= n; i++) { ok.push(new Uint8Array(m + 1)); ok[i][m] = 1; }
    for (let j = m - 1; j >= 0; j--) for (let i = n - 1; i >= 0; i--) ok[i][j] = (fits(i, j) && ok[i + 1][j + 1]) || ok[i + 1][j] ? 1 : 0;
    if (!ok[0][0]) return null;
    const hand = [], still = [], used = new Set();
    let i = 0;
    for (let j = 0; j < m; j++) {
      let pick = -1;
      for (let k = i; k < n; k++) if (prev[k] === guess[j] && ok[k + 1][j + 1]) { pick = k; break; }
      if (pick < 0) for (let k = i; k < n; k++) if (fits(k, j) && ok[k + 1][j + 1]) { pick = k; break; }
      if (pick < 0) return null;
      for (let k = i; k < pick; k++) used.add(k);   // skipped: played
      let c;
      if (!pg.has(prev[pick])) c = prev[pick];                  // known before
      else if (sure[j]) c = guess[j];                           // a guess before, clear now
      else { c = guess[j]; still.push(c); }                     // still a guess
      hand.push(c); i = pick + 1;
    }
    for (let k = i; k < n; k++) used.add(k);
    const gone = [...used].map((k) => prev[k]);
    // a card cleared up now must not stand twice
    if (new Set(hand).size !== hand.length) return null;
    return { hand, guess: still, gone };
  }

  // ---------- which play is on the table: from the cards of yours the game lights up ----------
  function combosOf(H, first) {
    const out = [];
    B.genSingles(H, out); B.genPairs(H, out); B.genStraights(H, out, true, true); B.genFulls(H, out); B.genQuads(H, out); B.genDragon(H, out);
    return first ? out.filter((c) => c.set[0] & 1) : out;
  }
  function tops(n) {
    const out = [];
    if (n === 1) for (let k = 0; k < 52; k++) out.push({ type: B.T_SINGLE, key: k });
    if (n === 2) for (let r = 0; r < 13; r++) for (let s = 1; s < 4; s++) out.push({ type: B.T_PAIR, key: r * 4 + s });
    if (n === 5) {
      for (let k = 0; k < 40; k++) out.push({ type: B.T_STRAIGHT, key: k });
      for (let r = 0; r < 13; r++) out.push({ type: B.T_FULL, key: r });
      for (let r = 0; r < 13; r++) out.push({ type: B.T_QUADS, key: r });
      for (let k = 0; k < 40; k++) out.push({ type: B.T_SF, key: k });
    }
    return out;
  }
  // could this play be on the table at all, given the cards that are yours or known to be gone?
  function possible(t, mine, gone) {
    const free = (c) => !B.has(mine, c) && !B.has(gone, c);
    if (t.type === B.T_SINGLE) return free(t.key);
    if (t.type === B.T_PAIR) { const r = t.key >> 2, s = t.key & 3; if (!free(t.key)) return false; for (let x = 0; x < s; x++) if (free(r * 4 + x)) return true; return false; }
    if (t.type === B.T_STRAIGHT || t.type === B.T_SF) {
      const R = B.WINR[t.key >> 2], top = B.WINTOP[t.key >> 2];
      for (const r of R) { let any = false; for (let s = 0; s < 4; s++) if (free(r * 4 + s) && (r !== top || s === (t.key & 3)) && (t.type !== B.T_SF || s === (t.key & 3))) any = true; if (!any) return false; }
      return true;
    }
    if (t.type === B.T_FULL) { let k = 0; for (let s = 0; s < 4; s++) if (free(t.key * 4 + s)) k++; return k >= 3; }
    if (t.type === B.T_QUADS) { for (let s = 0; s < 4; s++) if (!free(t.key * 4 + s)) return false; return true; }
    return false;
  }
  // every play of the given size that would light up exactly the cards that are lit (fewest mismatches)
  function inferTop(handIds, lit, n, first, goneIds) {
    const H = B.fromIds(handIds), mine = H, gone = B.fromIds(goneIds || []), C = combosOf(H, first);
    const want = new Set(handIds.filter((c, i) => lit[i]));
    let best = Infinity, list = [];
    for (const t of tops(n)) {
      if (!possible(t, mine, gone)) continue;
      const on = new Set();
      for (const c of C) if (B.beats(c, t)) for (const x of B.toIds(c.set)) on.add(x);
      let miss = 0;
      for (const x of handIds) if (on.has(x) !== want.has(x)) miss++;
      if (miss < best) { best = miss; list = [t]; } else if (miss === best) list.push(t);
    }
    return { miss: best, list };
  }
  const sameTop = (a, b) => a.type === b.type && a.key === b.key;
  // what the lit cards narrow an unread play down to, in words (only when that is narrow enough to help)
  const RK = ["3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K", "A", "2"], SG = ["♣︎", "♦︎", "♥︎", "♠︎"];
  function guessText(list) {
    if (!list.length) return "";
    const t0 = list[0].type;
    if (list.every((t) => t.type === B.T_SINGLE)) {
      if (list.length > 6) return "";
      return list.map((t) => SG[t.key & 3] + RK[t.key >> 2]).join("、") + (list.length > 1 ? " 其中一張" : "");
    }
    if (list.every((t) => t.type === B.T_PAIR)) {
      const ranks = [...new Set(list.map((t) => t.key >> 2))];
      return ranks.length <= 3 ? ranks.map((r) => RK[r]).join(" 或 ") + " 的對子" : "";
    }
    const types = [...new Set(list.map((t) => t.type))];
    if (types.length === 1) {
      if (t0 === B.T_FULL || t0 === B.T_QUADS) { const ranks = [...new Set(list.map((t) => t.key))]; return ranks.length <= 3 ? ranks.map((r) => RK[r]).join(" 或 ") + " 的" + B.TNAME[t0] : B.TNAME[t0]; }
      return B.TNAME[t0];
    }
    return "";
  }

  // ---------- the state of one hand (deal) ----------
  function blank() {
    return { v: 2, deal: 0, shots: 0, my: null, hand0: null, counts: [0, 13, 13, 13], fresh: [true, false, false, false], played: [], guess: [], countAt: [0, -1, -1, -1], est: [false, false, false, false], unk: [false, false, false, false], events: [], lastTurnAt: -1, prevTurnAt: -1, turnCounts: null, view: null, round: null };
  }
  function newDeal(S, o, hand) {
    const n = blank();
    n.deal = S.deal + 1; n.shots = S.shots;
    n.my = hand.slice(); n.hand0 = hand.length === 13 ? hand.slice() : null;
    // (a deal picked up part way: a count not read is only a guess, unk, until it is read)
    for (let q = 1; q <= 3; q++) { n.counts[q] = o.counts[q] != null ? o.counts[q] : hand.length === 13 ? 13 : hand.length; n.fresh[q] = o.counts[q] != null; n.countAt[q] = o.counts[q] != null ? n.shots : -1; n.unk[q] = o.counts[q] == null && hand.length !== 13; }
    n.counts[0] = hand.length;
    return n;
  }
  // live: still the same deal as the cards you had? Nothing the others were seen to play is in your row, and no count
  // read now is higher than before (counts only go down during a deal).
  function sameDeal(S, o, hand) {
    const mine = new Set();
    for (const e of S.events) if (e.k === "play") for (const c of e.c) mine.add(c);
    if (hand.some((c) => S.played.includes(c) && !mine.has(c))) return false;
    for (let q = 1; q <= 3; q++) if (o.counts[q] != null && o.counts[q] > S.counts[q]) return false;
    return true;
  }
  const ev = (S, e) => { e.at = S.shots; S.events.push(e); };

  // Live: who owns the table at your turn, from the plays seen in this deal (cards leaving your row, the others' counts
  // going down). The last one is the play to beat; if it was yours, the others all passed and you lead.
  function liveTop(S, o) {
    const evs = S.events;
    let k = evs.length - 1;
    for (; k >= 0; k--) if (evs[k].k === "play" || evs[k].k === "count") break;
    if (k < 0) return null;
    const lp = evs[k], passed = new Set();
    for (let i = k + 1; i < evs.length; i++) if (evs[i].k === "pass") passed.add(evs[i].s);
    for (let q = 1; q <= 3; q++) if (o.pass[q]) passed.add(q);
    if (lp.s === 0) return { lead: true, passed: [...passed] };
    return { owner: lp.s, n: lp.n, c: lp.c || null, part: lp.part || null, passed: [...passed] };
  }
  // live: the newest play at seat q, when it was counted from the play shown large (its count not seen then) a moment
  // ago, no count seen agreeing with it since, and nothing of yours played after it
  const SHOW_FIX = 5000, SEATW = ["你", "下家", "對家", "上家"];
  function shownPlay(S, q, now) {
    for (let i = S.events.length - 1; i >= 0; i--) {
      const e = S.events[i];
      if (e.k === "play") return null;
      if (e.k === "count" && e.s === q) return e.fromShow && !e.confirmed && now != null && e.t != null && now - e.t <= SHOW_FIX ? e : null;
    }
    return null;
  }

  // apply one screenshot's reading; returns { S, err?, notes[] }
  function apply(S0, r, opts) {
    opts = opts || {};
    const o = observe(r), buttons = o.myTurn;   // whether the play buttons were seen in the screenshot
    if (opts.myTurn != null) o.myTurn = opts.myTurn;
    if (!o.ok) return { S: S0, err: o.why };
    let S = clone(S0);
    const notes = [];
    S.shots++;
    // 1. the same hand as before? (cards only leave your row during a hand)
    let al = null, hand = null, fresh = false;
    if (S.my) al = align(S.my, S.guess, o.guess, o.sure);
    // (live: a new hand of 13 is a different 13; the same 13 cards with the others' counts covered is still this deal)
    if (al && o.guess.length === 13 && S.my.length === 13 && o.counts.every((c, q) => q === 0 || c == null || c === 13) && S.events.some((e) => e.k === "play" || e.k === "count")
        && !(opts.live && o.guess.every((c, i) => c === S.my[i]) && o.counts.some((c, q) => q > 0 && c == null))) al = null;
    if (!al) {
      if (o.unsure > 0 && S.my && o.guess.length < 13) return { S: S0, err: `手牌和上一張對不起來，而且有 ${o.unsure} 張看不清` };
      hand = o.guess.slice();
      if (opts.live && opts.resync && S.my && S.my.length && hand.length < 13 && hand.length <= S.my.length && sameDeal(S, o, hand)) {
        // live: your row read differently from the cards you had, but still this deal: only your row is put right.
        // What was seen played and every count stay; your plays recorded with cards that are in your row again were
        // misread (those cards are taken out of them).
        notes.push("手牌和前一張對不起來，只重抓你的手牌（記牌和各家張數照舊）");
        for (const e of S.events) if (e.k === "play") { e.c = e.c.filter((c) => !hand.includes(c)); e.n = e.c.length; }
        S.events = S.events.filter((e) => e.k !== "play" || e.c.length);
        S.played = S.played.filter((c) => !hand.includes(c));
        S.guess = o.guess.filter((c, i) => !o.sure[i]);
      } else {
        if (S.my) notes.push(o.guess.length === 13 ? "新的一局" : "手牌和前一張對不起來，從這張重新算");
        S = newDeal(S, o, hand);
        S.guess = o.guess.filter((c, i) => !o.sure[i]);
        fresh = true;
      }
    } else {
      hand = al.hand;
      const before = (S.guess || []).length;
      S.guess = al.guess;
      if (before > S.guess.length) notes.push(`之前看不清的牌這張看清楚了`);
      // 2. what you played since the last screenshot
      if (al.gone.length) {
        ev(S, { k: "play", s: 0, c: al.gone, n: al.gone.length });
        // live: plays counted from what was shown large since the last reading came after yours
        // (those shown before your old hand was last seen came before your play)
        const k = opts.live ? S.events.findIndex((e) => e.pend && !(opts.handT != null && e.t != null && e.t <= opts.handT)) : -1;
        if (k >= 0) S.events.splice(k, 0, S.events.pop());
        for (const c of al.gone) if (!S.played.includes(c)) S.played.push(c);
      }
    }
    if (S.guess.length) notes.push(`手牌有 ${S.guess.length} 張看不清，先照猜的算`);
    S.my = hand.slice(); S.counts[0] = hand.length;
    // 3. the others' counts (a less sure reading still counts when it does not go up)
    const drop = [0, 0, 0, 0];
    for (let q = 1; q <= 3; q++) {
      let c = o.counts[q];
      if (!opts.live && c == null && o.craw[q] != null && o.cp[q] >= 0.55 && o.craw[q] <= S.counts[q]) { c = o.craw[q]; o.counts[q] = c; }
      // a count only guessed so far (a deal picked up part way, that seat's count not read then): the first one read is
      // taken as it is, not as a play
      if (c != null && !fresh && S.unk && S.unk[q]) { S.unk[q] = false; S.counts[q] = c; S.fresh[q] = true; S.est[q] = false; S.countAt[q] = S.shots; continue; }
      // live: the play just shown large at this seat was counted by itself, and now its count says it was more cards: it
      // was read short where it was shown large (a rank mark lost). The count says how many cards it was; the cards read
      // are part of it. (A count agreeing with it confirms it.)
      if (c != null && opts.live && !fresh) {
        const F = shownPlay(S, q, opts.now);
        if (F && c === S.counts[q]) F.confirmed = true;
        const n2 = F && c < S.counts[q] ? F.n + S.counts[q] - c : 0;
        if (F && [2, 5].includes(n2) && F.c && F.c.length < n2) {
          F.part = F.c; F.c = null; F.n = n2; F.fixed = true; F.confirmed = true;
          notes.push(`${SEATW[q]}放大的牌只讀到 ${F.part.length} 張，張數卻少了 ${n2} 張：照張數算`);
          S.counts[q] = c; S.fresh[q] = true; S.est[q] = false; S.countAt[q] = S.shots;
          continue;
        }
      }
      // live: a count never goes up during a hand, so a higher one is a misreading (something lying over the badge)
      if (c != null && opts.live && !fresh && c > S.counts[q]) c = null;
      if (c == null) { S.fresh[q] = false; continue; }
      if (!fresh && c < S.counts[q]) {
        drop[q] = S.counts[q] - c;
        // live: the others play in turn (下家, 對家, 上家) after you; a count seen late goes before a play already counted
        // from what a later seat showed large since your last turn
        const e = { k: "count", s: q, n: drop[q], at: S.shots };
        let k = S.events.length;
        if (opts.live) for (let i = S.events.length - 1; i >= 0; i--) { const y = S.events[i]; if (y.k === "play" || y.k === "turn") break; if (y.k === "count" && y.fromShow && y.s > q) k = i; }
        S.events.splice(k, 0, e);
      }
      S.counts[q] = c; S.fresh[q] = true; S.est[q] = false; S.countAt[q] = S.shots;
    }
    // 4. the newest play on the table, and whose it is
    // Reading the screen live (opts.live), every play is seen as it happens: whoever put cards down last owns the table,
    // their card count says how many, and a single was read off the table when it landed (opts.disp: a single read off
    // the large display a moment before, for when the table is not clear).
    let LV = opts.live && o.myTurn ? liveTop(S, o) : null;
    // you lead only on an empty table: a card on it that is not from your last play means someone played after you
    if (LV && LV.lead && o.pile.n > 0 && o.pile.card != null && o.pile.sure) {
      let mineLast = null; for (let i = S.events.length - 1; i >= 0; i--) if (S.events[i].k === "play") { mineLast = S.events[i].c; break; }
      if (!mineLast || !mineLast.includes(o.pile.card)) LV = null;
    }
    let owner = null;
    if (o.myTurn) {
      if (LV && LV.owner != null) owner = LV.owner;
      else if (!(LV && LV.lead)) {
        // the last seat before you that did not pass; a seat whose count has not moved since your last turn did not play
        // either (its PASS sign may simply not be up yet)
        const T = S.turnCounts;
        for (const q of [3, 2, 1]) {
          if (o.pass[q]) continue;
          if (T && T[q] != null && o.counts[q] != null && o.counts[q] === T[q]) continue;
          owner = q; break;
        }
      }
    }
    else { const d = [1, 2, 3].filter((q) => drop[q] > 0); if (d.length === 1) owner = d[0]; }
    // the single on the table: as read now, else as read off the large display just before
    let pileCard = o.pile.card, pileSure = !!o.pile.sure;
    const dispCard = owner != null && opts.disp && opts.disp[owner] != null ? opts.disp[owner] : null;
    if ((pileCard == null || !pileSure) && dispCard != null && !hand.includes(dispCard) && (owner == null || [0, 1].includes(drop[owner]) || (LV && LV.n === 1))) { pileCard = dispCard; pileSure = true; }
    if (LV && LV.c && LV.c.length === 1 && (pileCard == null || !pileSure)) { pileCard = LV.c[0]; pileSure = true; }
    // live: the newest single seen surely on the table and not yet matched to an earlier play
    if (o.myTurn && opts.recent != null && (pileCard == null || !pileSure) && !hand.includes(opts.recent)) { pileCard = opts.recent; pileSure = true; }
    // 5. your turn: the round as it stands
    S.round = null;
    const view = { myTurn: o.myTurn, buttons, pass: o.pass.slice(), pile: o.pile, owner: null, lit: o.lit.slice() };
    if (o.myTurn) {
      // live: part of the play to beat read where it was shown large (the rest of its cards lost there)
      const part = LV && LV.owner != null && LV.owner === owner && LV.part ? LV.part : null;
      // cards known to be out of play, except the one on the table now (it may have been read on an earlier screenshot)
      // and those of the play to beat read in part
      const gone = S.played.filter((c) => c !== pileCard && !(part && part.includes(c)));
      const allThirteen = [1, 2, 3].every((q) => S.counts[q] === 13);
      const first = hand.length === 13 && hand.includes(0) && allThirteen;
      let lead = first || (LV ? !!LV.lead : o.pile.n === 0 || owner == null) || owner == null;
      let top = null;
      if (!lead) {
        // live: the play as read where it was shown large (or matched to its owner's count before): nothing to work out
        // (the play shown large only when it is as many cards as its owner was seen putting down)
        const showOk = opts.show && opts.show.seat === owner && !(LV && LV.owner === owner && LV.n !== opts.show.cards.length) && !(drop[owner] > 0 && drop[owner] !== opts.show.cards.length);
        const shown0 = LV && LV.owner === owner && LV.c && [1, 2, 5].includes(LV.c.length) ? LV.c : showOk ? opts.show.cards : null;
        const shown = shown0 && classify(shown0) ? shown0 : null;
        let inf = null;
        if (shown) top = { s: owner, n: shown.length, c: shown.slice(), read: null, shown: true };
        else {
        // its size: from how many cards its owner just put down (live), else from the table, else from what fits the
        // lit cards best
        const dn = LV && LV.owner === owner && [1, 2, 5].includes(LV.n) ? LV.n : drop[owner];
        let n = LV && LV.owner === owner && [1, 2, 5].includes(LV.n) ? LV.n : o.pile.n;
        if (n == null && [1, 2, 5].includes(dn)) n = dn;
        const infs = {};
        for (const k of [1, 2, 5]) infs[k] = inferTop(hand, o.lit, k, false, gone);
        const best = Math.min(infs[1].miss, infs[2].miss, infs[5].miss);
        // the size stands unless the lit cards clearly say otherwise (a count seen going down is trusted more)
        const slack = LV && LV.owner === owner && LV.n === n ? 3 : 2;
        if (n == null || infs[n].miss >= best + slack) {
          const fit = [1, 2, 5].filter((k) => infs[k].miss === best), want = n || dn || 1;
          n = fit.includes(dn) ? dn : fit.reduce((a, b) => (Math.abs(b - want) < Math.abs(a - want) ? b : a));
        }
        inf = infs[n];
        // a pair read in part: of the plays the lit cards allow, the pairs of that rank (when there are any)
        if (part && n === 2 && part.length === 1 && LV.n === 2) {
          const f = inf.list.filter((t) => t.type === B.T_PAIR && (t.key >> 2) === (part[0] >> 2) && t.key >= part[0]);
          if (f.length) inf = Object.assign({}, inf, { list: f });
        }
        top = { s: owner, n, c: null, read: null };
        if (part && LV.n === n) top.part = part.slice();
        if (pileCard != null && n === 1) {
          const t = { type: B.T_SINGLE, key: pileCard };
          const fits = inf.list.some((x) => sameTop(x, t));
          if ((pileSure && (fits || !inf.list.length)) || (!pileSure && fits && inf.list.length <= 8)) { top.c = [pileCard]; top.unsure = !pileSure; }
          else top.read = pileCard;   // read, but it does not fit the lit cards: not trusted
        }
        }
        if (!top.c) {
          if (inf && inf.list.length) {
            // the lit cards say nothing when every play of that size would leave them as they are: then a plain one stands in
            const all = tops(top.n).filter((t) => possible(t, B.fromIds(hand), B.fromIds(gone))).length, none = inf.list.length >= all;
            const pool = inf.list.filter((t) => !B.isBomb(t.type)).length ? inf.list.filter((t) => !B.isBomb(t.type)) : inf.list;
            const t = pool[Math.floor((pool.length - 1) / 2)];
            top.eff = { type: t.type, key: t.key }; top.range = inf.list.length; top.miss = inf.miss; top.guess = none ? "" : guessText(inf.list);
            top.lo = { type: inf.list[0].type, key: inf.list[0].key };   // the weakest play the lit cards allow
            top.hi = { type: inf.list[inf.list.length - 1].type, key: inf.list[inf.list.length - 1].key };   // and the strongest
          }
          else top.eff = top.n === 1 ? { type: B.T_SINGLE, key: 0 } : top.n === 2 ? { type: B.T_PAIR, key: 1 } : { type: B.T_STRAIGHT, key: 0 };
        } else {
          if (!(opts.live && top.unsure)) for (const c of top.c) if (!S.played.includes(c)) S.played.push(c);
          if (!top.unsure) for (let i = S.events.length - 1; i >= 0; i--) { const e = S.events[i]; if (e.k === "count" && e.s === owner) { if (!e.c && e.n === top.c.length) e.c = top.c.slice(); break; } }
        }
        // its owner's count hidden under the play just shown large: the count read before, less this play (not when the
        // drop was already seen live)
        const same = S0.round && S0.round.top && S0.round.top.s === owner && S0.round.top.n === top.n && JSON.stringify(S0.round.top.c) === JSON.stringify(top.c) && S0.my && S0.my.length === hand.length;
        if (!(LV && LV.owner === owner) && o.counts[owner] == null && S.countAt[owner] >= 0 && !same && S.counts[owner] > top.n) {
          S.counts[owner] -= top.n; S.est[owner] = true; drop[owner] = top.n;
          ev(S, { k: "count", s: owner, n: top.n, c: top.c || undefined });
        }
      }
      const passed = new Set(lead ? [] : [1, 2, 3].filter((q) => o.pass[q] && q !== owner));
      if (!lead && LV && LV.passed) for (const q of LV.passed) if (q !== owner) passed.add(q);
      S.round = { lead, first, top, passed: [...passed].sort(), at: S.shots, live: LV ? (LV.lead ? "lead" : "top") : null };
      view.owner = lead ? null : owner;
      ev(S, { k: "turn", lead, top: top ? { s: top.s, n: top.n, c: top.c } : null });
    } else if (!opts.live && owner != null && pileCard != null && pileSure && drop[owner] === 1) {
      // someone else's single, read off the table (or off the large display just before it landed)
      if (!S.played.includes(pileCard) && !hand.includes(pileCard)) S.played.push(pileCard);
      for (let i = S.events.length - 1; i >= 0; i--) { const e = S.events[i]; if (e.k === "count" && e.s === owner && e.at === S.shots) { e.c = [pileCard]; break; } }
      view.owner = owner;
    }
    // (live: the singles seen on the table are matched to the plays by the live reader, in the order both came)
    // pass signs that appeared since the last screenshot
    const prev = S0.view && S0.deal === S.deal ? S0.view.pass : [false, false, false, false];
    for (let q = 1; q <= 3; q++) if (o.pass[q] && !prev[q]) ev(S, { k: "pass", s: q });
    if (o.myTurn) { S.prevTurnAt = S.lastTurnAt; S.lastTurnAt = S.shots; S.turnCounts = [null, o.counts[1], o.counts[2], o.counts[3]]; }
    S.view = view;
    for (const e of S.events) if (e.pend) delete e.pend;
    return { S, notes };
  }

  // ---------- the position for the engine ----------
  function position(S) {
    const R = S.round;
    if (!R) return null;
    const my = B.fromIds(S.my), played = B.fromIds(S.played);
    let last = B.PASS(), lastP = -1;
    if (!R.lead && R.top) {
      if (R.top.c) { const c = classify(R.top.c); if (c) last = c; }
      if (last.type === B.T_PASS) last = { type: R.top.eff.type, key: R.top.eff.key, set: B.empty() };
      lastP = R.top.s;
    }
    let passed = 0;
    for (const q of R.passed) passed |= 1 << q;
    const U = B.toIds(B.unseenOf(my, played)), hands = [my];
    let k = 0;
    for (let q = 1; q <= 3; q++) { const n = Math.max(0, Math.min(S.counts[q], U.length - k)); hands.push(B.fromIds(U.slice(k, k + n))); k += n; }
    return { hand: hands, played, last, lastP, passed, cur: 0, first: !!R.first, winner: -1, finalPlay: null, nplays: 0 };
  }

  // ---------- several screenshots at once: put them in the order they were taken ----------
  // (cards only go down during a hand; a pass sign stays up for the rest of its round)
  function orderCost(obs) {
    let cost = 0;
    for (let i = 1; i < obs.length; i++) {
      const a = obs[i - 1], b = obs[i];
      if (!a.ok || !b.ok) continue;
      if (b.guess.length > a.guess.length) cost += b.guess.length === 13 ? 2 : 100;
      for (let q = 1; q <= 3; q++) if (a.counts[q] != null && b.counts[q] != null && b.counts[q] > a.counts[q]) cost += 50;
      if (b.guess.length === a.guess.length) {
        let pa = 0, pb = 0; for (let q = 1; q <= 3; q++) { pa += a.pass[q] ? 1 : 0; pb += b.pass[q] ? 1 : 0; }
        if (pb < pa) cost += 1;
      }
    }
    // the screenshot at your turn is usually the last one
    const lastTurn = obs.length > 1 && obs[obs.length - 1].ok && obs[obs.length - 1].myTurn;
    if (obs.some((o) => o.ok && o.myTurn) && !lastTurn) cost += 3;
    return cost;
  }
  function orderShots(readings) {
    const obs = readings.map(observe), n = obs.length, idx = obs.map((o, i) => i);
    if (n <= 1) return idx;
    if (n > 6) {
      return idx.sort((i, j) => {
        const a = obs[i], b = obs[j];
        if (!a.ok || !b.ok) return i - j;
        const sa = a.guess.length * 100 + a.counts.reduce((s, c) => s + (c == null ? 0 : c), 0), sb = b.guess.length * 100 + b.counts.reduce((s, c) => s + (c == null ? 0 : c), 0);
        return sb - sa || i - j;
      });
    }
    let best = null;
    const perm = (pre, rest) => {
      if (!rest.length) { const c = orderCost(pre.map((i) => obs[i])); if (!best || c < best.c) best = { c, p: pre.slice() }; return; }
      for (let k = 0; k < rest.length; k++) perm(pre.concat(rest[k]), rest.slice(0, k).concat(rest.slice(k + 1)));
    };
    perm([], idx);
    return best.p;
  }

  const api = { SEAT, liveTop, observe, align, tidy, inferTop, blank, apply, position, orderShots, classify, combosOf };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  else root.B2State = api;
})(typeof self !== "undefined" ? self : this);
