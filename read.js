// 大老二小助手：讀遊戲畫面（神來也大老二）。和截圖版「大老二出牌助手」同一套讀牌方法。
"use strict";
// 本地讀牌: find the 13-card row in a 神來也 十三支 screenshot, straighten it, cut out each card's rank and suit,
// and match them against templates made from labelled screenshots. It gives cards only when every check passes;
// otherwise it says why, and the page reads that screenshot with Claude instead.
const LocalRead = (() => {
  const BW = 1000, BH = 160;            // the straightened row: 13 cards, the last one whole
  const SW = 74;                        // one card strip (a little more than the pitch)
  const RWIN = [44, 56], SWIN = [34, 34];

  // ---------- helpers ----------
  function rng(seed) {
    let a = seed >>> 0;
    return () => { a = (a + 0x6d2b79f5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
  }
  function sorted(arr) { return Float32Array.from(arr).sort(); }
  function median(arr) { const a = sorted(arr), n = a.length; return n % 2 ? a[(n - 1) >> 1] : (a[n / 2 - 1] + a[n / 2]) / 2; }
  function percentile(arr, q) {
    const a = sorted(arr), pos = (a.length - 1) * q / 100, i = Math.floor(pos), t = pos - i;
    return i + 1 < a.length ? a[i] * (1 - t) + a[i + 1] * t : a[i];
  }
  // bilinear sample of a one-channel float image, clamped at the border
  function bil(A, W, H, x, y) {
    if (x < 0) x = 0; else if (x > W - 1) x = W - 1;
    if (y < 0) y = 0; else if (y > H - 1) y = H - 1;
    const x0 = Math.floor(x), y0 = Math.floor(y), x1 = x0 < W - 1 ? x0 + 1 : x0, y1 = y0 < H - 1 ? y0 + 1 : y0, tx = x - x0, ty = y - y0;
    const o0 = y0 * W, o1 = y1 * W;
    return (A[o0 + x0] * (1 - tx) + A[o0 + x1] * tx) * (1 - ty) + (A[o1 + x0] * (1 - tx) + A[o1 + x1] * tx) * ty;
  }
  // bilinear sample with zeros outside
  function bilZero(A, W, H, x, y) {
    const x0 = Math.floor(x), y0 = Math.floor(y), tx = x - x0, ty = y - y0;
    const g = (xx, yy) => (xx >= 0 && xx < W && yy >= 0 && yy < H ? A[yy * W + xx] : 0);
    return (g(x0, y0) * (1 - tx) + g(x0 + 1, y0) * tx) * (1 - ty) + (g(x0, y0 + 1) * (1 - tx) + g(x0 + 1, y0 + 1) * tx) * ty;
  }
  function lineFit(px, py) {
    const n = px.length; let sx = 0, sy = 0, sxx = 0, sxy = 0;
    for (let i = 0; i < n; i++) { sx += px[i]; sy += py[i]; sxx += px[i] * px[i]; sxy += px[i] * py[i]; }
    const m = (n * sxy - sx * sy) / (n * sxx - sx * sx);
    return { m, c: (sy - m * sx) / n };
  }
  // y = c + m x through the most points (within tol), then refitted to those points
  function ransacLine(X, Y, tol, iters, seed, maxSlope) {
    const n = X.length; if (n < 10) return null;
    const r = rng(seed); let best = null;
    for (let k = 0; k < iters; k++) {
      const i = Math.floor(r() * n); let j = Math.floor(r() * (n - 1)); if (j >= i) j++;
      const dx = X[j] - X[i]; if (Math.abs(dx) < 40) continue;
      const m = (Y[j] - Y[i]) / dx; if (Math.abs(m) > maxSlope) continue;
      let cnt = 0;
      for (let q = 0; q < n; q++) if (Math.abs(Y[q] - (Y[i] + m * (X[q] - X[i]))) < tol) cnt++;
      if (!best || cnt > best.cnt) best = { cnt, m, x: X[i], y: Y[i] };
    }
    if (!best) return null;
    const ix = [], iy = [];
    for (let q = 0; q < n; q++) if (Math.abs(Y[q] - (best.y + best.m * (X[q] - best.x))) < tol) { ix.push(X[q]); iy.push(Y[q]); }
    const f = lineFit(ix, iy);
    return { m: f.m, c: f.c, inl: ix.length / n };
  }
  // solve A x = b (n x n, small) by Gaussian elimination with partial pivoting
  function solve(A, b) {
    const n = b.length, M = A.map((row, i) => [...row, b[i]]);
    for (let c = 0; c < n; c++) {
      let p = c; for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r;
      [M[c], M[p]] = [M[p], M[c]];
      for (let r = 0; r < n; r++) if (r !== c) { const f = M[r][c] / M[c][c]; if (f) for (let k = c; k <= n; k++) M[r][k] -= f * M[c][k]; }
    }
    return M.map((row, i) => row[n] / row[i]);
  }
  // homography taking the 4 points P (x,y) to Q
  function homography(P, Q) {
    const A = [], b = [];
    for (let i = 0; i < 4; i++) {
      const [x, y] = P[i], [u, v] = Q[i];
      A.push([x, y, 1, 0, 0, 0, -u * x, -u * y]); b.push(u);
      A.push([0, 0, 0, x, y, 1, -v * x, -v * y]); b.push(v);
    }
    const h = solve(A, b);
    return [h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], 1];
  }

  // homography taking points P to Q, least squares over all of them (coordinates normalised first)
  function homographyLSQ(P, Q) {
    const norm = (A) => {
      let mx = 0, my = 0; for (const [x, y] of A) { mx += x; my += y; } mx /= A.length; my /= A.length;
      let d = 0; for (const [x, y] of A) d += Math.hypot(x - mx, y - my); d /= A.length; const k = Math.SQRT2 / d;
      return { k, mx, my, pts: A.map(([x, y]) => [(x - mx) * k, (y - my) * k]) };
    };
    const np = norm(P), nq = norm(Q);
    const N = Array.from({ length: 8 }, () => new Array(8).fill(0)), r = new Array(8).fill(0);
    const add = (row, val) => { for (let j = 0; j < 8; j++) { r[j] += row[j] * val; for (let k = 0; k < 8; k++) N[j][k] += row[j] * row[k]; } };
    for (let i = 0; i < P.length; i++) {
      const [x, y] = np.pts[i], [u, v] = nq.pts[i];
      add([x, y, 1, 0, 0, 0, -u * x, -u * y], u); add([0, 0, 0, x, y, 1, -v * x, -v * y], v);
    }
    const h = solve(N, r), Hn = [h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], 1];
    // undo the normalisation: H = Tq^-1 Hn Tp
    const Tp = [np.k, 0, -np.k * np.mx, 0, np.k, -np.k * np.my, 0, 0, 1];
    const Tqi = [1 / nq.k, 0, nq.mx, 0, 1 / nq.k, nq.my, 0, 0, 1];
    const mul = (A, B) => { const C = new Array(9).fill(0); for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) for (let k = 0; k < 3; k++) C[i * 3 + j] += A[i * 3 + k] * B[k * 3 + j]; return C; };
    const Hm = mul(Tqi, mul(Hn, Tp));
    return Hm.map((v) => v / Hm[8]);
  }

  // ---------- 1. the card row ----------
  function lumSat(img) {
    const { width: W, height: H, data } = img, n = W * H;
    const L = new Float32Array(n), S = new Float32Array(n);
    for (let i = 0, j = 0; i < n; i++, j += 4) {
      const r = data[j], g = data[j + 1], b = data[j + 2];
      L[i] = 0.299 * r + 0.587 * g + 0.114 * b;
      const mx = r > g ? (r > b ? r : b) : (g > b ? g : b), mn = r < g ? (r < b ? r : b) : (g < b ? g : b);
      S[i] = mx - mn;
    }
    return { L, S, W, H };
  }
  // card white: bright and grey. The bar is 200, lowered when the whole screenshot is darker.
  function whiteLevel(L, S) {
    const hist = new Uint32Array(256); let cnt = 0;
    for (let i = 0; i < L.length; i++) if (S[i] < 20) { hist[L[i] > 255 ? 255 : L[i] | 0]++; cnt++; }
    let acc = 0, p = 255; const target = cnt * 0.995;
    for (let v = 0; v < 256; v++) { acc += hist[v]; if (acc >= target) { p = v; break; } }
    return Math.min(200, Math.max(120, 0.86 * p));
  }
  function whiteMask(L, S, W, H, T) {
    const n = W * H, m = new Uint8Array(n), d = new Uint8Array(n), e = new Uint8Array(n);
    for (let i = 0; i < n; i++) m[i] = L[i] > T && S[i] < 45 ? 1 : 0;
    // close with a 7-wide horizontal bar: bridges the thin shadow lines between cards
    for (let y = 0; y < H; y++) {
      const o = y * W;
      for (let x = 0; x < W; x++) {
        let v = 0; const a = x - 3 < 0 ? 0 : x - 3, z = x + 3 > W - 1 ? W - 1 : x + 3;
        for (let xx = a; xx <= z; xx++) if (m[o + xx]) { v = 1; break; }
        d[o + x] = v;
      }
      for (let x = 0; x < W; x++) {
        let v = 1; const a = x - 3 < 0 ? 0 : x - 3, z = x + 3 > W - 1 ? W - 1 : x + 3;
        for (let xx = a; xx <= z; xx++) if (!d[o + xx]) { v = 0; break; }
        e[o + x] = v;
      }
    }
    return e;
  }
  // 8-connected components: labels (resolved to roots) and per-root area and box
  function components(m, W, H) {
    const lab = new Int32Array(W * H);
    let parent = new Int32Array(1024), next = 1;
    const find = (a) => { while (parent[a] !== a) { parent[a] = parent[parent[a]]; a = parent[a]; } return a; };
    const unite = (a, b) => { a = find(a); b = find(b); if (a !== b) { if (a < b) parent[b] = a; else parent[a] = b; } };
    for (let y = 0; y < H; y++) {
      const o = y * W;
      for (let x = 0; x < W; x++) {
        const i = o + x; if (!m[i]) continue;
        let a = 0, b = 0, c = 0, d = 0;
        if (x > 0 && m[i - 1]) a = lab[i - 1];
        if (y > 0) { const j = i - W; if (x > 0 && m[j - 1]) b = lab[j - 1]; if (m[j]) c = lab[j]; if (x < W - 1 && m[j + 1]) d = lab[j + 1]; }
        let mn = 0;
        for (const v of [a, b, c, d]) if (v && (!mn || v < mn)) mn = v;
        if (!mn) {
          if (next >= parent.length) { const p2 = new Int32Array(parent.length * 2); p2.set(parent); parent = p2; }
          parent[next] = next; lab[i] = next++;
        } else {
          lab[i] = mn;
          if (a && a !== mn) unite(mn, a); if (b && b !== mn) unite(mn, b); if (c && c !== mn) unite(mn, c); if (d && d !== mn) unite(mn, d);
        }
      }
    }
    const stats = new Map();
    for (let y = 0; y < H; y++) {
      const o = y * W;
      for (let x = 0; x < W; x++) {
        const i = o + x; if (!lab[i]) continue;
        const r = find(lab[i]); lab[i] = r;
        let s = stats.get(r);
        if (!s) { s = { id: r, area: 0, x0: x, x1: x, y0: y, y1: y }; stats.set(r, s); }
        s.area++; if (x < s.x0) s.x0 = x; if (x > s.x1) s.x1 = x; if (y < s.y0) s.y0 = y; if (y > s.y1) s.y1 = y;
      }
    }
    return { lab, stats: [...stats.values()] };
  }

  function findRow(img) {
    const { L, S, W, H } = lumSat(img);
    const sc = W / 1920;
    const T = whiteLevel(L, S);
    const { lab, stats } = components(whiteMask(L, S, W, H, T), W, H);
    let comp = null;
    for (const s of stats) {
      const w = s.x1 - s.x0 + 1, h = s.y1 - s.y0 + 1;
      if (w < 250 * sc || h < 25 * sc || w / h < 3) continue;
      if (!comp || s.area > comp.area) comp = s;
    }
    if (!comp) return { why: "沒找到牌列" };
    const x = comp.x0, y = comp.y0, w = comp.x1 - comp.x0 + 1, h = comp.y1 - comp.y0 + 1;
    // top edge: the first row of the white region in each column
    const TX = [], TY = [], faceVals = [];
    for (let xx = x; xx < x + w; xx++) {
      for (let yy = y; yy < y + h; yy++) if (lab[yy * W + xx] === comp.id) { TX.push(xx); TY.push(yy); break; }
    }
    for (let yy = y; yy < y + h; yy++) for (let xx = x; xx < x + w; xx++) if (lab[yy * W + xx] === comp.id) faceVals.push(L[yy * W + xx]);
    const top = ransacLine(TX, TY, 2.5, 400, 1, 0.2);
    if (!top) return { why: "牌列上緣不清楚" };
    const { m: mt, c: ct } = top;
    // the dark strip under the cards: the strongest bright-above / dark-below straight edge
    const xa = x + 0.04 * w, xb = x + 0.96 * w, xm = (xa + xb) / 2, NX = 120;
    const X = new Float32Array(NX); for (let i = 0; i < NX; i++) X[i] = xa + (xb - xa) * i / (NX - 1);
    const vals = new Float32Array(NX);
    let best = null;
    for (let d = 0.06 * w; d < 0.30 * w; d += 1) {
      for (let k = -10; k <= 10; k++) {
        const dm = k * 0.004;
        for (let i = 0; i < NX; i++) {
          const Y = ct + mt * X[i] + d + dm * (X[i] - xm);
          const up = bil(L, W, H, X[i], Y - 3), dn = bil(L, W, H, X[i], Y + 4), dn2 = bil(L, W, H, X[i], Y + 10);
          vals[i] = Math.min(up - dn, up - dn2);
        }
        const s = median(vals);
        if (!best || s > best.s) best = { s, d, dm };
      }
    }
    // finer, around the best
    for (let d = best.d - 1; d <= best.d + 1 + 1e-9; d += 0.25) {
      for (let dm = best.dm - 0.004; dm <= best.dm + 0.004 + 1e-9; dm += 0.0005) {
        for (let i = 0; i < NX; i++) {
          const Y = ct + mt * X[i] + d + dm * (X[i] - xm);
          const up = bil(L, W, H, X[i], Y - 3), dn = bil(L, W, H, X[i], Y + 4), dn2 = bil(L, W, H, X[i], Y + 10);
          vals[i] = Math.min(up - dn, up - dn2);
        }
        const s = median(vals);
        if (s > best.s) best = { s, d, dm };
      }
    }
    const mb = mt + best.dm, cb = ct + best.d - best.dm * xm;
    const face = median(faceVals);
    // the row's ends: where the white faces start and stop, just under the top edge (above the rank glyphs)
    const x0s = x - 0.12 * w, nx = Math.floor(w * 1.17);
    const on = new Uint8Array(nx);
    for (const frac of [0.03, 0.05, 0.07]) {
      for (let i = 0; i < nx; i++) {
        const xx = x0s + i, yy = (ct + mt * xx) * (1 - frac) + (cb + mb * xx) * frac;
        if (bil(L, W, H, xx, yy) > 0.78 * face && bil(S, W, H, xx, yy) < 22) on[i] = 1;
      }
    }
    let mid = Math.round(x + w / 2 - x0s), lo = -1, hi = -1;
    if (on[mid]) { lo = hi = mid; }
    let gap = 0;
    for (let i = mid - 1; i >= 0; i--) { if (on[i]) { lo = i; gap = 0; if (hi < 0) hi = i; } else if (++gap > 6) break; }
    gap = 0;
    for (let i = mid + 1; i < nx; i++) { if (on[i]) { hi = i; gap = 0; if (lo < 0) lo = i; } else if (++gap > 6) break; }
    if (lo < 0 || hi <= lo) return { why: "找不到牌列兩端" };
    const xl = x0s + lo, xr = x0s + hi;
    return { mt, ct, mb, cb, xl, xr, edge: best.s, face, topInl: top.inl, T };
  }

  // ---------- 2. straighten it ----------
  // the row's corners from its top line and strip line, the ends pushed out by `ext` of the width on each side
  function quadOf(g, ext) {
    const { mt, ct, mb, cb } = g, m = ext * (g.xr - g.xl), xl = g.xl - m, xr = g.xr + m;
    const th = Math.atan(mt), nx = -Math.sin(th), ny = Math.cos(th);
    const hit = (x0, y0) => { const t = (cb + mb * x0 - y0) / (ny - mb * nx); return [x0 + t * nx, y0 + t * ny]; };
    const TL = [xl, ct + mt * xl], TR = [xr, ct + mt * xr];
    return [TL, TR, hit(...TR), hit(...TL)];
  }
  const applyH = (Hm, u, v) => { const z = Hm[6] * u + Hm[7] * v + Hm[8]; return [(Hm[0] * u + Hm[1] * v + Hm[2]) / z, (Hm[3] * u + Hm[4] * v + Hm[5]) / z]; };
  function straighten(img, quad, Hgiven) {
    const Hm = Hgiven || homography([[0, 0], [BW, 0], [BW, BH], [0, BH]], quad);   // band -> screenshot
    const { width: W, height: H, data } = img;
    const band = new Float32Array(BW * BH * 3);
    for (let v = 0; v < BH; v++) for (let u = 0; u < BW; u++) {
      const zz = Hm[6] * u + Hm[7] * v + Hm[8];
      let x = (Hm[0] * u + Hm[1] * v + Hm[2]) / zz, y = (Hm[3] * u + Hm[4] * v + Hm[5]) / zz;
      if (x < 0) x = 0; else if (x > W - 1) x = W - 1;
      if (y < 0) y = 0; else if (y > H - 1) y = H - 1;
      const x0 = Math.floor(x), y0 = Math.floor(y), x1 = x0 < W - 1 ? x0 + 1 : x0, y1 = y0 < H - 1 ? y0 + 1 : y0, tx = x - x0, ty = y - y0;
      const o = (v * BW + u) * 3;
      for (let ch = 0; ch < 3; ch++) {
        const a = data[(y0 * W + x0) * 4 + ch], b = data[(y0 * W + x1) * 4 + ch], c = data[(y1 * W + x0) * 4 + ch], d = data[(y1 * W + x1) * 4 + ch];
        band[o + ch] = (a * (1 - tx) + b * tx) * (1 - ty) + (c * (1 - tx) + d * tx) * ty;
      }
    }
    return { band, Hm };
  }
  function bandLum(band, w, h) {
    const L = new Float32Array(w * h);
    for (let i = 0; i < w * h; i++) L[i] = 0.299 * band[i * 3] + 0.587 * band[i * 3 + 1] + 0.114 * band[i * 3 + 2];
    return L;
  }

  // ---------- 3. the 13 card edges: an even comb ----------
  function lineProfile(Lb, r0, r1, face) {
    // thin dark vertical lines (each card's left edge): both neighbours 3 px away brighter than the column itself
    const v = new Float32Array(BW), bar = 0.68 * face;
    for (let x = 3; x < BW - 3; x++) {
      let s = 0;
      for (let r = r0; r < r1; r++) {
        const o = r * BW, l = Lb[o + x - 3], rr = Lb[o + x + 3], mn = l < rr ? l : rr;
        if (mn > bar) { let d = mn - Lb[o + x]; if (d < 0) d = 0; else if (d > 60) d = 60; s += d; }
      }
      v[x] = s / (r1 - r0);
    }
    return v;
  }
  function interp(p, x) {
    if (x < 0) x = 0; else if (x > p.length - 1.001) x = p.length - 1.001;
    const i = Math.floor(x), t = x - i; return p[i] * (1 - t) + p[i + 1] * t;
  }
  const RHO = 1.65, P0 = BW / (12 + RHO);   // the last card is 1.65 pitches wide; in the final band the pitch is P0
  function edgeProfile(Lb, face) {
    const a = lineProfile(Lb, 3, 14, face), b = lineProfile(Lb, 60, 112, face), prof = new Float32Array(BW);
    for (let i = 0; i < BW; i++) prof[i] = 2 * a[i] + b[i];
    return prof;
  }
  // card left edges 1..12 at x0 + i p; with ends, also the row's two ends (white starts at x0, stops at x0 + (12 + RHO) p)
  function fitComb(prof, pr, xr, ends) {
    let best = null;
    for (let p = pr[0]; p <= pr[1] + 1e-9; p += 0.1) {
      for (let x0 = xr[0]; x0 <= xr[1] + 1e-9; x0 += 0.5) {
        let s = 0;
        for (let i = 1; i <= 12; i++) s += interp(prof, x0 + p * i);
        let e = 0;
        if (ends) e = interp(ends.L, x0) + interp(ends.R, x0 + (12 + RHO) * p);
        if (!best || s + e > best.t) best = { t: s + e, s, e, p, x0 };
      }
    }
    return best;
  }
  // each edge 1..12: the strongest point within 7 px of the comb, to a fraction of a pixel
  function edgePeaks(prof, comb) {
    const out = [];
    for (let i = 1; i <= 12; i++) {
      const xc = comb.x0 + i * comb.p; let bx = -1, bv = -1;
      for (let x = Math.max(1, Math.round(xc - 7)); x <= Math.min(BW - 2, Math.round(xc + 7)); x++) if (prof[x] > bv) { bv = prof[x]; bx = x; }
      if (bx < 0) continue;
      const a = prof[bx - 1], b = prof[bx], c = prof[bx + 1], den = a - 2 * b + c;
      out.push({ i, x: bx + (den < 0 ? 0.5 * (a - c) / den : 0), v: bv });
    }
    return out;
  }
  // x = (a + b i) / (1 + c i) through the edge positions (weak ones and outliers dropped)
  function projFit(pk) {
    if (!pk.length) return null;
    const vmed = median(pk.map((q) => q.v));
    let pts = pk.filter((q) => q.v >= 0.35 * vmed);
    const fit = (P) => {
      // least squares for [1, i, -i x] . [a, b, c] = x
      const A = [[0, 0, 0], [0, 0, 0], [0, 0, 0]], r = [0, 0, 0];
      for (const q of P) { const row = [1, q.i, -q.i * q.x]; for (let j = 0; j < 3; j++) { r[j] += row[j] * q.x; for (let k = 0; k < 3; k++) A[j][k] += row[j] * row[k]; } }
      const [a, b, c] = solve(A, r);
      return { a, b, c, f: (i) => (a + b * i) / (1 + c * i) };
    };
    let F = null;
    for (let it = 0; it < 4; it++) {
      if (pts.length < 8) return null;
      F = fit(pts);
      let worst = null;
      for (const q of pts) { const e = Math.abs(F.f(q.i) - q.x); if (!worst || e > worst.e) worst = { e, q }; }
      F.res = worst.e; F.n = pts.length;
      if (worst.e <= 1.5) break;
      pts = pts.filter((q) => q !== worst.q);
    }
    return F;
  }
  // white just under the top edge (rows 3..12): where it starts (L) and stops (R)
  function endProfiles(band, Lb, face) {
    const w = new Float32Array(BW), L = new Float32Array(BW), R = new Float32Array(BW);
    for (let x = 0; x < BW; x++) {
      let c = 0;
      for (let r = 3; r < 13; r++) {
        const i = r * BW + x, o = i * 3, mx = Math.max(band[o], band[o + 1], band[o + 2]), mn = Math.min(band[o], band[o + 1], band[o + 2]);
        if (Lb[i] > 0.78 * face && mx - mn < 22) c++;
      }
      w[x] = c / 10;
    }
    for (let x = 3; x < BW - 3; x++) { L[x] = 40 * Math.max(0, w[x + 3] - w[x - 3]); R[x] = 40 * Math.max(0, w[x - 3] - w[x + 3]); }
    return { L, R };
  }

  // ---------- 4. each card's rank and suit ----------
  function cardStrip(band, xa) {
    const st = new Float32Array(SW * BH * 3);
    for (let y = 0; y < BH; y++) for (let x = 0; x < SW; x++) {
      let sx = x + xa; if (sx < 0) sx = 0; else if (sx > BW - 1) sx = BW - 1;
      const x0 = Math.floor(sx), x1 = x0 < BW - 1 ? x0 + 1 : x0, t = sx - x0, o = (y * SW + x) * 3;
      for (let ch = 0; ch < 3; ch++) st[o + ch] = band[(y * BW + x0) * 3 + ch] * (1 - t) + band[(y * BW + x1) * 3 + ch] * t;
    }
    return st;
  }
  function runs(v, thr, minlen) {
    const out = []; let i = 0;
    while (i < v.length) {
      if (v[i] > thr) { let j = i; while (j < v.length && v[j] > thr) j++; if (j - i >= minlen) out.push([i, j]); i = j; } else i++;
    }
    return out;
  }
  // a W x H window of the ink centred on the ink's box inside rows r0..r1, cols c0..c1
  function cut(ink, r0, r1, c0, c1, Wn, Hn) {
    let rmin = -1, rmax = -1, cmin = -1, cmax = -1;
    for (let r = r0; r < r1; r++) for (let c = c0; c < c1; c++) if (ink[r * SW + c] > 0.5) {
      if (rmin < 0) rmin = r; rmax = r; if (cmin < 0 || c < cmin) cmin = c; if (c > cmax) cmax = c;
    }
    if (rmin < 0) return null;
    const cy = (rmin + rmax) / 2, cx = (cmin + cmax) / 2, out = new Float32Array(Wn * Hn);
    for (let y = 0; y < Hn; y++) for (let x = 0; x < Wn; x++) out[y * Wn + x] = bilZero(ink, SW, BH, x + cx - Wn / 2, y + cy - Hn / 2);
    return { win: out, h: rmax - rmin + 1, w: cmax - cmin + 1, top: rmin, left: cmin };
  }
  function half(a, Wn, Hn) {
    const w = Wn >> 1, h = Hn >> 1, o = new Float32Array(w * h);
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
      const i = 2 * y * Wn + 2 * x; o[y * w + x] = (a[i] + a[i + 1] + a[i + Wn] + a[i + Wn + 1]) / 4;
    }
    return o;
  }
  function glyphs(st) {
    const Ls = bandLum(st, SW, BH), reg = [];
    for (let r = 4; r < 112; r++) for (let c = 2; c < 52; c++) reg.push(Ls[r * SW + c]);
    const face = percentile(reg, 92), dark = percentile(reg, 1), span = Math.max(30, face - dark);
    const ink = new Float32Array(SW * BH);
    for (let i = 0; i < SW * BH; i++) { let v = (face - Ls[i]) / span; ink[i] = v < 0 || i % SW < 5 ? 0 : v > 1 ? 1 : v; }
    const prof = new Float32Array(115);
    for (let r = 0; r < 115; r++) { let m = 0; for (let c = 4; c < 48; c++) if (ink[r * SW + c] > m) m = ink[r * SW + c]; prof[r] = m; }
    const rr = runs(prof, 0.5, 6).filter((q) => q[0] >= 4);
    const k = rr.findIndex((q) => q[1] - q[0] >= 20);
    if (k < 0 || k + 1 >= rr.length) return null;
    const [a0, a1] = rr[k];
    const rank = cut(ink, a0, a1, 2, 52, RWIN[0], RWIN[1]);
    if (!rank) return null;
    // the suit: the ink blob right under the rank (the big suit symbol further down stays out)
    const r0 = a1 + 2, r1 = Math.min(a1 + 40, BH), c0 = 2, c1 = 46, ww = c1 - c0, hh = r1 - r0;
    const m = new Uint8Array(ww * hh);
    for (let r = 0; r < hh; r++) for (let c = 0; c < ww; c++) m[r * ww + c] = ink[(r0 + r) * SW + c0 + c] > 0.5 ? 1 : 0;
    const { lab, stats } = components(m, ww, hh);
    let bestc = null;
    for (const s of stats) { if (s.area < 30) continue; const sc = s.area - 3 * s.y0; if (!bestc || sc > bestc.sc) bestc = { sc, id: s.id }; }
    if (!bestc) return null;
    const ink2 = new Float32Array(SW * BH);
    for (let r = 0; r < hh; r++) for (let c = 0; c < ww; c++) {
      let near = false;
      for (let dy = -2; dy <= 2 && !near; dy++) for (let dx = -2; dx <= 2; dx++) {
        const yy = r + dy, xx = c + dx;
        if (yy >= 0 && yy < hh && xx >= 0 && xx < ww && lab[yy * ww + xx] === bestc.id) { near = true; break; }
      }
      if (near) ink2[(r0 + r) * SW + c0 + c] = ink[(r0 + r) * SW + c0 + c];
    }
    const suit = cut(ink2, r0, r1, c0, c1, SWIN[0], SWIN[1]);
    if (!suit) return null;
    let rs = 0, rn = 0;
    for (let r = 0; r < 115; r++) for (let c = 0; c < SW; c++) {
      const i = r * SW + c; if (ink[i] > 0.5) { rs += st[i * 3] - 0.5 * (st[i * 3 + 1] + st[i * 3 + 2]); rn++; }
    }
    return {
      r: half(rank.win, RWIN[0], RWIN[1]), s: half(suit.win, SWIN[0], SWIN[1]),
      red: rn > 5 ? rs / rn : 0, rh: rank.h, sh: suit.h, rtop: rank.top, rleft: rank.left, stop: suit.top,
    };
  }

  // ---------- matching ----------
  const RW2 = RWIN[0] >> 1, RH2 = RWIN[1] >> 1, SW2 = SWIN[0] >> 1, SH2 = SWIN[1] >> 1;
  // zero-mean normalised correlation of a (w x h) against T, best over shifts of a by up to sh px (zeros come in)
  function ncc(a, T, w, h, sh) {
    let tm = 0; for (let i = 0; i < w * h; i++) tm += T[i]; tm /= w * h;
    let tt = 0; for (let i = 0; i < w * h; i++) tt += (T[i] - tm) * (T[i] - tm);
    let best = -1;
    for (let dy = -sh; dy <= sh; dy++) for (let dx = -sh; dx <= sh; dx++) {
      let s = 0, ss = 0, st = 0, n = w * h;
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
        const yy = y + dy, xx = x + dx, b = yy >= 0 && yy < h && xx >= 0 && xx < w ? a[yy * w + xx] : 0;
        s += b; ss += b * b; st += b * (T[y * w + x] - tm);
      }
      const bm = s / n, var_ = ss - n * bm * bm, v = st / (Math.sqrt(Math.max(var_, 0) * tt) + 1e-6);
      if (v > best) best = v;
    }
    return best;
  }
  function classify(gl, model) {
    const sc = model.rank.map((T) => ncc(gl.r, T, RW2, RH2, 1));
    const order = sc.map((v, i) => i).sort((p, q) => sc[q] - sc[p]);
    const rank = order[0], rTop = sc[rank], rMargin = sc[rank] - sc[order[1]];
    const isRed = gl.red > 35, colourSure = gl.red > 35 || gl.red < 20;
    const L = isRed ? model.lda.red : model.lda.black;     // red: 1 ♦ vs 2 ♥ ; black: 0 ♣ vs 3 ♠
    let z = -L.t; for (let i = 0; i < L.w.length; i++) z += gl.s[i] * L.w[i]; z /= L.s;
    const suit = isRed ? (z > 0 ? 2 : 1) : (z > 0 ? 3 : 0);
    return { card: rank * 4 + suit, rank, suit, rTop, rMargin, z, red: gl.red, colourSure };
  }

  // the game shows the row sorted by rank (♣ ♦ ♥ ♠ within a rank), or grouped by suit (♠ ♥ ♣ ♦, A 2 3 … K within a suit)
  const SUIT_GROUP = [2, 3, 1, 0];
  function gameOrder(cards) {
    const byRank = (c) => c, bySuit = (c) => SUIT_GROUP[c & 3] * 13 + (((c >> 2) + 1) % 13);
    return [byRank, bySuit].some((k) => cards.every((c, i) => i === 0 || k(c) > k(cards[i - 1])));
  }

  // ---------- the whole reading ----------
  const LIMITS = { topInl: 0.85, edge: 100, hRatio: [0.14, 0.2], x0: 4, dp: 1.5, comb: 6, rTop: 0.9, rMargin: 0.04, z: 0.3,
    rtop: [10, 25], rh: [33, 52], sh: [14, 30], gap: [4, 16], dev: 3.5 };
  function extract(img) {
    const t0 = Date.now();
    const g = findRow(img);
    if (g.why) return { why: g.why };
    const width = Math.hypot(g.xr - g.xl, (g.ct + g.mt * g.xr) - (g.ct + g.mt * g.xl));
    const hgt = (g.cb + g.mb * g.xl) - (g.ct + g.mt * g.xl);
    // pass 1: a wider band. Its card edges are straight lines, spaced evenly only up to perspective, so: a rough even comb,
    // then each edge found on the top rows and on the lower rows, then x = (a + b i) / (1 + c i) through each set.
    const EXT = 0.05, b1 = straighten(img, quadOf(g, EXT)), L1 = bandLum(b1.band, BW, BH);
    // top rows: only the card edges are there (weighted up); lower rows: above the arrange screen's buttons
    const pTop = lineProfile(L1, 3, 14, g.face), pLow = lineProfile(L1, 60, 112, g.face), sum = new Float32Array(BW);
    for (let i = 0; i < BW; i++) sum[i] = 2 * pTop[i] + pLow[i];
    const pe = BW / ((1 + 2 * EXT) * (12 + RHO)), x0e = BW * EXT / (1 + 2 * EXT);
    const c1 = fitComb(sum, [0.85 * pe, 1.15 * pe], [x0e - 0.6 * pe, x0e + 0.6 * pe], endProfiles(b1.band, L1, g.face));
    const fitT = projFit(edgePeaks(pTop, c1)), fitL = projFit(edgePeaks(pLow, c1));
    if (!fitT || !fitL) return { why: "分不出 13 張牌的邊" };
    // each edge as a line in the screenshot; where it meets the top line and the strip line, it is at x = i * P0
    const yT = 8.5, yL = 86, P = [], Q = [];
    const meet = (p1, p2, m, c) => { const dx = p2[0] - p1[0], dy = p2[1] - p1[1], t = (c + m * p1[0] - p1[1]) / (dy - m * dx); return [p1[0] + t * dx, p1[1] + t * dy]; };
    for (let i = 1; i <= 12; i++) {
      const a = applyH(b1.Hm, fitT.f(i), yT), b = applyH(b1.Hm, fitL.f(i), yL);
      P.push([i * P0, 0]); Q.push(meet(a, b, g.mt, g.ct));
      P.push([i * P0, BH]); Q.push(meet(a, b, g.mb, g.cb));
    }
    const H2 = homographyLSQ(P, Q);
    const quad = [applyH(H2, 0, 0), applyH(H2, BW, 0), applyH(H2, BW, BH), applyH(H2, 0, BH)];
    // pass 2: exactly the row; the cards should now sit at i * P0
    const { band } = straighten(img, null, H2), Lb = bandLum(band, BW, BH);
    const prof2 = edgeProfile(Lb, g.face);
    const comb = fitComb(prof2, [P0 - 2.5, P0 + 2.5], [-8, 8], null);
    const pk = edgePeaks(prof2, comb);
    comb.dev = Math.max(...pk.map((q) => Math.abs(q.x - (comb.x0 + q.i * comb.p))));
    comb.fitT = fitT.res; comb.fitL = fitL.res; comb.nT = fitT.n; comb.nL = fitL.n;
    const cards = [];
    for (let i = 0; i < 13; i++) cards.push(glyphs(cardStrip(band, comb.x0 + i * comb.p)));
    return { band, g: { topInl: g.topInl, edge: g.edge, hRatio: hgt / width, width, face: g.face, T: g.T }, comb1: { p: c1.p, x0: c1.x0, s: c1.s / 12, e: c1.e, c: fitT.c },
      comb: { p: comb.p, x0: comb.x0, s: comb.s / 12, dev: comb.dev, fitT: comb.fitT, fitL: comb.fitL, nT: comb.nT, nL: comb.nL }, cards, quad, ms: Date.now() - t0 };
  }
  function read(img, model) {
    const ex = extract(img);
    if (ex.why) return { ok: false, why: ex.why };
    const { g, comb } = ex, why = [];
    if (g.topInl < LIMITS.topInl) why.push("牌列上緣不直");
    if (g.edge < LIMITS.edge) why.push("牌列下方的深色條不清楚");
    if (g.hRatio < LIMITS.hRatio[0] || g.hRatio > LIMITS.hRatio[1]) why.push("牌列比例不對");
    if (Math.abs(comb.x0) > LIMITS.x0 || Math.abs(comb.p - P0) > LIMITS.dp || comb.s < LIMITS.comb || comb.dev > LIMITS.dev) why.push("分不出 13 張牌的邊");
    const res = ex.cards.map((gl) => (gl ? classify(gl, model) : null));
    const unsure = [];
    res.forEach((c, i) => {
      if (!c) { unsure.push(i); return; }
      const gl = ex.cards[i], inR = (v, r) => v >= r[0] && v <= r[1];
      const placed = inR(gl.rtop, LIMITS.rtop) && inR(gl.rh, LIMITS.rh) && inR(gl.sh, LIMITS.sh) && inR(gl.stop - (gl.rtop + gl.rh), LIMITS.gap);
      if (!placed || c.rTop < LIMITS.rTop || c.rMargin < LIMITS.rMargin || !c.colourSure || Math.abs(c.z) < LIMITS.z) unsure.push(i);
    });
    if (unsure.length) why.push(`第 ${unsure.map((i) => i + 1).join("、")} 張不確定`);
    const cards = res.map((c) => (c ? c.card : -1));
    if (!why.length && !gameOrder(cards)) why.push("讀到的順序和遊戲排法不合");
    const got = res.filter(Boolean), low = (k, f) => (got.length ? Math.min(...got.map(f)) : 0);
    const conf = { t: low("t", (c) => c.rTop), m: low("m", (c) => c.rMargin), z: low("z", (c) => Math.abs(c.z)) };
    return { ok: !why.length, why: why.join("；"), cards, detail: res, geo: g, comb, unsure, conf, ms: ex.ms };
  }

  // ---------- making the model from labelled screenshots ----------
  function alignedMean(samples, w, h, sh) {
    let m = new Float32Array(w * h);
    for (const s of samples) for (let i = 0; i < m.length; i++) m[i] += s[i] / samples.length;
    for (let it = 0; it < 2; it++) {
      const acc = new Float32Array(w * h);
      let mn = 0; for (let i = 0; i < m.length; i++) mn += m[i] * m[i]; mn = Math.sqrt(mn);
      for (const s of samples) {
        let best = null;
        for (let dy = -sh; dy <= sh; dy++) for (let dx = -sh; dx <= sh; dx++) {
          let dot = 0, bb = 0;
          for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
            const yy = y + dy, xx = x + dx, b = yy >= 0 && yy < h && xx >= 0 && xx < w ? s[yy * w + xx] : 0;
            dot += b * m[y * w + x]; bb += b * b;
          }
          const v = dot / (Math.sqrt(bb) * mn + 1e-6);
          if (!best || v > best.v) best = { v, dy, dx };
        }
        for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
          const yy = y + best.dy, xx = x + best.dx;
          acc[y * w + x] += (yy >= 0 && yy < h && xx >= 0 && xx < w ? s[yy * w + xx] : 0) / samples.length;
        }
      }
      m = acc;
    }
    return m;
  }
  function lda(A, B, reg) {
    const d = A[0].length, mean = (X) => { const m = new Float64Array(d); for (const x of X) for (let i = 0; i < d; i++) m[i] += x[i] / X.length; return m; };
    const ma = mean(A), mb = mean(B), n = A.length + B.length;
    const C = Array.from({ length: d }, () => new Float64Array(d));
    for (const [X, m] of [[A, ma], [B, mb]]) for (const x of X) {
      const c = new Float64Array(d); for (let i = 0; i < d; i++) c[i] = x[i] - m[i];
      for (let i = 0; i < d; i++) { const ci = c[i]; if (!ci) continue; const row = C[i]; for (let j = 0; j < d; j++) row[j] += ci * c[j]; }
    }
    // covariance of the pooled, centred samples (numpy's n-1), plus a ridge
    let tot = new Float64Array(d);
    const allc = [];
    for (const [X, m] of [[A, ma], [B, mb]]) for (const x of X) { const c = new Float64Array(d); for (let i = 0; i < d; i++) c[i] = x[i] - m[i]; allc.push(c); }
    for (const c of allc) for (let i = 0; i < d; i++) tot[i] += c[i] / n;
    const M = C.map((row, i) => Array.from(row, (v, j) => (v - n * tot[i] * tot[j]) / (n - 1) + (i === j ? reg : 0)));
    const w = solve(M, Array.from(mb, (v, i) => v - ma[i]));
    const dot = (x) => { let s = 0; for (let i = 0; i < d; i++) s += x[i] * w[i]; return s; };
    const t = 0.5 * (dot(ma) + dot(mb));
    const sa = A.reduce((s, x) => s + dot(x) - t, 0) / A.length, sb = B.reduce((s, x) => s + dot(x) - t, 0) / B.length;
    return { w: Float32Array.from(w), t, s: (sb - sa) / 2 };
  }
  // samples: [{gl, card}] ; returns the model
  function train(samples) {
    const byRank = Array.from({ length: 13 }, () => []), bySuit = Array.from({ length: 4 }, () => []);
    for (const { gl, card } of samples) { byRank[card >> 2].push(gl.r); bySuit[card & 3].push(gl.s); }
    return {
      rank: byRank.map((s) => alignedMean(s, RW2, RH2, 1)),
      lda: { black: lda(bySuit[0], bySuit[3], 0.05), red: lda(bySuit[1], bySuit[2], 0.05) },
    };
  }
  // compact model for the page: rank templates as bytes, LDA weights as float32, both base64
  function pack(model, b64) {
    const ranks = new Uint8Array(13 * RW2 * RH2);
    model.rank.forEach((T, k) => { let mx = 0; for (const v of T) if (v > mx) mx = v; T.forEach((v, i) => { ranks[k * RW2 * RH2 + i] = Math.round(255 * v / (mx || 1)); }); });
    const L = (o) => ({ w: b64(new Uint8Array(o.w.buffer.slice(0))), t: o.t, s: o.s });
    return { v: 1, rank: b64(ranks), lda: { black: L(model.lda.black), red: L(model.lda.red) } };
  }
  function unpack(p, unb64) {
    const bytes = unb64(p.rank), rank = [];
    for (let k = 0; k < 13; k++) rank.push(Float32Array.from(bytes.subarray(k * RW2 * RH2, (k + 1) * RW2 * RH2), (v) => v / 255));
    const L = (o) => ({ w: new Float32Array(unb64(o.w).buffer.slice(0)), t: o.t, s: o.s });
    return { rank, lda: { black: L(p.lda.black), red: L(p.lda.red) } };
  }
  // the low-level pieces, shared with the 大老二 reader
  const _ = { median, percentile, bil, bilZero, ransacLine, solve, homography, homographyLSQ, lumSat, components, applyH, straighten, bandLum, interp, cardStrip, glyphs, classify, ncc, quadOf, SW };
  return { read, extract, classify, train, pack, unpack, gameOrder, LIMITS, BW, BH, P0, _ };
})();
"use strict";
// 大老二 screenshots read on the device: your own row of cards (1 to 13 of them, lit or shaded).
// The low-level pieces come from LocalRead (the 十三支 reader); the cards are drawn the same way in both games.
const B2Read = (() => {
  const K = (typeof LocalRead !== "undefined" ? LocalRead : require("./localread.js"))._;
  const BW = 1000, BH = 160, EXT = 0.05;
  const CW = BW * 1.65 / 13.65;       // a whole card's width in the straightened row
  const HC0 = 1.278;                  // 大老二: the visible card height is 1.28 card widths seen head-on (十三支: 1.348)
  const VROWS0 = BH * HC0 / 1.348;    // rows that height takes, so that glyphs keep the size the templates have
  const NEUTRAL = 40, DIM = 95;       // a card face, lit or shaded: grey to white
  // spacing between cards, in card widths, for 1..13 cards in the row (measured on recordings)
  const PITCH = [0, 0, 0.842, 0.842, 0.842, 0.842, 0.842, 0.842, 0.842, 0.842, 0.788, 0.7145, 0.654, 0.606];

  function closeH(m, W, H, r) {
    const n = W * H, d = new Uint8Array(n), e = new Uint8Array(n);
    for (let y = 0; y < H; y++) {
      const o = y * W;
      for (let x = 0; x < W; x++) { let v = 0; const a = Math.max(0, x - r), z = Math.min(W - 1, x + r); for (let xx = a; xx <= z; xx++) if (m[o + xx]) { v = 1; break; } d[o + x] = v; }
      for (let x = 0; x < W; x++) { let v = 1; const a = Math.max(0, x - r), z = Math.min(W - 1, x + r); for (let xx = a; xx <= z; xx++) if (!d[o + xx]) { v = 0; break; } e[o + x] = v; }
    }
    return e;
  }
  // ---------- the black strip along the bottom of the game window ----------
  // Its top edge is the longest straight line in the screenshot with something bright right above and black right below
  // (cards, buttons or table above it, across the whole window). Found first; the cards are then looked for above it only.
  // the table's purple (blue above green, red above green): it fills the bottom of the window from edge to edge, so just
  // above the strip it shows where the window starts and ends, whatever lies around the window
  const isPurple = (r, g, b) => b - g > 30 && r - g > 10 && b > r && b > 150;
  function windowSpan(img, st, len) {
    const { width: W, height: H, data } = img;
    const yAt = (x) => st.c + st.m * x;
    // (wide: something lying over the strip, such as the window's own handle, can cut the dark run short)
    const bx0 = Math.max(0, Math.floor(st.x0 - 1.2 * len)), bx1 = Math.min(W - 1, Math.ceil(st.x1 + 1.2 * len));
    const by0 = Math.max(0, Math.floor(Math.min(yAt(bx0), yAt(bx1)) - 0.75 * len)), by1 = Math.min(H - 1, Math.ceil(Math.max(yAt(bx0), yAt(bx1))));
    const bw = bx1 - bx0 + 1, bh = by1 - by0 + 1;
    if (bw < 10 || bh < 10) return null;
    // at half resolution: plenty for a region this size
    const w2 = bw >> 1, h2 = bh >> 1, m = new Uint8Array(w2 * h2);
    for (let y = 0; y < h2; y++) for (let x = 0; x < w2; x++) {
      const xx = bx0 + 2 * x, yy = by0 + 2 * y;
      if (yy > yAt(xx)) continue;
      const i = (yy * W + xx) * 4;
      if (isPurple(data[i], data[i + 1], data[i + 2])) m[y * w2 + x] = 1;
    }
    const { lab, stats } = K.components(m, w2, h2);
    let big = null; for (const c of stats) if (!big || c.area > big.area) big = c;
    if (!big || big.area < 0.02 * len * len / 4) return null;
    // its extent in the lowest 6 % above the strip
    let lo = Infinity, hi = -Infinity;
    for (let y = 0; y < h2; y++) for (let x = 0; x < w2; x++) {
      if (lab[y * w2 + x] !== big.id) continue;
      const xx = bx0 + 2 * x, yy = by0 + 2 * y, d = yAt(xx) - yy;
      if (d < 0 || d > 0.06 * len) continue;
      if (xx < lo) lo = xx; if (xx > hi) hi = xx;
    }
    return hi - lo > 0.3 * len ? { x0: lo, x1: hi + 1 } : null;
  }
  function findStrip(LS, img) {
    const { L, W, H } = LS, sc = W / 1920, PX = [], PY = [], step = 2;
    for (let x = 0; x < W; x += step) {
      let was = false;
      for (let y = 5; y < H - 12; y++) {
        const is = L[(y - 3) * W + x] > 90 && L[(y + 3) * W + x] < 30 && L[(y + 5) * W + x] < 40;   // the white text sits lower in the strip
        if (is && !was) { PX.push(x); PY.push(y); }
        was = is;
      }
    }
    const n = PX.length; if (n < 60) return null;
    let a = 12345; const rnd = () => { a = (a + 0x6d2b79f5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
    const cols = Math.ceil(W / step), hit = new Uint8Array(cols);
    // the longest run of columns on the line (holes up to 60 px: a black suit symbol or a dark button can break the edge)
    const runOf = (m, c) => {
      hit.fill(0);
      for (let q = 0; q < n; q++) if (Math.abs(PY[q] - (c + m * PX[q])) < 2.5) hit[PX[q] / step] = 1;
      let best = null, s = -1, last = -1, cnt = 0;
      const close = () => { if (s >= 0 && (!best || cnt > best.cnt)) best = { cnt, x0: s * step, x1: last * step }; };
      for (let i = 0; i < cols; i++) if (hit[i]) { if (s < 0 || (i - last) * step > 60 * sc) { close(); s = i; cnt = 0; } last = i; cnt++; }
      close();
      return best;
    };
    let best = null;
    for (let k = 0; k < 1500; k++) {
      const i = Math.floor(rnd() * n), j = Math.floor(rnd() * n), dx = PX[j] - PX[i];
      if (Math.abs(dx) < 120 * sc) continue;
      const m = (PY[j] - PY[i]) / dx; if (Math.abs(m) > 0.15) continue;
      const r = runOf(m, PY[i] - m * PX[i]);
      if (r && (!best || r.cnt > best.cnt)) best = { cnt: r.cnt, m, c: PY[i] - m * PX[i], x0: r.x0, x1: r.x1 };
    }
    if (!best || (best.x1 - best.x0) < 250 * sc) return null;
    // least squares through the points on it
    let sx = 0, sy = 0, sxx = 0, sxy = 0, cnt = 0;
    for (let q = 0; q < n; q++) if (PX[q] >= best.x0 && PX[q] <= best.x1 && Math.abs(PY[q] - (best.c + best.m * PX[q])) < 2.5) { sx += PX[q]; sy += PY[q]; sxx += PX[q] * PX[q]; sxy += PX[q] * PY[q]; cnt++; }
    const m = (cnt * sxy - sx * sy) / (cnt * sxx - sx * sx), c = (sy - m * sx) / cnt;
    // how far the strip runs: black just under the line (dark buttons or suit symbols above it do not matter here)
    // (a button may overlap the strip's top few pixels, white text sits in its middle: black at any of four depths counts)
    const black = (x) => { const y = Math.round(c + m * x); for (const d of [3, 8, 14, 20]) { const yy = y + Math.round(d * sc); if (yy >= 0 && yy < H && L[yy * W + x] < 40) return true; } return false; };
    let x0 = best.x0, x1 = best.x1, gap = 0;
    for (let x = best.x0 - 1; x >= 0; x--) { if (black(x)) { x0 = x; gap = 0; } else if (++gap > 25 * sc) break; }
    gap = 0;
    for (let x = best.x1 + 1; x < W; x++) { if (black(x)) { x1 = x; gap = 0; } else if (++gap > 25 * sc) break; }
    // with a light room around the window the dark run can stop early or run on into the room: the table says where the
    // window is
    const st = { m, c, x0, x1, cnt, from: "strip" };
    if (img) {
      const sp = windowSpan(img, st, x1 - x0);
      if (sp) { st.sx0 = x0; st.sx1 = x1; st.x0 = sp.x0; st.x1 = sp.x1; st.from = "table"; }
    }
    return st;
  }
  // ---------- the row of cards standing on the strip ----------
  function findRow(LS, img) {
    const { L, S, W, H } = LS;
    const st = findStrip(LS, img);
    if (!st) return { why: "沒找到遊戲視窗底下的黑條" };
    // card faces (lit or shaded) in the band above the strip, as one component that reaches down to the strip
    // (inside the window: around it may be a light room)
    // With the window's own edges known (from the table), the band stays inside them (a light rim or room beside it would
    // join the cards to things higher up) and runs parallel to the strip, no higher than the cards and a little more.
    const inWin = st.from === "table", len = st.x1 - st.x0, up = Math.round((inWin ? 0.2 : 0.34) * len), mg = inWin ? -0.01 * len : 0.03 * len;
    const bx0 = Math.max(0, Math.floor(st.x0 - mg)), bx1 = Math.min(W - 1, Math.ceil(st.x1 + mg));
    const yAt = (x) => st.c + st.m * x, band = inWin ? 0.18 * len : Infinity;
    const by0 = Math.max(0, Math.floor(Math.min(yAt(bx0), yAt(bx1)) - up)), by1 = Math.min(H - 1, Math.ceil(Math.max(yAt(bx0), yAt(bx1)) + 2));
    const bw = bx1 - bx0 + 1, bh = by1 - by0 + 1, m = new Uint8Array(bw * bh);
    for (let y = 0; y < bh; y++) for (let x = 0; x < bw; x++) {
      const yy = by0 + y, xx = bx0 + x, i = yy * W + xx;
      if (yy < yAt(xx) + 1 && yy > yAt(xx) - band && S[i] < NEUTRAL && L[i] > DIM) m[y * bw + x] = 1;
    }
    const { lab, stats } = K.components(closeH(m, bw, bh, 3), bw, bh);
    let comp = null;
    for (const s of stats) {
      if (s.area < 600) continue;
      // how many of its columns reach the strip
      let reach = 0; const w = s.x1 - s.x0 + 1;
      for (let x = s.x0; x <= s.x1; x++) { const yb = Math.round(yAt(bx0 + x)) - by0; for (let y = yb; y >= Math.max(0, yb - 6); y--) if (y < bh && lab[y * bw + x] === s.id) { reach++; break; } }
      if (reach < 0.15 * w) continue;                 // buttons lie over the cards' lower part on much of the width
      if (!comp || s.area > comp.area) comp = s;
    }
    if (!comp) return { why: "黑條上面沒找到手牌" };
    const cx = [], cy = [], ch = [], vals = [];
    for (let x = comp.x0; x <= comp.x1; x++) for (let y = comp.y0; y <= comp.y1; y++) if (lab[y * bw + x] === comp.id) { cx.push(bx0 + x); cy.push(by0 + y); ch.push(yAt(bx0 + x) - (by0 + y)); break; }
    for (let y = comp.y0; y <= comp.y1; y += 2) for (let x = comp.x0; x <= comp.x1; x += 2) if (lab[y * bw + x] === comp.id) vals.push(L[(by0 + y) * W + bx0 + x]);
    // the cards' top edge: only columns standing a full card high (the hint buttons across the window are lower)
    const h95 = K.percentile(ch, 95), TX = [], TY = [];
    for (let i = 0; i < cx.length; i++) if (ch[i] >= 0.75 * h95) { TX.push(cx[i]); TY.push(cy[i]); }
    const top = K.ransacLine(TX, TY, 2.5, 400, 1, 0.2);
    if (!top) return { why: "手牌上緣不清楚" };
    const { m: mt, c: ct } = top, faceHigh = K.percentile(vals, 90), thr = Math.max(90, 0.5 * faceHigh);
    const x = bx0 + comp.x0, w = comp.x1 - comp.x0 + 1, tallMid = K.median(TX);
    // the strip edge again, where the cards are, by the brightest-above / darkest-below rule (the measure the heights use)
    const xa = x + 0.04 * w, xb = x + 0.96 * w, xm = (xa + xb) / 2, NX = 120;
    const X = new Float32Array(NX); for (let i = 0; i < NX; i++) X[i] = xa + (xb - xa) * i / (NX - 1);
    const v = new Float32Array(NX);
    const edgeAt = (c0, m0) => {
      for (let i = 0; i < NX; i++) {
        const Y = c0 + m0 * X[i];
        const u = K.bil(L, W, H, X[i], Y - 3), dn = K.bil(L, W, H, X[i], Y + 4), dn2 = K.bil(L, W, H, X[i], Y + 10);
        v[i] = Math.min(u - dn, u - dn2);
      }
      return K.median(v);
    };
    let best = null;
    for (let d = -6; d <= 8 + 1e-9; d += 0.25) for (let dm = -0.004; dm <= 0.004 + 1e-9; dm += 0.0005) {
      const m0 = st.m + dm, c0 = st.c + d - dm * xm, s = edgeAt(c0, m0);
      if (!best || s > best.s) best = { s, m: m0, c: c0 };
    }
    const mb = best.m, cb = best.c;
    // the ends: where card faces start and stop just under the top edge (above the rank glyphs)
    const x0s = x - 0.12 * w, nx = Math.floor(w * 1.24), on = new Uint8Array(nx);
    for (const frac of [0.03, 0.05, 0.07]) for (let i = 0; i < nx; i++) {
      const xx = x0s + i, yy = (ct + mt * xx) * (1 - frac) + (cb + mb * xx) * frac;
      if (st.from === "table" && (xx < st.x0 || xx > st.x1)) continue;
      if (K.bil(L, W, H, xx, yy) > thr && K.bil(S, W, H, xx, yy) < 30) on[i] = 1;
    }
    const mid = Math.max(0, Math.min(nx - 1, Math.round(tallMid - x0s))); let lo = on[mid] ? mid : -1, hi = lo, gap = 0;
    for (let i = mid - 1; i >= 0; i--) { if (on[i]) { lo = i; gap = 0; if (hi < 0) hi = i; } else if (++gap > 6) break; }
    gap = 0;
    for (let i = mid + 1; i < nx; i++) { if (on[i]) { hi = i; gap = 0; if (lo < 0) lo = i; } else if (++gap > 6) break; }
    if (lo < 0 || hi <= lo) return { why: "找不到手牌兩端" };
    return { mt, ct, mb, cb, xl: x0s + lo, xr: x0s + hi, edge: best.s, rel: best.s / faceHigh, faceHigh, thr, topInl: top.inl, strip: st, box: [x, by0 + comp.y0, w, comp.y1 - comp.y0 + 1] };
  }

  // ---------- the card edges: an even comb whose number of teeth is not known ----------
  // thin dark vertical lines, as a share of the brightness beside them (works on lit and shaded cards alike)
  function relProfile(Lb, r0, r1, steps) {
    const v = new Float32Array(BW);
    for (let x = 3; x < BW - 3; x++) {
      let s = 0;
      for (let r = r0; r < r1; r++) {
        const o = r * BW, l = Lb[o + x - 3], rr = Lb[o + x + 3], mn = l < rr ? l : rr, mx = l < rr ? rr : l;
        if (mn > 80) {
          let d = (mn - Lb[o + x]) / mn; if (d < 0) d = 0; else if (d > 0.25) d = 0.25;
          if (steps) { let e = (mx - mn) / mx - 0.12; if (e > 0.25) e = 0.25; if (e > d) d = e; }   // a shaded card next to a lit one
          s += d;
        }
      }
      v[x] = 240 * s / (r1 - r0);
    }
    return v;
  }
  function endProfiles(band, Lb, thr) {
    const w = new Float32Array(BW), Lp = new Float32Array(BW), Rp = new Float32Array(BW);
    for (let x = 0; x < BW; x++) {
      let c = 0;
      for (let r = 3; r < 13; r++) {
        const i = r * BW + x, o = i * 3, mx = Math.max(band[o], band[o + 1], band[o + 2]), mn = Math.min(band[o], band[o + 1], band[o + 2]);
        if (Lb[i] > thr && mx - mn < 30) c++;
      }
      w[x] = c / 10;
    }
    for (let x = 3; x < BW - 3; x++) { Lp[x] = 40 * Math.max(0, w[x + 3] - w[x - 3]); Rp[x] = 40 * Math.max(0, w[x - 3] - w[x + 3]); }
    return { L: Lp, R: Rp };
  }
  function peakNear(prof, xc, r) {
    let bx = -1, bv = -1;
    for (let x = Math.max(1, Math.round(xc - r)); x <= Math.min(BW - 2, Math.round(xc + r)); x++) if (prof[x] > bv) { bv = prof[x]; bx = x; }
    if (bx < 0) return null;
    const a = prof[bx - 1], b = prof[bx], c = prof[bx + 1], den = a - 2 * b + c;
    return { x: bx + (den < 0 ? 0.5 * (a - c) / den : 0), v: bv };
  }
  // edges i = 1..n-1 through x = (a + b i) / (1 + c i); with few edges, a straight a + b i
  function edgeFit(pk, comb) {
    const strong = pk.length ? pk.filter((q) => q.v >= 0.35 * K.median(pk.map((q) => q.v))) : [];
    const lin = (P) => {
      if (P.length < 2) { const q = P[0]; const a = q ? q.x - q.i * comb.p : comb.x0; return { f: (i) => a + comb.p * i, res: 0, n: P.length }; }
      let sx = 0, sy = 0, sxx = 0, sxy = 0; for (const q of P) { sx += q.i; sy += q.x; sxx += q.i * q.i; sxy += q.i * q.x; }
      const b = (P.length * sxy - sx * sy) / (P.length * sxx - sx * sx), a = (sy - b * sx) / P.length;
      return { f: (i) => a + b * i, res: Math.max(...P.map((q) => Math.abs(a + b * q.i - q.x))), n: P.length };
    };
    const proj = (P) => {
      const A = [[0, 0, 0], [0, 0, 0], [0, 0, 0]], r = [0, 0, 0];
      for (const q of P) { const row = [1, q.i, -q.i * q.x]; for (let j = 0; j < 3; j++) { r[j] += row[j] * q.x; for (let k = 0; k < 3; k++) A[j][k] += row[j] * row[k]; } }
      const [a, b, c] = K.solve(A, r);
      return { f: (i) => (a + b * i) / (1 + c * i), res: Math.max(...P.map((q) => Math.abs((a + b * q.i) / (1 + c * q.i) - q.x))), n: P.length };
    };
    let pts = strong, F = null;
    for (let it = 0; it < 4; it++) {
      F = pts.length >= 8 ? proj(pts) : lin(pts);
      if (F.res <= 1.5 || pts.length <= 2) break;
      let worst = null; for (const q of pts) { const e = Math.abs(F.f(q.i) - q.x); if (!worst || e > worst.e) worst = { e, q }; }
      pts = pts.filter((q) => q !== worst.q);
    }
    return F;
  }

  // ---------- the whole row ----------
  function readRow(img, LS, hc, maxShift, g0) {
    const HC = hc || HC0, VROWS = BH * HC / 1.348, MS = maxShift || 20;
    const g = g0 || findRow(LS, img);
    if (g.why) return { why: g.why };
    const rowLen = Math.hypot(g.xr - g.xl, g.mt * (g.xr - g.xl)), hgt = (g.cb + g.mb * g.xl) - (g.ct + g.mt * g.xl);
    // pass 1: a wider band; how many cards, where their edges are
    const b1 = K.straighten(img, K.quadOf(g, EXT)), L1 = K.bandLum(b1.band, BW, BH);
    // Top rows 3..14 hold nothing but the card edges: the comb is fitted there. The game lays the row out by the number
    // of cards (up to 9: a fixed spacing, the row centred; 10 to 13: squeezed to the full width), so each count has its
    // own spacing and row length, in card widths; the card width comes from the visible height.
    const pTop = relProfile(L1, 3, 14, true), pLow = relProfile(L1, 60, 112, false);
    const near = new Float32Array(BW);
    for (let x = 0; x < BW; x++) { let m = 0; for (let k = Math.max(0, x - 5); k <= Math.min(BW - 1, x + 5); k++) if (pTop[k] > m) m = pTop[k]; near[x] = m; }
    const ends = endProfiles(b1.band, L1, g.thr);
    const k1 = BW / ((1 + 2 * EXT) * rowLen), len1 = rowLen * k1, x0e = BW * EXT / (1 + 2 * EXT), ch = (hgt / HC) * k1;
    let comb = null; const dbg = typeof process !== "undefined" && process.env.B2DBG ? {} : null;
    for (let n = 1; n <= 13; n++) {
      // a row of n cards is n - 1 spacings and one card long: that fixes the spacing; the card must be about as wide as
      // the visible height says (a tilted window changes that ratio by a few per cent)
      const pn = n > 1 ? len1 / (n - 1 + 1 / PITCH[n]) : len1, cn = n > 1 ? pn / PITCH[n] : len1;
      if (Math.abs(cn - ch) > 0.15 * ch) continue;
      if (n === 1) { comb = { n, p: cn, x0: x0e, s: 0, sc: 20, c: cn }; continue; }
      const r = Math.min(30, 0.5 * pn);
      for (let p = 0.96 * pn; p <= 1.04 * pn; p += 0.1) for (let x0 = x0e - r; x0 <= x0e + r; x0 += 0.5) {
        let e = 0, tmax = 0; const t = [];
        for (let i = 1; i < n; i++) { const v = K.interp(near, x0 + p * i); t.push(v); e += v; if (v > tmax) tmax = v; }
        let weak = 0; for (const v of t) if (v < 0.25 * tmax) weak++;
        const en = K.interp(ends.L, x0) + K.interp(ends.R, x0 + (n - 1) * p + p / PITCH[n]);
        const sc = e - 0.5 * tmax * weak + 0.25 * en;
        if (!comb || sc > comb.sc) comb = { n, p, x0, s: e / (n - 1), sc, en, weak, c: p / PITCH[n] };
        if (dbg && (!dbg[n] || sc > dbg[n].sc)) dbg[n] = { sc: +sc.toFixed(1), p: +p.toFixed(1), x0, e: +(e / (n - 1)).toFixed(0), weak, en: +en.toFixed(0) };
      }
    }
    if (dbg) console.log("  ch", ch.toFixed(1), "len1", len1.toFixed(0), JSON.stringify(dbg));
    if (!comb) return { why: "手牌的寬度對不上任何張數" };
    const n = comb.n;
    // the same edges lower down (rows 60..112) sit a little to one side when the window is tilted: find that offset first
    let shift = 0;
    if (n > 1) { let bs = -1; for (let d = -MS; d <= MS; d += 0.5) { let v = 0; for (let i = 1; i < n; i++) v += K.interp(pLow, comb.x0 + i * comb.p + d); if (v > bs) { bs = v; shift = d; } } }
    const pk = (pf, d) => { const out = []; for (let i = 1; i < n; i++) { const q = peakNear(pf, comb.x0 + i * comb.p + d, 7); if (q) out.push({ i, x: q.x, v: q.v }); } return out; };
    const fT = edgeFit(pk(pTop, 0), comb), fL = edgeFit(pk(pLow, shift), { p: comb.p, x0: comb.x0 + shift });
    // the card width, from where the faces stop on the right when that is clear
    const c1 = comb.c, pR = peakNear(ends.R, fT.f(n - 1) + c1, 0.1 * c1), pitch1 = n > 1 ? (fT.f(n - 1) - fT.f(0)) / (n - 1) : c1;
    const cw1 = pR && pR.v > 15 ? pR.x - fT.f(n - 1) : c1;
    const p2 = n > 1 ? CW * pitch1 / cw1 : CW, iR = n - 1 + cw1 / pitch1;
    // pass 2: every edge as a line in the screenshot; it meets the top line at (i p2, 0) and the strip at (i p2, VROWS)
    const yT = 8.5, yL = 86, P = [], Q = [];
    const meet = (a, b, m, c) => { const dx = b[0] - a[0], dy = b[1] - a[1], t = (c + m * a[0] - a[1]) / (dy - m * dx); return [a[0] + t * dx, a[1] + t * dy]; };
    const idx = []; for (let i = 0; i < n; i++) idx.push(i); idx.push(iR);
    for (const i of idx) {
      const a = K.applyH(b1.Hm, fT.f(i), yT), b = K.applyH(b1.Hm, fL.f(i), yL);
      P.push([i * p2, 0]); Q.push(meet(a, b, g.mt, g.ct));
      P.push([i * p2, VROWS]); Q.push(meet(a, b, g.mb, g.cb));
    }
    const H2 = K.homographyLSQ(P, Q), { band } = K.straighten(img, null, H2), Lb = K.bandLum(band, BW, BH);
    // how far the edges sit from where the straightened row puts them: the second worst counts (one card's own artwork,
    // or the step between a lit and a shaded card, can pull a single peak aside)
    const pf2 = relProfile(Lb, 3, 14), devs = [];
    for (let i = 1; i < n; i++) { const q = peakNear(pf2, i * p2, 7); if (q && q.v > 8) devs.push(Math.abs(q.x - i * p2)); }
    devs.sort((a, b) => b - a);
    const dev = devs.length > 2 ? devs[1] : devs.length ? devs[0] : 0, devMax = devs.length ? devs[0] : 0;
    const cards = [], lit = [];
    for (let i = 0; i < n; i++) {
      cards.push(K.glyphs(K.cardStrip(band, i * p2)));
      const f = []; for (let r = 4; r < 13; r++) for (let x = Math.round(i * p2 + 6); x < Math.round(i * p2 + Math.min(p2, CW) - 6); x += 2) f.push(Lb[r * BW + x]);
      lit.push(K.median(f) >= 180);
    }
    return { n, p2, cards, lit, band, g, geo: { edge: g.edge, rel: g.rel, topInl: g.topInl, hRatio: hgt / rowLen, rowLen, face: g.faceHigh, xl: g.xl, xr: g.xr, strip: g.strip, box: g.box }, comb: { n, p: comb.p, x0: comb.x0, s: comb.s, sc: comb.sc, shift, dev, resT: fT.res, resL: fL.res, cw: cw1 / pitch1, devMax },
      quad: [K.applyH(H2, 0, 0), K.applyH(H2, (n - 1) * p2 + CW, 0), K.applyH(H2, (n - 1) * p2 + CW, VROWS), K.applyH(H2, 0, VROWS)] };
  }
  // ---------- the game window, from its strip ----------
  // Positions in "window pixels": X along the strip (the window is 920 wide), Y down, the strip's top edge at Y = 644.
  const WIN = 920, YSTRIP = 644;
  function frameOf(st) {
    const th = Math.atan(st.m), cu = Math.cos(th), su = Math.sin(th), k = (st.x1 - st.x0) / cu / WIN, ox = st.x0, oy = st.c + st.m * st.x0;
    return { k, at: (X, Y) => [ox + k * (X * cu + (YSTRIP - Y) * su), oy + k * (X * su - (YSTRIP - Y) * cu)] };
  }
  // a w x h patch of the window (RGB floats), its top-left at window pixel (X0, Y0)
  function grab(img, F, X0, Y0, w, h) {
    const { width: W, height: H, data } = img, out = new Float32Array(w * h * 3);
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
      let [px, py] = F.at(X0 + x, Y0 + y);
      if (px < 0) px = 0; else if (px > W - 1.001) px = W - 1.001;
      if (py < 0) py = 0; else if (py > H - 1.001) py = H - 1.001;
      const x0 = Math.floor(px), y0 = Math.floor(py), tx = px - x0, ty = py - y0, i = (y0 * W + x0) * 4, o = (y * w + x) * 3;
      for (let c = 0; c < 3; c++) out[o + c] = (data[i + c] * (1 - tx) + data[i + 4 + c] * tx) * (1 - ty) + (data[i + W * 4 + c] * (1 - tx) + data[i + W * 4 + 4 + c] * tx) * ty;
    }
    return out;
  }
  const lumOf = (P, n) => { const L = new Float32Array(n); for (let i = 0; i < n; i++) L[i] = 0.299 * P[i * 3] + 0.587 * P[i * 3 + 1] + 0.114 * P[i * 3 + 2]; return L; };

  // ---------- how many cards each of the others holds: the round badge at the head of their face-down fan ----------
  // navy with white digits (7 to 13), crimson with yellow digits (6 or fewer); both have a light ring around a dark disc
  // (the badge sits at the head of the fan and moves along it as the fan shrinks: high up with 13 cards, lower with few)
  const SEATBOX = { right: [628, 222, 124, 132], top: [358, 205, 168, 82], left: [178, 222, 124, 132] };   // [X0, Y0, w, h]
  const RING = [], INNER = [[0, 0]];
  for (let a = 0; a < 16; a++) RING.push([Math.cos(a * Math.PI / 8), Math.sin(a * Math.PI / 8)]);
  for (let a = 0; a < 4; a++) INNER.push([4.5 * Math.cos(a * Math.PI / 2 + 0.4), 4.5 * Math.sin(a * Math.PI / 2 + 0.4)]);
  for (let a = 0; a < 8; a++) INNER.push([9 * Math.cos(a * Math.PI / 4), 9 * Math.sin(a * Math.PI / 4)]);
  const BP = 30;   // badge patch size
  function findBadge(img, F, box) {
    const [X0, Y0, w, h] = box, P = grab(img, F, X0, Y0, w, h), L = lumOf(P, w * h);
    const tmp = new Float32Array(INNER.length);
    // a dark disc in a light ring around (x, y): its score, or null
    const at = (x, y) => {
      const ci = y * w + x;
      if (L[ci] > 170) return null;
      // the fill: the 4th darkest of the inner samples (a few digit pixels among them do not matter)
      let n = 0;
      for (let k = 0; k < INNER.length; k++) {
        const v = L[Math.round(y + INNER[k][1]) * w + Math.round(x + INNER[k][0])];
        let j = n < 4 ? n++ : 4;
        if (j === 4 && v >= tmp[3]) continue;
        while (j > 0 && tmp[j - 1] > v) { if (j < 4) tmp[j] = tmp[j - 1]; j--; }
        tmp[j] = v;
      }
      const fill = tmp[3];
      if (fill > 115) return null;
      let rbest = -1, rmin = 0;
      for (const rad of [13.5, 14.5, 15.5]) {
        let s = 0, mn = 999;
        for (const [cx, cy] of RING) { const v = L[Math.round(y + rad * cy) * w + Math.round(x + rad * cx)]; s += v; if (v < mn) mn = v; }
        if (s / 16 > rbest) { rbest = s / 16; rmin = mn; }
      }
      if (rbest - fill < 55 || rmin < fill + 20) return null;
      return { x, y, sc: rbest - fill + 0.5 * (rmin - fill), fill, ring: rbest };
    };
    let best = null;
    for (let y = 17; y < h - 17; y++) for (let x = 17; x < w - 17; x++) { const v = at(x, y); if (v && (!best || v.sc > best.sc)) best = v; }
    if (!best) return null;
    // the digits: brightness between the disc's fill and its ring, inside the disc; and the fill's colour
    const d = new Float32Array(BP * BP), span = Math.max(40, best.ring - best.fill);
    let rb = 0, nf = 0;
    for (let yy = 0; yy < BP; yy++) for (let xx = 0; xx < BP; xx++) {
      const sx = best.x - 15 + xx, sy = best.y - 15 + yy, r2 = (xx - 14.5) * (xx - 14.5) + (yy - 14.5) * (yy - 14.5);
      if (r2 > 11.5 * 11.5) continue;
      const i = sy * w + sx; let v = (L[i] - best.fill) / span; d[yy * BP + xx] = v < 0 ? 0 : v > 1.2 ? 1.2 : v;
      if (L[i] < best.fill + 0.25 * span) { rb += P[i * 3] - P[i * 3 + 2]; nf++; }
    }
    const red = nf ? rb / nf : 0;                 // navy: about -70; crimson: about +100
    if (red > -20 && red < 40) return null;       // neither: not a badge
    return { X: X0 + best.x, Y: Y0 + best.y, sc: best.sc, d, red };
  }
  // the number on a badge: a small linear classifier over the disc's pixels (classes: 0 = not a badge, 1..13)
  let DISC = null;
  function badgeNumber(b, M) {
    if (!DISC) { DISC = []; for (let y = 0; y < BP; y++) for (let x = 0; x < BP; x++) if ((x - 14.5) * (x - 14.5) + (y - 14.5) * (y - 14.5) <= M.mask * M.mask) DISC.push(y * BP + x); }
    const z = new Float64Array(14);
    for (let k = 0; k < DISC.length; k++) { const v = b.d[DISC[k]]; if (v) for (let c = 0; c < 14; c++) z[c] += v * M.w[k * 14 + c]; }
    let mx = -1e9; for (let c = 0; c < 14; c++) { z[c] = z[c] * M.scale + M.b[c]; if (z[c] > mx) mx = z[c]; }
    let sum = 0; for (let c = 0; c < 14; c++) { z[c] = Math.exp(z[c] - mx); sum += z[c]; }
    let n = 0; for (let c = 1; c < 14; c++) if (z[c] > z[n]) n = c;
    return { n, p: z[n] / sum };
  }

  // ---------- PASS: the golden word over a seat ----------
  // (taller than the word: in a taller game window the table sits higher, the word with it)
  const PASSBOX = { right: [570, 212, 220, 128], top: [360, 160, 220, 110], left: [150, 212, 220, 128] };
  const golden = (r, g, bl) => r > 200 && g > 150 && bl < 160 && r - bl > 70;
  // the PASS word runs from pale yellow at the top to orange at the bottom; on some screens the pale half is paler still
  const passGold = (r, g, bl) => r > 200 && g > 150 && bl < 215 && r - bl > 40 && g - bl > 30;
  function findPass(img, F, box, T) {
    const [X0, Y0, w, h] = box, P = grab(img, F, X0, Y0, w, h), m = new Uint8Array(w * h);
    let cnt = 0, x0 = w, x1 = -1, y0 = h, y1 = -1;
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) { const i = (y * w + x) * 3; if (passGold(P[i], P[i + 1], P[i + 2])) { m[y * w + x] = 1; cnt++; if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y; } }
    if (cnt < 700) return { pass: false, gold: cnt, score: 0 };
    // the word's shape at a third of the size, slid over the box (other golden things nearby move a box-centred guess);
    // also a little larger, as the sign is while it pops up and on the right-hand seat
    const a = new Float32Array(T.w * T.h);
    let score = -1;
    for (const c of [3, 2.6]) {
      const w3 = Math.floor(w / c), h3 = Math.floor(h / c), d3 = new Float32Array(w3 * h3);
      for (let y = 0; y < h3; y++) for (let x = 0; x < w3; x++) {
        let s = 0;
        for (let dy = 0; dy < 3; dy++) for (let dx = 0; dx < 3; dx++) { const yy = Math.min(h - 1, Math.floor((y + (dy + 0.5) / 3) * c)), xx = Math.min(w - 1, Math.floor((x + (dx + 0.5) / 3) * c)); s += m[yy * w + xx]; }
        d3[y * w3 + x] = s / 9;
      }
      for (let oy = 0; oy + T.h <= h3; oy++) for (let ox = 0; ox + T.w <= w3; ox++) {
        let sum = 0;
        for (let ty = 0; ty < T.h; ty++) for (let tx = 0; tx < T.w; tx++) { const v = d3[(oy + ty) * w3 + ox + tx]; a[ty * T.w + tx] = v; sum += v; }
        if (sum < 0.4 * 700 / 9) continue;
        const sc = K.ncc(a, T.t, T.w, T.h, 0);
        if (sc > score) score = sc;
      }
    }
    return { pass: score >= 0.6, gold: cnt, score };
  }

  // ---------- the pile in the middle: the newest play lies on top, lit; older ones are shaded ----------
  const PILEBOX = [250, 255, 430, 195];
  const CARD_H = 1.38;                 // a card's height in card widths
  function pileWhite(img, F) {
    const [X0, Y0, w, h] = PILEBOX, P = grab(img, F, X0, Y0, w, h), m = new Uint8Array(w * h);
    let gold = 0;
    for (let i = 0; i < w * h; i++) {
      const r = P[i * 3], g = P[i * 3 + 1], bl = P[i * 3 + 2], mx = Math.max(r, g, bl), mn = Math.min(r, g, bl), L = 0.299 * r + 0.587 * g + 0.114 * bl;
      if (L > 185 && mx - mn < 45) m[i] = 1;
      if (golden(r, g, bl)) gold++;
    }
    const { lab, stats } = K.components(m, w, h);
    // lit cards only (a badge's ring is far smaller; the buttons lie below the box)
    const comps = stats.filter((c) => c.area >= 1500 && c.y1 < h - 2).sort((p, q) => q.area - p.area);
    // a play just made is shown large with a golden frame for a moment: golden pixels hugging the white region
    for (const c of comps) {
      let ring = 0, rg = 0;
      for (let y = Math.max(0, c.y0 - 5); y <= Math.min(h - 1, c.y1 + 5); y++) for (let x = Math.max(0, c.x0 - 5); x <= Math.min(w - 1, c.x1 + 5); x++) {
        const i = y * w + x; if (lab[i] === c.id) continue;
        let nearC = false;
        for (let dy = -4; dy <= 4 && !nearC; dy += 2) for (let dx = -4; dx <= 4; dx += 2) { const yy = y + dy, xx = x + dx; if (yy >= 0 && yy < h && xx >= 0 && xx < w && lab[yy * w + xx] === c.id) { nearC = true; break; } }
        if (!nearC) continue;
        ring++; if (golden(P[i * 3], P[i * 3 + 1], P[i * 3 + 2])) rg++;
      }
      c.goldRing = ring ? rg / ring : 0;
    }
    return { comps, lab, gold, w, h, X0, Y0 };
  }
  function convexHull(pts) {
    pts = pts.slice().sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    const cross = (o, a, b) => (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]);
    const lo = [], up = [];
    for (const p of pts) { while (lo.length >= 2 && cross(lo[lo.length - 2], lo[lo.length - 1], p) <= 0) lo.pop(); lo.push(p); }
    for (let i = pts.length - 1; i >= 0; i--) { const p = pts[i]; while (up.length >= 2 && cross(up[up.length - 2], up[up.length - 1], p) <= 0) up.pop(); up.push(p); }
    lo.pop(); up.pop();
    return lo.concat(up);
  }
  const polyArea = (P) => { let a = 0; for (let i = 0; i < P.length; i++) { const p = P[i], q = P[(i + 1) % P.length]; a += p[0] * q[1] - q[0] * p[1]; } return Math.abs(a) / 2; };
  // the four sides of a card-shaped region: hull cut down to 4 corners, then each side fitted to the outline between them
  function fitQuad(lab, w, h, comp) {
    const pts = [];
    for (let y = comp.y0; y <= comp.y1; y++) { let a = -1, z = -1; for (let x = comp.x0; x <= comp.x1; x++) if (lab[y * w + x] === comp.id) { if (a < 0) a = x; z = x; } if (a >= 0) { pts.push([a, y]); if (z !== a) pts.push([z, y]); } }
    for (let x = comp.x0; x <= comp.x1; x++) { let a = -1, z = -1; for (let y = comp.y0; y <= comp.y1; y++) if (lab[y * w + x] === comp.id) { if (a < 0) a = y; z = y; } if (a >= 0) { pts.push([x, a]); if (z !== a) pts.push([x, z]); } }
    const hull = convexHull(pts), hullArea = polyArea(hull);
    let Q = hull.slice();
    const tri = (i) => { const n = Q.length, a = Q[(i + n - 1) % n], b = Q[i], c = Q[(i + 1) % n]; return Math.abs((b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])) / 2; };
    while (Q.length > 4) { let bi = 0, ba = 1e18; for (let i = 0; i < Q.length; i++) { const t = tri(i); if (t < ba) { ba = t; bi = i; } } Q.splice(bi, 1); }
    if (Q.length < 4) return null;
    // refit each side through the hull points along it (the middle 70%: the corners are rounded)
    const lines = [];
    for (let k = 0; k < 4; k++) {
      const a = Q[k], b = Q[(k + 1) % 4], dx = b[0] - a[0], dy = b[1] - a[1], len = Math.hypot(dx, dy);
      const sel = hull.filter((p) => { const t = ((p[0] - a[0]) * dx + (p[1] - a[1]) * dy) / (len * len), d = Math.abs((p[0] - a[0]) * dy - (p[1] - a[1]) * dx) / len; return t > 0.15 && t < 0.85 && d < 4; });
      if (sel.length < 2) { lines.push({ p: a, d: [dx / len, dy / len] }); continue; }
      let mx = 0, my = 0; for (const p of sel) { mx += p[0]; my += p[1]; } mx /= sel.length; my /= sel.length;
      let sxx = 0, sxy = 0, syy = 0; for (const p of sel) { const x = p[0] - mx, y = p[1] - my; sxx += x * x; sxy += x * y; syy += y * y; }
      const th = 0.5 * Math.atan2(2 * sxy, sxx - syy);
      lines.push({ p: [mx, my], d: [Math.cos(th), Math.sin(th)] });
    }
    const meet = (A, B) => { const det = A.d[0] * B.d[1] - A.d[1] * B.d[0]; if (Math.abs(det) < 1e-6) return null; const t = ((B.p[0] - A.p[0]) * B.d[1] - (B.p[1] - A.p[1]) * B.d[0]) / det; return [A.p[0] + t * A.d[0], A.p[1] + t * A.d[1]]; };
    const corners = [];
    for (let k = 0; k < 4; k++) { const c = meet(lines[(k + 3) % 4], lines[k]); if (!c) return null; corners.push(c); }
    const quadArea = polyArea(corners);
    return { corners, hullArea, quadArea, solid: hullArea / quadArea, white: comp.area / hullArea };
  }
  // one card seen through its four corners (window pixels, in order around the card starting at its own top-left):
  // the strip the hand reader takes (its left part, at the size the templates have)
  function cardStripFrom(img, F, corners) {
    const SWd = K.SW, cw = CW, chh = CW * CARD_H * (BH * HC0 / 1.348) / (CW * HC0);   // card: cw wide, chh rows high in strip pixels
    const Hc = K.homography([[0, 0], [cw, 0], [cw, chh], [0, chh]], corners);
    const st = new Float32Array(SWd * BH * 3), { width: W, height: H, data } = img;
    for (let y = 0; y < BH; y++) for (let x = 0; x < SWd; x++) {
      const q = K.applyH(Hc, x, Math.min(y, chh)); let [px, py] = F.at(q[0], q[1]);
      if (px < 0) px = 0; else if (px > W - 1.001) px = W - 1.001;
      if (py < 0) py = 0; else if (py > H - 1.001) py = H - 1.001;
      const x0 = Math.floor(px), y0 = Math.floor(py), tx = px - x0, ty = py - y0, i = (y0 * W + x0) * 4, o = (y * SWd + x) * 3;
      for (let c = 0; c < 3; c++) st[o + c] = (data[i + c] * (1 - tx) + data[i + 4 + c] * tx) * (1 - ty) + (data[i + W * 4 + c] * (1 - tx) + data[i + W * 4 + 4 + c] * tx) * ty;
    }
    return st;
  }
  // a single card lying on the pile, whichever way up: try the four ways round, keep the one that reads best
  function readPileCard(img, F, corners, model) {
    let best = null;
    for (let rot = 0; rot < 4; rot++) {
      const c = [0, 1, 2, 3].map((k) => corners[(k + rot) % 4]);
      const gl = K.glyphs(cardStripFrom(img, F, c));
      if (!gl) continue;
      const r = K.classify(gl, model);
      const placed = gl.rtop >= 8 && gl.rtop <= 30 && gl.rh >= 30 && gl.rh <= 54 && gl.sh >= 12 && gl.sh <= 32;
      const sc = r.rTop + (placed ? 0.1 : 0);
      if (!best || sc > best.sc) best = { sc, rot, card: toB2(r.card), rTop: r.rTop, rMargin: r.rMargin, z: r.z, colourSure: r.colourSure, placed, red: gl.red };
    }
    return best;
  }
  // dark marks (ranks, suits) enclosed by the lit cards: holes in the white region, each of a glyph's size
  function inkBlobs(pw, comp) {
    const { lab, w, h } = pw, bw = comp.x1 - comp.x0 + 1, bh = comp.y1 - comp.y0 + 1, m = new Uint8Array(bw * bh);
    // inside the component's row span and not white
    for (let y = 0; y < bh; y++) {
      let a = -1, z = -1;
      for (let x = 0; x < bw; x++) if (lab[(comp.y0 + y) * w + comp.x0 + x] === comp.id) { if (a < 0) a = x; z = x; }
      if (a < 0) continue;
      for (let x = a; x <= z; x++) if (lab[(comp.y0 + y) * w + comp.x0 + x] !== comp.id) m[y * bw + x] = 1;
    }
    const { stats } = K.components(m, bw, bh);
    let n = 0;
    for (const c of stats) { const cw = c.x1 - c.x0 + 1, ch = c.y1 - c.y0 + 1; if (c.area >= 12 && c.area <= 900 && cw < 0.6 * bw && ch < 0.6 * bh) n++; }
    return n;
  }
  const sureCard = (c) => c.placed && c.rTop >= 0.86 && c.rMargin >= 0.04 && c.colourSure && Math.abs(c.z) >= 0.3;
  function readPile(img, F, model) {
    const pw = pileWhite(img, F);
    // a play just made, shown large in a golden frame near whoever made it (yours in the middle), before it lands on the pile
    const displays = [];
    for (const c of pw.comps) {
      if (!(c.goldRing > 0.15 || c.area > 8200)) continue;
      const cx = pw.X0 + (c.x0 + c.x1) / 2, cy = pw.Y0 + (c.y0 + c.y1) / 2;
      const d = { seat: cx < 330 ? 3 : cx > 600 ? 1 : cy < 300 ? 2 : 0, area: c.area };
      const q = fitQuad(pw.lab, pw.w, pw.h, c);
      if (q && q.solid < 1.12 && q.white > 0.8) {
        const r = readPileCard(img, F, q.corners.map((p) => [pw.X0 + p[0], pw.Y0 + p[1]]), model);
        if (r) { d.card = r.card; d.sure = sureCard(r); }
      }
      displays.push(d);
    }
    const piles = pw.comps.filter((c) => !(c.goldRing > 0.15 || c.area > 8200));
    if (!piles.length) return { n: displays.length ? null : 0, busy: displays.length > 0, displays, area: 0, gold: pw.gold, solid: 0, white: 0, hull: 0 };
    const comp = piles[0], q = fitQuad(pw.lab, pw.w, pw.h, comp);
    const out = { area: comp.area, gold: pw.gold, goldRing: comp.goldRing, busy: false, displays, solid: q ? q.solid : 0, white: q ? q.white : 0, hull: q ? q.hullArea : 0, n: 0, quad: q ? q.corners.map((p) => [pw.X0 + p[0], pw.Y0 + p[1]]) : null };
    // how many cards: one card fills its outline; five fanned out fill far less of the four-sided shape around them,
    // and show five corners' worth of ink (rank and small suit on each)
    const solid = q ? q.solid : 2;
    out.ink = inkBlobs(pw, comp);
    out.n = comp.area < 4100 && solid < 1.2 ? 1 : out.ink >= 9 ? 5 : out.ink >= 4 ? 2 : solid < 1.22 && comp.area < 7500 ? 2 : 5;
    if (q && out.n === 1 && q.solid > 0.9) {
      const corners = q.corners.map((p) => [pw.X0 + p[0], pw.Y0 + p[1]]);
      const c = readPileCard(img, F, corners, model);
      if (c) { out.cards = [c.card]; out.sure = sureCard(c); out.detail = c; }
    }
    return out;
  }
  // ---------- your turn: the buttons 重選 / PASS / 出牌 stand over the table, grey or pink ----------
  // (colours relative to the table's own, measured on four patches: a card flying past may cover one)
  const BTNBOX = [[292, 457, 116, 24], [438, 457, 124, 24], [588, 457, 194, 24]];
  const TABLEREF = [[150, 400, 130, 40], [610, 400, 120, 40], [60, 420, 70, 30], [790, 420, 60, 30]];
  const BTN_GREY = [19, 43, 0], BTN_PINK = [45, -40, -76];
  function medianRGB(P, n) { const r = [], g = [], b = []; for (let i = 0; i < n; i++) { r.push(P[i * 3]); g.push(P[i * 3 + 1]); b.push(P[i * 3 + 2]); } return [K.median(r), K.median(g), K.median(b)]; }
  function buttonsShown(img, F) {
    const refs = TABLEREF.map(([x, y, w, h]) => medianRGB(grab(img, F, x, y, w, h), w * h));
    const ref = [0, 1, 2].map((c) => K.median(refs.map((r) => r[c])));
    let on = 0; const det = [];
    for (const [X0, Y0, w, h] of BTNBOX) {
      const c = medianRGB(grab(img, F, X0, Y0, w, h), w * h), d = [c[0] - ref[0], c[1] - ref[1], c[2] - ref[2]];
      const dist = (o) => Math.hypot(d[0] - o[0], d[1] - o[1], d[2] - o[2]), e = Math.min(dist(BTN_GREY), dist(BTN_PINK));
      det.push(Math.round(e)); if (e < 20) on++;
    }
    return { on: on >= 2, det, ref: ref.map(Math.round) };
  }
  // a card picked in your row stands higher with a golden frame: the row cannot be read right then
  function raisedCard(img, F) {
    const P = grab(img, F, 0, 470, WIN, 60);
    let n = 0; for (let i = 0; i < WIN * 60; i++) if (golden(P[i * 3], P[i * 3 + 1], P[i * 3 + 2])) n++;
    return n;
  }

  // ---------- a play shown large near the seat that made it: an upright fan of 1 to 5 cards glowing yellow ----------
  // (or a single card in a medallion, for a 2). Each card's rank and the small suit under it are cut out, turned upright
  // by the line from rank to suit, and matched like the cards in your row.
  // (generous boxes that overlap: whose play it is goes by where its marks are, not by the box)
  const SHOWBOX = { right: [490, 60, 400, 290], top: [300, 30, 320, 220], left: [30, 60, 400, 290] };
  const FANOPTS = { right: { keepEdge: true, dropLeft: true }, top: {}, left: { keepEdge: true, dropRight: true } };
  const SEATOF = { right: 1, top: 2, left: 3 };
  function grabFine(img, F, X0, Y0, w, h, step) {
    const { width: W, height: Hh, data } = img, ow = Math.round(w / step), oh = Math.round(h / step), out = new Float32Array(ow * oh * 3);
    for (let y = 0; y < oh; y++) for (let x = 0; x < ow; x++) {
      let [px, py] = F.at(X0 + x * step, Y0 + y * step);
      if (px < 0) px = 0; else if (px > W - 1.001) px = W - 1.001;
      if (py < 0) py = 0; else if (py > Hh - 1.001) py = Hh - 1.001;
      const x0 = Math.floor(px), y0 = Math.floor(py), tx = px - x0, ty = py - y0, i = (y0 * W + x0) * 4, o = (y * ow + x) * 3;
      for (let c = 0; c < 3; c++) out[o + c] = (data[i + c] * (1 - tx) + data[i + 4 + c] * tx) * (1 - ty) + (data[i + W * 4 + c] * (1 - tx) + data[i + W * 4 + 4 + c] * tx) * ty;
    }
    return { P: out, w: ow, h: oh };
  }
  const glowPx = (r, g, b) => r > 180 && g > 140 && b < 140 && r - b > 70;
  // worth a closer look: golden glow and white card face both there
  function showHint(img, F, box) {
    const [X0, Y0, w, h] = box, { width: W, height: Hh, data } = img;
    let g = 0, wh = 0;
    // every 4th window pixel
    for (let Y = Y0; Y < Y0 + h; Y += 4) for (let X = X0; X < X0 + w; X += 4) {
      const [px, py] = F.at(X, Y), xi = Math.round(px), yi = Math.round(py);
      if (xi < 0 || yi < 0 || xi >= W || yi >= Hh) continue;
      const i = (yi * W + xi) * 4, r = data[i], gg = data[i + 1], b = data[i + 2], L = 0.299 * r + 0.587 * gg + 0.114 * b;
      if (glowPx(r, gg, b)) g++;
      if (L > 190 && Math.max(r, gg, b) - Math.min(r, gg, b) < 45) wh++;
    }
    return g >= 40 && wh >= 400;
  }
  function readFan(img, F, box, model, opts) {
    opts = opts || {};
    const step = opts.step || 0.7, [X0, Y0, w, h] = box, { P, w: dw, h: dh } = grabFine(img, F, X0, Y0, w, h, step), n = dw * dh;
    const L = new Float32Array(n), white = new Uint8Array(n), gold = new Uint8Array(n), red = new Float32Array(n);
    for (let i = 0; i < n; i++) {
      const r = P[i * 3], g = P[i * 3 + 1], b = P[i * 3 + 2], mx = Math.max(r, g, b), mn = Math.min(r, g, b);
      L[i] = 0.299 * r + 0.587 * g + 0.114 * b; red[i] = r - 0.5 * (g + b);
      if (L[i] > 190 && mx - mn < 45) white[i] = 1;
      if (glowPx(r, g, b)) gold[i] = 1;
    }
    const wc = K.components(white, dw, dh), lab0 = wc.lab;
    // the white areas glowing round their edge (the pile below does not glow); one cut by the box's side belongs to a
    // play shown at the next seat
    const cand = wc.stats.filter((c) => c.area > (opts.minArea || 750) / (step * step) && (opts.keepEdge || (c.x0 > 0 && c.x1 < dw - 1)) && !(opts.dropLeft && c.x0 === 0) && !(opts.dropRight && c.x1 === dw - 1)), gl = new Map();
    for (const c of cand) gl.set(c.id, [0, 0]);
    const R = Math.max(2, Math.round(2 / step));
    for (let y = R; y < dh - R; y++) for (let x = R; x < dw - R; x++) {
      const k = y * dw + x; if (white[k]) continue;
      for (const [dx, dy] of [[R, 0], [-R, 0], [0, R], [0, -R]]) { const id = lab0[(y + dy) * dw + x + dx], e = id && gl.get(id); if (e) { e[0]++; if (gold[k]) e[1]++; break; } }
    }
    const keep = new Set(cand.filter((c) => { const e = gl.get(c.id); return opts.noGlow ? e[0] > 20 : e[0] > 20 && e[1] / e[0] > 0.12; }).map((c) => c.id));
    if (!keep.size) return null;
    const area = new Uint8Array(n);
    for (let y = 0; y < dh; y++) { let lo = -1, hi = -1; for (let x = 0; x < dw; x++) if (keep.has(lab0[y * dw + x])) { if (lo < 0) lo = x; hi = x; } if (lo >= 0) for (let x = lo; x <= hi; x++) area[y * dw + x] = 1; }
    const fv = []; for (let k = 0; k < n; k += 3) if (white[k] && area[k]) fv.push(L[k]);
    const face = K.percentile(Float32Array.from(fv), 90);
    const near = new Uint8Array(n), GR = Math.round(2 / step);
    for (let y = 0; y < dh; y++) for (let x = 0; x < dw; x++) if (gold[y * dw + x]) for (let dy = -GR; dy <= GR; dy++) for (let dx = -GR; dx <= GR; dx++) { const yy = y + dy, xx = x + dx; if (yy >= 0 && yy < dh && xx >= 0 && xx < dw) near[yy * dw + xx] = 1; }
    const ink = new Uint8Array(n), inkv = new Float32Array(n);
    for (let k = 0; k < n; k++) {
      let v = (face - L[k]) / Math.max(30, face - 20); inkv[k] = v < 0 ? 0 : v > 1 ? 1 : v;
      if (!area[k] || near[k]) continue;
      if (L[k] < 0.6 * face || (red[k] > 60 && P[k * 3] > 120)) ink[k] = 1;
    }
    const ic = K.components(ink, dw, dh);
    const comps = ic.stats.filter((c) => c.area >= 6 / (step * step)).map((c) => ({ ...c, w: c.x1 - c.x0 + 1, h: c.y1 - c.y0 + 1, cx: (c.x0 + c.x1) / 2, cy: (c.y0 + c.y1) / 2 }));
    const under = (g, t) => t.id !== g.id && t.h >= 0.35 * g.h && t.h <= 0.85 * g.h && t.cy > g.cy && Math.hypot(t.cx - g.cx, t.cy - g.cy) < 1.5 * g.h && Math.abs(t.cx - g.cx) < 0.75 * (t.cy - g.cy);
    const RMIN = opts.rmin || 15, RMAX = opts.rmax || 55;
    const tall = comps.filter((c) => c.h >= RMIN / step && c.h <= RMAX / step && c.w <= 1.3 * c.h);
    const hs = tall.filter((g) => comps.some((t) => under(g, t))).map((c) => c.h).sort((a, b) => a - b);
    if (!hs.length) return null;
    const rh = hs[Math.floor(hs.length / 2)];
    // rank marks of about that height, left to right (the 1 and 0 of a 10 make one)
    const ranks = [], used = new Set();
    for (const c of tall.filter((t) => Math.abs(t.h - rh) < 0.22 * rh).sort((a, b) => a.x0 - b.x0)) {
      if (used.has(c.id)) continue;
      const g = { ids: [c.id], x0: c.x0, x1: c.x1, y0: c.y0, y1: c.y1, id: c.id };
      for (const t of tall) if (t !== c && !used.has(t.id) && t.x0 >= c.x0 + 0.25 * c.w && t.x0 - c.x1 < 0.45 * rh && Math.min(c.y1, t.y1) - Math.max(c.y0, t.y0) > 0.6 * Math.min(c.h, t.h) && Math.abs(t.h - c.h) < 0.25 * rh) { g.ids.push(t.id); g.x1 = Math.max(g.x1, t.x1); g.y0 = Math.min(g.y0, t.y0); g.y1 = Math.max(g.y1, t.y1); used.add(t.id); }
      used.add(c.id); g.cx = (g.x0 + g.x1) / 2; g.cy = (g.y0 + g.y1) / 2; g.h = g.y1 - g.y0 + 1;
      ranks.push(g);
    }
    const cards = [];
    for (const g of ranks) {
      let best = null;
      for (const t of comps) {
        if (g.ids.includes(t.id) || !under(g, t)) continue;
        const d = Math.hypot(t.cx - g.cx, t.cy - g.cy);
        if (!best || d < best.d) best = { t, d };
      }
      if (!best) continue;
      const th0 = Math.atan2(-(best.t.cx - g.cx), best.t.cy - g.cy);
      const r = readMark(g, best.t, th0, ic.lab, inkv, red, dw, dh, model);
      if (r) { r.X = X0 + r.x * step; r.Y = Y0 + r.y * step; cards.push(r); }
    }
    return cards.length ? cards : null;
  }
  // one rank and its suit, turned upright at the size the card templates have; the best fit over small turns and sizes
  function readMark(g, su, th0, lab, inkv, red, dw, dh, model) {
    const rset = new Set(g.ids), sset = new Set([su.id]);
    // only the mark's own pixels (and a pixel round them) count: neighbouring cards' marks stay out
    const rbox = [g.x0 - 2, g.y0 - 2, g.x1 + 2, g.y1 + 2], sbox = [su.x0 - 2, su.y0 - 2, su.x1 + 2, su.y1 + 2];
    const masked = (set, box) => {
      const v = new Float32Array(dw * dh);
      for (let y = Math.max(1, box[1]); y <= Math.min(dh - 2, box[3]); y++) for (let x = Math.max(1, box[0]); x <= Math.min(dw - 2, box[2]); x++) {
        let on = false;
        for (let dy = -1; dy <= 1 && !on; dy++) for (let dx = -1; dx <= 1; dx++) if (set.has(lab[(y + dy) * dw + x + dx])) { on = true; break; }
        if (on) v[y * dw + x] = inkv[y * dw + x];
      }
      return v;
    };
    const rv = masked(rset, rbox), sv = masked(sset, sbox);
    const sample = (src, cx, cy, th, k, Wn, Hn) => {
      const c = Math.cos(th), s = Math.sin(th), BWn = Math.round(Wn * 1.6), BHn = Math.round(Hn * 1.6), tmp = new Float32Array(BWn * BHn);
      let rmin = Infinity, rmax = -1, cmin = Infinity, cmax = -1;
      for (let v = 0; v < BHn; v++) for (let u = 0; u < BWn; u++) {
        const du = (u - BWn / 2) / k, dv = (v - BHn / 2) / k, val = K.bilZero(src, dw, dh, cx + c * du - s * dv, cy + s * du + c * dv);
        tmp[v * BWn + u] = val;
        if (val > 0.5) { if (v < rmin) rmin = v; if (v > rmax) rmax = v; if (u < cmin) cmin = u; if (u > cmax) cmax = u; }
      }
      if (rmax < 0) return null;
      const my = (rmin + rmax) / 2, mx = (cmin + cmax) / 2, raw = new Float32Array(Wn * Hn);
      for (let y = 0; y < Hn; y++) for (let x = 0; x < Wn; x++) raw[y * Wn + x] = K.bilZero(tmp, BWn, BHn, x + mx - Wn / 2, y + my - Hn / 2);
      const hw = Wn >> 1, hh = Hn >> 1, half = new Float32Array(hw * hh);
      for (let y = 0; y < hh; y++) for (let x = 0; x < hw; x++) { const i = 2 * y * Wn + 2 * x; half[y * hw + x] = (raw[i] + raw[i + 1] + raw[i + Wn] + raw[i + Wn + 1]) / 4; }
      return half;
    };
    let rs = 0, rn = 0;
    for (let y = g.y0; y <= g.y1; y++) for (let x = g.x0; x <= g.x1; x++) { const k = y * dw + x; if (rset.has(lab[k])) { rs += red[k]; rn++; } }
    const redness = rn ? rs / rn : 0;
    let best = null;
    for (const dth of [-0.08, 0, 0.08]) for (const ks of [0.94, 1.06]) {
      const th = th0 + dth, k = ks * 44 / g.h;
      const r = sample(rv, g.cx, g.cy, th, k, 44, 56), s = sample(sv, su.cx, su.cy, th, k, 34, 34);
      if (!r || !s) continue;
      const res = K.classify({ r, s, red: redness }, model);
      if (!best || res.rTop > best.rTop) best = res;
    }
    if (!best) return null;
    return { card: toB2(best.card), rTop: best.rTop, rMargin: best.rMargin, z: best.z, colourSure: best.colourSure, x: g.cx, y: g.cy };
  }
  // the plays shown large at the others' seats right now: [{ seat, cards, sure }]
  // where each seat's marks lie (window px): 對家's fan high up in the middle, 上家's and 下家's lower at the sides;
  // yours lower still in the middle (not read: your plays are known from your row)
  const SHOWZONE = { top: (X, Y) => Y < 170 && X > 320 && X < 580, left: (X, Y) => X < 360 && Y >= 170 && Y < 262, right: (X, Y) => X > 510 && Y >= 170 && Y < 262 };
  function readShows(img, F, model) {
    const out = [];
    for (const k of ["right", "top", "left"]) {
      if (!showHint(img, F, SHOWBOX[k])) continue;
      const all = readFan(img, F, SHOWBOX[k], model, FANOPTS[k]);
      const cards = all ? all.filter((c) => SHOWZONE[k](c.X, c.Y)) : [];
      if (!cards.length) continue;
      const ids = cards.map((c) => c.card);
      const sure = cards.every((c) => c.rTop >= 0.85 && c.rMargin >= 0.03 && c.colourSure && Math.abs(c.z) >= 0.3) && new Set(ids).size === ids.length;
      out.push({ seat: SEATOF[k], cards: ids, sure, conf: Math.min(...cards.map((c) => c.rTop)) });
    }
    return out;
  }

  // ---------- everything on the table besides your own row ----------
  function readTable(img, st, M) {
    const F = frameOf(st), seats = {};
    for (const seat of ["right", "top", "left"]) {
      const bd = findBadge(img, F, SEATBOX[seat]), ps = findPass(img, F, PASSBOX[seat], M.pass);
      const nb = bd ? badgeNumber(bd, M.badge) : null;
      seats[seat] = { count: nb && nb.n > 0 ? nb.n : null, p: nb ? nb.p : 0, pass: ps.pass, gold: ps.gold, ps: ps.score };
    }
    return { seats, F };
  }
  // the model for the table: badge classifier weights and the PASS template, from their packed form
  function unpackTable(p, unb64) {
    return { badge: { mask: p.badge.mask, scale: p.badge.scale, b: p.badge.b, w: new Int8Array(unb64(p.badge.w).buffer.slice(0)) }, pass: { w: p.pass.w, h: p.pass.h, t: Float32Array.from(p.pass.t, (v) => v / 255) } };
  }

  // 13 支 template ranks run 2..A; 大老二 cards run 3..A,2 (card = rank * 4 + suit, ♣ ♦ ♥ ♠)
  const toB2 = (c13) => (((c13 >> 2) + 12) % 13) * 4 + (c13 & 3);
  const LIMITS = { rel: 0.3, topInl: 0.6, dev: 3.5, rTop: 0.88, rMargin: 0.04, z: 0.3 };
  function judge(row, model) {
    const why = [];
    if (row.geo.rel < LIMITS.rel) why.push("手牌下面的黑條不清楚");
    if (row.geo.topInl < LIMITS.topInl) why.push("手牌上緣不直");
    if (row.comb.dev > LIMITS.dev) why.push("分不出每張牌的邊");
    const detail = row.cards.map((gl) => (gl ? K.classify(gl, model) : null));
    const cards = detail.map((c) => (c ? toB2(c.card) : -1));
    const sure = detail.map((c) => !!c && c.rTop >= LIMITS.rTop && c.rMargin >= LIMITS.rMargin && c.colourSure && Math.abs(c.z) >= LIMITS.z);
    const inOrder = cards.every((c, i) => i === 0 || !sure[i] || !sure[i - 1] || c > cards[i - 1]);
    if (!why.length && !inOrder) why.push("讀到的順序和遊戲排法不合");
    const nSure = sure.filter(Boolean).length, mean = detail.reduce((a, c) => a + (c ? c.rTop : 0), 0) / Math.max(1, detail.length);
    return { ok: !why.length && sure.every(Boolean), geoOk: !why.length, why: why.join("；"), n: row.n, cards, sure, lit: row.lit, detail, geo: row.geo, comb: row.comb, quad: row.quad, band: row.band, nSure, mean };
  }
  function readHand(img, model, LS, hc) {
    const t0 = Date.now(), ls = LS || K.lumSat(img);
    const row = readRow(img, ls, hc);
    if (row.why) return { ok: false, why: row.why, ms: Date.now() - t0 };
    let res = judge(row, model);
    // the edges lower down are pulled to one side by the hint buttons now and then: a large offset is checked against a small one
    if (Math.abs(row.comb.shift) > 7) {
      const row2 = readRow(img, ls, hc, 7, row.g);
      if (!row2.why) {
        const r2 = judge(row2, model), score = (r) => (r.geoOk ? 100 : 0) + r.nSure + r.mean;
        if (score(r2) > score(res)) res = r2;
      }
    }
    res.ms = Date.now() - t0;
    return res;
  }
  // one screenshot, everything: your row (with which cards are lit), the others' counts and PASS signs, the newest play on the pile
  function readShot(img, M) {
    const t0 = Date.now(), LS = K.lumSat(img);
    const hand = readHand(img, M.cards, LS);
    const st = hand.geo ? hand.geo.strip : findStrip(LS, img);
    if (!st) return { hand, ms: Date.now() - t0 };
    const tb = readTable(img, st, M.table);
    const pile = readPile(img, tb.F, M.cards), turn = buttonsShown(img, tb.F), raised = raisedCard(img, tb.F), shows = readShows(img, tb.F, M.cards);
    return { hand, seats: tb.seats, pile, shows, myTurn: turn.on, turn, raised: raised > 150, raisedPx: raised, ms: Date.now() - t0, strip: st };
  }
  return { readShot, readShows, readFan, SHOWBOX, readHand, readRow, findStrip, findRow, frameOf, grab, findBadge, badgeNumber, findPass, pileWhite, readPile, buttonsShown, raisedCard, fitQuad, cardStripFrom, readTable, unpackTable, SEATBOX, PASSBOX, PILEBOX, BP, toB2, LIMITS, BW, BH, CW, VROWS: VROWS0, K };
})();
if (typeof module !== "undefined") module.exports = { LocalRead, B2Read };
