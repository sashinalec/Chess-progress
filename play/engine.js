/* Sashin's chess bots in the browser (26 Oct 2026): a JavaScript copy of engine_v2's alpha-beta search and of the
   clipped both-sides networks ("CHW7" / "CHW8" / "CHW9": AI29 onwards). Same rules as the bots' own engine:
   evaluation = the network's value (side to move, -1..1) + 0.01 x the material change since the root; search =
   iterative deepening, transposition table, check extension, null move, late-move reductions, reverse futility,
   futility and late-move pruning (engine_v2 --ab-v2), capture search with captures and queen promotions.
   No tablebases. Used by the page (rules, legal moves, notation) and by the worker (the search). */
(function (G) {
"use strict";

const WHITE = 0, BLACK = 1;
const PAWN = 0, KNIGHT = 1, BISHOP = 2, ROOK = 3, QUEEN = 4, KING = 5;
const PIECE_VALUE = [1, 3, 3, 5, 9, 0];
const pcode = (c, t) => 1 + t + 8 * c;           // 0 = empty; white 1..6, black 9..14
const colourOf = p => p >> 3;
const typeOf = p => (p & 7) - 1;
const F_EP = 1, F_CASTLE = 2, F_DOUBLE = 3;
const mkMove = (f, t, promo, flag) => f | (t << 6) | (promo << 12) | (flag << 15);
const mFrom = m => m & 63, mTo = m => (m >> 6) & 63, mPromo = m => (m >> 12) & 7, mFlag = m => (m >> 15) & 3;

// ---- attack tables
const KN = [], KG = [], RAY = [];                 // RAY[dir][sq] = squares in that direction
const DIRS = [[0, 1], [0, -1], [1, 0], [-1, 0], [1, 1], [-1, 1], [1, -1], [-1, -1]];   // file, rank steps
for (let s = 0; s < 64; s++) {
  const f = s & 7, r = s >> 3, kn = [], kg = [];
  for (const [df, dr] of [[1, 2], [2, 1], [2, -1], [1, -2], [-1, -2], [-2, -1], [-2, 1], [-1, 2]]) {
    const ff = f + df, rr = r + dr;
    if (ff >= 0 && ff < 8 && rr >= 0 && rr < 8) kn.push(rr * 8 + ff);
  }
  for (const [df, dr] of DIRS) {
    const ff = f + df, rr = r + dr;
    if (ff >= 0 && ff < 8 && rr >= 0 && rr < 8) kg.push(rr * 8 + ff);
  }
  KN.push(kn); KG.push(kg);
}
for (let d = 0; d < 8; d++) {
  RAY.push([]);
  for (let s = 0; s < 64; s++) {
    const out = [];
    let f = (s & 7) + DIRS[d][0], r = (s >> 3) + DIRS[d][1];
    while (f >= 0 && f < 8 && r >= 0 && r < 8) { out.push(r * 8 + f); f += DIRS[d][0]; r += DIRS[d][1]; }
    RAY[d].push(out);
  }
}
const ROOK_DIRS = [0, 1, 2, 3], BISHOP_DIRS = [4, 5, 6, 7];

// ---- hashing (two 32-bit halves)
let seed = 0x9E3779B9;
const rnd = () => { seed ^= seed << 13; seed >>>= 0; seed ^= seed >>> 17; seed ^= seed << 5; seed >>>= 0; return seed; };
const ZL = new Uint32Array(16 * 64), ZH = new Uint32Array(16 * 64);
for (let i = 0; i < 16 * 64; i++) { ZL[i] = rnd(); ZH[i] = rnd(); }
const ZSL = rnd(), ZSH = rnd();
const ZCL = new Uint32Array(16), ZCH = new Uint32Array(16), ZEL = new Uint32Array(8), ZEH = new Uint32Array(8);
for (let i = 0; i < 16; i++) { ZCL[i] = rnd(); ZCH[i] = rnd(); }
for (let i = 0; i < 8; i++) { ZEL[i] = rnd(); ZEH[i] = rnd(); }
const CASTLE_KEEP = new Uint8Array(64).fill(15);
CASTLE_KEEP[4] = 15 & ~3; CASTLE_KEEP[60] = 15 & ~12; CASTLE_KEEP[7] = 15 & ~1; CASTLE_KEEP[0] = 15 & ~2;
CASTLE_KEEP[63] = 15 & ~4; CASTLE_KEEP[56] = 15 & ~8;

class Position {
  constructor() {
    this.b = new Int8Array(64); this.stm = WHITE; this.castle = 0; this.ep = -1; this.hm = 0; this.fm = 1;
    this.king = [4, 60]; this.hl = 0; this.hh = 0; this.mat = [0, 0]; this.npm = [0, 0]; this.count = 0;
    this.stack = [];                              // undo records
    this.delta = new Int32Array(8); this.nd = 0;  // the last move's changes: (sign, colour, type, square) packed
    this.lostCastle = 0; this.kingMoved = -1;
  }
  clone() {
    const p = new Position();
    p.b.set(this.b); p.stm = this.stm; p.castle = this.castle; p.ep = this.ep; p.hm = this.hm; p.fm = this.fm;
    p.king = this.king.slice(); p.hl = this.hl; p.hh = this.hh; p.mat = this.mat.slice(); p.npm = this.npm.slice(); p.count = this.count;
    return p;
  }
  setFen(fen) {
    const parts = fen.trim().split(/\s+/);
    this.b.fill(0); this.mat = [0, 0]; this.npm = [0, 0]; this.count = 0;
    let r = 7, f = 0;
    for (const ch of parts[0]) {
      if (ch === "/") { r--; f = 0; continue; }
      if (ch >= "1" && ch <= "8") { f += +ch; continue; }
      const c = ch === ch.toUpperCase() ? WHITE : BLACK, t = "pnbrqk".indexOf(ch.toLowerCase());
      if (t < 0) return false;
      const s = r * 8 + f++;
      this.b[s] = pcode(c, t); this.mat[c] += PIECE_VALUE[t]; if (t !== PAWN) this.npm[c] += PIECE_VALUE[t]; this.count++;
      if (t === KING) this.king[c] = s;
    }
    this.stm = parts[1] === "b" ? BLACK : WHITE;
    const cs = parts[2] || "-";
    this.castle = (cs.includes("K") ? 1 : 0) | (cs.includes("Q") ? 2 : 0) | (cs.includes("k") ? 4 : 0) | (cs.includes("q") ? 8 : 0);
    const ep = parts[3] || "-";
    this.ep = ep === "-" ? -1 : (ep.charCodeAt(0) - 97) + 8 * (ep.charCodeAt(1) - 49);
    this.hm = +(parts[4] || 0); this.fm = +(parts[5] || 1);
    this.rehash(); this.stack = [];
    return true;
  }
  rehash() {
    let l = 0, h = 0;
    for (let s = 0; s < 64; s++) if (this.b[s]) { l ^= ZL[this.b[s] * 64 + s]; h ^= ZH[this.b[s] * 64 + s]; }
    if (this.stm) { l ^= ZSL; h ^= ZSH; }
    l ^= ZCL[this.castle]; h ^= ZCH[this.castle];
    if (this.ep >= 0) { l ^= ZEL[this.ep & 7]; h ^= ZEH[this.ep & 7]; }
    this.hl = l >>> 0; this.hh = h >>> 0;
  }
  fen() {
    let s = "";
    for (let r = 7; r >= 0; r--) {
      let e = 0;
      for (let f = 0; f < 8; f++) {
        const p = this.b[r * 8 + f];
        if (!p) { e++; continue; }
        if (e) { s += e; e = 0; }
        const ch = "pnbrqk"[typeOf(p)];
        s += colourOf(p) === WHITE ? ch.toUpperCase() : ch;
      }
      if (e) s += e;
      if (r) s += "/";
    }
    const cs = (this.castle & 1 ? "K" : "") + (this.castle & 2 ? "Q" : "") + (this.castle & 4 ? "k" : "") + (this.castle & 8 ? "q" : "");
    const ep = this.ep >= 0 ? "abcdefgh"[this.ep & 7] + (1 + (this.ep >> 3)) : "-";
    return `${s} ${this.stm ? "b" : "w"} ${cs || "-"} ${ep} ${this.hm} ${this.fm}`;
  }
  attacked(s, by) {                                // is square s attacked by colour `by`?
    const b = this.b;
    // pawns
    const f = s & 7;
    if (by === WHITE) {
      if (s >= 8) { if (f > 0 && b[s - 9] === 1) return true; if (f < 7 && b[s - 7] === 1) return true; }
    } else {
      if (s < 56) { if (f > 0 && b[s + 7] === 9) return true; if (f < 7 && b[s + 9] === 9) return true; }
    }
    const kn = pcode(by, KNIGHT), kg = pcode(by, KING), q = pcode(by, QUEEN), ro = pcode(by, ROOK), bi = pcode(by, BISHOP);
    for (const t of KN[s]) if (b[t] === kn) return true;
    for (const t of KG[s]) if (b[t] === kg) return true;
    for (let d = 0; d < 8; d++) {
      const ray = RAY[d][s], straight = d < 4;
      for (let i = 0; i < ray.length; i++) {
        const p = b[ray[i]];
        if (!p) continue;
        if (p === q || p === (straight ? ro : bi)) return true;
        break;
      }
    }
    return false;
  }
  inCheck() { return this.attacked(this.king[this.stm], this.stm ^ 1); }
  // Pseudo-legal moves into out (Int32Array); noisy: captures (any promotion) and queen promotions only.
  gen(out, noisy) {
    const b = this.b, us = this.stm, them = us ^ 1;
    let n = 0;
    const fwd = us === WHITE ? 8 : -8, startR = us === WHITE ? 1 : 6, lastR = us === WHITE ? 7 : 0;
    for (let s = 0; s < 64; s++) {
      const p = b[s];
      if (!p || colourOf(p) !== us) continue;
      const t = typeOf(p);
      if (t === PAWN) {
        const r = s >> 3, f = s & 7, one = s + fwd;
        if (!b[one]) {
          if ((one >> 3) === lastR) {
            out[n++] = mkMove(s, one, QUEEN, 0);
            if (!noisy) { out[n++] = mkMove(s, one, KNIGHT, 0); out[n++] = mkMove(s, one, ROOK, 0); out[n++] = mkMove(s, one, BISHOP, 0); }
          } else if (!noisy) {
            out[n++] = mkMove(s, one, 0, 0);
            if (r === startR && !b[one + fwd]) out[n++] = mkMove(s, one + fwd, 0, F_DOUBLE);
          }
        }
        for (const df of [-1, 1]) {
          if (f + df < 0 || f + df > 7) continue;
          const to = one + df, q = b[to];
          if (q && colourOf(q) === them) {
            if ((to >> 3) === lastR) for (const pr of [QUEEN, KNIGHT, ROOK, BISHOP]) out[n++] = mkMove(s, to, pr, 0);
            else out[n++] = mkMove(s, to, 0, 0);
          } else if (to === this.ep) out[n++] = mkMove(s, to, 0, F_EP);
        }
      } else if (t === KNIGHT || t === KING) {
        for (const to of (t === KNIGHT ? KN[s] : KG[s])) {
          const q = b[to];
          if (q ? colourOf(q) === them : !noisy) out[n++] = mkMove(s, to, 0, 0);
        }
        if (t === KING && !noisy) {
          const home = us === WHITE ? 4 : 60, kb = us === WHITE ? 1 : 4, qb = us === WHITE ? 2 : 8;
          if (s === home && (this.castle & kb) && !b[home + 1] && !b[home + 2] && b[home + 3] === pcode(us, ROOK) &&
              !this.attacked(home, them) && !this.attacked(home + 1, them) && !this.attacked(home + 2, them))
            out[n++] = mkMove(home, home + 2, 0, F_CASTLE);
          if (s === home && (this.castle & qb) && !b[home - 1] && !b[home - 2] && !b[home - 3] && b[home - 4] === pcode(us, ROOK) &&
              !this.attacked(home, them) && !this.attacked(home - 1, them) && !this.attacked(home - 2, them))
            out[n++] = mkMove(home, home - 2, 0, F_CASTLE);
        }
      } else {
        const dirs = t === ROOK ? ROOK_DIRS : t === BISHOP ? BISHOP_DIRS : null;
        for (let d = 0; d < 8; d++) {
          if (dirs && dirs.indexOf(d) < 0) continue;
          const ray = RAY[d][s];
          for (let i = 0; i < ray.length; i++) {
            const to = ray[i], q = b[to];
            if (!q) { if (!noisy) out[n++] = mkMove(s, to, 0, 0); continue; }
            if (colourOf(q) === them) out[n++] = mkMove(s, to, 0, 0);
            break;
          }
        }
      }
    }
    return n;
  }
  isCapture(m) { return mFlag(m) === F_EP || this.b[mTo(m)] !== 0; }
  _put(s, p) {
    this.b[s] = p; this.hl ^= ZL[p * 64 + s]; this.hh ^= ZH[p * 64 + s];
    this.delta[this.nd++] = (1 << 12) | (colourOf(p) << 9) | (typeOf(p) << 6) | s;
  }
  _take(s) {
    const p = this.b[s];
    this.b[s] = 0; this.hl ^= ZL[p * 64 + s]; this.hh ^= ZH[p * 64 + s];
    this.delta[this.nd++] = (colourOf(p) << 9) | (typeOf(p) << 6) | s;
    return p;
  }
  make(m) {
    const from = mFrom(m), to = mTo(m), promo = mPromo(m), flag = mFlag(m), us = this.stm, them = us ^ 1;
    const piece = this.b[from];
    this.nd = 0; this.kingMoved = -1;
    const capSq = flag === F_EP ? to - (us === WHITE ? 8 : -8) : to;
    const undo = { m, cap: this.b[capSq], castle: this.castle, ep: this.ep, hm: this.hm, hl: this.hl, hh: this.hh,
                   mat0: this.mat[0], mat1: this.mat[1], npm0: this.npm[0], npm1: this.npm[1], count: this.count };
    this.stack.push(undo);
    if (this.ep >= 0) { this.hl ^= ZEL[this.ep & 7]; this.hh ^= ZEH[this.ep & 7]; }
    this.hl ^= ZCL[this.castle]; this.hh ^= ZCH[this.castle];
    if (undo.cap) { this._take(capSq); this.mat[them] -= PIECE_VALUE[typeOf(undo.cap)]; if (typeOf(undo.cap) !== PAWN) this.npm[them] -= PIECE_VALUE[typeOf(undo.cap)]; this.count--; }
    this._take(from);
    if (promo) { this._put(to, pcode(us, promo)); this.mat[us] += PIECE_VALUE[promo] - 1; this.npm[us] += PIECE_VALUE[promo]; }
    else this._put(to, piece);
    if (typeOf(piece) === KING) {
      this.king[us] = to; this.kingMoved = us;
      if (flag === F_CASTLE) {
        const rf = to > from ? to + 1 : to - 2, rt = to > from ? to - 1 : to + 1;
        this._put(rt, this._take(rf));
      }
    }
    const before = this.castle;
    this.castle &= CASTLE_KEEP[from] & CASTLE_KEEP[to];
    this.lostCastle = before & ~this.castle;
    this.ep = flag === F_DOUBLE ? (from + to) >> 1 : -1;
    this.hm = (typeOf(piece) === PAWN || undo.cap) ? 0 : this.hm + 1;
    if (us === BLACK) this.fm++;
    this.stm = them;
    this.hl ^= ZSL; this.hh ^= ZSH;
    this.hl ^= ZCL[this.castle]; this.hh ^= ZCH[this.castle];
    if (this.ep >= 0) { this.hl ^= ZEL[this.ep & 7]; this.hh ^= ZEH[this.ep & 7]; }
    this.hl >>>= 0; this.hh >>>= 0;
  }
  unmake() {
    const u = this.stack.pop(), m = u.m;
    const from = mFrom(m), to = mTo(m), promo = mPromo(m), flag = mFlag(m);
    this.stm ^= 1;
    const us = this.stm;
    if (us === BLACK) this.fm--;
    const piece = promo ? pcode(us, PAWN) : this.b[to];
    this.b[to] = 0; this.b[from] = piece;
    if (typeOf(piece) === KING) {
      this.king[us] = from;
      if (flag === F_CASTLE) {
        const rf = to > from ? to + 1 : to - 2, rt = to > from ? to - 1 : to + 1;
        this.b[rf] = this.b[rt]; this.b[rt] = 0;
      }
    }
    if (u.cap) this.b[flag === F_EP ? to - (us === WHITE ? 8 : -8) : to] = u.cap;
    this.castle = u.castle; this.ep = u.ep; this.hm = u.hm; this.hl = u.hl; this.hh = u.hh;
    this.mat[0] = u.mat0; this.mat[1] = u.mat1; this.npm[0] = u.npm0; this.npm[1] = u.npm1; this.count = u.count;
  }
  makeNull() {
    this.stack.push({ m: -1, ep: this.ep, hl: this.hl, hh: this.hh, hm: this.hm });
    if (this.ep >= 0) { this.hl ^= ZEL[this.ep & 7]; this.hh ^= ZEH[this.ep & 7]; }
    this.ep = -1; this.stm ^= 1; this.hm++;
    this.hl = (this.hl ^ ZSL) >>> 0; this.hh = (this.hh ^ ZSH) >>> 0;
  }
  unmakeNull() {
    const u = this.stack.pop();
    this.stm ^= 1; this.ep = u.ep; this.hl = u.hl; this.hh = u.hh; this.hm = u.hm;
  }
  // legal moves (for the page)
  legal() {
    const buf = new Int32Array(256), n = this.gen(buf, false), out = [];
    for (let i = 0; i < n; i++) {
      this.make(buf[i]);
      if (!this.attacked(this.king[this.stm ^ 1], this.stm)) out.push(buf[i]);
      this.unmake();
    }
    return out;
  }
  insufficient() {
    if (this.count > 4) return false;
    let minors = 0;
    for (let s = 0; s < 64; s++) {
      const p = this.b[s];
      if (!p) continue;
      const t = typeOf(p);
      if (t === PAWN || t === ROOK || t === QUEEN) return false;
      if (t === KNIGHT || t === BISHOP) minors++;
    }
    return minors <= 1;
  }
  materialWhite() { return this.mat[0] - this.mat[1]; }
}

// ---- notation
const sqName = s => "abcdefgh"[s & 7] + (1 + (s >> 3));
function uci(m) { return sqName(mFrom(m)) + sqName(mTo(m)) + (mPromo(m) ? "nbrq"[mPromo(m) - 1] : ""); }
function san(pos, m) {
  const from = mFrom(m), to = mTo(m), p = pos.b[from], t = typeOf(p);
  let s;
  if (mFlag(m) === F_CASTLE) s = to > from ? "O-O" : "O-O-O";
  else {
    const cap = pos.isCapture(m);
    if (t === PAWN) s = (cap ? "abcdefgh"[from & 7] + "x" : "") + sqName(to) + (mPromo(m) ? "=" + "NBRQ"[mPromo(m) - 1] : "");
    else {
      const others = pos.legal().filter(o => o !== m && mTo(o) === to && pos.b[mFrom(o)] === p);
      let dis = "";
      if (others.length) {
        const sameFile = others.some(o => (mFrom(o) & 7) === (from & 7)), sameRank = others.some(o => (mFrom(o) >> 3) === (from >> 3));
        dis = !sameFile ? "abcdefgh"[from & 7] : !sameRank ? String(1 + (from >> 3)) : sqName(from);
      }
      s = "NBRQK"[t - 1] + dis + (cap ? "x" : "") + sqName(to);
    }
  }
  pos.make(m);
  const check = pos.inCheck(), mate = check && pos.legal().length === 0;
  pos.unmake();
  return s + (mate ? "#" : check ? "+" : "");
}

// ---- the networks: "CHW1" / "CHW3" (LayerNorm, one value head), "CHW5" (LayerNorm, phase value heads), "CHW7" /
// "CHW8" / "CHW9" (clipped, both sides, king-relative) - and "CHW6" (separate networks by phase, NetParts below)
const CHW1 = 0x31574843, CHW3 = 0x33574843, CHW5 = 0x35574843, CHW6 = 0x36574843, CHW7 = 0x37574843, CHW8 = 0x38574843, CHW9 = 0x39574843;
class Net {
  constructor(buf) {
    const dv = new DataView(buf);
    let pos = 0;
    const i32 = () => { const v = dv.getInt32(pos, true); pos += 4; return v; };
    const f32s = n => { const a = new Float32Array(n); for (let i = 0; i < n; i++) a[i] = dv.getFloat32(pos + 4 * i, true); pos += 4 * n; return a; };
    const magic = i32();
    if (![CHW1, CHW3, CHW5, CHW7, CHW8, CHW9].includes(magic)) throw new Error("this kind of network can't be played here");
    this.crelu = magic >= CHW7; this.dual = magic === CHW8 || magic === CHW9; this.kr = magic === CHW9;
    const nh = i32();
    this.slope = magic === CHW1 ? 0 : f32s(1)[0];
    this.L = [];
    for (let i = 0; i < nh; i++) {
      const li = i32(), lo = i32(), W = f32s(li * lo), b = f32s(lo), gamma = f32s(lo), beta = f32s(lo);
      this.L.push({ in: li, out: lo, W, b, gamma, beta });     // (gamma / beta: 1 and 0 in a clipped network)
    }
    const l0 = this.L[0], O = l0.out, T = new Float32Array(l0.in * O);       // layer 0 as rows [input][neuron]
    for (let o = 0; o < O; o++) for (let k = 0; k < l0.in; k++) T[k * O + o] = l0.W[o * l0.in + k];
    l0.W = T; this.O = O;
    const po = i32(), pi = i32(); pos += 4 * (po * pi + po);                   // the move head (not used)
    const nheads = magic === CHW1 || magic === CHW3 ? 1 : i32();
    this.cuts = []; if (nheads > 1) for (let k = 0; k + 1 < nheads; k++) this.cuts.push(i32());
    this.heads = [];
    for (let k = 0; k < nheads; k++) {
      const hid = i32(), vin = i32();
      this.heads.push({ hid, vin, W1: f32s(hid * vin), b1: f32s(hid), W2: f32s(hid), b2: f32s(1)[0] });
    }
    this.stride = 2 * this.O;                      // the search's first-layer sums for one position
    this.hmRow = this.kr ? 6148 : 772;
    this.feat = this.L[nh - 1].out * (this.dual && nh === 1 ? 2 : 1);
    let widest = 2 * O; for (const l of this.L) widest = Math.max(widest, l.out, l.in);
    this.x = new Float32Array(widest); this.y = new Float32Array(widest); this.hv = new Float32Array(512);
  }
  kview(pos, view) {
    if (!this.kr) return 0;
    const sq = view === WHITE ? pos.king[WHITE] : pos.king[BLACK] ^ 56;
    const f = sq & 7, r = sq >> 3, mir = f >= 4 ? 7 : 0, rg = r === 0 ? 0 : r === 1 ? 1 : r <= 3 ? 2 : 3;
    return (((rg * 2 + ((f ^ mir) >> 1)) * 768) << 3) | mir;     // base x 8 | mirror
  }
  row(i, kv) {
    if (!this.kr) return i;
    if (i < 768) return (kv >> 3) + (i & ~63) + ((i & 63) ^ (kv & 7));
    return 6144 + (i - 768);
  }
  static pieceInput(view, c, t, sq) { return ((c === view ? 0 : 6) + t) * 64 + (view === WHITE ? sq : sq ^ 56); }
  static castleInput(view, right) {                // 1 wK, 2 wQ, 4 bK, 8 bQ
    const own = view === WHITE ? right <= 2 : right >= 4;
    return (own ? 768 : 770) + ((right === 2 || right === 8) ? 1 : 0);
  }
  addRow(acc, off, r, sign) {
    const W = this.L[0].W, O = this.O, base = r * O;
    if (sign > 0) for (let o = 0; o < O; o++) acc[off + o] += W[base + o];
    else for (let o = 0; o < O; o++) acc[off + o] -= W[base + o];
  }
  accView(pos, view, acc, off) {
    const O = this.O, kv = this.kview(pos, view);
    acc.set(this.L[0].b, off);
    for (let s = 0; s < 64; s++) {
      const p = pos.b[s];
      if (p) this.addRow(acc, off, this.row(Net.pieceInput(view, colourOf(p), typeOf(p), s), kv), 1);
    }
    for (const right of [1, 2, 4, 8]) if (pos.castle & right) this.addRow(acc, off, this.row(Net.castleInput(view, right), kv), 1);
  }
  accFull(pos, acc, off) { this.accView(pos, WHITE, acc, off); this.accView(pos, BLACK, acc, off + this.O); }
  // The sums after the move just made (pos.delta / lostCastle), from the parent's at pOff into cOff.
  accChild(pos, acc, pOff, cOff, kvBefore) {
    const O = this.O;
    for (let view = 0; view < 2; view++) {
      const src = pOff + view * O, dst = cOff + view * O, kv = this.kview(pos, view);
      if (this.kr && kv !== kvBefore[view]) { this.accView(pos, view, acc, dst); continue; }
      acc.copyWithin(dst, src, src + O);
      for (let i = 0; i < pos.nd; i++) {
        const d = pos.delta[i], sign = (d >> 12) ? 1 : -1;
        this.addRow(acc, dst, this.row(Net.pieceInput(view, (d >> 9) & 1, (d >> 6) & 7, d & 63), kv), sign);
      }
      for (const right of [1, 2, 4, 8]) if (pos.lostCastle & right) this.addRow(acc, dst, this.row(Net.castleInput(view, right), kv), -1);
    }
  }
  value(pos, acc, off) {
    const O = this.O, hm = Math.min(pos.hm, 100) / 100, W = this.L[0].W, hr = this.hmRow * O;
    let x = this.x, y = this.y;
    const a = off + pos.stm * O, b = off + (pos.stm ^ 1) * O;
    if (!this.crelu) return this.valueNorm(pos, acc, a, hm);
    for (let o = 0; o < O; o++) { const v = acc[a + o] + hm * W[hr + o]; x[o] = v < 0 ? 0 : v > 1 ? 1 : v; }
    if (this.dual) for (let o = 0; o < O; o++) { const v = acc[b + o] + hm * W[hr + o]; x[O + o] = v < 0 ? 0 : v > 1 ? 1 : v; }
    for (let li = 1; li < this.L.length; li++) {
      const l = this.L[li];
      for (let o = 0; o < l.out; o++) {
        let s = l.b[o];
        const base = o * l.in;
        for (let k = 0; k < l.in; k++) s += l.W[base + k] * x[k];
        y[o] = s < 0 ? 0 : s > 1 ? 1 : s;
      }
      const t = x; x = y; y = t;
    }
    return this.head(pos, x);
  }
  head(pos, x) {
    let k = 0;
    while (k < this.cuts.length && pos.count < this.cuts[k]) k++;
    const hd = this.heads[k], f = hd.vin;
    let v = hd.b2;
    for (let h = 0; h < hd.hid; h++) {
      let s = hd.b1[h];
      const base = h * f;
      for (let i = 0; i < f; i++) s += hd.W1[base + i] * x[i];
      v += s > 0 ? hd.W2[h] * s : hd.W2[h] * s * this.slope;
    }
    return Math.tanh(v);
  }
  // LayerNorm networks (engine: layer_norm_relu_lanes): normalise, scale, shift, (leaky) ReLU, layer by layer.
  norm(x, n, gamma, beta) {
    let mean = 0, v = 0;
    for (let o = 0; o < n; o++) mean += x[o];
    mean /= n;
    for (let o = 0; o < n; o++) { const d = x[o] - mean; v += d * d; }
    const inv = 1 / Math.sqrt(v / n + 1e-5), sl = this.slope;
    for (let o = 0; o < n; o++) { const t = (x[o] - mean) * inv * gamma[o] + beta[o]; x[o] = t > 0 ? t : t * sl; }
  }
  valueNorm(pos, acc, a, hm) {
    const O = this.O, W = this.L[0].W, hr = this.hmRow * O;
    let x = this.x, y = this.y;
    for (let o = 0; o < O; o++) x[o] = acc[a + o] + hm * W[hr + o];
    this.norm(x, O, this.L[0].gamma, this.L[0].beta);
    for (let li = 1; li < this.L.length; li++) {
      const l = this.L[li];
      for (let o = 0; o < l.out; o++) {
        let s2 = l.b[o];
        const base = o * l.in;
        for (let k = 0; k < l.in; k++) s2 += l.W[base + k] * x[k];
        y[o] = s2;
      }
      this.norm(y, l.out, l.gamma, l.beta);
      const t = x; x = y; y = t;
    }
    return this.head(pos, x);
  }
}

// "CHW6" (AI25 / AI26): separate networks for the opening, middlegame and endgame, chosen by the number of pieces.
class NetParts {
  constructor(buf) {
    const dv = new DataView(buf);
    let pos = 4;
    const np = dv.getInt32(pos, true); pos += 4;
    this.cuts = []; for (let k = 0; k + 1 < np; k++) { this.cuts.push(dv.getInt32(pos, true)); pos += 4; }
    this.parts = [];
    for (let k = 0; k < np; k++) {
      const len = dv.getInt32(pos, true); pos += 4;
      this.parts.push(new Net(buf.slice(pos, pos + len))); pos += len;
    }
    this.O = this.parts[0].O; this.kr = false;
    this.stride = this.parts.reduce((t, p) => t + p.stride, 0);
  }
  kview() { return 0; }
  accFull(pos, acc, off) { for (const p of this.parts) { p.accFull(pos, acc, off); off += p.stride; } }
  accChild(pos, acc, pOff, cOff, kvb) { for (const p of this.parts) { p.accChild(pos, acc, pOff, cOff, kvb); pOff += p.stride; cOff += p.stride; } }
  value(pos, acc, off) {
    let k = 0;
    while (k < this.cuts.length && pos.count < this.cuts[k]) k++;
    for (let i = 0; i < k; i++) off += this.parts[i].stride;
    return this.parts[k].value(pos, acc, off);
  }
}
function loadNet(buf) { return new DataView(buf).getInt32(0, true) === CHW6 ? new NetParts(buf) : new Net(buf); }

// ---- the search (engine_v2 alpha-beta, --ab-v2: reverse futility, futility, late-move pruning)
const MATE = 2.0, INF = 10.0, MAXPLY = 96, MW = 0.01;
const TT_BITS = 20, TT_SIZE = 1 << TT_BITS, TT_MASK = TT_SIZE - 1;
class Searcher {
  // opts: v2 (reverse futility, futility, late-move pruning - engine --ab-v2; off for AI6), contempt (AI26: a draw
  // counts this much against the side 2+ pawns of material ahead, for the one behind)
  constructor(net, opts) {
    this.net = net;
    this.v2 = !opts || opts.v2 !== false; this.contempt = (opts && opts.contempt) || 0;
    this.acc = new Float32Array((MAXPLY + 4) * net.stride);
    this.ttL = new Uint32Array(TT_SIZE); this.ttH = new Uint32Array(TT_SIZE); this.ttS = new Float32Array(TT_SIZE);
    this.ttM = new Int32Array(TT_SIZE); this.ttD = new Int8Array(TT_SIZE); this.ttF = new Int8Array(TT_SIZE);
    this.moves = []; this.scores = [];
    for (let i = 0; i < MAXPLY + 4; i++) { this.moves.push(new Int32Array(256)); this.scores.push(new Int32Array(256)); }
    this.killers = new Int32Array((MAXPLY + 4) * 2);
    this.hist = new Int32Array(2 * 64 * 64);
    this.counter = new Int32Array(16 * 64);
    this.stMove = new Int32Array(MAXPLY + 4); this.stPc = new Int32Array(MAXPLY + 4);
    this.pvT = []; this.pvLen = new Int32Array(MAXPLY + 4);
    for (let i = 0; i < MAXPLY + 4; i++) this.pvT.push(new Int32Array(MAXPLY + 4));
    this.lmr = [];
    for (let d = 0; d < 64; d++) { const row = new Int32Array(64); for (let i = 0; i < 64; i++) row[i] = (d < 3 || i < 3) ? 0 : Math.floor(0.75 + Math.log(d) * Math.log(i) / 2.25); this.lmr.push(row); }
    this.kvb = [0, 0];
  }
  newGame() { this.ttL.fill(0); this.ttH.fill(0); this.ttD.fill(0); this.hist.fill(0); this.counter.fill(0); }
  countNode() {
    if (++this.nodes >= this.budget) this.stop = true;
    else if ((this.nodes & 1023) === 0 && this.deadline && performance.now() >= this.deadline) this.stop = true;
  }
  make(pos, m, ply) {
    const net = this.net;
    this.kvb[0] = net.kview(pos, WHITE); this.kvb[1] = net.kview(pos, BLACK);
    pos.make(m);
    const O2 = net.stride;
    net.accChild(pos, this.acc, ply * O2, (ply + 1) * O2, this.kvb);
    this.path.push(pos.hl, pos.hh);
  }
  unmake(pos) { pos.unmake(); this.path.length -= 2; }
  evaluate(pos, ply) {
    const dm = pos.materialWhite() - this.rootMat;
    return this.net.value(pos, this.acc, ply * this.net.stride) + MW * (pos.stm === WHITE ? dm : -dm);
  }
  repeated(pos) {
    const n = this.path.length / 2, lim = Math.min(pos.hm, n - 1);
    for (let i = 2; i <= lim; i += 2) {
      const j = 2 * (n - 1 - i);
      if (this.path[j] === pos.hl && this.path[j + 1] === pos.hh) return true;
    }
    return false;
  }
  legalAfter(pos) { return !pos.attacked(pos.king[pos.stm ^ 1], pos.stm); }
  victim(pos, m) {
    if (mFlag(m) === F_EP) return 1;
    const p = pos.b[mTo(m)];
    return p ? PIECE_VALUE[typeOf(p)] : -1;
  }
  order(pos, mv, n, ply, ttMove) {
    const sc = this.scores[ply], k0 = this.killers[2 * ply], k1 = this.killers[2 * ply + 1];
    const cm = ply >= 1 && this.stMove[ply - 1] ? this.counter[this.stPc[ply - 1] * 64 + mTo(this.stMove[ply - 1])] : 0;
    for (let i = 0; i < n; i++) {
      const m = mv[i], v = this.victim(pos, m);
      if (m === ttMove) sc[i] = 1 << 30;
      else if (v >= 0) sc[i] = (1 << 28) + 64 * v - PIECE_VALUE[typeOf(pos.b[mFrom(m)])];
      else if (mPromo(m) === QUEEN) sc[i] = 1 << 27;
      else if (m === k0) sc[i] = 1 << 26;
      else if (m === k1) sc[i] = (1 << 26) - 1;
      else if (m === cm) sc[i] = (1 << 26) - 2;
      else sc[i] = this.hist[(pos.stm * 64 + mFrom(m)) * 64 + mTo(m)];
    }
    for (let i = 1; i < n; i++) {
      const m = mv[i], v = sc[i];
      let j = i - 1;
      while (j >= 0 && sc[j] < v) { mv[j + 1] = mv[j]; sc[j + 1] = sc[j]; j--; }
      mv[j + 1] = m; sc[j + 1] = v;
    }
  }
  qsearch(pos, alpha, beta, ply) {
    this.pvLen[ply] = 0;
    this.countNode();
    if (this.stop) return 0;
    const check = pos.inCheck(), mv = this.moves[ply];
    let n, best = -INF;
    if (check) {
      n = pos.gen(mv, false);
    } else {
      if (pos.insufficient()) return 0;
      const stand = this.evaluate(pos, ply);
      if (stand >= beta || ply >= MAXPLY) return stand;
      best = stand;
      if (stand > alpha) alpha = stand;
      n = pos.gen(mv, true);
    }
    this.order(pos, mv, n, ply, 0);
    let legal = 0;
    for (let i = 0; i < n; i++) {
      const m = mv[i];
      this.make(pos, m, ply);
      if (!this.legalAfter(pos)) { this.unmake(pos); continue; }
      legal++;
      const sc = -this.qsearch(pos, -beta, -alpha, ply + 1);
      this.unmake(pos);
      if (this.stop) return 0;
      if (sc > best) {
        best = sc;
        if (sc > alpha) {
          alpha = sc;
          this.setPv(ply, m);
          if (alpha >= beta) break;
        }
      }
    }
    if (check && legal === 0) return -(MATE - 0.001 * ply);
    return best;
  }
  setPv(ply, m) {
    const a = this.pvT[ply], c = this.pvT[ply + 1], n = this.pvLen[ply + 1];
    a[0] = m;
    for (let j = 0; j < n; j++) a[j + 1] = c[j];
    this.pvLen[ply] = n + 1;
  }
  search(pos, depth, alpha, beta, ply, pvNode, nullOk) {
    this.pvLen[ply] = 0;
    if (ply > 0) {
      if (pos.insufficient()) return 0;
      if (pos.hm >= 100 || this.repeated(pos)) {
        if (!this.contempt) return 0;
        const lead = pos.stm === WHITE ? pos.materialWhite() : -pos.materialWhite();
        return lead >= 2 ? -this.contempt : lead <= -2 ? this.contempt : 0;
      }
    }
    const check = pos.inCheck();
    if (check && ply < MAXPLY) depth++;
    if (depth <= 0 || ply >= MAXPLY) return this.qsearch(pos, alpha, beta, ply);
    this.countNode();
    if (this.stop) return 0;
    const ti = pos.hl & TT_MASK, hit = this.ttL[ti] === pos.hl && this.ttH[ti] === pos.hh && this.ttD[ti] > 0;
    let ttMove = 0;
    if (hit) {
      ttMove = this.ttM[ti];
      if (!pvNode && this.ttD[ti] - 1 >= depth) {
        let sc = this.ttS[ti];
        if (sc > MATE - 0.5) sc -= 0.001 * ply; else if (sc < -MATE + 0.5) sc += 0.001 * ply;
        const fl = this.ttF[ti];
        if (fl === 0 || (fl === 1 && sc >= beta) || (fl === 2 && sc <= alpha)) return sc;
      }
    }
    let staticEval = 0, haveStatic = false;
    if (this.v2 && !pvNode && !check && ply > 0) {
      staticEval = this.evaluate(pos, ply); haveStatic = true;
      if (depth <= 4 && Math.abs(beta) < MATE - 0.5 && staticEval - 0.12 * depth >= beta) return staticEval;
    }
    if (nullOk && !pvNode && !check && ply > 0 && depth >= 3 && beta < MATE - 0.5 && pos.npm[pos.stm] > 0 &&
        (haveStatic ? staticEval : this.evaluate(pos, ply)) >= beta) {
      const O2 = this.net.stride;
      this.acc.copyWithin((ply + 1) * O2, ply * O2, (ply + 1) * O2);
      pos.makeNull(); this.path.push(pos.hl, pos.hh);
      this.stMove[ply] = 0;
      const R = 2 + Math.floor(depth / 6);
      const sc = -this.search(pos, depth - 1 - R, -beta, -beta + 1e-5, ply + 1, false, false);
      pos.unmakeNull(); this.path.length -= 2;
      if (this.stop) return 0;
      if (sc >= beta) return sc > MATE - 0.5 ? beta : sc;
    }
    const mv = this.moves[ply];
    const n = pos.gen(mv, false);
    this.order(pos, mv, n, ply, ttMove);
    const alpha0 = alpha;
    let best = -INF, bestMove = 0, li = -1;
    const canPrune = !pvNode && !check && ply > 0 && haveStatic && depth <= 3;
    const futile = canPrune && depth === 1 && staticEval + 0.15 <= alpha;
    const lmpLimit = 3 + 2 * depth * depth;
    const quiets = []; const k0 = this.killers[2 * ply], k1 = this.killers[2 * ply + 1];
    for (let i = 0; i < n; i++) {
      const m = mv[i];
      const quiet = !pos.isCapture(m) && mPromo(m) === 0;
      const pc = pos.b[mFrom(m)];
      this.make(pos, m, ply);
      if (!this.legalAfter(pos)) { this.unmake(pos); continue; }
      li++;
      const givesCheck = pos.inCheck();
      if (canPrune && li > 0 && best > -MATE + 0.5 && quiet && m !== k0 && m !== k1 && (futile || li >= lmpLimit) && !givesCheck) {
        this.unmake(pos); continue;
      }
      this.stMove[ply] = m; this.stPc[ply] = pc;
      let sc;
      if (li === 0) sc = -this.search(pos, depth - 1, -beta, -alpha, ply + 1, pvNode, true);
      else {
        let r = 0;
        if (!check && depth >= 3 && li >= 3 && quiet && m !== k0 && m !== k1 && !givesCheck)
          r = Math.min(this.lmr[Math.min(depth, 63)][Math.min(li, 63)], depth - 2);
        sc = -this.search(pos, depth - 1 - r, -alpha - 1e-5, -alpha, ply + 1, false, true);
        if (!this.stop && r > 0 && sc > alpha) sc = -this.search(pos, depth - 1, -alpha - 1e-5, -alpha, ply + 1, false, true);
        if (!this.stop && sc > alpha && sc < beta) sc = -this.search(pos, depth - 1, -beta, -alpha, ply + 1, true, true);
      }
      this.unmake(pos);
      if (this.stop) return 0;
      if (sc > best) {
        best = sc; bestMove = m;
        if (sc > alpha) {
          alpha = sc;
          this.setPv(ply, m);
          if (alpha >= beta) {
            if (quiet) {
              if (k0 !== m) { this.killers[2 * ply + 1] = k0; this.killers[2 * ply] = m; }
              const bonus = Math.min(48 * depth * depth, 3000), base = pos.stm * 4096;
              this.hist[base + mFrom(m) * 64 + mTo(m)] += bonus;
              for (const q of quiets) this.hist[base + mFrom(q) * 64 + mTo(q)] -= bonus;
              if (ply >= 1 && this.stMove[ply - 1]) this.counter[this.stPc[ply - 1] * 64 + mTo(this.stMove[ply - 1])] = m;
            }
            break;
          }
        }
      }
      if (quiet && quiets.length < 64) quiets.push(m);
    }
    if (li < 0) return check ? -(MATE - 0.001 * ply) : 0;
    let ts = best;
    if (ts > MATE - 0.5) ts += 0.001 * ply; else if (ts < -MATE + 0.5) ts -= 0.001 * ply;
    this.ttL[ti] = pos.hl; this.ttH[ti] = pos.hh; this.ttS[ti] = ts; this.ttM[ti] = bestMove;
    this.ttD[ti] = Math.min(depth, 126) + 1; this.ttF[ti] = best >= beta ? 1 : best <= alpha0 ? 2 : 0;
    return best;
  }
  // One move: the root position, the game's earlier positions' hashes ([lo, hi, ...]), a budget.
  go(pos, history, nodes, seconds, onInfo) {
    this.nodes = 0; this.budget = nodes > 0 ? nodes : Infinity;
    this.deadline = seconds > 0 ? performance.now() + 1000 * seconds : 0;
    this.stop = false; this.path = history.slice(); this.path.push(pos.hl, pos.hh);
    this.rootMat = pos.materialWhite();
    this.killers.fill(0);
    for (let i = 0; i < this.hist.length; i++) this.hist[i] = (this.hist[i] / 8) | 0;
    this.net.accFull(pos, this.acc, 0);
    const legal = pos.legal();
    const res = { best: legal[0] || 0, score: 0, depth: 0, nodes: 0, pv: [] };
    if (!legal.length) return res;
    const t0 = performance.now();
    for (let depth = 1; depth <= MAXPLY - 8; depth++) {
      const sc = this.search(pos, depth, -INF, INF, 0, true, true);
      if (this.pvLen[0] > 0 && this.pvT[0][0]) {
        if (!this.stop || legal.includes(this.pvT[0][0])) { res.best = this.pvT[0][0]; res.pv = Array.from(this.pvT[0].subarray(0, this.pvLen[0])); }
      }
      if (this.stop) break;
      res.score = sc; res.depth = depth;
      if (onInfo) onInfo({ depth, score: sc, nodes: this.nodes, ms: performance.now() - t0, pv: res.pv.map(uci) });
      if (Math.abs(sc) > MATE - 0.5) break;
    }
    res.nodes = this.nodes;
    return res;
  }
}

G.Chess = { Position, Net, NetParts, loadNet, Searcher, san, uci, sqName, mFrom, mTo, mPromo, mFlag, WHITE, BLACK, typeOf, colourOf,
            PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, START: "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1" };
})(typeof self !== "undefined" ? self : this);
