/* (owner, 29 Oct 2026) Guest codes: 6 characters that set up ONE game against one bot, played on the guest page
   (guest/) without the bot list, the passcodes, take-backs or the bot's evaluation. The site is static, so the code
   itself holds the game: bot number (6 bits, AI1-AI63), easier level (3), the guest's colour (1), thinking per move
   (4, an index into LIMITS), random opening (1), a random number (10: which opening, and different codes for the
   same game) and a check (5 bits: a mistyped code is almost always rejected). The 30 bits are shuffled (a small
   Feistel network) so that codes look random, then written in 32 characters without 0 / O / 1 / I.
   Used by index.html (making codes) and guest/index.html (playing them). Needs engine.js (Chess) for openings. */
const GuestCode = (() => {
  const ALPHABET = "23456789ABCDEFGHJKLMNPQRSTUVWXYZ";
  // Append only: a code stores the index.
  const LIMITS = [["time", 0.1], ["time", 0.5], ["time", 1], ["time", 2], ["time", 5], ["time", 10],
                  ["nodes", 5000], ["nodes", 16000], ["nodes", 64000], ["nodes", 250000], ["nodes", 1000000]];
  const KEYS = [0x5A17, 0x3C9E, 0x71D2, 0x0BE4];
  const OPENING_PLIES = 4;                      // a random opening: 2 random legal moves each

  const F = (r, k) => (Math.imul(r ^ KEYS[k], 0x9E3779B1) >>> 17) & 0x7FFF;
  const check = p => Math.imul(p, 0x27D4EB2F) >>> 27;

  function make(o) {
    if (!(o.bot >= 1 && o.bot < 64 && o.level >= 0 && o.level < 8 && o.limit >= 0 && o.limit < 16))
      throw new Error("this bot or setting can't go in a code");
    const p = (o.bot << 19) | (o.level << 16) | ((o.white ? 1 : 0) << 15) | (o.limit << 11) |
              ((o.random ? 1 : 0) << 10) | (o.seed & 1023);
    const x = (p << 5) | check(p);
    let L = x >>> 15, R = x & 0x7FFF;
    for (let k = 0; k < 4; k++) [L, R] = [R, L ^ F(R, k)];
    const y = L * 32768 + R;
    let s = "";
    for (let i = 5; i >= 0; i--) s += ALPHABET[(y >>> (5 * i)) & 31];
    return s;
  }

  // The game a code sets up, or null if it isn't a code (wrong length, a character not used, failed check).
  function read(text) {
    const s = String(text || "").toUpperCase().replace(/[^0-9A-Z]/g, "");
    if (s.length !== 6) return null;
    let y = 0;
    for (const ch of s) {
      const v = ALPHABET.indexOf(ch);
      if (v < 0) return null;
      y = y * 32 + v;
    }
    let L = Math.floor(y / 32768), R = y & 0x7FFF;
    for (let k = 3; k >= 0; k--) [L, R] = [R ^ F(L, k), L];
    const x = L * 32768 + R, p = x >>> 5;
    if ((x & 31) !== check(p)) return null;
    const o = { code: s, bot: p >>> 19, level: (p >>> 16) & 7, white: !!((p >>> 15) & 1), limit: (p >>> 11) & 15,
                random: !!((p >>> 10) & 1), seed: p & 1023 };
    if (!o.bot || o.limit >= LIMITS.length) return null;
    o.kind = LIMITS[o.limit][0];
    o.amount = LIMITS[o.limit][1];
    return o;
  }

  function rng(seed) {                          // mulberry32: the same numbers in every browser
    let a = seed >>> 0;
    return () => {
      a = (a + 0x6D2B79F5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  // A code's random opening: {uci: [...], san: [...]}, random legal moves (never one that ends the game).
  function opening(seed) {
    for (let salt = 0; ; salt++) {
      const r = rng(seed * 7919 + salt + 1), pos = new Chess.Position(), uci = [], san = [];
      pos.setFen(Chess.START);
      for (let i = 0; i < OPENING_PLIES; i++) {
        const legal = pos.legal(), m = legal[Math.floor(r() * legal.length)];
        san.push(Chess.san(pos, m));
        uci.push(Chess.uci(m));
        pos.make(m);
      }
      if (pos.legal().length) return { uci, san };
    }
  }

  const limitText = o => o.kind === "time" ? `${o.amount} s` : `${o.amount.toLocaleString("en-GB")} positions`;
  const sanText = san => san.map((m, i) => (i % 2 === 0 ? (i / 2 + 1) + ". " : "") + m).join(" ");

  return { LIMITS, make, read, opening, limitText, sanText, format: s => s.slice(0, 3) + " " + s.slice(3) };
})();
