/* The bot's thinking, off the page's main thread. Messages in: {type: "load", url, passcode} and
   {type: "go", moves: [uci...], nodes, seconds}. Out: "loaded" / "error" / "info" / "best". */
importScripts("engine.js?v=9");
let searcher = null;

async function decrypt(buf, passcode) {
  // salt (16) | iv (12) | AES-GCM ciphertext; key = PBKDF2-SHA256(passcode, salt, 150,000)
  const salt = buf.slice(0, 16), iv = buf.slice(16, 28), data = buf.slice(28);
  const base = await crypto.subtle.importKey("raw", new TextEncoder().encode(passcode), "PBKDF2", false, ["deriveKey"]);
  const key = await crypto.subtle.deriveKey({ name: "PBKDF2", salt, iterations: 150000, hash: "SHA-256" }, base,
                                            { name: "AES-GCM", length: 256 }, false, ["decrypt"]);
  return crypto.subtle.decrypt({ name: "AES-GCM", iv }, key, data);
}

function positionAfter(moves) {
  const pos = new Chess.Position();
  pos.setFen(Chess.START);
  const history = [];
  for (const u of moves) {
    const m = pos.legal().find(x => Chess.uci(x) === u);
    if (!m) throw new Error("illegal move " + u);
    history.push(pos.hl, pos.hh);
    pos.make(m);
    if (pos.hm === 0) history.length = 0;        // nothing before an irreversible move can repeat
  }
  pos.stack = [];
  return { pos, history };
}

onmessage = async e => {
  const msg = e.data;
  try {
    if (msg.type === "load") {
      const r = await fetch(msg.url, { cache: "force-cache" });
      if (!r.ok) throw new Error("could not download the network (" + r.status + ")");
      let plain;
      try { plain = await decrypt(new Uint8Array(await r.arrayBuffer()), msg.passcode); }
      catch (err) { throw new Error("wrong passcode"); }
      const net = Chess.loadNet(plain);
      searcher = new Chess.Searcher(net, msg.search);
      postMessage({ type: "loaded", kr: net.kr, width: net.O });
    } else if (msg.type === "go") {
      if (!searcher) throw new Error("no bot loaded");
      const { pos, history } = positionAfter(msg.moves);
      if (msg.newGame) searcher.newGame();
      const res = searcher.go(pos, history, msg.nodes || 0, msg.seconds || 0,
                              info => postMessage({ type: "info", ...info }));
      postMessage({ type: "best", move: Chess.uci(res.best), depth: res.depth, nodes: res.nodes, score: res.score,
                    pv: res.pv.map(Chess.uci) });
    }
  } catch (err) {
    postMessage({ type: "error", message: String(err.message || err) });
  }
};
