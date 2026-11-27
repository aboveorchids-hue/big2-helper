// A helper thread for the advice: runs a share of the simulated deals (Big2.pimcRun) or, for the swap advice, of the
// tables (B2Swap.runTables) and sends the results back.
// Loaded as worker.js?v=<version>, so it takes the engine of the same version.
"use strict";
importScripts("engine.js" + self.location.search, "swap.js" + self.location.search);
self.onmessage = (e) => {
  const { id, kind, g, p, C, pol, seed, count, alive, my, gaves, opts } = e.data;
  try {
    const r = kind === "swap" ? self.B2Swap.runTables(my, gaves, alive, seed, count, opts) : self.Big2.pimcRun(g, p, C, pol, seed, count, alive);
    self.postMessage({ id, r });
  } catch (err) {
    self.postMessage({ id, err: String((err && err.message) || err) });
  }
};
