// A helper thread for the play advice: runs a share of the simulated deals (Big2.pimcRun) and sends the results back.
// Loaded as worker.js?v=<version>, so it takes the engine of the same version.
"use strict";
importScripts("engine.js" + self.location.search);
self.onmessage = (e) => {
  const { id, g, p, C, pol, seed, count, alive } = e.data;
  try {
    self.postMessage({ id, r: self.Big2.pimcRun(g, p, C, pol, seed, count, alive) });
  } catch (err) {
    self.postMessage({ id, err: String((err && err.message) || err) });
  }
};
