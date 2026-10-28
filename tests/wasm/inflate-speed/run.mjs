// The speed of inflate_cells_proved in wasm (keyword: inflate-speed): instantiates the module, writes the compressed
// chapter into the memory it asks for, and times only bats_inflate_run with performance.now(): one warm-up, then five runs,
// and the median is reported. The output must be the chapter zlib inflates to (its size and sha256, data/chapter.expect).
// usage: node run.mjs <web.wasm> <data-dir>
import { readFileSync } from "node:fs";
import os from "node:os";

const [wasmPath, dataDir] = process.argv.slice(2);
const bytes = readFileSync(wasmPath);
const mod = new WebAssembly.Module(bytes);
console.log("imports:", JSON.stringify(WebAssembly.Module.imports(mod)));
console.log("exports:", WebAssembly.Module.exports(mod).map((e) => e.name).join(", "));
const stream = readFileSync(`${dataDir}/chapter.deflate`);
const [wantHash, wantSize, wantCompressed] = readFileSync(`${dataDir}/chapter.expect`, "utf8").trim().split(" ");
if (stream.length !== Number(wantCompressed)) throw new Error("chapter.deflate is not the size chapter.expect says");

const env = { bats_host_print: () => {}, bats_host_exit: () => {} };
const { exports } = new WebAssembly.Instance(mod, { env });
exports.bats_dynload();
exports.mainats_0_void();
const memory = exports.memory;

function once() {
  const at = exports.bats_inflate_prepare(stream.length);
  new Uint8Array(memory.buffer, at, stream.length).set(stream);
  const start = performance.now();
  const size = exports.bats_inflate_run(stream.length);
  const elapsed = performance.now() - start;
  const digest = Buffer.from(new Uint8Array(memory.buffer, exports.bats_inflate_digest(), 64)).toString("latin1");
  return { size, digest, elapsed };
}

once(); // warm-up
const times = [];
for (let i = 0; i < 5; i++) {
  const run = once();
  if (run.size !== Number(wantSize) || run.digest !== wantHash) {
    console.log(`FAIL: run ${i}: size ${run.size} sha256 ${run.digest}, zlib's ${wantSize} ${wantHash}`);
    process.exit(1);
  }
  times.push(run.elapsed);
}
const sorted = [...times].sort((a, b) => a - b);
console.log(`output ${wantSize} bytes, sha256 ${wantHash} (zlib's), from ${stream.length} compressed bytes`);
console.log(`five runs (ms): ${times.map((t) => t.toFixed(1)).join(", ")}`);
console.log(`median ${sorted[2].toFixed(1)} ms`);
console.log(`node ${process.version}, ${os.cpus()[0].model}, ${os.cpus().length} cpus, ${os.type()} ${os.release()}`);
