// Host-driven interpreter for the free-monad program of WasmIO.v.
//
// The Wasm module that Peregrine emits has no imports.  Its main_function
// leaves the program's value in the exported global `result`: either
// `Pure a`, or `Op o k` with an operation `o` and a continuation closure `k`.
// The host performs `o`, writes the response into the module's memory, calls
// `k` on it and reads `result` again, until it finds `Pure a`.
//
// Value layout (CertiRocq's Wasm backend): a constructor without arguments is
// the unboxed i32 (2 * ordinal + 1); one with arguments is a pointer to its
// ordinal followed by one i32 per argument.  Ordinals are counted separately
// among the constructors with and without arguments.  A closure is a block
// whose fields 1 and 2 are the index of its code in the function table and its
// environment; the code takes (environment, argument).
//
//   node host.mjs wasmio.wasm < input
import { readFileSync } from "fs";

const bytes = readFileSync(process.argv[2]);
const input = readFileSync(0, "utf8").split(/\s+/).filter((s) => s.length > 0);

// The function index of every exported function, from the export section
// (the JS API gives the names only).  Table index = function index: the
// module's element segment maps them one to one from 0.
function exportedFunctions(buf) {
  let pos = 8;
  const leb = () => {
    let r = 0, shift = 0, b;
    do { b = buf[pos++]; r |= (b & 0x7f) << shift; shift += 7; } while (b & 0x80);
    return r >>> 0;
  };
  const byIndex = new Map();
  while (pos < buf.length) {
    const id = buf[pos++];
    const size = leb();
    const end = pos + size;
    if (id === 7) {
      for (let n = leb(); n > 0; n--) {
        const len = leb();
        const name = buf.subarray(pos, pos + len).toString("utf8");
        pos += len;
        const kind = buf[pos++];
        const index = leb();
        if (kind === 0) byIndex.set(index, name);
      }
    }
    pos = end;
  }
  return byIndex;
}

const { instance } = await WebAssembly.instantiate(bytes, {});
const ex = instance.exports;
const names = exportedFunctions(bytes);
const call = (fn, env, arg) => {
  const name = names.get(fn);
  if (name === undefined) throw new Error(`no exported function at table index ${fn}`);
  if (ex[name].length !== 2) throw new Error(`${name} takes ${ex[name].length} arguments, not 2 (direct style only)`);
  ex[name](env, arg);
  return checkedResult();
};
function checkedResult() {
  if (ex.out_of_mem.value !== 0) throw new Error("out of linear memory");
  return ex.result.value;
}

const view = () => new DataView(ex.memory.buffer);
const load = (p, i) => view().getInt32(p + 4 * i, true);
const boxed = (v) => (v & 1) === 0;

// Bump allocation at mem_ptr, as the module allocates.
function alloc(words) {
  const p = ex.mem_ptr.value;
  const need = p + 4 * words;
  const pages = Math.ceil(need / 65536) - ex.memory.buffer.byteLength / 65536;
  if (pages > 0) ex.memory.grow(pages);
  ex.mem_ptr.value = need;
  return p;
}
function block(ord, args) {
  const p = alloc(1 + args.length);
  const dv = view();
  dv.setInt32(p, ord, true);
  args.forEach((a, i) => dv.setInt32(p + 4 * (i + 1), a, true));
  return p;
}

// nat: O is unboxed 1, S n a block of ordinal 0
function natToWasm(n) {
  let v = 1;
  for (let i = 0; i < n; i++) v = block(0, [v]);
  return v;
}
function natOfWasm(v) {
  let n = 0;
  while (boxed(v)) { v = load(v, 1); n++; }
  return n;
}

// free: Pure a (ordinal 0), Op o k (ordinal 1); op: PutNat n (boxed 0),
// GetNat (unboxed 0); resp: RUnit (unboxed 0), RNat n (boxed 0)
const RUnit = 1;
ex.main_function();
let v = checkedResult();
for (;;) {
  if (!boxed(v)) throw new Error(`not a free-monad value: ${v}`);
  const tag = load(v, 0);
  if (tag === 0) {
    console.log(`result ${natOfWasm(load(v, 1))}`);
    break;
  }
  if (tag !== 1) throw new Error(`not a free-monad value: tag ${tag}`);
  const o = load(v, 1), k = load(v, 2);
  let r;
  if (boxed(o)) {
    console.log(natOfWasm(load(o, 1)));
    r = RUnit;
  } else {
    const x = input.shift() ?? "0";
    if (!/^\d+$/.test(x)) throw new Error(`input is not a natural number: ${x}`);
    r = block(0, [natToWasm(Number(x))]);
  }
  v = call(load(k, 1), load(k, 2), r);
}
