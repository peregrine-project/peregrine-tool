import { readFileSync } from "fs";
import { ExecResult, ProgramType, SimpleType, TestCase } from "./types";


function write_int(value) {
  process.stdout.write(value.toString())
}
function write_char(value) {
  var chr = String.fromCharCode(value);
  process.stdout.write(chr);
}
let importObject = {
  env: {
    write_char: write_char,
    write_int: write_int,
  }
};

// Print bool
function pp_bool(val: number): string {
  if (val & 1) {
    switch (val >> 1) {
      case 0:
        return "false";
      case 1:
        return "true";
    }
  }
  else {
    return "error: expected unboxed constr"
  }
}

// Print nat
function pp_nat_sexp(val: number, dataView: any): string {
  if (val & 1) {
    switch (val >> 1) {
      case 0:
        return "O";
    }
  }
  else {
    const tag = dataView.getInt32(val, true);
    switch (tag) {
      case 0:
        const arg = dataView.getInt32(val + 4, true);
        const n = pp_nat_sexp(arg, dataView);
        return "(S " + n + ")";
    }
  }
}

// Print 63-bit integers
function pp_uint63(val, dataView): string {
  return dataView.getBigUint64(val, true).toString();
}

// Print lists
function pp_list_sexp(val, dataView, a_t): string {
  if (val & 1) {
    switch (val >> 1) {
      case 0:
        return "nil";
    }
  }
  else {
    const tag = dataView.getInt32(val, true);
    switch (tag) {
      case 0:
        const head = dataView.getInt32(val + 4, true);
        const elem_s = pp_wasm(a_t, head, dataView);

        const tail = dataView.getInt32(val + 8, true);
        const tail_s = pp_list_sexp(tail, dataView, a_t);

        return "(cons " + elem_s + " " + tail_s + ")";
    }
  }
}

// Print option type
function pp_option(val, dataView, a_t): string {
  if (val & 1) {
    return "None";
  }
  else {
    const arg = dataView.getInt32(val + 4, true);
    const elem_s = pp_wasm(a_t, arg, dataView);

    return "(Some " + elem_s + ")";
  }
}

// Print pairs
function pp_prod(val, dataView, a_t, b_t): string {
  const a = dataView.getInt32(val + 4, true);
  const a_s = pp_wasm(a_t, a, dataView);

  const b = dataView.getInt32(val + 8, true);
  const b_s = pp_wasm(b_t, b, dataView);

  return "(pair " + a_s + " " + b_s + ")";
}

// Pretty print a value `val` of type `type`
function pp_wasm(type: ProgramType, val: number, dataView: any): string {
  switch (type) {
    case SimpleType.Bool:
      return pp_bool(val);
    case SimpleType.Nat:
      return pp_nat_sexp(val, dataView);
    case SimpleType.UInt63:
      return pp_uint63(val, dataView);
    default:
      switch (type.type) {
        case "list":
          return pp_list_sexp(val, dataView, type.a_t);
        case "option":
          return pp_option(val, dataView, type.a_t);
        case "prod":
          return pp_prod(val, dataView, type.a_t, type.b_t);
      }
      break;
  }
}

// Runs the wasm code from `file`
export async function run_wasm(file: string, test: TestCase): Promise<ExecResult> {
  try {
    // Read code and initialize WebAssembly module
    const bytes = readFileSync(file);
    const obj = await WebAssembly.instantiate(
      new Uint8Array(bytes), importObject
    );

    // Run the main function
    const start_main = Date.now();
    obj.instance.exports.main_function();
    const stop_main = Date.now();
    const time_main = stop_main - start_main;

    // Get memory information and check for out of memoery exception
    var out_of_mem = obj.instance.exports.result_out_of_mem;
    var bytes_used = obj.instance.exports.bytes_used;

    // backwards compatibility
    if (out_of_mem == undefined) {
      // variable renamed from result_out_of_mem into out_of_mem
      out_of_mem = obj.instance.exports.out_of_mem;
    }
    if (bytes_used == undefined) {
      // variable renamed from bytes_used into mem_ptr
      bytes_used = obj.instance.exports.mem_ptr;
    }

    bytes_used = bytes_used.value;
    out_of_mem = out_of_mem.value;

    if (out_of_mem == 1) {
      return { type: "error", reason: "runtime error", error: "out of memory" };
    }

    // Pretty print output and check that it matches the expected output
    const res_value = obj.instance.exports.result.value;
    const memory = obj.instance.exports.memory;
    const dataView = new DataView(memory.buffer);
    const res = pp_wasm(test.output_type, res_value, dataView);
    if (res !== test.expected_output[0]) {
      return { type: "error", reason: "incorrect result", expected: test.expected_output[0], actual: res };
    }

    return { type: "success", time: time_main };
  } catch (e) {
    return { type: "error", reason: "runtime error", error: e};
  }
}
