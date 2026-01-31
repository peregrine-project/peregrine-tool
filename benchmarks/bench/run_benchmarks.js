#!/usr/bin/env node
/**
 * Benchmark Runner for Peregrine-compiled WASM
 *
 * Runs all WASM benchmarks and collects timing data.
 * Outputs results in JSON and markdown table format.
 *
 * Usage: node run_benchmarks.js [--json] [--runs N]
 */

const fs = require('fs');
const path = require('path');
const { execSync } = require('child_process');

const SCRIPT_DIR = __dirname;
const TARGETS_DIR = path.join(SCRIPT_DIR, 'targets');
const RESULTS_DIR = path.join(SCRIPT_DIR, 'results');

// WASM import object for Peregrine-compiled code
const importObject = {
    env: {
        write_char: (c) => process.stdout.write(String.fromCharCode(c)),
        write_int: (n) => process.stdout.write(n.toString()),
    }
};

// Parse command line arguments
const args = process.argv.slice(2);
const outputJson = args.includes('--json');
const runsIndex = args.indexOf('--runs');
const NUM_RUNS = runsIndex >= 0 ? parseInt(args[runsIndex + 1]) || 3 : 3;
const WARMUP_RUNS = 1;

// Reference times from Benchmarks Game (for comparison context)
const REFERENCE_TIMES = {
    'binary_trees': { input: 21, c_gcc: 1.56, rust: 1.07, ocaml: 3.55, nodejs: 8.61 },
    'fannkuch': { input: 12, c_gcc: 2.14, rust: 3.81, ocaml: 8.84, nodejs: 11.07 },
    'pidigits': { input: 10000, c_gcc: 0.74, rust: 0.71, ocaml: 2.77, nodejs: 1.15 }
};

async function runWasm(wasmPath) {
    const bytes = fs.readFileSync(wasmPath);
    const { instance } = await WebAssembly.instantiate(new Uint8Array(bytes), importObject);

    const start = process.hrtime.bigint();
    instance.exports.main_function();
    const end = process.hrtime.bigint();

    const timeMs = Number(end - start) / 1e6;
    const memUsed = instance.exports.bytes_used?.value || instance.exports.mem_ptr?.value || 0;
    const outOfMem = instance.exports.out_of_mem?.value || instance.exports.result_out_of_mem?.value || 0;

    return { timeMs, memUsed, outOfMem };
}

async function benchmarkWasm(wasmPath, runs = NUM_RUNS) {
    const times = [];

    // Warmup
    for (let i = 0; i < WARMUP_RUNS; i++) {
        await runWasm(wasmPath);
    }

    // Timed runs
    for (let i = 0; i < runs; i++) {
        const result = await runWasm(wasmPath);
        times.push(result.timeMs);
    }

    const mean = times.reduce((a, b) => a + b, 0) / times.length;
    const sorted = [...times].sort((a, b) => a - b);
    const median = sorted[Math.floor(sorted.length / 2)];
    const min = sorted[0];
    const max = sorted[sorted.length - 1];

    return { mean, median, min, max, runs: times };
}

function findWasmFiles(dir) {
    const results = [];
    if (!fs.existsSync(dir)) return results;

    const entries = fs.readdirSync(dir, { withFileTypes: true });
    for (const entry of entries) {
        const fullPath = path.join(dir, entry.name);
        if (entry.isDirectory()) {
            results.push(...findWasmFiles(fullPath));
        } else if (entry.name.endsWith('.wasm')) {
            results.push(fullPath);
        }
    }
    return results;
}

function parseBenchmarkInfo(wasmPath) {
    const relative = path.relative(TARGETS_DIR, wasmPath);
    const parts = relative.split(path.sep);
    // e.g., wasm/direct/binary_trees_10.wasm
    const backend = parts[0];
    const pipeline = parts[1];
    const filename = parts[parts.length - 1];
    const name = filename.replace('.wasm', '');

    // Extract benchmark name and input size
    const match = name.match(/^(.+?)_(\d+)$/);
    const benchName = match ? match[1] : name;
    const inputSize = match ? parseInt(match[2]) : null;

    return { backend, pipeline, name, benchName, inputSize, path: wasmPath };
}

async function main() {
    console.error(`=== Peregrine Benchmark Suite ===`);
    console.error(`Runs per benchmark: ${NUM_RUNS} (+ ${WARMUP_RUNS} warmup)`);
    console.error('');

    const wasmFiles = findWasmFiles(path.join(TARGETS_DIR, 'wasm'));

    if (wasmFiles.length === 0) {
        console.error('No WASM files found. Run compile_all.sh first.');
        process.exit(1);
    }

    console.error(`Found ${wasmFiles.length} WASM benchmarks`);
    console.error('');

    const results = [];

    for (const wasmPath of wasmFiles.sort()) {
        const info = parseBenchmarkInfo(wasmPath);
        console.error(`Running: ${info.pipeline}/${info.name}...`);

        try {
            const timing = await benchmarkWasm(wasmPath);
            results.push({
                ...info,
                ...timing,
                status: 'success'
            });
            console.error(`  -> ${timing.median.toFixed(2)} ms (median)`);
        } catch (err) {
            results.push({
                ...info,
                status: 'error',
                error: err.message
            });
            console.error(`  -> ERROR: ${err.message}`);
        }
    }

    // Ensure results directory exists
    if (!fs.existsSync(RESULTS_DIR)) {
        fs.mkdirSync(RESULTS_DIR, { recursive: true });
    }

    // Save JSON results
    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const jsonPath = path.join(RESULTS_DIR, `results_${timestamp}.json`);
    fs.writeFileSync(jsonPath, JSON.stringify({ timestamp, results }, null, 2));
    console.error(`\nResults saved to: ${jsonPath}`);

    // Output summary
    if (outputJson) {
        console.log(JSON.stringify(results, null, 2));
    } else {
        printMarkdownTable(results);
    }
}

function printMarkdownTable(results) {
    console.log('\n## Benchmark Results\n');

    // Group by benchmark name
    const byBenchmark = {};
    for (const r of results) {
        if (!byBenchmark[r.benchName]) byBenchmark[r.benchName] = [];
        byBenchmark[r.benchName].push(r);
    }

    for (const [benchName, benchResults] of Object.entries(byBenchmark)) {
        console.log(`### ${benchName}\n`);
        console.log('| Input | Pipeline | Median (ms) | Min | Max | Memory (bytes) |');
        console.log('|-------|----------|-------------|-----|-----|----------------|');

        const sorted = benchResults.sort((a, b) => {
            if (a.inputSize !== b.inputSize) return a.inputSize - b.inputSize;
            return a.pipeline.localeCompare(b.pipeline);
        });

        for (const r of sorted) {
            if (r.status === 'success') {
                console.log(`| ${r.inputSize} | ${r.pipeline} | ${r.median.toFixed(2)} | ${r.min.toFixed(2)} | ${r.max.toFixed(2)} | - |`);
            } else {
                console.log(`| ${r.inputSize} | ${r.pipeline} | ERROR | - | - | - |`);
            }
        }
        console.log('');
    }

    // Reference comparison
    console.log('### Reference Times (Benchmarks Game, official inputs)\n');
    console.log('| Benchmark | Input | C gcc | Rust | OCaml | Node.js |');
    console.log('|-----------|-------|-------|------|-------|---------|');
    for (const [name, times] of Object.entries(REFERENCE_TIMES)) {
        console.log(`| ${name} | ${times.input} | ${times.c_gcc}s | ${times.rust}s | ${times.ocaml}s | ${times.nodejs}s |`);
    }
    console.log('\n*Note: Reference implementations are highly optimized (multi-threaded, SIMD). Our inputs are smaller.*');
}

main().catch(console.error);
