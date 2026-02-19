# Benchmarks

Running the benchmarks assumes an intel-based Linux machine.
First you need to run the following commands on the host machine (i.e. when docker is used, outside of docker) to ensure that processor speed stays constant through benchmarking, e.g. that no thermal throttling occurs.

```bash
echo performance | sudo tee /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor
sudo cpupower idle-set -D 0
echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
```

The commands are taken from https://llvm.org/docs/Benchmarking.html. They likely rely on an Intel processor.
The benchmarks can still be run without issuing these commands first.

You need to have installed `core_bench.v0.16.0``.

Then on the client (i.e. when docker is used, inside of docker)

```bash
make
```

There are 7 different benchmarks:
- `ocaml-o0` runs `ocamlopt` with `-Oclassic` arguments, i.e. no `flambda` optimisations
- `ocaml` uses `ocamlopt` with `-O2` arguments
- `ocaml-noopt` uses `ocamlopt` with `-O2` arguments and `Unset Extraction Optimize`
- `malfunction` uses Malfunction with `-O0` arguments. This column is *not* displayed in the paper, because it is identicaly with `malfunction-verified`.
- `malfunction-o2` uses Malfunction with `-O2` arguments. This column is *not* displayed in the paper, because it is identicaly with `malfunction-verified-o2`.
- `malfunction-verified` uses the bootstrapped extraction plugin and then Malfunction with `-O0` arguments.
- `malfunction-verified-O2` uses the bootstrapped extraction plugin and then Malfunction with `-O2` arguments.
