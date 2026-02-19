Building benchmark files in Rocq
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/ocaml'
OCaml with extraction optimisations on. Bytecode:
./main 50
demo0 execution time: 0.001907 milliseconds
demo1 execution time: 1.345873 milliseconds
demo2 execution time: 0.609875 milliseconds
list_sum execution time: 5.150080 milliseconds
vs_easy execution time: 1196.338892 milliseconds
vs_hard execution time: 5572.000027 milliseconds
binom execution time: 971.048117 milliseconds
sha_fast execution time: 3076.499939 milliseconds
OCaml with extraction optimisations on. Native:
./mainopt 50
demo0 execution time: 0.000000 milliseconds
demo1 execution time: 1.197815 milliseconds
demo2 execution time: 0.411034 milliseconds
list_sum execution time: 1.753092 milliseconds
vs_easy execution time: 59.525013 milliseconds
vs_hard execution time: 707.523823 milliseconds
binom execution time: 182.524920 milliseconds
sha_fast execution time: 1089.809895 milliseconds
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/ocaml'
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/ocaml-noopt'
OCaml with extraction optimisations off. Bytecode:
./main 50
demo0 execution time: 0.001907 milliseconds
demo1 execution time: 1.357079 milliseconds
demo2 execution time: 0.618935 milliseconds
list_sum execution time: 4.220009 milliseconds
vs_easy execution time: 1390.561819 milliseconds
vs_hard execution time: 6331.865788 milliseconds
binom execution time: 963.052988 milliseconds
sha_fast execution time: 3167.626143 milliseconds
OCaml with extraction optimisations off. Native:
./mainopt 50
demo0 execution time: 0.000000 milliseconds
demo1 execution time: 1.112938 milliseconds
demo2 execution time: 0.326872 milliseconds
list_sum execution time: 1.699924 milliseconds
vs_easy execution time: 74.374914 milliseconds
vs_hard execution time: 684.942961 milliseconds
binom execution time: 141.510963 milliseconds
sha_fast execution time: 914.949179 milliseconds
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/ocaml-noopt'
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction'
Malfunction with no optimisations
./mainopt 50
demo0 execution time: 0.000000 milliseconds
demo1 execution time: 1.184940 milliseconds
demo2 execution time: 0.385046 milliseconds
list_sum execution time: 2.251863 milliseconds
vs_easy execution time: 192.233086 milliseconds
vs_hard execution time: 1721.196890 milliseconds
binom execution time: 162.120104 milliseconds
color xecution time: 9.726379 seconds
sha_fast execution time: 1134.437084 milliseconds
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction'
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-o2'
Malfunction with -O2 optimisations
./mainopt 50
demo0 execution time: 0.000000 milliseconds
demo1 execution time: 1.029968 milliseconds
demo2 execution time: 0.390053 milliseconds
list_sum execution time: 1.731873 milliseconds
vs_easy execution time: 64.817905 milliseconds
vs_hard execution time: 953.161001 milliseconds
binom execution time: 155.874014 milliseconds
color xecution time: 5.510898 seconds
sha_fast execution time: 986.850023 milliseconds
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-o2'
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-verified'
Bootstrapped Malfunction with no optimisations
./mainopt 50
demo0 execution time: 0.000954 milliseconds
demo1 execution time: 1.096010 milliseconds
demo2 execution time: 0.367165 milliseconds
list_sum execution time: 1.991987 milliseconds
vs_easy execution time: 181.107044 milliseconds
vs_hard execution time: 1634.962082 milliseconds
binom execution time: 150.362015 milliseconds
color xecution time: 9.617011 seconds
sha_fast execution time: 1239.794016 milliseconds
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-verified'
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-verified-o2'
Bootstrapped Malfunction with -O2 optimisations
./mainopt 50
demo0 execution time: 0.000000 milliseconds
demo1 execution time: 1.156092 milliseconds
demo2 execution time: 0.355959 milliseconds
list_sum execution time: 1.696110 milliseconds
vs_easy execution time: 65.499067 milliseconds
vs_hard execution time: 951.756001 milliseconds
binom execution time: 150.038958 milliseconds
color xecution time: 5.393737 seconds
sha_fast execution time: 985.840797 milliseconds
