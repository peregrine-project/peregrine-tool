make -C ocaml all
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/ocaml'
Finished, 36 targets (36 cached) in 00:00:00.
OCaml with extraction optimisations on. Native:
Estimated testing time 1m20s (8 benchmarks x 10s). Change using '-quota'.
┌──────────┬──────────┬─────────────────┬───────────────┬────────────┬────────────┬────────────┬────────────┐
│ Name     │ Time R^2 │        Time/Run │          95ci │    mWd/Run │   mjWd/Run │   Prom/Run │ Percentage │
├──────────┼──────────┼─────────────────┼───────────────┼────────────┼────────────┼────────────┼────────────┤
│ demo0    │     1.00 │          3.16ns │ -0.03% +0.03% │            │            │            │            │
│ demo1    │     1.00 │     15_568.77ns │ -0.07% +0.07% │     3.90kw │     29.33w │     29.33w │      0.06% │
│ demo2    │     1.00 │      4_228.99ns │ -0.08% +0.08% │     1.20kw │      2.74w │      2.74w │      0.02% │
│ list_sum │     1.00 │     46_877.17ns │ -0.06% +0.06% │    10.20kw │      6.47w │      6.47w │      0.19% │
│ vs_easy  │     1.00 │  1_507_876.58ns │ -0.09% +0.10% │   509.30kw │    210.23w │    210.23w │      6.09% │
│ vs_hard  │     1.00 │ 18_895_057.60ns │ -1.46% +1.58% │ 1_571.30kw │ 68_747.66w │ 68_747.66w │     76.30% │
│ binom    │     1.00 │  3_726_351.68ns │ -0.05% +0.05% │    54.02kw │  2_256.97w │  2_256.97w │     15.05% │
│ sha_fast │     1.00 │ 24_765_277.05ns │ -0.15% +0.19% │ 5_707.29kw │ 63_670.43w │ 63_670.43w │    100.00% │
└──────────┴──────────┴─────────────────┴───────────────┴────────────┴────────────┴────────────┴────────────┘
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/ocaml'
make -C ocaml-noopt all
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/ocaml-noopt'
Extraction Optimize is off
Finished, 36 targets (36 cached) in 00:00:00.
OCaml with extraction optimisations off. Native:
Estimated testing time 1m20s (8 benchmarks x 10s). Change using '-quota'.
┌──────────┬──────────┬─────────────────┬───────────────┬────────────┬─────────────┬─────────────┬────────────┐
│ Name     │ Time R^2 │        Time/Run │          95ci │    mWd/Run │    mjWd/Run │    Prom/Run │ Percentage │
├──────────┼──────────┼─────────────────┼───────────────┼────────────┼─────────────┼─────────────┼────────────┤
│ demo0    │     1.00 │          3.17ns │ -0.01% +0.01% │            │             │             │            │
│ demo1    │     1.00 │     15_698.93ns │ -0.06% +0.06% │     3.90kw │      29.39w │      29.39w │      0.06% │
│ demo2    │     1.00 │      4_206.51ns │ -0.08% +0.09% │     1.20kw │       2.77w │       2.77w │      0.02% │
│ list_sum │     1.00 │     47_120.71ns │ -0.07% +0.07% │    10.20kw │       6.70w │       6.70w │      0.19% │
│ vs_easy  │     1.00 │  1_683_707.82ns │ -0.12% +0.12% │   762.00kw │     363.24w │     363.24w │      6.69% │
│ vs_hard  │     1.00 │ 21_396_434.78ns │ -0.52% +0.57% │ 2_968.84kw │ 116_682.97w │ 116_682.97w │     85.02% │
│ binom    │     1.00 │  3_728_951.08ns │ -0.04% +0.04% │    54.02kw │   2_266.03w │   2_266.03w │     14.82% │
│ sha_fast │     1.00 │ 25_167_666.67ns │ -0.08% +0.07% │ 5_772.21kw │  63_808.20w │  63_808.20w │    100.00% │
└──────────┴──────────┴─────────────────┴───────────────┴────────────┴─────────────┴─────────────┴────────────┘
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/ocaml-noopt'
make -C malfunction all
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction'
Malfunction with no optimisations
Estimated testing time 1m30s (9 benchmarks x 10s). Change using '-quota'.
┌──────────┬──────────┬─────────────────┬───────────────┬─────────────┬─────────────┬─────────────┬────────────┐
│ Name     │ Time R^2 │        Time/Run │          95ci │     mWd/Run │    mjWd/Run │    Prom/Run │ Percentage │
├──────────┼──────────┼─────────────────┼───────────────┼─────────────┼─────────────┼─────────────┼────────────┤
│ demo0    │     1.00 │          3.17ns │               │             │             │             │            │
│ demo1    │     1.00 │     16_083.36ns │ -0.06% +0.06% │      3.90kw │      20.58w │      20.58w │      0.04% │
│ demo2    │     1.00 │      4_326.36ns │ -0.07% +0.08% │      1.20kw │       1.38w │       1.38w │            │
│ list_sum │     1.00 │     52_215.75ns │ -0.04% +0.04% │     10.71kw │       7.00w │       7.00w │      0.12% │
│ vs_easy  │     1.00 │  4_926_079.04ns │ -0.09% +0.12% │  2_336.01kw │   1_527.96w │   1_527.96w │     11.12% │
│ vs_hard  │     1.00 │ 44_301_208.47ns │ -0.07% +0.07% │ 23_386.09kw │ 248_992.37w │ 248_992.37w │    100.00% │
│ binom    │     1.00 │  3_790_843.84ns │ -0.08% +0.08% │     74.10kw │   3_135.42w │   3_135.42w │      8.56% │
│ color    │     1.00 │ 24_923_917.45ns │ -0.29% +0.37% │ 12_351.11kw │ 317_134.40w │ 317_134.40w │     56.26% │
│ sha_fast │     1.00 │ 30_324_795.85ns │ -0.14% +0.15% │  6_767.36kw │  66_037.84w │  66_037.84w │     68.45% │
└──────────┴──────────┴─────────────────┴───────────────┴─────────────┴─────────────┴─────────────┴────────────┘
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction'
make -C malfunction-o2 all
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-o2'
Malfunction with optimisations -O2
Estimated testing time 1m30s (9 benchmarks x 10s). Change using '-quota'.
┌──────────┬──────────┬─────────────────┬───────────────┬────────────┬─────────────┬─────────────┬────────────┐
│ Name     │ Time R^2 │        Time/Run │          95ci │    mWd/Run │    mjWd/Run │    Prom/Run │ Percentage │
├──────────┼──────────┼─────────────────┼───────────────┼────────────┼─────────────┼─────────────┼────────────┤
│ demo0    │     1.00 │          3.17ns │ -0.01% +0.01% │            │             │             │            │
│ demo1    │     1.00 │     15_598.49ns │ -0.07% +0.07% │     3.90kw │      20.56w │      20.56w │      0.06% │
│ demo2    │     1.00 │      3_785.58ns │ -0.10% +0.10% │     1.20kw │       1.36w │       1.36w │      0.01% │
│ list_sum │     1.00 │     49_960.08ns │ -0.23% +0.35% │    10.20kw │       6.38w │       6.38w │      0.18% │
│ vs_easy  │     1.00 │  1_801_819.19ns │ -0.14% +0.13% │   905.00kw │     471.32w │     471.32w │      6.63% │
│ vs_hard  │     1.00 │ 26_570_385.91ns │ -0.17% +0.17% │ 9_136.15kw │ 212_780.49w │ 212_780.49w │     97.79% │
│ binom    │     1.00 │  3_732_085.28ns │ -0.05% +0.05% │    54.02kw │   2_257.60w │   2_257.60w │     13.74% │
│ color    │     1.00 │ 16_237_004.11ns │ -1.42% +1.35% │ 3_595.03kw │ 288_631.07w │ 288_631.07w │     59.76% │
│ sha_fast │     1.00 │ 27_171_878.42ns │ -1.19% +1.62% │ 5_868.03kw │  62_356.53w │  62_356.53w │    100.00% │
└──────────┴──────────┴─────────────────┴───────────────┴────────────┴─────────────┴─────────────┴────────────┘
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-o2'
make -C malfunction-verified all
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-verified'
Bootstrapped Malfunction with no optimisations
Estimated testing time 1m30s (9 benchmarks x 10s). Change using '-quota'.
┌──────────┬──────────┬─────────────────┬───────────────┬─────────────┬─────────────┬─────────────┬────────────┐
│ Name     │ Time R^2 │        Time/Run │          95ci │     mWd/Run │    mjWd/Run │    Prom/Run │ Percentage │
├──────────┼──────────┼─────────────────┼───────────────┼─────────────┼─────────────┼─────────────┼────────────┤
│ demo0    │     1.00 │          3.17ns │ -0.01% +0.01% │             │             │             │            │
│ demo1    │     1.00 │     16_095.25ns │ -0.05% +0.05% │      3.90kw │      20.55w │      20.55w │      0.04% │
│ demo2    │     1.00 │      4_335.33ns │ -0.09% +0.09% │      1.20kw │       1.38w │       1.38w │            │
│ list_sum │     1.00 │     52_271.64ns │ -0.07% +0.08% │     10.71kw │       7.00w │       7.00w │      0.12% │
│ vs_easy  │     1.00 │  4_917_007.85ns │ -0.08% +0.08% │  2_336.01kw │   1_526.59w │   1_526.59w │     11.11% │
│ vs_hard  │     1.00 │ 44_255_963.95ns │ -0.06% +0.08% │ 23_386.09kw │ 248_888.43w │ 248_888.43w │    100.00% │
│ binom    │     1.00 │  3_791_651.98ns │ -0.07% +0.08% │     74.10kw │   3_136.12w │   3_136.12w │      8.57% │
│ color    │     1.00 │ 24_935_127.27ns │ -0.15% +0.14% │ 12_351.11kw │ 317_262.52w │ 317_262.52w │     56.34% │
│ sha_fast │     1.00 │ 30_305_223.81ns │ -0.15% +0.13% │  6_767.36kw │  65_847.98w │  65_847.98w │     68.48% │
└──────────┴──────────┴─────────────────┴───────────────┴─────────────┴─────────────┴─────────────┴────────────┘
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-verified'
make -C malfunction-verified-o2 all
make[1]: Entering directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-verified-o2'
Bootstrapped Malfunction optimisations -O2
Estimated testing time 1m30s (9 benchmarks x 10s). Change using '-quota'.
┌──────────┬──────────┬─────────────────┬───────────────┬────────────┬─────────────┬─────────────┬────────────┐
│ Name     │ Time R^2 │        Time/Run │          95ci │    mWd/Run │    mjWd/Run │    Prom/Run │ Percentage │
├──────────┼──────────┼─────────────────┼───────────────┼────────────┼─────────────┼─────────────┼────────────┤
│ demo0    │     1.00 │          3.15ns │ -0.27% +0.24% │            │             │             │            │
│ demo1    │     1.00 │     15_703.84ns │ -0.14% +0.16% │     3.90kw │      20.58w │      20.58w │      0.06% │
│ demo2    │     1.00 │      3_775.89ns │ -0.28% +0.29% │     1.20kw │       1.37w │       1.37w │      0.01% │
│ list_sum │     1.00 │     49_965.10ns │ -0.06% +0.05% │    10.20kw │       6.38w │       6.38w │      0.19% │
│ vs_easy  │     1.00 │  1_804_627.52ns │ -0.17% +0.17% │   905.00kw │     471.65w │     471.65w │      6.79% │
│ vs_hard  │     1.00 │ 26_566_991.43ns │ -0.12% +0.13% │ 9_136.15kw │ 213_025.61w │ 213_025.61w │    100.00% │
│ binom    │     1.00 │  3_732_430.50ns │ -0.04% +0.04% │    54.02kw │   2_271.09w │   2_271.09w │     14.05% │
│ sha_fast │     1.00 │ 26_362_365.66ns │ -0.11% +0.13% │ 5_868.02kw │  62_400.31w │  62_400.31w │     99.23% │
└──────────┴──────────┴─────────────────┴───────────────┴────────────┴─────────────┴─────────────┴────────────┘
make[1]: Leaving directory '/home/yannick/research/coq-malfunction/benchmarks/malfunction-verified-o2'
