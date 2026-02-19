open Core
open Core_bench

let () =
  Command_unix.run (Bench.make_command [
    Bench.Test.create ~name:"demo0"
      (fun () -> ignore(Demo0.demo0 ()));
    Bench.Test.create ~name:"demo1"
      (fun () -> ignore(Demo1.demo1 ()));
    Bench.Test.create ~name:"demo2"
      (fun () -> ignore (Demo2.demo2 ()));
    Bench.Test.create ~name:"list_sum"
      (fun () -> ignore (List_sum.list_sum ()));
    Bench.Test.create ~name:"vs_easy"
      (fun () -> ignore ( Vs_easy.vs_easy ()));
    Bench.Test.create ~name:"vs_hard"
      (fun () -> ignore ( Vs_hard.vs_hard ()));
    Bench.Test.create ~name:"binom"
      (fun () -> ignore (Binom.binom ()));
    Bench.Test.create ~name:"color"
      (fun () -> ignore (Color.color ()));
    Bench.Test.create ~name:"sha_fast"
      (fun () -> ignore ( Sha_fast.sha_fast ()));
])
