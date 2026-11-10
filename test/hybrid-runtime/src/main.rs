// Boundary-value test of the rust-hybrid runtime against GMP: every pair of the
// edge values below (0, ±1, ±2^62, the ends of the small range, i64::MIN/MAX, two
// large values, a few small ones), for every operation of the remap table, with
// overflow checks and debug assertions on.  src/runtime.rs is assembled by
// assemble.py from RustHybridRemaps.v and HybridRuntimeGen.v.
#![allow(dead_code, non_snake_case, non_camel_case_types, unused_variables, unused_macros, unused_imports)]
include!("runtime.rs");

use std::cmp::Ordering;

fn big(n: Num) -> rug::Integer { __big(n) }

fn main() {
    let p = Program { __alloc: bumpalo::Bump::new() };
    let two62 = rug::Integer::from(1i64 << 62);
    let vals: Vec<rug::Integer> = vec![
        rug::Integer::from(0), rug::Integer::from(1), rug::Integer::from(-1),
        two62.clone(), rug::Integer::from(-&two62),
        rug::Integer::from(&two62 - 1), rug::Integer::from(-&two62) - 1,
        rug::Integer::from(i64::MIN), rug::Integer::from(i64::MAX),
        rug::Integer::from(10).pow(30u32), rug::Integer::from(-rug::Integer::from(7).pow(25u32)),
        rug::Integer::from(2), rug::Integer::from(-3), rug::Integer::from(7),
    ];
    let nums: Vec<Num> = vals.iter().map(|v| p.__num(v.clone())).collect();
    let checks = std::cell::Cell::new(0u64);
    let fails = std::cell::Cell::new(0u64);
    let check = |what: &str, got: rug::Integer, want: rug::Integer| {
        checks.set(checks.get() + 1);
        if got != want { fails.set(fails.get() + 1); println!("FAIL {what}: got {got}, want {want}"); }
    };
    // canonical: a value in the small range is small
    let canon = |n: Num| -> bool { let v = big(n); let small = v >= -rug::Integer::from(1i64 << 62) && v < rug::Integer::from(1i64 << 62); small == n.small().is_some() };
    let mut noncanon = 0u64;
    for (i, a) in nums.iter().enumerate() {
        let x = &vals[i];
        check(&format!("neg {x}"), big(p.Peregrine_backends_HybridRuntime_neg(*a)), rug::Integer::from(-x));
        check(&format!("abs {x}"), big(p.Peregrine_backends_HybridRuntime_abs(*a)), rug::Integer::from(x.abs_ref()));
        check(&format!("succ {x}"), big(p.Peregrine_backends_HybridRuntime_succ(*a)), rug::Integer::from(x + 1));
        check(&format!("pred {x}"), big(p.Peregrine_backends_HybridRuntime_pred(*a)), rug::Integer::from(x - 1));
        for r in [p.Peregrine_backends_HybridRuntime_neg(*a), p.Peregrine_backends_HybridRuntime_abs(*a), p.Peregrine_backends_HybridRuntime_succ(*a)] { if !canon(r) { noncanon += 1; } }
        for (j, b) in nums.iter().enumerate() {
            let y = &vals[j];
            let ops: Vec<(&str, Num, rug::Integer)> = vec![
                ("add", p.Peregrine_backends_HybridRuntime_add(*a, *b), rug::Integer::from(x + y)),
                ("sub", p.Peregrine_backends_HybridRuntime_sub(*a, *b), rug::Integer::from(x - y)),
                ("mul", p.Peregrine_backends_HybridRuntime_mul(*a, *b), rug::Integer::from(x * y)),
                ("divf", p.Peregrine_backends_HybridRuntime_divf(*a, *b), if *y == 0 { rug::Integer::from(0) } else { rug::Integer::from(x.div_floor(y)) }),
                ("modf", p.Peregrine_backends_HybridRuntime_modf(*a, *b), if *y == 0 { x.clone() } else { rug::Integer::from(x.rem_floor(y)) }),
                ("min", p.Peregrine_backends_HybridRuntime_min(*a, *b), if x <= y { x.clone() } else { y.clone() }),
                ("max", p.Peregrine_backends_HybridRuntime_max(*a, *b), if y <= x { x.clone() } else { y.clone() }),
                ("sub0", p.Peregrine_backends_HybridRuntime_sub0(*a, *b), { let d = rug::Integer::from(x - y); if d < 0 { rug::Integer::from(0) } else { d } }),
                ("sub1", p.Peregrine_backends_HybridRuntime_sub1(*a, *b), { let d = rug::Integer::from(x - y); if d < 1 { rug::Integer::from(1) } else { d } }),
            ];
            for (name, got, want) in ops {
                if !canon(got) { noncanon += 1; println!("NONCANON {name} {x} {y}"); }
                check(&format!("{name} {x} {y}"), big(got), want);
            }
            let leb = p.Peregrine_backends_HybridRuntime_leb(*a, *b);
            let ltb = p.Peregrine_backends_HybridRuntime_ltb(*a, *b);
            let cmp = p.Peregrine_backends_HybridPrims_num_compare(*a, *b);
            let eqb = p.Peregrine_backends_HybridPrims_num_eqb(*a, *b);
            checks.set(checks.get() + 4);
            if leb != (x <= y) || ltb != (x < y) || cmp != x.cmp(y) || eqb != (x == y) {
                fails.set(fails.get() + 1); println!("FAIL cmp {x} {y}");
            }
        }
        // pow with small exponents
        for e in [0i64, 1, 2, 3, 5, 31, 63, 64] {
            let r = p.Peregrine_backends_HybridRuntime_pow(*a, Num::S(e));
            if !canon(r) { noncanon += 1; }
            check(&format!("pow {x} {e}"), big(r), rug::Integer::from(x.pow(e as u32)));
        }
    }
    // pow with an exponent beyond u32 for the bases 0 and 1
    let huge = p.__num(rug::Integer::from(u32::MAX) + 1);
    check("pow 0 2^32", big(p.Peregrine_backends_HybridRuntime_pow(Num::S(0), huge)), rug::Integer::from(0));
    check("pow 1 2^32", big(p.Peregrine_backends_HybridRuntime_pow(Num::S(1), huge)), rug::Integer::from(1));
    let _ = Ordering::Equal;
    println!("{} checks, {} failures, {noncanon} non-canonical results", checks.get(), fails.get());
    if fails.get() > 0 || noncanon > 0 { std::process::exit(1); }
}
