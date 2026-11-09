#!/usr/bin/env python3
"""Write src/runtime.rs: the rust-hybrid kernel (hybrid_top_preamble of
theories/backends/RustHybridRemaps.v), a Program with __int/__num, and the
runtime methods of theories/backends/HybridRuntimeGen.v."""
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
TH = HERE.parent.parent / "theories" / "backends"
remaps = (TH / "RustHybridRemaps.v").read_text()
# "..." ++ rt <%% HybridRuntime.f %%> ++ "..." is one string with the printed name of f.
remaps = re.sub(r'" \+\+ rt <%% (\w+)\.(\w+) %%> \+\+ "', r'Peregrine_backends_\1_\2', remaps)
gmp = (TH / "RustGMPRemaps.v").read_text()
gen = (TH / "HybridRuntimeGen.v").read_text()

def strings(src: str, name: str, extra=None, end="]."):
    i = src.index("Definition " + name)
    body = src[src.index("[", i) + 1: src.index(end, i)]
    out = []
    for m in re.finditer(r'"((?:[^"]|"")*)"|(\b[a-z_]+_macro\b)', body):
        if m.group(2):
            out.append(extra[m.group(2)])
        else:
            out.append(m.group(1).replace('""', '"'))
    return out

def rocq_string(src: str, name: str) -> str:
    i = src.index("Definition " + name)
    m = re.search(r'"((?:[^"]|"")*)"', src[i:])
    return m.group(1).replace('""', '"')

macros = {"cmp_elim_macro": rocq_string(gmp, "cmp_elim_macro")}
top = strings(remaps, "hybrid_top_preamble", macros)
prog = [l for l in strings(remaps, "hybrid_program_preamble", end="] hybrid_runtime_lines")
        if l.startswith("fn __int(") or l.startswith("fn __num(")]
methods = strings(gen, "hybrid_runtime_lines")
lines = top + ["", "struct Program { __alloc: bumpalo::Bump }", "impl<'a> Program {",
               "fn alloc<T>(&'a self, t: T) -> &'a T { self.__alloc.alloc(t) }",
               "fn closure<TArg, TRet>(&'a self, F: impl Fn(TArg) -> TRet + 'a) -> &'a dyn Fn(TArg) -> TRet { self.__alloc.alloc(F) }"]
lines += prog + methods + ["}"]
(HERE / "src" / "runtime.rs").write_text("\n".join(lines) + "\n")
print(f"assemble: {len(top)} kernel lines, {len(methods)} runtime lines")
