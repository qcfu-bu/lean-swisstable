#!/usr/bin/env python3
"""Check the C that Lean generates for the public API at Nat and String keys.

`bench/Bench/CCheck.lean` defines one monomorphic function per operation (`getDNat`, `insertStr`,
...). Build it with `lake build Bench.CCheck`; this script reads `.lake/build/ir/Bench/CCheck.c`
and the library's own C (`.lake/build/ir/SwissTable/**/*.c`), follows every direct call from each of
those functions to the functions defined there, and checks:

1. closures: no `lean_apply_*` anywhere: `hash`, `==`, the probes and the traversals are
   specialised at the key type;
2. bug A: no array or byte array is shared (`lean_inc`) in the same straight-line block before an
   in-place update of it (`lean_array_uset`, `lean_byte_array_uset`, ...), which would make the
   update copy the whole array;
3. lookups (getD, get!, contains, getKeyD, HashSet.contains): no allocation on the machine-word
   path. Allocation calls are allowed only in the Nat-indexed probes for tables of more than 2^31
   slots (`findN`, `findLoopN`, which return an `Option`) and in `panic`;
4. updates (insert, insertIfNew, getThenInsertIfNew?, containsThenInsert, erase, modify, alter,
   HashSet.insert): the result reuses the argument's table cell when that is unshared (Lean's
   `reuseFailAlloc` pattern: the table is allocated only when the argument is shared, or by a
   rebuild), and the arrays are updated in place (2). A table cell allocated by the Nat-indexed
   versions (tables of more than 2^31 slots) is printed as a note.

    lake build Bench.CCheck && python3 -I tools/check_c.py [-v] [CCheck.c]
"""
import glob, os, re, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IR = os.path.join(HERE, ".lake/build/ir")
PREFIX = "lp_swisstable_Bench_CCheck_"
LOOKUPS = ["getDNat", "getDStr", "getBangNat", "containsNat", "containsStr", "getKeyDStr",
           "setContainsNat", "setContainsStr"]
UPDATES = ["insertNat", "insertStr", "insertIfNewNat", "getThenInsertIfNewStr",
           "containsThenInsertNat", "eraseNat", "eraseStr", "modifyNat", "alterStr",
           "setInsertStr"]
TRAVERSALS = ["foldNat"]
DEF = re.compile(r"^(?:LEAN_EXPORT |static |LEAN_EXPORT static )?[\w\s\*]*?\b(\w+)\(([^;]*)\)\s*\{$")
CALL = re.compile(r"\b([A-Za-z_]\w*)\(")
SET = re.compile(r"\b(lean_array_uset|lean_array_fset|lean_array_set|lean_byte_array_uset|"
                 r"lean_byte_array_fset|lean_byte_array_set)\((\w+)\s*,")
ALLOC = re.compile(r"\b(lean_alloc_\w+|lean_box_uint64|lean_box_usize|lean_box_uint32|"
                   r"lean_box_float\w*|lean_mk_string\w*|lean_mk_array|lean_mk_empty_\w+|"
                   r"lean_copy_\w+|lean_nat_big_\w+|lean_usize_to_nat|lean_uint64_to_nat|"
                   r"lean_cnstr_\w+)\(")
# The Nat-indexed probes (tables of more than 2^31 slots) return an `Option`; `panic` builds its
# message. Only these may allocate on a lookup.
COLD = re.compile(r"_find(Loop)?N___|panic")
# The functions that build a fresh table (the allocation, the rebuild and its loops), and the
# allocation of a table cell: 6 object fields, a USize and a UInt64.
FRESH = re.compile(r"_(rebuild|emptyTable|reserveTable|emptyImpl|moveLoop|moveLoopN)___")
TABLE_ALLOC = "lean_alloc_ctor(0, 6, sizeof(size_t)*1 + 8)"
# The Nat-indexed versions of the operations (`containsThenInsertN`, `eraseN`, ...), which run
# only on tables of more than 2^31 slots. A table cell they allocate is reported, not failed.
NAT_PATH = re.compile(r"[a-z]N___at___")


HEADS = {}


def parse(path):
    """Function name -> body lines, by brace depth (Lean's C nests blocks for join points)."""
    funcs, cur, body, depth = {}, None, [], 0
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            if cur is None:
                m = DEF.match(line)
                if m:
                    cur, body, depth = m.group(1), [], 1
                    HEADS.setdefault(cur, line)
            else:
                depth += line.count("{") - line.count("}")
                if depth <= 0:
                    funcs.setdefault(cur, body)
                    cur = None
                else:
                    body.append(line)
    return funcs


def reach(funcs, root):
    seen, stack = set(), [root]
    while stack:
        f = stack.pop()
        if f in seen or f not in funcs:
            continue
        seen.add(f)
        for c in CALL.findall("\n".join(funcs[f])):
            if c in funcs and c not in seen:
                stack.append(c)
    return seen


def bug_a(lines):
    """`lean_inc(X)` earlier in the same straight-line block as an update of the array `X`."""
    out = []
    for n, line in enumerate(lines):
        m = SET.search(line)
        if not m:
            continue
        arr = m.group(2)
        for prev in reversed(lines[:n]):
            s = prev.strip()
            if s in ("{", "}") or s.endswith(":") or s.startswith(("if ", "else", "goto ")):
                break
            if re.search(r"\blean_dec(_ref)?\(" + re.escape(arr) + r"\)", s):
                break
            if re.search(r"\blean_inc(_ref)?(_n)?\(" + re.escape(arr) + r"\b", s):
                out.append(line.strip())
                break
    return out


def main():
    verbose = "-v" in sys.argv
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    path = args[0] if args else os.path.join(IR, "Bench/CCheck.c")
    if not os.path.exists(path):
        print(f"{path} is not built: run `lake build Bench.CCheck` first")
        return 1
    funcs = parse(path)
    for p in glob.glob(os.path.join(IR, "SwissTable/**/*.c"), recursive=True) + \
            [os.path.join(IR, "SwissTable.c")]:
        if os.path.exists(p):
            for k, v in parse(p).items():
                funcs.setdefault(k, v)
    failures = 0
    notes = set()
    for kind, names in (("lookup", LOOKUPS), ("update", UPDATES), ("traversal", TRAVERSALS)):
        for name in names:
            root = PREFIX + name
            if root not in funcs:
                print(f"FAIL {name}: {root} not found in {path}")
                failures += 1
                continue
            fs = reach(funcs, root)
            problems = []
            for f in sorted(fs):
                body = funcs[f]
                text = "\n".join(body)
                k = len(re.findall(r"\blean_apply_\w+\(", text))
                if k:
                    problems.append(f"{k} closure call(s) in {f}")
                for l in bug_a(body):
                    problems.append(f"bug A in {f}: {l}")
                if kind == "lookup" and not COLD.search(f):
                    for a in sorted(set(ALLOC.findall(text))):
                        problems.append(f"allocation {a} in {f}")
            if kind == "update":
                # The table is updated in place: some reached function makes its unshared table
                # argument the result's cell (`x = t;` before the `lean_ctor_set`s of the reuse
                # join point), and every other table (6 fields, a USize and a UInt64) is allocated
                # only when the argument is shared (`reuseFailAlloc`) or by a rebuild.
                reusers = []
                for f in fs:
                    if NAT_PATH.search(f):
                        continue
                    arg = re.search(r"\(lean_object\* (\w+)", HEADS.get(f, ""))
                    if arg and re.search(r"\b\w+ = " + re.escape(arg.group(1)) + ";",
                                         "\n".join(funcs[f])):
                        reusers.append(f)
                if not reusers:
                    problems.append("no reached function reuses its table argument's cell")
                for f in sorted(fs):
                    if FRESH.search(f):
                        continue
                    for l in funcs[f]:
                        l = l.strip()
                        if TABLE_ALLOC in l and not l.startswith("v_reuseFailAlloc"):
                            msg = f"table cell allocated outside a reuse fallback in {f}"
                            if NAT_PATH.search(f):
                                notes.add(msg + " (Nat path, tables of more than 2^31 slots)")
                            else:
                                problems.append(msg)
            status = "ok  " if not problems else "FAIL"
            failures += bool(problems)
            print(f"{status} {kind:9} {name:22} {len(fs):3} functions reached")
            for p in problems:
                print(f"       {p}")
            if verbose:
                for f in sorted(fs):
                    print(f"       reached: {f}")
    for n in sorted(notes):
        print(f"note: {n}")
    print("check_c: ok" if not failures else f"check_c: {failures} operations FAILED")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
