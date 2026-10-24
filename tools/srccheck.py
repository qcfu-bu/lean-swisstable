"""Source-text check of the 16 iterator declarations that the parity checker ignores.

Usage: python3 -I tools/srccheck.py tools/inventory.json OAMap

`docs/ARCHITECTURE.md` §8 and §9.1: the elaborated types of `iter`, `keysIter`, `valuesIter`,
`HashSet.iter` and of their 12 lemmas mention the iterator state, which is necessarily different
from Std's (Std's exposes its bucket `AssocList`s), so `test/OAMapTest/ParityRun.lean` ignores
them. This script checks instead that each one is declared in the file corresponding to Std's
(`Std/Data/HashMap/Iterator.lean` -> `OAMap/HashMap/Iterator.lean`, ...), in namespace
`OAMap.HashMap`/`OAMap.HashSet`, with Std's statement text (the `src_statement` of
`inventory.json`, whitespace-normalised) and Std's attributes (`inherit_doc Raw.…` excepted:
there is no `Raw`, so the docstring is literal).

Exit status 1 when a declaration is missing or differs.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import split  # noqa: E402

ITER_DECLS = [
    'Std.HashMap.iter', 'Std.HashMap.keysIter', 'Std.HashMap.valuesIter', 'Std.HashSet.iter',
    'Std.HashMap.toList_iter', 'Std.HashMap.toListRev_iter', 'Std.HashMap.toArray_iter',
    'Std.HashMap.toList_keysIter', 'Std.HashMap.toListRev_keysIter',
    'Std.HashMap.toArray_keysIter', 'Std.HashMap.toList_valuesIter_eq_toList_map_snd',
    'Std.HashMap.toListRev_valuesIter', 'Std.HashMap.toArray_valuesIter',
    'Std.HashSet.toList_iter', 'Std.HashSet.toListRev_iter', 'Std.HashSet.toArray_iter',
]


def norm(s):
    return ' '.join(s.split())


def find_decl(text, ns, short):
    """(attrs, statement) of `short` declared in namespace `ns` of a source file, or None."""
    lines = text.split('\n')
    stack = []
    for i, l in enumerate(lines):
        m = re.match(r'namespace\s+(\S+)', l)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r'end\s+(\S+)', l)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
            continue
        cur = '.'.join(stack)
        m = re.match(r'(?:(@\[[^\]]*\])\s*)?(?:public\s+|protected\s+)*(?:def|theorem|abbrev)\s+'
                     + re.escape(short) + r'(?=[\s:]|$)', l)
        if not m or cur != ns:
            continue
        attrs = m.group(1)
        if attrs is None and i > 0 and lines[i - 1].startswith('@['):
            attrs = lines[i - 1]
        # the declaration text: this line and its indented continuation
        j = i + 1
        while j < len(lines) and (not lines[j] or lines[j][0].isspace()):
            j += 1
        decl = '\n'.join(lines[i:j])
        decl = decl[re.search(r'(?:def|theorem|abbrev)\s+', decl).end():]
        stmt, _ = split.split_text(decl)
        stmt = re.split(r'\swhere\b', stmt)[0]
        al = [a.strip() for a in (attrs or '@[]')[2:-1].split(',') if a.strip()]
        return al, stmt
    return None


def main():
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(2)
    inv = json.load(open(sys.argv[1]))
    root = os.path.dirname(os.path.abspath(sys.argv[2].rstrip('/')))
    decls = {d['name']: d for d in inv['decls']}
    bad = 0
    for name in ITER_DECLS:
        d = decls[name]
        rel = d['file'].replace('Std/Data/', 'OAMap/')
        path = os.path.join(root, rel)
        fam, short = name.rsplit('.', 1)
        ns = fam.replace('Std.', 'OAMap.')
        found = find_decl(open(path).read(), ns, short) if os.path.exists(path) else None
        if found is None:
            print(f'srccheck: MISSING {name} (expected in {rel}, namespace {ns})')
            bad += 1
            continue
        attrs, stmt = found
        want_attrs = sorted(a for a in d.get('attrs', []) if not a.startswith('inherit_doc'))
        have_attrs = sorted(a for a in attrs if not a.startswith('inherit_doc'))
        want = norm(d['src_statement'])
        have = norm(short + ' ' + stmt[len(short):]) if stmt.startswith(short) else norm(stmt)
        if want != have:
            print(f'srccheck: STATEMENT {name}\n  Std:  {want}\n  ours: {have}')
            bad += 1
        if want_attrs != have_attrs:
            print(f'srccheck: ATTRS {name}: Std {want_attrs}, ours {have_attrs}')
            bad += 1
    if bad:
        print(f'srccheck: {bad} problem(s) in {len(ITER_DECLS)} iterator declarations')
        sys.exit(1)
    print(f'srccheck: ok, {len(ITER_DECLS)} iterator declarations match Std\'s source text')


if __name__ == '__main__':
    main()
