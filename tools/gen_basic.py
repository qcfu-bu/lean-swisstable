"""Generate OAMap/HashMap/Basic.lean and OAMap/HashMap/AdditionalOperations.lean from Std's text.

ARCHITECTURE.md section 4.3: the files are Std's `Std/Data/HashMap/Basic.lean` and
`Std/Data/HashMap/AdditionalOperations.lean` with the namespace renamed, the imports replaced and
the bodies rewritten onto `OAMap.Core.Table`; binders, attributes, declaration order and the
anonymous instances are Std's text, so elaborated signatures and auto-generated instance names
match. `@[inherit_doc DHashMap.X]` (there is no DHashMap to inherit from) becomes a literal
docstring with the text of the `doc` field of `inventory.json`.

Every edit is an exact substitution that must match exactly once, so a change in Std's text makes
the script fail instead of silently producing something else.

Usage: python3 -I gen_basic.py STD_DATA_DIR INVENTORY_JSON OUT_DIR
  STD_DATA_DIR   ~/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Std/Data
  OUT_DIR        the package's OAMap/HashMap directory
"""
import json
import re
import sys


def sub1(text, old, new):
    n = text.count(old)
    if n != 1:
        raise SystemExit(f'expected exactly one occurrence, found {n}:\n{old}')
    return text.replace(old, new)


def docstring(doc):
    doc = doc if doc.endswith('\n') else doc + '\n'
    return '/--\n' + doc + '-/\n'


def inline_docs(text, docs, family):
    """`@[a, inherit_doc X, b] def name` -> `/-- doc of family.name -/ @[a, b] def name`."""
    pat = re.compile(r'@\[([^\]]*)\](\s*)(def|structure)\s+([^\s(\[{:]+)')
    out, pos = [], 0
    for m in pat.finditer(text):
        attrs = [a.strip() for a in m.group(1).split(',')]
        inh = [a for a in attrs if re.fullmatch(r'inherit_doc\s+\S+', a)]
        if not inh:
            continue
        doc = docs.get(family + '.' + m.group(4))
        if doc is None:
            raise SystemExit(f'no inventory doc for {family}.{m.group(4)}')
        rest = [a for a in attrs if a not in inh]
        out.append(text[pos:m.start(0)])
        out.append(docstring(doc))
        if rest:
            out.append('@[' + ', '.join(rest) + ']' + m.group(2))
        pos = m.start(3)
    out.append(text[pos:])
    return ''.join(out)


BASIC_HEADER_STD = '''module

prelude
public import Std.Data.DHashMap.Basic
public import Init.Data.List.Impl

@[expose] public section
'''

BASIC_HEADER_OURS = '''module

public import OAMap.Core.Bulk

@[expose] public section
'''

BASIC_MODDOC_STD = '''/-!
# Hash maps

This module develops the type `Std.HashMap` of hash maps. Dependent hash maps are defined in
`Std.Data.DHashMap`.

The operations `map` and `filterMap` on `Std.HashMap` are defined in the module
`Std.Data.HashMap.AdditionalOperations`.

Lemmas about the operations on `Std.HashMap` are available in the
module `Std.Data.HashMap.Lemmas`.

See the module `Std.Data.HashMap.Raw` for a variant of this type which is safe to use in
nested inductive types.
-/
'''

BASIC_MODDOC_OURS = '''/-!
# Hash maps

This module develops the type `OAMap.HashMap` of hash maps, a drop-in replacement for
`Std.HashMap`: the same operations, with Std's names, binders, attributes and semantics.

The operations `map` and `filterMap` on `OAMap.HashMap` are defined in the module
`OAMap.HashMap.AdditionalOperations`.

Lemmas about the operations on `OAMap.HashMap` are available in the
module `OAMap.HashMap.Lemmas`.

Implementation notes (`docs/ARCHITECTURE.md` §4.3). This file is Std's
`Std/Data/HashMap/Basic.lean`, generated from Std's text so that binders, attributes,
declaration order and auto-generated instance names are Std's; only the bodies differ. A map is a
one-field wrapper of the sealed core table `OAMap.Core.Table` (§3), and every operation is a
one-line call to a core, `OAMap.Core.Derived` or `OAMap.Core.Bulk` function. Docstrings that
Std inherits from `DHashMap` are copied as literal text. The file also defines
`OAMap.Model.toListModel`, the entry list that `Equiv` and all lemmas are stated against.
`Array.groupByKey` and `List.groupByKey` stay Std's (they return `Std.HashMap`).

Owner: API, Wave 1.
-/
'''

HASHMAP_DOC_STD_START = '/--\nHash maps.\n\nThis is a simple separate-chaining hash table.'

HASHMAP_DOC_OURS = '''/--
Hash maps.

This is a drop-in replacement for `Std.HashMap`, with the same operations, lemmas and semantics.
The data of the hash map is a hash table (`OAMap.Core.Table`) whose layout is an implementation
detail: no lemma depends on it, and every lemma is stated in terms of the operations, exactly as
for `Std.HashMap`.

Users should make sure that the hash map is used linearly to avoid expensive copies.

The hash map uses `==` (provided by the `BEq` typeclass) to compare keys and `hash` (provided by
the `Hashable` typeclass) to hash them. To ensure that the operations behave as expected, `==`
should be an equivalence relation and `a == b` should imply `hash a = hash b` (see also the
`EquivBEq` and `LawfulHashable` typeclasses). Both of these conditions are automatic if the BEq
instance is lawful, i.e., if `a == b` implies `a = b`.

These hash maps contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types.
-/
'''

# (Std text, our text): bodies and the few signature-free edits of section 4.3.
BASIC_EDITS = [
    ('namespace Std\n', 'namespace OAMap\n'),
    ('''  /-- Internal implementation detail of the hash map -/
  inner : DHashMap α (fun _ => β)

namespace HashMap
''', '''  /-- Internal implementation detail of the hash map -/
  inner : OAMap.Core.Table α β

namespace HashMap

/-- The entries of a map in iteration order: the model that `Equiv` and all lemmas are stated
against (ARCHITECTURE.md §2.3). The core's `Table.toListModel` below it stays sealed. -/
def _root_.OAMap.Model.toListModel (m : HashMap α β) : List ((_ : α) × β) :=
  m.inner.toListModel
'''),
    ('  ⟨DHashMap.emptyWithCapacity capacity⟩\n', '  ⟨Core.Table.emptyWithCapacity capacity⟩\n'),
    ('''  /-- Internal implementation detail of the hash map -/
  inner : m₁.1.Equiv m₂.1
''', '''  /-- Internal implementation detail of the hash map -/
  inner : (Model.toListModel m₁).Perm (Model.toListModel m₂)
'''),
    ('  let ⟨previous, r⟩ := DHashMap.Const.getThenInsertIfNew? m.inner a b\n',
     '  let ⟨previous, r⟩ := m.inner.getThenInsertIfNew? a b\n'),
    ('  DHashMap.Const.get? m.inner a\n', '  m.inner.get? a\n'),
    ('  mem m a := a ∈ m.inner\n', '  mem m a := m.inner.contains a = true\n'),
    ('  inferInstanceAs (Decidable (a ∈ m.inner))\n',
     '  inferInstanceAs (Decidable (m.inner.contains a = true))\n'),
    ('  DHashMap.Const.get m.inner a h\n', '  m.inner.get a h\n'),
    ('  DHashMap.Const.getD m.inner a fallback\n', '  m.inner.getD a fallback\n'),
    ('  DHashMap.Const.get! m.inner a\n', '  m.inner.get! a\n'),
    ('  DHashMap.getKey? m.inner a\n', '  m.inner.getKey? a\n'),
    ('  DHashMap.getKey m.inner a h\n', '  m.inner.getKey a h\n'),
    ('  DHashMap.getKeyD m.inner a fallback\n', '  m.inner.getKeyD a fallback\n'),
    ('  DHashMap.getKey! m.inner a\n', '  m.inner.getKey! a\n'),
    ('  ⟨DHashMap.Const.ofList l⟩\n', '  ⟨Core.Table.ofList l⟩\n'),
    ('  ⟨DHashMap.Const.unitOfList l⟩\n', '  ⟨Core.Table.unitOfList l⟩\n'),
    ('  ⟨DHashMap.Const.ofArray a⟩\n', '  ⟨Core.Table.ofArray a⟩\n'),
    ('  DHashMap.Const.toList m.inner\n', '  m.inner.toList\n'),
    ('  ⟨DHashMap.Const.modify m.inner a f⟩\n', '  ⟨m.inner.modify a f⟩\n'),
    ('  ⟨DHashMap.Const.alter m.inner a f⟩\n', '  ⟨m.inner.alter a f⟩\n'),
    ('  ⟨DHashMap.Const.insertMany m.inner l⟩\n', '  ⟨(m.inner.insertMany l).1⟩\n'),
    ('  ⟨DHashMap.Const.insertManyIfNewUnit m.inner l⟩\n',
     '  ⟨(m.inner.insertManyIfNewUnit l).1⟩\n'),
    ('  DHashMap.Const.toArray m.inner\n', '  m.inner.toArray\n'),
    ('  ⟨DHashMap.union m₁.inner m₂.inner⟩\n', '  ⟨m₁.inner.union m₂.inner⟩\n'),
    ('  ⟨DHashMap.inter m₁.inner m₂.inner⟩\n', '  ⟨m₁.inner.inter m₂.inner⟩\n'),
    ('  DHashMap.Const.beq m₁.inner m₂.inner\n', '  m₁.inner.beq m₂.inner\n'),
    ('  ⟨DHashMap.diff m₁.inner m₂.inner⟩\n', '  ⟨m₁.inner.diff m₂.inner⟩\n'),
    ('  ⟨DHashMap.Const.unitOfArray l⟩\n', '  ⟨Core.Table.unitOfArray l⟩\n'),
    ('  DHashMap.Internal.numBuckets m.inner\n', '  m.inner.numBuckets\n'),
    ('("Std.HashMap.ofList " ++ reprArg m.toList)', '("OAMap.HashMap.ofList " ++ reprArg m.toList)'),
]

ADDOPS_HEADER_STD = '''module

prelude
public import Std.Data.DHashMap.AdditionalOperations
public import Std.Data.HashMap.Basic
public import Std.Data.HashMap.Raw

@[expose] public section

/-!
# Additional hash map operations

This module defines the operations `map` and `filterMap` on `Std.HashMap`.
Lemmas about these operations are found in `Std.Data.HashMap.Lemmas`.
-/
'''

ADDOPS_HEADER_OURS = '''module

public import OAMap.HashMap.Basic

@[expose] public section

/-!
# Additional hash map operations

This module defines the operations `map` and `filterMap` on `OAMap.HashMap`.
Lemmas about these operations are found in `OAMap.HashMap.Lemmas`.

Implementation notes: Std's `Std/Data/HashMap/AdditionalOperations.lean`, generated from Std's
text (`docs/ARCHITECTURE.md` §4.3) without the `Raw` part (deferred); the bodies call
`OAMap.Core.Table.filterMap` and `OAMap.Core.Table.map`.

Owner: API, Wave 1.
-/
'''

ADDOPS_RAW = '''namespace Raw

theorem WF.filterMap [BEq α] [Hashable α] {m : Raw α β} {f : α → β → Option γ} (h : m.WF) :
    (m.filterMap f).WF :=
  ⟨DHashMap.Raw.WF.filterMap h.out⟩

theorem WF.map [BEq α] [Hashable α] {m : Raw α β} {f : α → β → γ} (h : m.WF) : (m.map f).WF :=
  ⟨DHashMap.Raw.WF.map h.out⟩

end Raw

'''


def main():
    std_dir, inv_path, out_dir = sys.argv[1:4]
    docs = {x['name']: x['doc'] for x in json.load(open(inv_path))['decls'] if x.get('doc')}

    # ---- Basic.lean
    t = open(std_dir + '/HashMap/Basic.lean').read()
    t = sub1(t, BASIC_HEADER_STD, BASIC_HEADER_OURS)
    t = sub1(t, BASIC_MODDOC_STD, BASIC_MODDOC_OURS)
    # the type's docstring describes our map (ARCHITECTURE.md Q9)
    i = t.index(HASHMAP_DOC_STD_START)
    j = t.index('-/\n', i) + 3
    t = t[:i] + HASHMAP_DOC_OURS + t[j:]
    for old, new in BASIC_EDITS:
        t = sub1(t, old, new)
    # drop Array.groupByKey / List.groupByKey (they stay Std's, ARCHITECTURE.md Q8)
    k = t.index('end Std.HashMap\n')
    t = t[:k] + 'end OAMap.HashMap\n'
    t = inline_docs(t, docs, 'Std.HashMap')
    if 'DHashMap' in t.replace('DHashMap`', '').replace('`DHashMap', ''):
        bad = [l for l in t.split('\n') if 'DHashMap' in l]
        raise SystemExit('DHashMap left in Basic.lean:\n' + '\n'.join(bad))
    open(out_dir + '/Basic.lean', 'w').write(t)

    # ---- AdditionalOperations.lean
    a = open(std_dir + '/HashMap/AdditionalOperations.lean').read()
    a = sub1(a, ADDOPS_HEADER_STD, ADDOPS_HEADER_OURS)
    a = sub1(a, 'namespace Std\n', 'namespace OAMap\n')
    a = sub1(a, 'end Std\n', 'end OAMap\n')
    a = sub1(a, ADDOPS_RAW, '')
    a = inline_docs(a, docs, 'Std.HashMap')
    if 'DHashMap' in a:
        raise SystemExit('DHashMap left in AdditionalOperations.lean')
    open(out_dir + '/AdditionalOperations.lean', 'w').write(a)


if __name__ == '__main__':
    main()
