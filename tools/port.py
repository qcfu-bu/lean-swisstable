"""Port Std's HashMap and HashSet lemma files onto OAMap (`docs/ARCHITECTURE.md` §6.2).

Two modes.

    python3 -I tools/port.py lemmas [--std DIR] [--force | --check]

writes, from Std's sources (default: the toolchain's `src/lean/Std/Data`), the chain data in
`tools/data/` and the hand proofs of `tools/data/hand.json`,

  * `OAMap/HashMap/Lemmas/{Basic,GetKey,...,FilterMap}.lean`: Std's `HashMap/Lemmas.lean` cut by
    `tools/split.py`, with Std's statements, attributes, comments and non-theorem commands kept
    as text and every proof replaced by a generated one;
  * `OAMap/HashMap/Lemmas.lean`: the aggregator, with Std's final
    `attribute [simp] contains_eq_false_iff_not_mem`;
  * `OAMap/HashSet/{Basic,Lemmas,DecidableEquiv}.lean`: Std's text with the namespace renamed and
    the edits of ARCHITECTURE.md §7.

    python3 -I port.py hmchain.json dhm.json raw0.json hm.json NAMES.json OUT.lean

is the original design-study script (run from `tools/data/`; it reproduces the study's
`auto_all.lean` exactly): the first candidate of the rules below without the Wave-1 extensions.

Proofs (`proofs.md` §6). A theorem with an entry in `tools/data/hand.json` gets that hand-written
proof (the text after the statement, verbatim); the module docstring of its file lists it. For
every other theorem the script lists *candidate* proofs, built from Std's own proof chain
(HashMap -> DHashMap -> Raw₀):

  0. hand-written proofs from `OVERRIDES` (the induction principles and their users, whose Std
     proofs thread the unbundled `WF` invariant);
  1. `ext DHashMap.X`, `ext DHashMap.Const.X` and `apply ext; apply DHashMap.Const.X` become the
     same text with `Core.Table.X`, the Table-level twins in `OAMap.Core.Derived`/`Bulk` (§6.3);
     a bare `DHashMap.Const.X` with a twin becomes `Core.Table.X`;
  2. a HashMap proof that does not mention `DHashMap` is copied (siblings, `rfl`, `by simp`);
  3. a DHashMap proof that does not mention `Raw₀` is copied with DHashMap names renamed to
     HashMap names;
  4. a Raw₀ proof `[revert h;] simp_to_model [qs] [; intro x; apply T x] [; wf_trivial]` becomes
     `simp_to_model [qs'] [at *] using T'` (queries renamed, `at *` when the statement has
     hypotheses and `T` does not use `h.1`, Raw₀ siblings renamed and their `_ h` arguments
     dropped). The same is done through `h.1.foo`, `⟨h.1.foo …⟩`, `⟨.foo …⟩` and
     `⟨DHashMap.X …⟩` (the `Equiv` constructions), which lead to `DHashMap.Equiv.foo` or
     `DHashMap.X` and then to a Raw₀ lemma;
  5. otherwise the renamed Raw₀ text, with the query lists of its `simp_to_model` calls renamed;
  6. variants of the `simp_to_model` candidates with and without `at *`.

The generated files are reproduced exactly: `--check` regenerates them in memory and fails (exit
status 1, with a diff) when a file on disk differs, and `tools/ci.sh` runs it. A proof is
therefore fixed by hand in `tools/data/hand.json`, never in the generated file. A file that
differs from the generated text is not overwritten unless `--force` is given, so that an edit
made in the file by mistake is not lost before it is moved to `hand.json`.

`tools/portcheck.py` compiles the generated files and records in `tools/data/review.json`, for
each theorem whose first candidate fails, the first candidate that compiles, or `"sorry"`.
A theorem marked `"sorry"` is emitted as `sorry` under a `-- REVIEW` comment that carries the
error, the candidates tried and Std's proof chain. Statements are never changed.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DATA = os.path.join(HERE, 'data')
sys.path.insert(0, HERE)

import split  # noqa: E402  (tools/split.py)

QUERY = {
    'Const.get?': ['getElem?'], 'Const.get': ['getElem'], 'Const.get!': ['getElem!'],
    'Const.getD': ['getD'], 'contains': ['contains', 'mem'], 'Const.toList': ['toList'],
    'Const.insertMany': ['insertMany'], 'Const.insertManyIfNewUnit': ['insertManyIfNewUnit'],
    'Const.alter': ['alter'], 'Const.modify': ['modify'], 'Const.beq': ['beq'],
    'Const.toArray': ['toArray'],
}


# --------------------------------------------------------------------------------------------
# The design-study rules (unchanged, used by both modes)

def proof_split(b):
    depth = 0
    i = 0
    while i < len(b) - 1:
        c = b[i]
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        elif c == ':' and b[i + 1] == '=' and depth == 0:
            return b[:i], b[i + 2:].strip()
        i += 1
    return b, ''


def build_rename(rows):
    """DHashMap / Raw0 lemma name -> HashMap lemma name, from Std's delegation lines."""
    dren, rren = {}, {}
    for n, r in rows.items():
        short = n.replace('Std.HashMap.', '')
        if 'dhm' in r:
            d = r['dhm'].replace('Std.', '').replace('DHashMap.', '')
            dren.setdefault(d, short)
            dren.setdefault(d.replace('Const.', ''), short)
        if 'raw' in r:
            k = r['raw'].replace('Std.DHashMap.Internal.Raw₀.', '')
            rren.setdefault(k, short)
            rren.setdefault(k.replace('Const.', ''), short)
    return dren, rren


def rename_names(text, ren):
    def sub(m):
        w = m.group(0)
        return ren.get(w, w)
    return re.sub(r'(?<![\w.])(?:Const\.)?[A-Za-z_][\w?!\']*', sub, text)


def drop_raw_args(text):
    # `foo _ h` / `foo m h` / `(by wf_trivial)` arguments of Raw0 siblings
    text = re.sub(r'\s+_\s+h\b(?!\.)', '', text)
    text = re.sub(r'\s+m\s+h\b(?!\.)', '', text)
    text = re.sub(r'\s+_\s+h₁\s+h₂\b', '', text)
    text = re.sub(r'\(by wf_trivial\)', '_', text)
    return text


def has_hyps(stmt):
    # explicit binders before the colon that are hypotheses (Prop-ish), not data
    depth, i, top = 0, 0, None
    for i, c in enumerate(stmt):
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        elif c == ':' and depth == 0 and not stmt[i:].startswith(':='):
            top = i
            break
    binders = stmt[:top] if top else stmt
    for m in re.finditer(r'\((\w+)\s*:\s*([^()]*(?:\([^()]*\)[^()]*)*)\)', binders):
        ty = m.group(2)
        if re.search(r'∈|∉|==|=|~m|Pairwise|↔|¬|→', ty):
            return True
    return False


def port_simp(raw_proof, stmt, rren, extended=False):
    """`[revert h;] simp_to_model [qs] [using T]` (and its `intro`/`apply` form) as one line.

    With `extended`, also accepts trailing `wf_trivial` lines and several reverted hypotheses
    (`revert a b; simp_to_model [qs]; intro a b; apply T a b`)."""
    body = raw_proof[2:].strip() if raw_proof.startswith('by') else raw_proof
    lines = [l.strip() for l in body.split('\n') if l.strip()]
    reverted = False
    if lines and lines[0].startswith('revert'):
        lines = lines[1:]
        reverted = True
    if extended:
        while lines and re.fullmatch(r'(?:all_goals |any_goals )?wf_trivial', lines[-1]):
            lines = lines[:-1]
    # `simp_to_model [qs]; intro x; apply T x` (after a revert) is `simp_to_model [qs] at * using T`
    if (reverted and len(lines) == 3 and lines[1].startswith('intro ')
            and lines[2].startswith('apply ')):
        xs = lines[1].split()[1:]
        t = lines[2][len('apply '):]
        if extended:
            for x in reversed(xs):
                t = re.sub(r'\s+' + re.escape(x) + r'$', '', t)
        else:
            t = re.sub(r'\s+' + re.escape(xs[0]) + r'$', '', t)
        lines = [lines[0] + ' using ' + t]
    text = ' '.join(lines)
    m = re.match(r'simp_to_model(?:\s*\[([^\]]*)\])?\s*(?:using\s+(.*))?$', text)
    if not m:
        return None
    qs = [q.strip() for q in (m.group(1) or '').split(',') if q.strip()]
    out = []
    for q in qs:
        for q2 in QUERY.get(q, [q]):
            if q2 not in out:
                out.append(q2)
    using = m.group(2)
    uses_hyp = bool(using and re.search(r'\bh\.1\b', using))
    at = ' at *' if ((reverted or has_hyps(stmt)) and not uses_hyp) else ''
    s = 'simp_to_model' + (' [' + ', '.join(out) + ']' if out else '') + at
    if using:
        using = drop_raw_args(rename_names(using, rren))
        s += ' using ' + using
    return s


def raw_lookup(raw, name):
    for pre in ['Std.DHashMap.Internal.Raw₀.', 'Std.DHashMap.Internal.']:
        if pre + name in raw:
            return raw[pre + name]
    return None


# --------------------------------------------------------------------------------------------
# The chain data and the candidate proofs

def rename_queries(text):
    """Rename the query lists of every `simp_to_model [...]` in a multi-line Raw₀ proof."""
    def sub(m):
        out = []
        for q in [q.strip() for q in m.group(1).split(',') if q.strip()]:
            for q2 in QUERY.get(q, [q]):
                if q2 not in out:
                    out.append(q2)
        return 'simp_to_model [' + ', '.join(out) + ']'
    return re.sub(r'simp_to_model\s*\[([^\]]*)\]', sub, text)


def fix_tactics(text):
    """Std's RawLemmas tactics that OAMap does not provide, replaced by their expansion: `empty`
    is `{ intros; simp_all [List.isEmpty_iff] }` (OAMap.HashMap.Tactic does not define it)."""
    return re.sub(r'(?<![\w.])empty\s*;?[ \t]*$', '{ intros; simp_all [List.isEmpty_iff] }', text,
                  flags=re.M)


def render_proof(p):
    """The text ` := <proof>` after a statement: `:= by` with the tactic block at column 2, or a
    term at column 2 with its continuation lines at column 4."""
    lines = p.strip('\n').strip().split('\n')

    def dedent(ls):
        ind = min((len(l) - len(l.lstrip()) for l in ls if l.strip()), default=0)
        return [l[ind:] if l.strip() else '' for l in ls]
    if lines[0] == 'by' and len(lines) > 1:
        return ' := by\n' + '\n'.join(('  ' + l) if l else '' for l in dedent(lines[1:]))
    if lines[0].startswith('by ') and len(lines) == 1:
        return ' := by\n  ' + lines[0][3:].strip()
    if lines[0].startswith('by '):
        return ' :=\n  ' + indent_proof(p)
    if len(lines) == 1:
        return ' :=\n  ' + lines[0]
    return (' :=\n  ' + lines[0] + '\n' +
            '\n'.join(('    ' + l) if l else '' for l in dedent(lines[1:])))


def indent_proof(p):
    """A proof text, re-indented to start at column 2 after `:=`."""
    lines = p.strip('\n').split('\n')
    if len(lines) == 1:
        return lines[0].strip()
    # keep the relative indentation of the continuation lines, with at least 2 columns
    rest = lines[1:]
    ind = min((len(l) - len(l.lstrip()) for l in rest if l.strip()), default=2)
    return '\n'.join([lines[0].strip()] + [('  ' + l[ind:]) if l.strip() else '' for l in rest])


# Hand-written candidates (tried first). Their Std proofs thread the unbundled `WF` invariant
# through `insertMany_ind`; ours is bundled (ARCHITECTURE.md §6.3, proofs.md §6).
OVERRIDES = {
    'insertMany_ind': [
        '(m.inner.insertMany l).2 (fun t => motive ⟨t⟩) (fun h => insert _ _ _ h) init'],
    'insertManyIfNewUnit_ind': [
        '(m.inner.insertManyIfNewUnit l).2 (fun t => motive ⟨t⟩) (fun h => insert _ _ h) init'],
    'mem_insertMany_of_mem': [
        'fun h => insertMany_ind (motive := fun m => k ∈ m) m h fun _ _ _ h => mem_insert.2 (Or.inr h)'],
    'mem_insertManyIfNewUnit_of_mem': [
        'fun h => insertManyIfNewUnit_ind (motive := fun m => k ∈ m) m l h\n'
        '    fun _ _ h => mem_insertIfNew.2 (Or.inr h)'],
    'size_le_size_insertMany': [
        'insertMany_ind (motive := fun m\' => m.size ≤ m\'.size) m (Nat.le_refl _)\n'
        '    fun _ _ _ h => Nat.le_trans h size_le_size_insert'],
    'isEmpty_of_isEmpty_insertMany': [
        'insertMany_ind (motive := fun m\' => m\'.isEmpty → m.isEmpty) m id\n'
        '    fun _ _ _ _ h => by simp only [isEmpty_insert, Bool.false_eq_true] at h'],
    'size_le_size_insertManyIfNewUnit': [
        'insertManyIfNewUnit_ind (motive := fun m\' => m.size ≤ m\'.size) m l (Nat.le_refl _)\n'
        '    fun _ _ h => Nat.le_trans h size_le_size_insertIfNew'],
    'isEmpty_of_isEmpty_insertManyIfNewUnit': [
        'insertManyIfNewUnit_ind (motive := fun m\' => m\'.isEmpty → m.isEmpty) m l id\n'
        '    fun _ _ _ h => by simp only [isEmpty_insertIfNew, Bool.false_eq_true] at h'],
    # `beq` through Model.beq_of_perm/perm_of_beq/beq_congr (there is no bridge to Const.beqModel)
    'Equiv.beq': ['Model.beq_of_perm h.1'],
    'equiv_of_beq': ['⟨Model.perm_of_beq h⟩'],
    'Equiv.beq_congr': ['Model.beq_congr w₁.1 w₂.1'],
    # Std's DHashMap text `simp [contains_map]` trips the unused-simp-argument linter here
    'mem_of_mem_map': ['by\n  simp'],
    'insertMany_list_equiv_foldl': [
        'by\n  rw [Model.insertMany_list_eq_foldl]'],
    'insertManyIfNewUnit_list_equiv_foldl': [
        'by\n  rw [Model.insertManyIfNewUnit_list_eq_foldl]'],
}


def lean_names(path, kind='theorem'):
    p = os.path.join(ROOT, path)
    return set(re.findall(r'^' + kind + r'\s+(\S+)', open(p).read(), re.M)) if os.path.exists(p) else set()


def table_twins():
    """Names of the Table-level lemmas in OAMap.Core.Derived/Bulk and the core contract."""
    names = lean_names('OAMap/Core/Derived.lean') | lean_names('OAMap/Core/Bulk.lean')
    names |= {'erase_emptyWithCapacity', 'toListModel_emptyWithCapacity',
              'lookup_emptyWithCapacity'}
    return names


# Names of Std's internal (`WF.lean`, `Raw`) lemmas used in RawLemmas proofs, and the
# `OAMap.Model` lemma that states the same thing for a `HashMap` (explicit map argument).
INTERNAL = {
    'Raw.isEmpty_eq_isEmpty': 'Model.isEmpty_eq_isEmpty',
    'Raw.size_eq_length': 'Model.size_eq_length',
    'Raw.keys_eq_keys_toListModel': 'Model.keys_eq_keys_toListModel',
    'Raw.Const.toList_eq_toListModel_map': 'Model.toList_eq_toListModel_map',
    'Raw.values_eq_values_toListModel': 'Model.values_eq_values_toListModel',
    'toListModel_buckets_emptyWithCapacity': 'Model.toListModel_emptyWithCapacity',
    'toListModel_insert': 'Model.toListModel_insert',
    'toListModel_insertIfNew': 'Model.toListModel_insertIfNew',
    'toListModel_erase': 'Model.toListModel_erase',
    'toListModel_filter': 'Model.toListModel_filter',
    'toListModel_map': 'Model.toListModel_map',
    'toListModel_filterMap': 'Model.toListModel_filterMap',
    'Const.toListModel_alter': 'Model.toListModel_alter',
    'Const.toListModel_modify': 'Model.toListModel_modify',
    'toListModel_union': 'Model.toListModel_union',
    'toListModel_inter': 'Model.toListModel_inter',
    'toListModel_diff': 'Model.toListModel_diff',
}


def rename_internal(text):
    text = re.sub(r'\(Raw\.WF\.out h\)\.distinct', '(Model.distinctKeys m)', text)
    text = re.sub(r'(?<![\w.])toListModel (\w+)\.(?:val|1)\.buckets', r'(Model.toListModel \1)', text)
    return re.sub(r'(?<![\w.])(?:Raw\.Const\.|Raw\.|Const\.)?[A-Za-z_][\w?!\']*',
                  lambda mm: INTERNAL.get(mm.group(0), mm.group(0)), text)


def binders(stmt):
    """(name, type) of the explicit binders of a statement, before its top-level colon."""
    depth, top = 0, len(stmt)
    for i, c in enumerate(stmt):
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        elif c == ':' and depth == 0 and not stmt[i:].startswith(':='):
            top = i
            break
    out = []
    for m in re.finditer(r'\(([^\s():]+(?:\s+[^\s():]+)*)\s*:\s*((?:[^()]|\((?:[^()]|\([^()]*\))*\))*)\)',
                         stmt[:top]):
        for name in m.group(1).split():
            out.append((name, m.group(2).strip()))
    return out


def is_wf(ty):
    return re.search(r'\.WF$', ty) is not None


def is_hyp(name, ty):
    if name in ('m', 'm₁', 'm₂', 'm₃', 'm₄', 'k', 'v', 'f', 'g', 'p', 'l', 'a', 'c', 'init',
                'fallback', 'motive', 'insert'):
        return False
    return re.search(r'∈|∉|==|=|~m|Pairwise|↔|¬|\.isSome|\.contains|\.WF', ty) is not None


def rename_hyps(text, raw_stmt, stmt):
    """Rename the hypotheses of a Raw₀ proof to the HashMap statement's names, by position;
    the `WF` hypotheses of the raw statement are dropped from `simp`/`rw` lists."""
    rb = [(n, t) for n, t in binders(raw_stmt) if is_hyp(n, t)]
    hb = [n for n, t in binders(stmt) if is_hyp(n, t)]
    wf = [n for n, t in rb if is_wf(t)]
    rh = [n for n, t in rb if not is_wf(t)]
    ren = dict(zip(rh, hb)) if len(rh) == len(hb) else {}
    for w in wf:
        # drop the WF hypothesis from lemma lists (`[a, h]`, `[h, a]`, `[h]`), before renaming
        text = re.sub(r',\s*' + re.escape(w) + r'(?=\s*[\],])', '', text)
        text = re.sub(r'\[\s*' + re.escape(w) + r'\s*,\s*', '[', text)
        text = re.sub(r'\[\s*' + re.escape(w) + r'\s*\]', '[]', text)
    if ren:
        text = re.sub(r"(?<![\w.'])[^\W\d][\w'₀-₉]*",
                      lambda mm: ren.get(mm.group(0), mm.group(0)), text)
    return text


def drop_noop_lines(text):
    """`simp only [Bool.not_eq_true]` before `simp_to_model`: our tactic does it already."""
    return re.sub(r'^(\s*)simp only \[Bool\.not_eq_true\]\n(?=\s*simp_to_model)', '', text,
                  flags=re.M)


class Porter:
    def __init__(self, data=DATA):
        def load(n):
            return json.load(open(os.path.join(data, n)))
        self.rows = {r['name']: r for r in load('hmchain.json')}
        self.dhm = {x['full']: x for x in load('dhm.json')}
        self.dhm.update({('Std.' + k if not k.startswith('Std.') else k): v
                         for k, v in list(self.dhm.items())})
        self.raw = {x['full']: x for x in load('raw0.json')}
        self.hm = {x['full']: x for x in load('hm.json')}
        self.dren, self.rren = build_rename(self.rows)
        self.twins = table_twins()
        self.model = lean_names('OAMap/HashMap/Model.lean')

    # the design-study rule set, for one theorem (the body of the original main loop)
    def legacy(self, n):
        r, x = self.rows[n], self.hm[n]
        stmt, _ = proof_split(x['body'])
        hp, dp, rp = r['hm_proof'], r.get('dhm_proof', ''), r.get('raw_proof', '')
        mh = re.match(r'^h\.1\.(\S+)$', hp.strip())
        if mh:
            d = self.dhm.get('Std.DHashMap.Equiv.' + mh.group(1))
            if d:
                dp = proof_split(d['body'])[1]
                mr = re.search(r'Raw₀\.((?:Const\.)?[\w?!\']+)', dp)
                rr = raw_lookup(self.raw, mr.group(1)) if mr else None
                if rr:
                    rp = proof_split(rr['body'])[1]
        mr = re.search(r'@?Raw₀\.((?:Const\.)?[\w?!\']+)', dp) if dp.startswith('by') else None
        if mr and 'Raw₀' in dp:
            rr = raw_lookup(self.raw, mr.group(1))
            if rr:
                rp = proof_split(rr['body'])[1]
                dp = ''
        if 'DHashMap' not in hp and not mh:
            return 'copy-HashMap', hp
        if dp and 'Raw₀' not in dp:
            return 'copy-DHashMap-renamed', rename_names(dp, self.dren)
        if rp:
            p = port_simp(rp, stmt, self.rren)
            if p:
                return ('simp_to_model (via Equiv/DHashMap hop)' if (mh or mr)
                        else 'simp_to_model'), 'by ' + p
            return 'renamed Raw0 text (check)', drop_raw_args(rename_names(rp, self.rren))
        return 'review', '-- REVIEW (no Raw0 proof found)\n  sorry'

    def dhm_decl(self, name):
        """(statement, proof) of a DHashMap lemma given as `DHashMap.X` or `Std.DHashMap.X`."""
        n = name if name.startswith('Std.') else 'Std.' + name
        d = self.dhm.get(n)
        return split.split_text(d['body'].rstrip()) if d else (None, None)

    def raw_decl(self, text):
        """(name, statement, proof) of the first Raw₀ lemma named in a DHashMap proof."""
        mr = re.search(r'Raw₀\.((?:Const\.)?(?:Equiv\.)?[\w?!\']+)', text or '')
        if not mr:
            return None, None, None
        rr = raw_lookup(self.raw, mr.group(1))
        if not rr:
            return mr.group(1), None, None
        st, pf = split.split_text(rr['body'].rstrip())
        return mr.group(1), st, pf

    def chain(self, n):
        """Std's proof chain of a HashMap theorem: [(label, statement, proof)] below HashMap."""
        r = self.rows.get(n)
        if not r:
            return []
        hp = r['hm_proof']
        if r.get('dhm'):
            dname = r['dhm']
        else:
            m = (re.search(r'DHashMap\.((?:Const\.)?(?:Equiv\.)?[\w?!\']+)', hp) or
                 re.search(r'h\.1\.([\w?!\']+)', hp) or re.search(r'⟨\.([\w?!\']+)', hp))
            if not m:
                return []
            dname = ('Std.DHashMap.' + m.group(1) if 'DHashMap' in m.group(0)
                     else 'Std.DHashMap.Equiv.' + m.group(1))
        dst, dpf = self.dhm_decl(dname)
        if dpf is None:
            return []
        out = [(dname, dst, dpf)]
        rn, rst, rpf = self.raw_decl(dpf)
        if rpf is not None:
            out.append(('Std.DHashMap.Internal.Raw₀.' + rn, rst, rpf))
        return out

    def port_raw(self, raw_stmt, prf, header):
        """Candidates from a Raw₀ proof: the one-line form, then the renamed text."""
        out = []
        prf2 = drop_noop_lines(prf)
        p = port_simp(prf2, header, self.rren, extended=True)
        if p:
            out.append(('simp_to_model (chain)', 'by ' + rename_internal(p)))
        t = drop_raw_args(rename_names(prf2, self.rren))
        if raw_stmt:
            t = rename_hyps(t, raw_stmt, header)
        t = fix_tactics(rename_queries(rename_internal(t)))
        out.append(('renamed Raw0 text (chain)', t))
        return out

    def candidates(self, n, header, std_proof):
        """Candidate proofs (kind, text) for the HashMap theorem `n` (full Std name)."""
        out = []

        def add(kind, p):
            if p and p.strip() and all(p.strip() != q.strip() for _, q in out):
                out.append((kind, p.strip()))

        short = n[len('Std.HashMap.'):]
        hp = (std_proof or '').strip()
        for p in OVERRIDES.get(short, []):
            add('override', p)
        # 1. Table-level twins
        m = re.fullmatch(r'ext \(?DHashMap\.(?:Const\.)?([\w?!\']+)\)?', hp)
        if m and m.group(1) in self.twins:
            add('ext-twin', f'ext Core.Table.{m.group(1)}')
        m = re.fullmatch(r'by\s+apply ext\s+apply DHashMap\.(?:Const\.)?([\w?!\']+)', hp)
        if m and m.group(1) in self.twins:
            add('ext-twin', f'by\n  apply ext\n  apply Core.Table.{m.group(1)}')
        # 2-5. the design-study rules
        if n in self.rows and n in self.hm:
            kind, p = self.legacy(n)
            if kind != 'review':
                add(kind, fix_tactics(p))
        elif 'DHashMap' not in hp:
            add('copy-HashMap', hp)
        # 4'-5'. the chain, with the fixed statement/proof split (`haveI` statements), the
        # Equiv constructions and the other hops into a Raw₀ lemma
        for (label, st, prf) in self.chain(n):
            if 'Raw₀' in label:
                for kind, p in self.port_raw(st, prf, header):
                    add(kind, p)
            elif 'Raw₀' not in prf:
                add('copy-DHashMap-renamed (chain)', fix_tactics(rename_names(prf, self.dren)))
                add('copy-DHashMap (names kept)', fix_tactics(prf))
        # Model and Table lemmas of the same name
        if short in self.model:
            for p in (f'Model.{short} m', f'Model.{short} _', f'Model.{short}'):
                add('Model twin', p)
        m = re.fullmatch(r'DHashMap\.(?:Const\.)?([\w?!\']+)', hp)
        if m and m.group(1) in self.twins:
            add('twin', f'Core.Table.{m.group(1)}')
        # 8. `ofList`/`unitOfList` lemmas from their `insertMany`/`insertManyIfNewUnit` sibling
        for (a, b, eq) in (('unitOfList', 'insertManyIfNewUnit_list', 'unitOfList_eq_insertManyIfNewUnit_empty'),
                           ('ofList', 'insertMany_list', 'ofList_eq_insertMany_empty')):
            if a in short and not short.startswith(a + '_eq'):
                sib = 'Std.HashMap.' + short.replace(a, b, 1)
                if sib in self.rows:
                    op = b.replace('_list', '')
                    for kind, p in self.candidates(sib, header, self.rows[sib]['hm_proof']):
                        if p.startswith('by simp_to_model') and '\n' not in p:
                            q = re.sub(r'\b' + op + r'\b', a, p, count=1)
                            add('from sibling ' + sib[12:], q)
                            add('from sibling ' + sib[12:],
                                q.replace('by simp_to_model', 'by\n  simp_to_model', 1)
                                .replace(' using ', '\n  apply ', 1) + ' <;> simp_all')
                    add('via ' + eq, f'by\n  rw [{eq}]\n  simp_all [{sib[12:]}]')
                break
        # 6. `at *` variants
        for kind, p in list(out):
            if p.startswith('by simp_to_model') and '\n' not in p:
                if ' at *' in p:
                    add(kind + ' (no at *)', p.replace(' at *', ''))
                else:
                    q = re.sub(r'^(by simp_to_model(?: \[[^\]]*\])?)', r'\1 at *', p)
                    add(kind + ' (at *)', q)
        return out


# --------------------------------------------------------------------------------------------
# Generation of the lemma files

GEN_NOTE = ('Generated by `tools/port.py lemmas` from Std v4.35.0 and `tools/data/hand.json`; edit '
            'those,\nnot this file (`tools/ci.sh` checks that regenerating reproduces it).')


def load_hand():
    """{full Std name: proof text after the statement} of `tools/data/hand.json`."""
    p = os.path.join(DATA, 'hand.json')
    return json.load(open(p))['proofs'] if os.path.exists(p) else {}


def name_list(names):
    """`a`, `b` and `c`."""
    q = [f'`{n}`' for n in names]
    return q[0] if len(q) == 1 else ', '.join(q[:-1]) + ' and ' + q[-1]


def wrap(par, width=100):
    import textwrap
    return textwrap.fill(par, width=width, break_long_words=False, break_on_hyphens=False)


# Notes appended to the hand-proof sentence of a file's module docstring.
HAND_NOTES = {
    'SetOps': ('The last two do have generated proofs, in Std\'s `revert` form; their hand proofs '
               'are the shorter `simp_to_model … at *` versions.'),
    'UnitOf': ('They go through `ofList_eq_insertMany_empty` or '
               '`unitOfList_eq_insertManyIfNewUnit_empty`.'),
    'FilterMap': ('`filterMap_equiv_filter` and `filterMap_equiv_map` go through the model, because '
                  'Std\'s proofs use Raw₀\'s map equalities `filterMap_eq_filter` and '
                  '`filterMap_eq_map`, which we do not have. `keys_filter` is Std\'s proof with the '
                  'map argument given explicitly. In Std\'s order the `LawfulBEq` lemmas '
                  '`getElem?_map`, `getElem_map`, `getElem!_map` and `getD_map` come before the '
                  'primed lemmas their DHashMap proofs cite, so the first two are proved from the '
                  'model and the other two from `getElem?_map`.'),
}


def proofs_paragraph(intro, hand_names, n_sorry, note=None, none_text='Every generated proof compiles.'):
    """The paragraph of a module docstring that says where the proofs come from."""
    par = intro
    if hand_names:
        par += (' Where no generated proof compiled, the proof was written by hand '
                f'(`tools/data/hand.json`): {name_list(hand_names)}.')
        if note:
            par += ' ' + note
    elif not n_sorry:
        par += ' ' + none_text
    if n_sorry:
        par += (' Proofs that do not compile yet are `sorry` under a `-- REVIEW` comment with '
                'Std\'s chain.')
    return wrap(par)


def load_review():
    p = os.path.join(DATA, 'review.json')
    return json.load(open(p)) if os.path.exists(p) else {}


def comment(text, prefix='  -- '):
    return '\n'.join((prefix + l).rstrip() for l in text.strip('\n').split('\n'))


def render_theorem(block, full, porter, review, choice_log, hand):
    header, std_proof = split.split_statement(block)
    if std_proof is None:
        return block.text                      # pattern-matching definition: Std's text
    cands = porter.candidates(full, header, std_proof)
    if full in hand:
        choice_log[full] = {'candidates': cands, 'choice': 'hand'}
        return header + hand[full]
    rv = review.get(full, {})
    choice = rv.get('choice', 0)
    choice_log[full] = {'candidates': cands, 'choice': choice}
    if choice != 'sorry' and isinstance(choice, int) and choice < len(cands):
        return header + render_proof(cands[choice][1])
    # REVIEW: no candidate compiles
    notes = ['REVIEW: no generated proof compiles.']
    if rv.get('error'):
        notes.append('error: ' + rv['error'])
    notes.append('Std (HashMap): ' + std_proof)
    for (label, _, prf) in porter.chain(full):
        notes.append(f'Std ({label.replace("Std.", "")}): ' + prf)
    errs = rv.get('errors', {})
    for i, (kind, p) in enumerate(cands):
        notes.append(f'tried {i} ({kind}): ' + p)
        if str(i) in errs and i > 0:
            notes.append(f'  error {i}: ' + errs[str(i)])
    return header + ' :=\n' + comment('\n'.join(notes)) + '\n  sorry'


def uses_ext(text):
    return re.search(r'(?<![\w.])ext(?![\w.?!\'])', text) is not None


def hashmap_lemma_files(std, porter, review, choice_log, hand):
    """{module path: text} of the nine Lemmas files and the aggregator."""
    src = open(os.path.join(std, 'HashMap', 'Lemmas.lean')).read()
    blocks = split.parse(src)
    ext_block = next(b for b in blocks if b.kind == 'private theorem' and b.name == 'ext')
    out = {}
    prev = None
    for (fname, lo, hi, title, owner) in split.HASHMAP_CUTS:
        top_vars, stack = split.walk_scopes(blocks, lo)
        body_blocks = split.blocks_in(blocks, lo, hi)
        # the scopes still open after the file's own blocks
        _, stack_after = split.walk_scopes(blocks, hi + 1)
        parts = []
        ns = []          # current namespace path below OAMap.HashMap
        hand_names = []
        n_sorry = 0
        for b in body_blocks:
            if b.kind == 'theorem':
                full = 'Std.HashMap.' + '.'.join(ns + [b.name])
                parts.append((b, render_theorem(b, full, porter, review, choice_log, hand)))
                if choice_log.get(full, {}).get('choice') == 'hand':
                    hand_names.append(full[len('Std.HashMap.'):])
                elif parts[-1][1].endswith('\n  sorry'):
                    n_sorry += 1
            else:
                if b.kind == 'namespace':
                    ns.append(b.name)
                elif b.kind == 'end' and ns and b.name == ns[-1]:
                    ns.pop()
                parts.append((b, b.text))
        body = split.join(parts)
        if fname == 'Basic':
            # Std's comment; Std's `attribute [simp]` command is in our aggregator
            body = replace_once(
                body, '-- The following lemma becomes a simp lemma at the bottom of the file.',
                '-- The following lemma becomes a simp lemma in `OAMap.HashMap.Lemmas`, after every '
                'lemma.', 'simp-later comment')
        if prev is None:
            imports = ('public import OAMap.HashMap.Tactic\n'
                       'public import OAMap.HashMap.AdditionalOperations\n'
                       'public import Std.Internal.ForIn.Basic\n'
                       'import Init.Data.List.Pairwise')
        else:
            imports = f'public import OAMap.HashMap.Lemmas.{prev}'
        pre = []
        for s in stack:
            if s.kind == 'namespace':
                pre.append('namespace ' + s.name.replace('Std.HashMap', 'OAMap.HashMap'))
                if s.name == 'Std.HashMap':
                    pre.append('open Std.Internal.List Std.Internal')
            else:
                pre.append(('section ' + s.name).strip())
            pre.extend(v.text for v in s.variables)
        need_ext = (uses_ext(body) and not any(b is ext_block for b in body_blocks))
        if need_ext:
            pre.append(ext_block.text)
        if not stack or stack[0].name != 'Std.HashMap':
            raise SystemExit(f'{fname}: unexpected scopes at line {lo}')
        if body_blocks and body_blocks[0].kind == 'namespace':
            pass
        # Basic opens the namespace itself? No: Std's `namespace Std.HashMap` is at line 32,
        # before every cut, so it is always in `stack`.
        post = []
        for s in reversed(stack_after):
            if s.kind == 'namespace':
                post.append('end ' + s.name.replace('Std.HashMap', 'OAMap.HashMap'))
            else:
                post.append(('end ' + s.name).strip())
        intro = (f'Std\'s `Std/Data/HashMap/Lemmas.lean`, lines {lo}-{hi}, with Std\'s statements, '
                 'attributes and commands; the proofs are generated from Std\'s proof chain '
                 '(`docs/ARCHITECTURE.md` §6.2).')
        par = proofs_paragraph(intro, hand_names, n_sorry, HAND_NOTES.get(fname))
        doc = (f'/-!\n# Hash map lemmas: {title}\n\n{par}\n\n{GEN_NOTE}\n\n'
               f'Owner: PORT (Wave 1), {owner} (Wave 2).\n-/')
        header = ('module\n\n' + imports + '\n\n@[expose] public section\n\n' + doc + '\n\n'
                  'set_option linter.missingDocs true\nset_option autoImplicit false\n\n'
                  'universe u v w w\'\n\n'
                  + '\n\n'.join(v.text for v in top_vars))
        text = header + '\n\n' + '\n\n'.join(pre) + '\n\n' + body + '\n\n' + '\n\n'.join(post) + '\n'
        out[f'OAMap/HashMap/Lemmas/{fname}.lean'] = text
        prev = fname
    # the aggregator, with Std's final attribute command
    last = next(b for b in blocks if b.kind == 'attribute')
    out['OAMap/HashMap/Lemmas.lean'] = (
        'module\n\npublic import OAMap.HashMap.Lemmas.FilterMap\n\n@[expose] public section\n\n'
        '/-!\n# Hash map lemmas\n\n'
        'This module contains lemmas about `OAMap.HashMap`. Most of the lemmas require\n'
        '`EquivBEq α` and `LawfulHashable α` for the key type `α`. The easiest way to obtain '
        'these instances\nis to provide an instance of `LawfulBEq α`.\n\n'
        'Aggregator of the nine `OAMap.HashMap.Lemmas.*` files, which are Std\'s\n'
        '`Std/Data/HashMap/Lemmas.lean` cut in Std\'s order, each importing the previous one. '
        'Std\'s last\ncommand, which makes `contains_eq_false_iff_not_mem` a simp lemma after '
        'every lemma has been\nproved, is here.\n\n'
        f'{GEN_NOTE}\n\nOwner: PORT (Wave 1).\n-/\n\n'
        'namespace OAMap.HashMap\n\n' + last.text + '\n\nend OAMap.HashMap\n')
    return out


# --------------------------------------------------------------------------------------------
# HashSet: Std's text, renamed (ARCHITECTURE.md §7)

HASHSET_BASIC_DOC = '''/-!
# Hash sets

This module develops the type `OAMap.HashSet` of hash sets, a drop-in replacement for
`Std.HashSet`.

Lemmas about the operations on `OAMap.HashSet` are available in the
module `OAMap.HashSet.Lemmas`.

Implementation notes (`docs/ARCHITECTURE.md` §7). This file is Std's `Std/Data/HashSet/Basic.lean`
with `namespace Std` renamed to `namespace OAMap`: a set wraps `OAMap.HashMap α Unit`, and every
operation is Std's one-line wrapper. Changed from Std: the type's docstring (Std's describes
separate chaining), the docstrings of `ofList` and `ofArray` (the first of several equal elements
is kept, as the lemmas `ofList_eq_insertMany_empty` and `insert = insertIfNew` say), and the `Repr`
prefix (`OAMap.HashSet.ofList`).

''' + GEN_NOTE + '''

Owner: SET, Wave 2.
-/'''

HASHSET_TYPE_DOC = '''/--
Hash sets.

This is a drop-in replacement for `Std.HashSet`, with the same operations, lemmas and semantics. A
hash set is a hash map with values of type `Unit` (`OAMap.HashMap α Unit`), whose layout is an
implementation detail: no lemma depends on it.

Users should make sure that the hash set is used linearly to avoid expensive copies.

The hash set uses `==` (provided by the `BEq` typeclass) to compare elements and `hash` (provided by
the `Hashable` typeclass) to hash them. To ensure that the operations behave as expected, `==`
should be an equivalence relation and `a == b` should imply `hash a = hash b` (see also the
`EquivBEq` and `LawfulHashable` typeclasses). Both of these conditions are automatic if the BEq
instance is lawful, i.e., if `a == b` implies `a = b`.

These hash sets contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types.
-/'''


def replace_once(text, old, new, what):
    if text.count(old) != 1:
        raise SystemExit(f'port.py: expected exactly one occurrence of {what!r}, '
                         f'found {text.count(old)}')
    return text.replace(old, new)


def hashset_basic(std):
    t = open(os.path.join(std, 'HashSet', 'Basic.lean')).read()
    t = replace_once(t, 'prelude\npublic import Std.Data.HashMap.Basic\n',
                     'public import OAMap.HashMap.Basic\n', 'imports')
    t = re.sub(r'/-!\n# Hash sets\n.*?-/', lambda _: HASHSET_BASIC_DOC, t, count=1, flags=re.S)
    t = re.sub(r'/--\nHash sets\.\n.*?-/', lambda _: HASHSET_TYPE_DOC, t, count=1, flags=re.S)
    t = replace_once(t, '\nnamespace Std\n', '\nnamespace OAMap\n', 'namespace Std')
    t = replace_once(t, '\nend Std\n', '\nend OAMap\n', 'end Std')
    t = replace_once(t, '"Std.HashSet.ofList "', '"OAMap.HashSet.ofList "', 'Repr prefix')
    # Std's docstrings say the last of several equal elements is kept; the lemmas
    # (`ofList_eq_insertMany_empty`, `insert` = `insertIfNew`) say the first (ARCHITECTURE.md §7)
    for what in ('list', 'array'):
        old = (f'Creates a hash set from a{"n" if what == "array" else ""} {what} of elements. '
               'Note that unlike repeatedly calling `insert`, if the\n'
               'collection contains multiple elements that are equal (with regard to `==`), then '
               'the last element\nin the collection will be present in the returned hash set.')
        new = (f'Creates a hash set from a{"n" if what == "array" else ""} {what} of elements. As '
               'with repeatedly calling `insert`, if the collection\ncontains multiple elements '
               'that are equal (with regard to `==`), then the first of them is the one\n'
               'present in the returned hash set.')
        t = replace_once(t, old, new, f'docstring of ofList/ofArray ({what})')
    return t


def hashset_lemmas(std, review, choice_log, hand):
    t = open(os.path.join(std, 'HashSet', 'Lemmas.lean')).read()
    t = replace_once(
        t, 'prelude\npublic import Std.Data.HashMap.Lemmas\npublic import Std.Data.HashSet.Basic\n',
        'public import OAMap.HashMap.Lemmas\npublic import OAMap.HashSet.Basic\n', 'imports')
    t = replace_once(t, "DHashMap.mem_of_mem_insertIfNew'", "Model.mem_of_mem_insertIfNew'",
                     'mem_of_mem_insertIfNew\'')
    t = replace_once(
        t, 'This module contains lemmas about `Std.Data.HashSet`.',
        'This module contains lemmas about `OAMap.HashSet`.', 'docstring')
    t = replace_once(t, '\nnamespace Std.HashSet\n', '\nnamespace OAMap.HashSet\n', 'namespace')
    t = replace_once(t, '\nend Std.HashSet', '\nend OAMap.HashSet', 'end')
    # per-theorem REVIEW marks
    blocks = split.parse(t)
    parts = []
    lines = t.split('\n')
    pos = 0
    ns = []
    out_lines = []
    hand_names = []
    n_sorry = 0
    for b in blocks:
        out_lines.extend(lines[pos:b.start - 1])
        if b.kind == 'namespace':
            ns.append(b.name)
        elif b.kind == 'end' and ns and b.name == ns[-1]:
            ns.pop()
        text = b.text
        if b.kind == 'theorem':
            full = '.'.join(['Std.HashSet'] + [x for x in ns if x != 'OAMap.HashSet'] + [b.name])
            header, prf = split.split_statement(b)
            rv = review.get(full, {})
            choice_log[full] = {'candidates': [('copy', prf)], 'choice': rv.get('choice', 0)}
            if prf is not None and full in hand:
                choice_log[full]['choice'] = 'hand'
                hand_names.append(full[len('Std.HashSet.'):])
                text = header + hand[full]
            elif prf is not None and rv.get('choice') == 'sorry':
                n_sorry += 1
                notes = ['REVIEW: Std\'s proof does not compile.']
                if rv.get('error'):
                    notes.append('error: ' + rv['error'])
                notes.append('Std: ' + prf)
                text = header + ' :=\n' + comment('\n'.join(notes)) + '\n  sorry'
        out_lines.extend(text.split('\n'))
        pos = b.start - 1 + len(b.lines)
    out_lines.extend(lines[pos:])
    t = '\n'.join(out_lines)
    intro = ('Std\'s `Std/Data/HashSet/Lemmas.lean` with the namespace renamed and '
             '`DHashMap.mem_of_mem_insertIfNew\'` replaced by `Model.mem_of_mem_insertIfNew\'` '
             '(`docs/ARCHITECTURE.md` §7).')
    par = proofs_paragraph(intro, hand_names, n_sorry,
                           none_text='All of Std\'s proofs compile unchanged.')
    return replace_once(
        t, 'is to provide an instance of `LawfulBEq α`.\n-/',
        'is to provide an instance of `LawfulBEq α`.\n\n' + par + '\n\n' + GEN_NOTE +
        '\n\nOwner: SET, Wave 2.\n-/', 'docstring end')


def hashset_decidable(std):
    t = open(os.path.join(std, 'HashSet', 'DecidableEquiv.lean')).read()
    t = replace_once(
        t, 'prelude\npublic import Std.Data.HashMap.DecidableEquiv\npublic import Std.Data.HashSet.Basic\n',
        'public import OAMap.HashMap.DecidableEquiv\npublic import OAMap.HashSet.Basic\n', 'imports')
    t = replace_once(
        t, '# Decidable equivalence for `HashSet`\n-/',
        '# Decidable equivalence for `HashSet`\n\n'
        'Std\'s `Std/Data/HashSet/DecidableEquiv.lean` with the namespace renamed: `m₁ ~m m₂` '
        'is decided\nthrough the `HashMap` instance of `OAMap.HashMap.DecidableEquiv`.\n\n'
        + GEN_NOTE + '\n\nOwner: SET, Wave 2.\n-/\n\nuniverse u', 'docstring')
    t = replace_once(t, '\nnamespace Std.HashSet\n', '\nnamespace OAMap.HashSet\n', 'namespace')
    t = replace_once(t, '\nend Std.HashSet', '\nend OAMap.HashSet', 'end')
    return t


def generate(std, only=None, force=False, base=None, write=True):
    """Write the generated files; returns ({path: text}, {theorem: {candidates, choice}}).

    A file on disk that differs from the generated text (edited by hand instead of through
    `tools/data/hand.json`) is kept unless `force`; the paths kept are listed in the returned
    `skipped`. `base` is the generated text of the previous run (portcheck.py), which may be
    overwritten. With `write=False` nothing is written."""
    porter = Porter()
    review = load_review()
    hand = load_hand()
    choice_log = {}
    files = hashmap_lemma_files(std, porter, review, choice_log, hand)
    files['OAMap/HashSet/Basic.lean'] = hashset_basic(std)
    files['OAMap/HashSet/Lemmas.lean'] = hashset_lemmas(std, review, choice_log, hand)
    files['OAMap/HashSet/DecidableEquiv.lean'] = hashset_decidable(std)
    unused = sorted(set(hand) - {n for n, v in choice_log.items() if v['choice'] == 'hand'})
    if unused:
        raise SystemExit('port.py: hand.json has proofs for unknown theorems: ' + ', '.join(unused))
    generate.skipped = []
    if not write:
        return files, choice_log
    skipped = []
    for path, text in files.items():
        if only and path not in only:
            continue
        full = os.path.join(ROOT, path)
        if not force and os.path.exists(full):
            old = open(full).read()
            if old != text and not (base and old == base.get(path)):
                skipped.append(path)
                continue
        with open(full, 'w') as f:
            f.write(text)
    generate.skipped = skipped
    return files, choice_log


def legacy_main(argv):
    rows = {r['name']: r for r in json.load(open(argv[1]))}
    dhm = {x['full']: x for x in json.load(open(argv[2]))}
    dhm.update({('Std.' + k if not k.startswith('Std.') else k): v for k, v in list(dhm.items())})
    raw = {x['full']: x for x in json.load(open(argv[3]))}
    hm = {x['full']: x for x in json.load(open(argv[4]))}
    names = json.load(open(argv[5]))
    p = Porter.__new__(Porter)
    p.rows, p.dhm, p.raw, p.hm = rows, dhm, raw, hm
    p.dren, p.rren = build_rename(rows)
    out, stats = [], {}
    for n in names:
        x = hm[n]
        stmt, _ = proof_split(x['body'])
        kind, proof = p.legacy(n)
        stats[kind] = stats.get(kind, 0) + 1
        attrs = '' if stmt.lstrip().startswith('@[') else x['attrs'].strip()
        out.append((attrs + '\n' if attrs else '') + stmt.rstrip() + ' :=\n  ' + proof.strip() + '\n')
    open(argv[6], 'w').write('\n'.join(out))
    print(stats)


def check(std):
    """Exit 1, with a diff, if a generated file on disk differs from the generated text."""
    import difflib
    files, log = generate(std, write=False)
    bad = []
    for path, text in files.items():
        full = os.path.join(ROOT, path)
        old = open(full).read() if os.path.exists(full) else ''
        if old != text:
            bad.append(path)
            diff = difflib.unified_diff(old.split('\n'), text.split('\n'), 'disk/' + path,
                                        'generated/' + path, lineterm='', n=1)
            print('\n'.join(list(diff)[:60]))
    if bad:
        print(f'port.py --check: {len(bad)} of {len(files)} files differ from the generated text '
              '(move hand edits to tools/data/hand.json): ' + ', '.join(bad))
        sys.exit(1)
    n_hand = sum(1 for v in log.values() if v['choice'] == 'hand')
    print(f'port.py --check: {len(files)} files reproduced ({len(log)} theorems, {n_hand} hand '
          'proofs)')


def main():
    if len(sys.argv) == 7 and sys.argv[1].endswith('.json'):
        return legacy_main(sys.argv)
    if len(sys.argv) >= 2 and sys.argv[1] == 'lemmas':
        std = split.std_data_dir()
        if '--std' in sys.argv:
            std = sys.argv[sys.argv.index('--std') + 1]
        if '--check' in sys.argv:
            return check(std)
        files, log = generate(std, force='--force' in sys.argv)
        n_sorry = sum(1 for v in log.values() if v['choice'] == 'sorry')
        n_hand = sum(1 for v in log.values() if v['choice'] == 'hand')
        print(f'port.py: generated {len(files)} files, {len(log)} theorems, {n_hand} hand proofs, '
              f'{n_sorry} REVIEW')
        for path in generate.skipped:
            print(f'port.py: kept {path}: it differs from the generated text (edited by hand?); '
                  'pass --force to overwrite it')
        return
    print(__doc__)
    sys.exit(2)


if __name__ == '__main__':
    main()
