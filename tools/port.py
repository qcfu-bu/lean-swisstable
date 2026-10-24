"""Mechanical port of Std's HashMap lemmas onto OAMap's model interface.

For each lemma of Std/Data/HashMap/Lemmas.lean, keep Std's statement and attributes and build the
proof from Std's own proof chain (HashMap -> DHashMap -> Raw0), applying the renaming rules of
proofs.md section 6:

  * the HashMap proof does not mention DHashMap: copy it (it uses sibling HashMap lemmas);
  * the DHashMap proof does not mention Raw0: copy it with DHashMap names renamed to HashMap names;
  * the Raw0 proof is `[revert h;] simp_to_model [qs] using T`: emit
    `simp_to_model [qs'] [at *] using T'` with Raw0 query names renamed (Const.get? -> getElem?,
    contains -> contains, mem, ...), `at *` when the statement has hypotheses, and Raw0 sibling
    references in T renamed with their `_ h` arguments dropped;
  * anything else: emit the Raw0 text renamed, marked `-- REVIEW`.

Usage: python3 -I port.py hmchain.json dhm.json raw0.json hm.json NAMES.json OUT.lean
"""
import json
import re
import sys

QUERY = {
    'Const.get?': ['getElem?'], 'Const.get': ['getElem'], 'Const.get!': ['getElem!'],
    'Const.getD': ['getD'], 'contains': ['contains', 'mem'], 'Const.toList': ['toList'],
    'Const.insertMany': ['insertMany'], 'Const.insertManyIfNewUnit': ['insertManyIfNewUnit'],
    'Const.alter': ['alter'], 'Const.modify': ['modify'], 'Const.beq': ['beq'],
    'Const.toArray': ['toArray'],
}


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
    head = stmt.split(':', 1)[0] if False else stmt
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


def port_simp(raw_proof, stmt, rren):
    body = raw_proof[2:].strip() if raw_proof.startswith('by') else raw_proof
    lines = [l.strip() for l in body.split('\n') if l.strip()]
    reverted = False
    if lines and lines[0].startswith('revert'):
        lines = lines[1:]
        reverted = True
    # `simp_to_model [qs]; intro x; apply T x` (after a revert) is `simp_to_model [qs] at * using T`
    if (reverted and len(lines) == 3 and lines[1].startswith('intro ')
            and lines[2].startswith('apply ')):
        x = lines[1].split()[1]
        t = re.sub(r'\s+' + re.escape(x) + r'$', '', lines[2][len('apply '):])
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


def main():
    rows = {r['name']: r for r in json.load(open(sys.argv[1]))}
    dhm = {x['full']: x for x in json.load(open(sys.argv[2]))}
    dhm.update({('Std.' + k if not k.startswith('Std.') else k): v for k, v in list(dhm.items())})
    raw = {x['full']: x for x in json.load(open(sys.argv[3]))}
    hm = {x['full']: x for x in json.load(open(sys.argv[4]))}
    names = json.load(open(sys.argv[5]))
    dren, rren = build_rename(rows)
    out, stats = [], {}
    for n in names:
        r, x = rows[n], hm[n]
        stmt, _ = proof_split(x['body'])
        hp, dp, rp = r['hm_proof'], r.get('dhm_proof', ''), r.get('raw_proof', '')
        kind = None
        mh = re.match(r'^h\.1\.(\S+)$', hp.strip())
        if mh:
            # Equiv: `h.1.foo` -> DHashMap.Equiv.foo -> Raw0 `..._of_equiv`
            d = dhm.get('Std.DHashMap.Equiv.' + mh.group(1))
            if d:
                dp = proof_split(d['body'])[1]
                mr = re.search(r'Raw₀\.((?:Const\.)?[\w?!\']+)', dp)
                rr = raw_lookup(raw, mr.group(1)) if mr else None
                if rr:
                    rp = proof_split(rr['body'])[1]
        mr = re.search(r'@?Raw₀\.((?:Const\.)?[\w?!\']+)', dp) if dp.startswith('by') else None
        if mr and 'Raw₀' in dp:
            rr = raw_lookup(raw, mr.group(1))
            if rr:
                rp = proof_split(rr['body'])[1]
                dp = ''   # use the Raw0 proof, with `at *` for the hypotheses
        if 'DHashMap' not in hp and not mh:
            proof, kind = hp, 'copy-HashMap'
        elif dp and 'Raw₀' not in dp:
            proof, kind = rename_names(dp, dren), 'copy-DHashMap-renamed'
        elif rp:
            p = port_simp(rp, stmt, rren)
            if p:
                proof, kind = 'by ' + p, 'simp_to_model'
                if mh or mr:
                    kind = 'simp_to_model (via Equiv/DHashMap hop)'
            else:
                proof = drop_raw_args(rename_names(rp, rren))
                kind = 'renamed Raw0 text (check)'
        else:
            proof, kind = '-- REVIEW (no Raw0 proof found)\n  sorry', 'review'
        stats[kind] = stats.get(kind, 0) + 1
        attrs = '' if stmt.lstrip().startswith('@[') else x['attrs'].strip()
        out.append((attrs + '\n' if attrs else '') + stmt.rstrip() + ' :=\n  ' + proof.strip() + '\n')
    open(sys.argv[6], 'w').write('\n'.join(out))
    print(stats)


if __name__ == '__main__':
    main()
