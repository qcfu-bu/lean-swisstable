"""Cross-section proof dependencies in Std's HashMap/HashSet Lemmas.lean.
Usage: python3 -I secdeps.py LEMMAS.lean SPLITSPEC
SPLITSPEC: comma list of name:startline (file chunks, ascending)."""
import re, sys
src = open(sys.argv[1]).read().split('\n')
spec = [(s.split(':')[0], int(s.split(':')[1])) for s in sys.argv[2].split(',')]
def chunk(line):
    c = None
    for name, start in spec:
        if line >= start: c = name
    return c
# collect theorem names and their bodies
thm_re = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+)?theorem\s+([^\s({\[:]+)')
decls = []
cur = None
for i, l in enumerate(src, 1):
    m = thm_re.match(l)
    if m or re.match(r'^\s*(?:@\[[^\]]*\]\s*)?(instance|section|end|namespace|grind_pattern|attribute|variable)\b', l):
        if cur: decls.append(cur)
        cur = None
        if m:
            cur = [m.group(1), i, []]
            continue
    if cur is not None:
        cur[2].append(l)
if cur: decls.append(cur)
owner = {}
for name, line, body in decls:
    owner.setdefault(name, chunk(line))
edges = {}
idre = re.compile(r"[A-Za-z_][A-Za-z0-9_.!?'₁₂₃]*")
for name, line, body in decls:
    c = chunk(line)
    text = '\n'.join(body)
    for tok in set(idre.findall(text)):
        t = tok.split('.')[-1] if tok.startswith('Equiv.') is False else tok
        for cand in (tok, tok.split('.')[-1]):
            o = owner.get(cand)
            if o and o != c:
                edges.setdefault((c, o), set()).add(cand)
                break
order = [n for n, _ in spec]
for (a, b), s in sorted(edges.items(), key=lambda e: (order.index(e[0][0]), order.index(e[0][1]))):
    back = order.index(b) > order.index(a)
    print(f"{a:12s} -> {b:12s} {'BACKWARD ' if back else ''}{len(s):3d}  e.g. {sorted(s)[:4]}")
