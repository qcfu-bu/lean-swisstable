import json,re,collections,sys
exec(open('classify.py').read().split('def classify')[0])
def strip_attr(s): return re.sub(r'^(@\[[^\]]*\]\s*)+','',s).strip()
def run(main, ext, mapn, extn, out, inner_prefix):
    hm=json.load(open(main)); ehm=json.load(open(ext))
    E={}
    for x in ehm:
        st,_=proof_split(x['body']); E[x['full'].replace(extn,mapn)]=strip_attr(norm(st))
    rows=[]; c=collections.Counter()
    for x in hm:
        st,pf=proof_split(x['body']); s=strip_attr(norm(st))
        iter_re=r'\b(toList|keys|values|toArray|keysArray|valuesArray|fold|foldM|forM|forIn|all|any|foldRev|partition)\b|ForIn|ForM'
        lawful = bool(re.search(r'EquivBEq|LawfulHashable|LawfulBEq',s))
        it = bool(re.search(iter_re, s))
        eq = ('~m' in s) or '.Equiv.' in x['full'] or bool(re.search(r'\bEquiv\b(?!BEq)', s))
        sameExt = x['full'] in E and E[x['full']]==s
        derived = not re.search(inner_prefix, pf) and not pf.startswith('⟨') and not re.match(r'^h\.',pf)
        if derived: k='derived(sibling/rfl)'
        elif it: k='iter'
        elif not lawful: k='nolawful-primitive'
        elif eq: k='equiv-primitive'
        elif sameExt: k='ext-same-primitive'
        elif x['full'] in E: k='ext-diff-primitive'
        else: k='other-primitive'
        c[k]+=1
        rows.append(dict(name=x['full'],line=x['line'],cls=k,stmt=s,proof=pf,ext_stmt=E.get(x['full'])))
    json.dump(rows,open(out,'w'),indent=0)
    print(main,sum(c.values()),dict(c))
run('hm.json','ehm.json','Std.HashMap','Std.ExtHashMap','hmcls.json',r'DHashMap')
run('hs.json','ehs.json','Std.HashSet','Std.ExtHashSet','hscls.json',r'HashMap\.|inner')
