import json,re,collections,sys
def load(n): return json.load(open(n+'.json'))
hm=load('hm'); dhm=load('dhm'); raw0=load('raw0')
def proof(b):
    # find ':=' that ends the statement: first occurrence of ':=' followed by newline/space-by/space-term at paren depth 0
    depth=0; i=0
    while i < len(b)-1:
        c=b[i]
        if c in '([{⟨': depth+=1
        elif c in ')]}⟩': depth-=1
        elif c==':' and b[i+1]=='=' and depth==0:
            return b[i+2:].strip()
        i+=1
    return ''
def index(r):
    d={}
    for x in r: d[x['full']]=x
    return d
D=index(dhm); R=index(raw0)
def head(p):
    p=p.lstrip('(@')
    m=re.match(r'([\w.?!\'₀-₉]+)',p)
    return m.group(1) if m else None
def resolve_d(name):
    # name as in HashMap proof, e.g. DHashMap.Const.get?_insert
    n=name
    if n.startswith('Std.'): n=n[4:]
    return D.get('Std.'+n) or D.get(n)
def resolve_r(name, ctxns):
    n=name
    for pre in ['Std.DHashMap.Internal.', 'Std.DHashMap.Internal.Raw₀.', 'Raw₀.', '', 'Std.DHashMap.Internal.Raw₀.Const.' if False else 'Std.DHashMap.Internal.']:
        if (pre+n) in R: return R[pre+n]
    return None
stats=collections.Counter(); rows=[]
for x in hm:
    p=proof(x['body']); h=head(p)
    rec={'name':x['full'],'line':x['line'],'hm_proof':p}
    if h and h.startswith('DHashMap'):
        d=resolve_d(h)
        if d is None:
            rec['kind']='deleg-unresolved'
        else:
            dp=proof(d['body']); dh=head(dp)
            rec['dhm']=d['full']; rec['dhm_proof']=dp
            if dh and dh.startswith('Raw₀'):
                r=resolve_r(dh, d['ns'])
                if r is None: rec['kind']='raw-unresolved'
                else:
                    rp=proof(r['body']); rec['raw']=r['full']; rec['raw_proof']=rp
                    if rp.startswith('by\n') or rp.startswith('by '):
                        t=rp[2:].strip()
                        lines=[l for l in t.split('\n') if l.strip()]
                        if t.startswith('simp_to_model') and len(lines)==1: rec['kind']='raw:simp_to_model-1line'
                        elif t.startswith('simp_to_model') and len(lines)<=3: rec['kind']='raw:simp_to_model-short'
                        elif t.startswith('simp_to_model'): rec['kind']='raw:simp_to_model-long'
                        elif len(lines)<=2: rec['kind']='raw:by-short'
                        else: rec['kind']='raw:by-long'
                    else:
                        rec['kind']='raw:term'
            elif dp.startswith('by'):
                lines=[l for l in dp[2:].strip().split('\n') if l.strip()]
                rec['kind']='dhm:by-short' if len(lines)<=2 else 'dhm:by-long'
            else:
                rec['kind']='dhm:term-other'
    else:
        if p.startswith('by'):
            lines=[l for l in p[2:].strip().split('\n') if l.strip()]
            rec['kind']='hm:by-short' if len(lines)<=2 else 'hm:by-long'
        elif p=='rfl' or p=='(rfl)': rec['kind']='hm:rfl'
        else: rec['kind']='hm:term'
    stats[rec['kind']]+=1; rows.append(rec)
json.dump(rows,open(sys.argv[1],'w'),indent=0)
for k,v in sorted(stats.items()): print(k,v)
