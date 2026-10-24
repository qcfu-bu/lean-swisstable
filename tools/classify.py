import json,re,collections,sys
def proof_split(b):
    depth=0; i=0
    while i < len(b)-1:
        c=b[i]
        if c in '([{⟨': depth+=1
        elif c in ')]}⟩': depth-=1
        elif c==':' and b[i+1]=='=' and depth==0:
            return b[:i], b[i+2:].strip()
        i+=1
    return b,''
def norm(s):
    s=re.sub(r'\s+',' ',s)
    return s.strip()
def classify(path_main, path_ext, mapname, extname):
    hm=json.load(open(path_main)); ehm=json.load(open(path_ext))
    E={}
    for x in ehm:
        st,_=proof_split(x['body']); E[x['full'].replace(extname,mapname)]=norm(st)
    out=[]
    for x in hm:
        st,pf=proof_split(x['body'])
        s=norm(st)
        iter_re=r'\b(toList|keys|values|toArray|keysArray|valuesArray|fold|foldM|forM|forIn|all|any|ForIn\.forIn|ForM\.forM|foldRev|partition)\b'
        lawful = bool(re.search(r'EquivBEq|LawfulHashable|LawfulBEq',s))
        iter_ = bool(re.search(iter_re, s))
        equiv = ('~m' in s) or '.Equiv.' in x['full'] or bool(re.search(r'\bEquiv\b(?!BEq)', s))
        beq = bool(re.search(r'\bbeq\b| == m|m₁ == m₂',s))
        inExt = x['full'] in E
        sameStmt = inExt and E[x['full']]==s
        out.append(dict(name=x['full'],line=x['line'],lawful=lawful,iter=iter_,equiv=equiv,inExt=inExt,sameStmt=sameStmt,stmt=s,proof=pf))
    return out
if __name__=='__main__':
    r=classify(sys.argv[1],sys.argv[2],sys.argv[3],sys.argv[4])
    json.dump(r,open(sys.argv[5],'w'),indent=0)
    c=collections.Counter()
    for x in r:
        if x['iter']: k='iter'
        elif not x['lawful']: k='nolawful'
        elif x['equiv']: k='equiv'
        elif x['sameStmt']: k='ext-same'
        elif x['inExt']: k='ext-diffstmt'
        else: k='other'
        x['cls']=k; c[k]+=1
    json.dump(r,open(sys.argv[5],'w'),indent=0)
    print(c)
