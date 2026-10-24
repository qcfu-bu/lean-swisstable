import re, sys, json
def extract(path):
    lines = open(path).read().split('\n')
    out = []
    ns = []
    i = 0
    starts = []
    for idx, l in enumerate(lines):
        m = re.match(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?(theorem|lemma|instance|def|abbrev)\s+(\S+)?', l)
        if m and m.group(1) in ('theorem','lemma'):
            starts.append((idx, m.group(2)))
    # block end = next line that starts at column 0 with non-space and is not continuation, approximated as next start/attr/section/namespace/end/doc
    ends = []
    for k,(idx,name) in enumerate(starts):
        j = idx+1
        while j < len(lines):
            l = lines[j]
            if l and not l[0].isspace() and not l.startswith(')') :
                break
            j += 1
        ends.append(j)
    # namespace tracking
    for k,(idx,name) in enumerate(starts):
        nsstack=[]
        body='\n'.join(lines[idx:ends[k]])
        out.append({'line':idx+1,'name':name,'body':body})
    return out
if __name__=='__main__':
    r = extract(sys.argv[1])
    json.dump(r, open(sys.argv[2],'w'), indent=0)
    print(len(r))
