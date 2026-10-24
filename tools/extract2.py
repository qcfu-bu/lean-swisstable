import re, sys, json
def extract(path):
    lines = open(path).read().split('\n')
    out = []
    stack = []  # (kind, name)
    idx = 0
    n = len(lines)
    while idx < n:
        l = lines[idx]
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: stack.append(('ns', m.group(1))); idx+=1; continue
        m = re.match(r'^section\b\s*(\S*)', l)
        if m: stack.append(('sec', m.group(1))); idx+=1; continue
        m = re.match(r'^end\b\s*(\S*)', l)
        if m and stack:
            stack.pop(); idx+=1; continue
        m = re.match(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)*(theorem|lemma)\s+(\S+)', l)
        if m:
            j = idx+1
            while j < n:
                lj = lines[j]
                if lj and not lj[0].isspace() and not lj.startswith(')'):
                    break
                j += 1
            ns = '.'.join(s for k,s in stack if k=='ns')
            attr_start = idx
            # include preceding attribute line(s)
            k = idx-1
            attrs=''
            while k>=0 and re.match(r'^@\[', lines[k]):
                attrs = lines[k]+' '+attrs; k-=1
            out.append({'line':idx+1,'ns':ns,'name':m.group(2),'full':(ns+'.' if ns else '')+m.group(2),'attrs':attrs+ (re.match(r'^\s*(@\[[^\]]*\])?',l).group(1) or ''),'body':'\n'.join(lines[idx:j])})
            idx = j; continue
        idx += 1
    return out
if __name__=='__main__':
    r = extract(sys.argv[1])
    json.dump(r, open(sys.argv[2],'w'), indent=0)
    print(len(r))
