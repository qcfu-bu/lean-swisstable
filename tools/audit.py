"""Text-level spec-integrity audit of the OAMap library sources.

Usage: python3 -I tools/audit.py [DIR ...]      (default: OAMap OAMap.lean)

Fails (exit status 1) when a library source file

  * does not start with `module` (every library file uses the module system, ARCHITECTURE.md §2.3);
  * contains, outside comments and string literals, one of the escape hatches excluded by the
    correctness standard: `sorry`, `admit`, `native_decide`, `decide +native`, `bv_decide`
    (its proofs use `Lean.ofReduceBool`), `ofReduceBool`, `trustCompiler`, `implemented_by`,
    `extern`, `unsafe`, `partial`, `opaque` (as a keyword: the attribute `cbv_opaque` is fine),
    `axiom`, `debug.skipKernelTC`, or `import all`.

Comments (including doc comments) and strings are blanked first, so documentation may mention
these words. The kernel-level counterpart is test/OAMapTest/Audit.lean.
"""
import os
import re
import sys

FORBIDDEN = [
    (re.compile(r'\bsorry\b'), 'sorry'),
    (re.compile(r'\badmit\b'), 'admit'),
    (re.compile(r'\bnative_decide\b'), 'native_decide'),
    (re.compile(r'\bdecide\s*\+\s*native\b'), 'decide +native'),
    (re.compile(r'\bbv_decide\b'), 'bv_decide'),
    (re.compile(r'\bofReduceBool\b'), 'ofReduceBool'),
    (re.compile(r'\btrustCompiler\b'), 'trustCompiler'),
    (re.compile(r'\bimplemented_by\b'), 'implemented_by'),
    (re.compile(r'\bextern\b'), 'extern'),
    (re.compile(r'\bunsafe\b'), 'unsafe'),
    (re.compile(r'\bpartial\b'), 'partial'),
    (re.compile(r'(?<![\w.])opaque\b'), 'opaque'),
    (re.compile(r'\baxiom\b'), 'axiom'),
    (re.compile(r'\bdebug\.skipKernelTC\b'), 'debug.skipKernelTC'),
    (re.compile(r'\bimport\s+all\b'), 'import all'),
]

IDENT = re.compile(r"[\w'?!.]")


def blank(src):
    """Replace comments and string literals by spaces, keeping line structure."""
    out = []
    i, n = 0, len(src)
    depth = 0  # nesting depth of block comments
    while i < n:
        c = src[i]
        two = src[i:i + 2]
        if depth > 0:
            if two == '/-':
                depth += 1
                out.append('  ')
                i += 2
            elif two == '-/':
                depth -= 1
                out.append('  ')
                i += 2
            else:
                out.append('\n' if c == '\n' else ' ')
                i += 1
            continue
        if two == '/-':
            depth = 1
            out.append('  ')
            i += 2
            continue
        if two == '--':
            while i < n and src[i] != '\n':
                out.append(' ')
                i += 1
            continue
        if c == '"':
            out.append(' ')
            i += 1
            while i < n and src[i] != '"':
                if src[i] == '\\' and i + 1 < n:
                    out.append('  ')
                    i += 2
                    continue
                out.append('\n' if src[i] == '\n' else ' ')
                i += 1
            out.append(' ')
            i += 1
            continue
        if c == "'" and (i == 0 or not IDENT.match(src[i - 1])):
            m = re.match(r"'(\\.|\\x[0-9a-fA-F]{2}|\\u[0-9a-fA-F]{4}|[^\\'])'", src[i:])
            if m:
                out.append(' ' * len(m.group(0)))
                i += len(m.group(0))
                continue
        out.append(c)
        i += 1
    return ''.join(out)


def lean_files(paths):
    for p in paths:
        if os.path.isfile(p):
            yield p
        elif os.path.isdir(p):
            for root, dirs, files in os.walk(p):
                dirs.sort()
                for f in sorted(files):
                    if f.endswith('.lean'):
                        yield os.path.join(root, f)
        else:
            print(f'audit: no such file or directory: {p}', file=sys.stderr)
            sys.exit(2)


def main():
    paths = sys.argv[1:] or ['OAMap', 'OAMap.lean']
    findings = []
    nfiles = 0
    for path in lean_files(paths):
        nfiles += 1
        code = blank(open(path, encoding='utf-8').read())
        first = code.split()
        if not first or first[0] != 'module':
            findings.append(f'{path}:1: does not start with `module`')
        for lineno, line in enumerate(code.split('\n'), 1):
            for rx, what in FORBIDDEN:
                if rx.search(line):
                    findings.append(f'{path}:{lineno}: forbidden `{what}`: {line.strip()}')
    for f in findings:
        print(f)
    if findings:
        print(f'audit: {len(findings)} findings in {nfiles} files')
        sys.exit(1)
    print(f'audit: ok ({nfiles} files)')


if __name__ == '__main__':
    main()
