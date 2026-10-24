"""Split Std's lemma files into commands and cut them into OAMap's module files.

`docs/ARCHITECTURE.md` §2.2 and §6.2: `OAMap/HashMap/Lemmas/*.lean` are Std's
`Std/Data/HashMap/Lemmas.lean`, cut at fixed Std line numbers into nine files that keep Std's order,
each importing the previous one. Every file gets the preamble that is active at its cut point (the
open `namespace`/`section`s and their `variable` lines, in Std's order), and closes the scopes that
are still open at its end, so every theorem is elaborated with exactly the variables it has in Std.

This module only knows the source structure. The proofs are built by `tools/port.py`, which imports
it; `python3 -I tools/split.py [STD_DATA_DIR]` prints the blocks of each cut, for inspection.

A *block* is one command of the source file: its docstring and attribute lines, its first line at
column 0, and every following line until the next command (blank lines included, trailing blank
lines dropped). Std's files start every command at column 0 and indent all continuation lines,
which is what makes this line-based split exact for them.
"""
import os
import re
import subprocess
import sys

# Std/Data/HashMap/Lemmas.lean, cut as in ARCHITECTURE.md §2.2: (file, first Std line, last Std line,
# title of the file's docstring, owner in Wave 2).
HASHMAP_CUTS = [
    ('Basic', 34, 502, '`isEmpty` to `getD`', 'LEM-1'),
    ('GetKey', 503, 859, '`getKey?` to `LawfulGetElem`', 'LEM-2'),
    ('Iterate', 860, 1192, '`keys`, `toList`, monadic traversals, `all`/`any`', 'LEM-3'),
    ('InsertMany', 1193, 1395, '`insertMany`', 'GEN'),
    ('SetOps', 1396, 2069, '`BEq`, union, intersection, difference', 'LEM-5'),
    ('UnitOf', 2070, 2527, '`insertManyIfNewUnit`, `ofList`, `unitOfList`', 'GEN'),
    ('Alter', 2528, 2879, '`alter`, `modify`', 'LEM-6'),
    ('Equiv', 2880, 3075, '`Equiv` (namespace `Equiv`, section `Equiv`)', 'LEM-6'),
    ('FilterMap', 3076, 3580, '`filterMap`, `filter`, `map`', 'LEM-7'),
]

COMMAND_KEYWORDS = (
    'theorem', 'private', 'protected', 'instance', 'section', 'end', 'namespace', 'variable',
    'grind_pattern', 'attribute', 'open', 'set_option', 'universe', 'def', 'abbrev', 'example',
    'noncomputable', 'scoped', 'local', 'structure', 'class', 'inductive', 'macro', 'syntax',
    'macro_rules', 'notation', 'infixl', 'infixr', 'export', 'module', 'prelude', 'public',
    'import', 'meta', 'deriving', 'mutual', 'omit', 'include')


def std_data_dir():
    """`<toolchain>/src/lean/Std/Data` of the `lean` on the PATH (the project's toolchain)."""
    try:
        prefix = subprocess.run(['lean', '--print-prefix'], capture_output=True, text=True,
                                check=True).stdout.strip()
        d = os.path.join(prefix, 'src', 'lean', 'Std', 'Data')
        if os.path.isdir(d):
            return d
    except (OSError, subprocess.CalledProcessError):
        pass
    return os.path.expanduser(
        '~/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Std/Data')


class Block:
    """One command of a source file. Lines are 1-based and inclusive."""

    def __init__(self, start, lines):
        self.start = start
        self.lines = lines
        self.end = start + len(lines) - 1
        self.kind, self.name = classify(lines)

    @property
    def text(self):
        return '\n'.join(self.lines)

    def __repr__(self):
        return f'Block({self.start}-{self.end} {self.kind} {self.name})'


def _strip_doc_attrs(lines):
    """The lines of a block without its leading docstring, comments and attribute lines."""
    i = 0
    n = len(lines)
    while i < n:
        s = lines[i]
        if s.startswith('/--'):
            # a docstring: skip to its closing `-/`
            if '-/' not in s[3:]:
                i += 1
                while i < n and '-/' not in lines[i]:
                    i += 1
            i += 1
            continue
        if (s.startswith('@[') and not re.search(r'\]\s*\S', s)) or s.startswith('--'):
            i += 1
            continue
        break
    return lines[i:]


def classify(lines):
    body = _strip_doc_attrs(lines)
    if not body:
        first = lines[0] if lines else ''
        return ('comment', None) if first.startswith(('--', '/-')) else ('other', None)
    first = re.sub(r'^@\[[^\]]*(?:\[[^\]]*\][^\]]*)*\]\s*', '', body[0])
    if first.startswith(('--', '/-')):
        return 'comment', None
    m = re.match(r'(?:private\s+|protected\s+)*theorem\s+(\S+)', first)
    if m:
        return ('private theorem' if first.startswith('private') else 'theorem'), m.group(1)
    for kw in ('section', 'namespace', 'end'):
        m = re.match(kw + r'\b\s*(\S*)', first)
        if m:
            return kw, m.group(1) or ''
    m = re.match(r'(instance|variable|grind_pattern|attribute|open|set_option|universe)\b', first)
    if m:
        return m.group(1), None
    return 'other', None


def parse(text):
    """The blocks of a file, in order. Docstrings, attribute-only lines and line comments that
    directly precede a command join its block."""
    lines = text.split('\n')
    starts = []
    in_comment = False
    for i, l in enumerate(lines):
        if in_comment:
            if '-/' in l:
                in_comment = False
            continue
        if not l or l[0].isspace() or l.startswith(')'):
            continue
        starts.append(i)
        if l.startswith('/-') and '-/' not in l[2:]:
            in_comment = True
    blocks = []
    pending = None   # index of the first line of a docstring/attribute prefix
    for j, s in enumerate(starts):
        e = starts[j + 1] if j + 1 < len(starts) else len(lines)
        chunk = lines[s:e]
        while chunk and not chunk[-1].strip():
            chunk = chunk[:-1]
        first = lines[s]
        # docstrings, attribute-only lines and line comments directly above the next command
        is_prefix = (first.startswith('/--') or
                     (first.startswith('@[') and not re.search(r'\]\s*\S', first.split('--')[0])) or
                     (first.startswith('--') and e == s + 1 and j + 1 < len(starts)))
        if is_prefix:
            if pending is None:
                pending = s
            continue
        if pending is not None:
            chunk = lines[pending:e]
            while chunk and not chunk[-1].strip():
                chunk = chunk[:-1]
            blocks.append(Block(pending + 1, chunk))
            pending = None
        else:
            blocks.append(Block(s + 1, chunk))
    return blocks


def split_statement(block):
    """(header, proof) of a theorem block: the header ends before the `:=` that starts the proof.

    The `:=` is the first one at bracket depth 0 that is not inside a `haveI`/`letI`/`have`/`let`
    line of the statement (the `getElem_alter` family has `haveI h' : … := …` in its statement).
    A theorem defined by pattern matching (`| ⟨h⟩ => …`) has no such `:=`; then proof is None.
    """
    return split_text(block.text)


def split_text(text):
    """`split_statement` on the text of a declaration."""
    depth = 0
    i = 0
    line_start = 0
    in_comment = 0
    in_line_comment = False
    while i < len(text) - 1:
        c = text[i]
        if c == '\n':
            line_start = i + 1
            in_line_comment = False
        elif in_line_comment:
            pass
        elif text.startswith('/-', i):
            in_comment += 1
            i += 2
            continue
        elif in_comment and text.startswith('-/', i):
            in_comment -= 1
            i += 2
            continue
        elif in_comment:
            pass
        elif text.startswith('--', i):
            in_line_comment = True
        elif c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        elif c == ':' and text[i + 1] == '=' and depth == 0:
            line = text[line_start:i].strip()
            if not re.match(r'(haveI|letI|have|let)\b', line):
                return text[:i].rstrip(), text[i + 2:].strip()
        i += 1
    return text, None


class Scope:
    def __init__(self, kind, name, block):
        self.kind = kind          # 'namespace' or 'section'
        self.name = name
        self.block = block
        self.variables = []       # variable blocks declared directly in this scope


def walk_scopes(blocks, upto):
    """The scopes (outermost first) and top-level variables open just before line `upto`."""
    top_vars = []
    stack = []
    for b in blocks:
        if b.start >= upto:
            break
        if b.kind in ('section', 'namespace'):
            stack.append(Scope(b.kind, b.name, b))
        elif b.kind == 'end':
            if stack:
                stack.pop()
        elif b.kind == 'variable':
            (stack[-1].variables if stack else top_vars).append(b)
    return top_vars, stack


def blocks_in(blocks, lo, hi):
    return [b for b in blocks if lo <= b.start <= hi]


def join(pairs):
    """The texts of consecutive blocks [(block, text)], separated as in the source (the blank
    lines between two blocks are kept)."""
    out = []
    prev = None
    for b, t in pairs:
        if prev is not None:
            out.append('\n' * max(1, b.start - prev.end))
        out.append(t)
        prev = b
    return ''.join(out)


def main():
    d = sys.argv[1] if len(sys.argv) > 1 else std_data_dir()
    src = open(os.path.join(d, 'HashMap', 'Lemmas.lean')).read()
    blocks = parse(src)
    print(f'{len(blocks)} blocks, {sum(b.kind == "theorem" for b in blocks)} theorems')
    for (f, lo, hi, _, _) in HASHMAP_CUTS:
        bs = blocks_in(blocks, lo, hi)
        _, stack = walk_scopes(blocks, lo)
        print(f'{f}: lines {lo}-{hi}, {len(bs)} blocks, '
              f'{sum(b.kind == "theorem" for b in bs)} theorems, open scopes '
              + ' > '.join(f'{s.kind} {s.name}'.strip() + f' ({len(s.variables)} var)' for s in stack))


if __name__ == '__main__':
    main()
