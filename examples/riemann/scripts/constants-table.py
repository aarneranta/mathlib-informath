"""constants.tsv: the Lean constants that the informalized statements use
(the statements of the theorems, without their proofs, and the statements and
bodies of the definitions, in exporter/out/<Module>.dk), with the number of
their occurrences, where they are declared (Mathlib or Lean's library, or the
riemann-hypothesis-original project), and the symbol table entry that the readings
use, if any. Sorted by occurrences, most first.

    python3 scripts/constants-table.py      # after build.sh; origins by
                                             # exporter/checks/Origins.lean
"""
import collections, glob, json, os, re, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..'))
MI = os.path.abspath(os.path.join(ROOT, '..', '..'))
OUT = os.path.join(ROOT, 'exporter', 'out')
INFORMATH = os.environ.get('INFORMATH_ROOT', os.path.join(MI, '..', 'informath'))
IDENT = re.compile(r"\{\|[^|]*\|\}|[A-Za-z_][A-Za-z0-9_']*")
# the framework of Informath's Dedukti, not Lean constants
FRAMEWORK = {'Set', 'Elem', 'Proof', 'Prop', 'forall', 'if', 'def'}
# the logical constants that Export.lean writes for Lean's
LOGIC = {'and': 'And', 'or': 'Or', 'not': 'Not', 'iff': 'Iff', 'exists': 'Exists',
         'Eq': 'Eq', 'Eqt': 'Eq', 'Neq': 'Ne', 'false': 'False', 'true': 'True'}


TOKEN = re.compile(r"\{\|[^|]*\|\}|->|=>|[():]|[A-Za-z_][A-Za-z0-9_']*|\d+|\S")


def parse(text):
    """A Dedukti term of the export as a tree: ('id', c), ('app', head, args),
    ('lam', x, body), ('pi', x, A, B), ('arrow', A, B)."""
    toks = TOKEN.findall(text)
    pos = [0]
    peek = lambda k=0: toks[pos[0] + k] if pos[0] + k < len(toks) else None
    def take():
        pos[0] += 1
        return toks[pos[0] - 1]
    def ident(t):
        return t is not None and (t[0].isalpha() or t[0] in '_{' or t[0].isdigit())
    def expr():
        if ident(peek()) and peek(1) == '=>':
            x = take(); take()
            return ('lam', x, expr())
        a = app()
        if peek() == '->':
            take()
            return ('arrow', a, expr())
        return a
    def app():
        items = [atom()]
        while ident(peek()) or peek() == '(':
            if ident(peek()) and peek(1) == '=>':
                break
            items.append(atom())
        return items[0] if len(items) == 1 else ('app', items[0], items[1:])
    def atom():
        t = take()
        if t == '(':
            if ident(peek()) and peek(1) == ':':
                x = take(); take()
                a = expr(); take()                  # )
                if peek() == '->':
                    take()
                    return ('pi', x, a, expr())
                return a
            e = expr(); take()                      # )
            return e
        return ('id', t)
    return expr()


def hidden_args():
    """c -> the positions that #HIDE hides in its applications."""
    h = {}
    for f in glob.glob(OUT + '/*-hide.dkgf'):
        for l in open(f):
            w = l.split()
            if len(w) > 2 and w[0] == '#HIDE':
                h[w[1]] = set(map(int, w[2:]))
    return h


def shown_constants(tree, hidden, bound=frozenset()):
    """The identifiers that a reading shows: not the bound variables, nor the
    arguments that #HIDE hides."""
    kind = tree[0]
    if kind == 'id':
        return [] if tree[1] in bound else [tree[1]]
    if kind == 'lam':
        return shown_constants(tree[2], hidden, bound | {tree[1]})
    if kind == 'pi':
        return shown_constants(tree[2], hidden, bound) + shown_constants(tree[3], hidden, bound | {tree[1]})
    if kind == 'arrow':
        return shown_constants(tree[1], hidden, bound) + shown_constants(tree[2], hidden, bound)
    head, args = tree[1], tree[2]
    if head[0] == 'id' and head[1] not in bound:
        hide = hidden.get(head[1], set())
        args = [a for i, a in enumerate(args, 1) if i not in hide]
    out = shown_constants(head, hidden, bound)
    for a in args:
        out += shown_constants(a, hidden, bound)
    return out


def modules():
    return sorted(os.path.basename(f)[:-5] for f in glob.glob(OUT + '/*.json')
                  if not f.endswith('-tactics.json'))


def blocks(path):
    """dk name -> (type, body or None) of the declarations of a module."""
    text = open(path).read()
    out = {}
    for b in re.split(r'\n(?=\(; //LEAN:)', text):
        m = re.search(r'^(?:def )?(\S+) : (.*?)(?: :=\n(.*))?\.\s*$', b.split(';)', 1)[-1].strip(), re.S)
        if m:
            out[m.group(1)] = (m.group(2), m.group(3))
    return out


def lean_names():
    """dk name -> Lean name, from the //LEAN comments of the export."""
    names = {}
    for f in glob.glob(OUT + '/*.dk'):
        for m in re.finditer(r'\(; //LEAN:(\S+) ;\)\n(?:def )?(\S+) :', open(f).read()):
            names.setdefault(m.group(2), m.group(1))
    return names


def mapping():
    """Informath base constant -> Lean constant (mapping.tsv, reversed)."""
    m = dict(LOGIC)
    for l in open(os.path.join(MI, 'mapping.tsv')):
        if l.startswith('#') or '\t' not in l:
            continue
        lean, base = l.split('\t')[:2]
        m.setdefault(base.strip(), lean.strip())
    return m


def entries():
    """dk name -> (entry, table) as build-index.py reads the tables: the later
    ones override the earlier; Informath's base entries for its constants."""
    tables = [os.path.join(INFORMATH, 'share', 'baseconstants.dkgf')] + \
        [os.path.join(MI, t) for t in ['definitions.dkgf', 'mathlib.dkgf', 'structures.dkgf']] + \
        [os.path.join(ROOT, t) for t in ['riemann-names.dkgf', 'riemann.dkgf']] + \
        sorted(glob.glob(OUT + '/*-hide.dkgf'))
    e = {}
    for t in tables:
        if not os.path.exists(t):
            continue
        name = os.path.relpath(t, MI) if t.startswith(MI) else 'informath/share/' + os.path.basename(t)
        if '-hide.dkgf' in t:
            name = 'generated by Export.lean'
        for l in open(t):
            m = re.match(r"([A-Za-z_][\w']*) : (.*)", l.rstrip('\n'))
            if m and not l.startswith('#'):
                e[m.group(1)] = (m.group(2).strip(), name)
    return e


PROJECT = os.environ.get('RIEMANN', os.path.join(MI, '..', 'riemann-hypothesis-original'))


def in_project(mod):
    """Whether a module is one of riemann-hypothesis-original's (its source is in src/)."""
    return bool(mod) and os.path.exists(os.path.join(PROJECT, 'src', *mod.split('.')) + '.lean')


def origins(leans):
    """Lean name -> the module that declares it (exporter/checks/Origins.lean)."""
    names = os.path.join(OUT, 'constants.txt')
    open(names, 'w').write('\n'.join(sorted(leans)) + '\n')
    r = subprocess.run(['lake', 'env', 'lean', '--run', 'checks/Origins.lean', names] + modules(),
                       cwd=os.path.join(ROOT, 'exporter'), capture_output=True, text=True)
    out = {}
    for l in r.stdout.splitlines():
        if '\t' in l:
            n, mod, kind = (l.split('\t') + ['', ''])[:3]
            out[n] = (mod, kind)
    if not out:
        raise SystemExit('Origins.lean gave nothing:\n' + r.stderr[-2000:])
    return out


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--roots', help='Lean names, comma-separated: only their statements, and the '
                    'definitions of the project that they use, transitively (column depth)')
    ap.add_argument('--out', default='constants.tsv')
    opts = ap.parse_args()
    leans, base = lean_names(), mapping()
    hidden = hidden_args()
    # dk -> the texts that its reading shows: a theorem's statement (not its
    # proof), a definition's statement and body; a structure's fields are its
    # constructor's statement
    decls = {}
    for m in modules():
        kinds = {d['dk']: d['kind'] for d in json.load(open(os.path.join(OUT, m + '.json')))}
        for dk, (typ, body) in blocks(os.path.join(OUT, m + '.dk')).items():
            decls[dk] = (kinds.get(dk), [typ] if kinds.get(dk) == 'theorem' or body is None else [typ, body])

    def constants_of(text):
        """The dk names of the constants a text shows (c__part<m> as c)."""
        out = []
        for t in shown_constants(parse(text), hidden):
            if t in FRAMEWORK or t.startswith('{|') or t[0].isdigit():
                continue
            out.append(re.sub(r'__(part|app)\d*$', '', t))
        return out

    def lean_of(c):
        return leans.get(c) or base.get(c) or ('EuclideanSpace' if c == 'EuclideanSpace__Fin' else None)

    counts, depth = collections.Counter(), {}
    if opts.roots:
        dk_of_lean = {v: k for k, v in leans.items()}
        level = [dk_of_lean[r] for r in opts.roots.split(',')]
        texts_of = lambda dk, d: decls[dk][1][:1] if d == 0 else decls[dk][1]
        seen, d = set(level), 0
        while level:
            nxt = []
            for dk in level:
                for text in texts_of(dk, d):
                    for c in constants_of(text):
                        lean = lean_of(c)
                        if not lean:
                            continue
                        counts[lean] += 1
                        depth.setdefault(lean, d)
                        # the project's definitions read next: their bodies, a
                        # structure's fields (its constructor c__mk)
                        for e in [c, c + '__mk']:
                            if e in decls and decls[e][0] != 'theorem' and e not in seen:
                                seen.add(e)
                                nxt.append(e)
            level, d = nxt, d + 1
    else:
        for dk, (kind, terms) in decls.items():
            for text in terms:
                for c in constants_of(text):
                    lean = lean_of(c)
                    if lean:
                        counts[lean] += 1
    orig = origins(counts)
    # the theorems (proofs inside definitions, as of a subtype) are not counted
    for lean in [l for l in counts if orig.get(l, ('', ''))[1] == 'theorem']:
        del counts[lean]
    ent = entries()
    dk_of = {v: k for k, v in leans.items()}
    base_of = {}
    for b, l in base.items():
        base_of.setdefault(l, b)
    rows = []
    for lean, n in counts.items():
        mod = orig.get(lean, ('', ''))[0]
        where = 'riemann-hypothesis-original' if in_project(mod) \
            else 'Mathlib' if mod.startswith('Mathlib') else 'Lean' if mod and not mod.startswith('(') else '?'
        dk = dk_of.get(lean)
        if dk is None and lean in base_of:
            dk = base_of[lean]
        if lean == 'EuclideanSpace':
            dk = 'EuclideanSpace__Fin'
        if dk not in ent and lean in base_of:
            dk = base_of[lean]              # mapped to Informath's base (Real.exp?)
        entry, table = ent.get(dk, ('', ''))
        rows.append((n, lean, where, mod, dk or '', entry, table) + ((depth.get(lean, ''),) if opts.roots else ()))
    rows.sort(key=lambda r: (-r[0], r[1]))
    with open(os.path.join(ROOT, opts.out), 'w') as f:
        f.write('occurrences\tlean\tdefined in\tmodule\tdedukti\tentry\ttable' + ('\tdepth' if opts.roots else '') + '\n')
        for r in rows:
            f.write('\t'.join(str(x).replace('\t', ' ') for x in r) + '\n')
    by = collections.Counter(r[2] for r in rows)
    print(('%d constants (%s), %d occurrences -> ' + opts.out + '; %d without an entry')
          % (len(rows), ', '.join('%d %s' % (n, w or '?') for w, n in by.most_common()),
             sum(counts.values()), sum(1 for r in rows if not r[5])))


if __name__ == '__main__':
    main()
