"""A symbol table (.dkgf) of the constants of a constants table (constants-table.py),
to be edited and added to the end of RunInformath's -symboltables= list (or to
build-index.py's tables), which it then completes and overrides:

    python3 scripts/dkgf-subtable.py constants-lemma86.tsv lemma86.dkgf

For each constant, most frequent first: its Lean name, origin, occurrences and
the table of its present entry in a comment, and the entry itself; a constant
without an entry gets a verbal mock-up of the right category and number of
arguments, made of words from outside mathematics (appendix, inflationary),
to be replaced. The #HIDE lines of the constants come first, so that the #k
count the same arguments as in the readings, and the #MACRO lines that the
entries use. Informath's own base constants are listed as comments.
"""
import glob, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..'))
MI = os.path.abspath(os.path.join(ROOT, '..', '..'))
OUT = os.path.join(ROOT, 'exporter', 'out')
INFORMATH = os.environ.get('INFORMATH_ROOT', os.path.join(MI, '..', 'informath'))
TABLES = [os.path.join(INFORMATH, 'share', 'baseconstants.dkgf')] + \
    [os.path.join(MI, t) for t in ['definitions.dkgf', 'mathlib.dkgf', 'structures.dkgf']] + \
    [os.path.join(ROOT, t) for t in ['navier-stokes-names.dkgf', 'navier-stokes.dkgf']]


def binders(t):
    """The named top-level binders (x : A) -> of a Dedukti type, and its value."""
    n, i = 0, 0
    while True:
        m = re.match(r"\s*\(\s*[\w']+\s*:", t[i:])
        if not m:
            break
        d, j = 0, i + t[i:].index('(')
        while True:
            d += {'(': 1, ')': -1}.get(t[j], 0)
            j += 1
            if d == 0:
                break
        m2 = re.match(r'\s*->', t[j:])
        if not m2:
            break
        n, i = n + 1, j + m2.end()
    return n, t[i:].strip()


def types_and_hides():
    types, hides = {}, {}
    for f in glob.glob(OUT + '/*.dk'):
        for l in open(f):
            m = re.match(r'(?:def )?(\S+) : (.*?)(?:\.|\s*:=)\s*$', l)
            if m:
                types.setdefault(m.group(1), m.group(2))
    for f in glob.glob(OUT + '/*-hide.dkgf'):
        for l in open(f):
            w = l.split()
            if len(w) > 2 and w[0] == '#HIDE':
                hides[w[1]] = l.strip()
    return types, hides


def macros():
    """\\Name -> its #MACRO line, from the tables."""
    out = {}
    for t in TABLES:
        if os.path.exists(t):
            for l in open(t):
                m = re.match(r'#MACRO \\newcommand\{\\(\w+)\}', l)
                if m:
                    out[m.group(1)] = l.rstrip('\n')
    return out


def mockup(n, value):
    """A verbal entry of the category of the value (Set: a noun, Prop: an
    adjective, else a term) with n arguments, in words from outside mathematics."""
    args = ['#%d' % i for i in range(1, n + 1)]
    if value == 'Set':
        return '"appendix"' if n == 0 else '"appendix of %s"' % ' and '.join(args) if n <= 2 else \
            '"appendix of %s with respect to %s"' % (args[0], ' and '.join(args[1:]))
    if value == 'Prop':
        if n == 0:
            return None                          # a proposition without arguments: no noun to hang it on
        if n == 1:
            return '"#1 is inflationary"'
        if n <= 3:
            return '"#1 is inflationary with respect to %s"' % ' and '.join(args[1:])
        return '"#1 and #2 are inflationary with respect to %s"' % ' and '.join(args[2:])
    if n == 0:
        return '"the appendix"'
    if n <= 2:
        return '"the appendix of %s"' % ' and '.join(args)
    return '"the appendix of #1 with respect to %s"' % ' and '.join(args[1:])


def main():
    src, dst = sys.argv[1], sys.argv[2]
    types, hides = types_and_hides()
    macro = macros()
    rows = [l.rstrip('\n').split('\t') for l in open(os.path.join(ROOT, src))][1:]
    out = ['# Symbol table of the constants of %s (scripts/dkgf-subtable.py), most frequent' % src,
           '# first: edit the entries and add the file to the end of RunInformath\'s',
           '# -symboltables= list, which it completes and overrides. A "mock-up" entry, of',
           '# words from outside mathematics (appendix, inflationary), stands for a missing',
           '# one, with the right category and number of arguments: replace it.',
           '', '# the implicit arguments that the readings hide (#k count the others)']
    out += sorted(hides[r[4]] for r in rows if r[4] in hides)
    used = sorted({m for r in rows if 'baseconstants' not in r[6]
                   for m in re.findall(r'\\(\w+)', r[5]) if m in macro})
    if used:
        out += ['', '# the macros of the entries'] + [macro[m] for m in used]
    out.append('')
    mock = 0
    for r in rows:
        n_occ, lean, where, module, dk, entry, table = r[:7]
        depth = r[7] if len(r) > 7 else ''
        info = '%s (%s, %s; %s occurrences%s)' % (lean, where, module, n_occ, ', depth ' + depth if depth else '')
        if not dk:
            continue
        if 'baseconstants' in table:
            out += ['# %s: Informath\'s base constant' % info, '# %s : %s' % (dk, entry), '']
            continue
        if entry:
            out += ['# %s: from %s' % (info, table), '%s : %s' % (dk, entry), '']
            continue
        n, value = binders(types.get(dk, ''))
        hidden = len(hides.get(dk, '').split()[2:])
        e = mockup(n - hidden, 'Prop' if value == 'Prop' else 'Set' if value == 'Set' else 'Exp')
        if e is None:
            out += ['# %s: no entry, and no mock-up for a proposition without arguments' % info, '']
            continue
        mock += 1
        out += ['# %s: no entry; a mock-up to replace' % info, '%s : %s' % (dk, e), '']
    open(os.path.join(ROOT, dst), 'w').write('\n'.join(out))
    print('%d constants -> %s; %d mock-ups' % (len(rows), dst, mock))


if __name__ == '__main__':
    main()
