"""The shown arguments of constants, for writing riemann.dkgf: for each dk name
given (or matching a regex with --re), its binder names, with the hidden ones
(#HIDE) in brackets and the shown ones numbered #1, #2, ...

    python3 scripts/arguments.py [--re] <name or regex> ...
"""
import glob, os, re, sys
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'exporter', 'out')
hidden, types = {}, {}
for f in glob.glob(OUT + '/*-hide.dkgf'):
    for l in open(f):
        w = l.split()
        if len(w) > 2 and w[0] == '#HIDE':
            hidden[w[1]] = set(map(int, w[2:]))
for f in glob.glob(OUT + '/*.dk'):
    for l in open(f):
        m = re.match(r"(?:def )?([A-Za-z_][\w']*) : (.*?)(?:\.|\s*:=)\s*$", l)
        if m:
            types.setdefault(m.group(1), m.group(2))
B = re.compile(r"\s*\(\s*([A-Za-z0-9_']+|\{\|[^|]*\|\})\s*:")
def binders(t):
    out, i = [], 0
    while True:
        m = B.match(t[i:])
        if not m:
            return out, t[i:].strip()
        d, j = 0, i + t[i:].index('(')
        while True:
            d += {'(': 1, ')': -1}.get(t[j], 0)
            j += 1
            if d == 0:
                break
        out.append(m.group(1))
        m2 = re.match(r'\s*->', t[j:])
        if not m2:
            return out, t[i:].strip()
        i = j + m2.end()
regex = sys.argv[1] == '--re'
pats = sys.argv[2:] if regex else sys.argv[1:]
for c in sorted(types):
    if (regex and any(re.search(p, c) for p in pats)) or c in pats:
        bs, cod = binders(types[c])
        k, shown = 0, []
        for n, b in enumerate(bs, 1):
            if n in hidden.get(c, set()):
                shown.append('[%s]' % b)
            else:
                k += 1
                shown.append('#%d=%s' % (k, b))
        print('%s %s -> %s' % (c, ' '.join(shown), cod[:60]))
