"""The shown arguments of constants: their binders in the exported Dedukti
types without the #HIDE positions.   python3 scripts/arity.py c ..."""
import glob, os, re, sys
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'exporter', 'out')
hidden = {}
for f in glob.glob(OUT + '/*-hide.dkgf'):
    for l in open(f):
        w = l.split()
        if len(w) > 2 and w[0] == '#HIDE': hidden[w[1]] = set(map(int, w[2:]))
types = {}
for f in glob.glob(OUT + '/*.dk'):
    for l in open(f):
        m = re.match(r'(?:def )?(\S+) : (.*?)(?:\.|\s*:=)\s*$', l)
        if m: types.setdefault(m.group(1), m.group(2))
for c in sys.argv[1:]:
    t = types.get(c, '')
    bs = re.findall(r'\((\w+) : ', t)   # approximate: the named binders at any depth
    top = []
    d = 0; i = 0
    for m in re.finditer(r'[()]|\(\s*(\w+)\s*:', t):
        pass
    # top-level binders
    names, depth, j = [], 0, 0
    while j < len(t):
        if t[j] == '(':
            if depth == 0:
                m = re.match(r'\(\s*([\w\']+)\s*:', t[j:])
                if m: names.append(m.group(1))
            depth += 1
        elif t[j] == ')': depth -= 1
        elif depth == 0 and t[j:j+2] != '->' and not t[j].isspace() and t[j] not in '-<>': break
        j += 1
    shown = [n for k, n in enumerate(names, 1) if k not in hidden.get(c, set())]
    print('%s: shown %s  (hidden %s)' % (c, shown, sorted(hidden.get(c, []))))
