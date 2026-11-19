"""Print readings with the index's macros expanded (for checking without MathJax).
    python3 scripts/expand.py index.json name ..."""
import json, re, sys
ix = json.load(open(sys.argv[1]))
M = ix['macros']
def args(s, i, n):
    out = []
    for _ in range(n):
        while i < len(s) and s[i] == ' ': i += 1
        if i < len(s) and s[i] == '{':
            d, j = 0, i
            while True:
                d += {'{': 1, '}': -1}.get(s[j], 0)
                if d == 0: break
                j += 1
            out.append(s[i+1:j]); i = j + 1
        else:
            out.append(s[i] if i < len(s) else ''); i += 1
    return out, i
def expand(s):
    for _ in range(2000):
        m = re.search(r'\\([A-Za-z]+MACRo[A-Za-z]+)', s)
        if not m: return s
        d = M.get(m.group(1))
        body, n = (d[0], d[1]) if isinstance(d, list) else (d or m.group(1), 0)
        a, e = args(s, m.end(), n)
        for k, x in enumerate(a): body = body.replace('#%d' % (k+1), x)
        s = s[:m.start()] + body + s[e:]
    return s
for x in ix['declarations']:
    if x['lean'].split('.')[-1] in sys.argv[2:] or x['lean'] in sys.argv[2:]:
        print('##', x['lean']); print(expand(x['readings']['Eng'])); print()
