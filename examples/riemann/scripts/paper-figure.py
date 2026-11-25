"""The two claims of comparison.html as a page for Figure 9 of the paper
(~/papers/mathlib/riemann-claims.pdf): python3 scripts/paper-figure.py fig.html,
then Chrome --headless --print-to-pdf (the page size is in the @page rule)
(Lean, Lean unfolded, English, Formula; without the Dedukti row)."""
import importlib.util, json, os, re, sys
EX = os.path.expanduser('~/claude/mathlib-informath/examples/riemann')
MI = os.path.dirname(os.path.dirname(EX))
PROJECT = os.path.expanduser('~/claude/riemann-hypothesis-original')
os.environ['MATHLIB'] = os.path.join(PROJECT, 'src')
sys.path.insert(0, MI)
spec = importlib.util.spec_from_file_location('build_html', os.path.join(MI, 'build-html.py'))
bh = importlib.util.module_from_spec(spec); argv = sys.argv; sys.argv = [argv[0]]; spec.loader.exec_module(bh); sys.argv = argv
bh.MATHLIB = os.path.join(PROJECT, 'src')
bh.GITHUB = 'https://github.com/homeowmorphism/riemann-hypothesis-original/blob/%s/src/%s#L%d'
ix = json.load(open(os.path.join(EX, 'work', 'index.json')))
d = {x['lean']: x for x in ix['declarations']}
names = ['riemannHypothesis', 'LFunction_eq_zero_re_of_isPrimitive']
body = '\n'.join(bh.entry_html(d[n], ['Eng'], 'e4ed6533e67aaf71e918c97ccf1ed4d5458a0b23', {}) for n in names)
body = re.sub(r'<div class="row"><div class=lab>Dedukti</div>.*?</details></div></div>', '', body, flags=re.S)
macros = ix['macros']
def used(text):
    seen, todo = {}, set(re.findall(r'\\([A-Za-z]+)', text))
    while todo:
        n = todo.pop()
        if n in macros and n not in seen:
            seen[n] = macros[n]; todo |= set(re.findall(r'\\([A-Za-z]+)', json.dumps(macros[n]).replace('\\\\', '\\')))
    return seen
css = ('<style>@page{size:228mm 120mm;margin:0} header{display:none} '
       'body{margin:0;padding:3mm 4mm;max-width:none} .entry{padding:.5rem 0} '
       '.entry:last-of-type{border-bottom:none} .doc{display:none} mjx-container{font-size:90% !important}</style>')
open(sys.argv[1], 'w').write(bh.page('Figure 9', css, body, used(body)))
