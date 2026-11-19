"""HTML pages of the informalized modules, in mathlib-informath's format
(build-html.py): one page per module in pages/, and index.html.

    python3 scripts/build-pages.py <index.json> ...
"""
import html, importlib.util, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..'))
MI = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
PROJECT = os.environ.get('NAVIER_STOKES', os.path.abspath(os.path.join(MI, '..', 'NavierStokesAndEuler')))
COMMIT = 'f9e8bc5b38b6e212696e8a30e3e91517af887bbd'
os.environ['MATHLIB'] = PROJECT
spec = importlib.util.spec_from_file_location('build_html', os.path.join(MI, 'build-html.py'))
bh = importlib.util.module_from_spec(spec)
argv = sys.argv; sys.argv = [argv[0]]
spec.loader.exec_module(bh)
sys.argv = argv
bh.MATHLIB = PROJECT
bh.GITHUB = 'https://github.com/openai/NavierStokesAndEuler/blob/%s/%s#L%d'

decls, macros = [], {}
for f in sys.argv[1:]:
    ix = json.load(open(f))
    decls += ix['declarations']
    macros.update(ix['macros'])
seen, uniq = set(), []
for d in decls:
    if d['lean'] not in seen:
        seen.add(d['lean']); uniq.append(d)
decls = uniq
mods = []
for d in decls:
    if d['module'] not in mods:
        mods.append(d['module'])
os.makedirs(os.path.join(ROOT, 'pages'), exist_ok=True)
langs = ['Eng']
page_of = lambda m: m.replace('.', '-') + '.html'
where = {d['lean']: page_of(d['module']) for d in decls}
for m in mods:
    ds = [d for d in decls if d['module'] == m]
    body = '\n'.join(bh.entry_html(d, langs, COMMIT, where) for d in ds)
    path = m.replace('.', '/') + '.lean'
    head = ('<p><a href="../index.html">NavierStokesAndEuler informalized</a></p><h1>%s</h1>'
            '<p><a href="https://github.com/openai/NavierStokesAndEuler/blob/%s/%s">%s</a>, %d declarations.</p>'
            % (html.escape(m), COMMIT, path, path, len(ds)))
    open(os.path.join(ROOT, 'pages', page_of(m)), 'w').write(bh.page(m + ' informalized', head, body, macros))
rows = ''.join('<li><a href="pages/%s">%s</a> (%d)</li>' % (page_of(m), html.escape(m), sum(1 for d in decls if d['module'] == m))
               for m in mods)
head = ('<h1>NavierStokesAndEuler informalized</h1>'
        '<p>The Lean statements of <a href="https://github.com/openai/NavierStokesAndEuler/tree/%s">'
        'openai/NavierStokesAndEuler</a> (commit <code>%s</code>), translated to Dedukti and read in English '
        'by <a href="https://github.com/GrammaticalFramework/informath">Informath</a>, with the symbol tables of '
        'mathlib-informath and of this project (<code>navier-stokes.dkgf</code>). '
        'See <a href="comparison.html">the comparison with "Navier-Stokes lost in translation"</a>.</p>'
        '<ul>%s</ul>' % (COMMIT, COMMIT[:7], rows))
open(os.path.join(ROOT, 'index.html'), 'w').write(bh.page('NavierStokesAndEuler informalized', head, '', macros))
print('%d declarations of %d modules -> index.html, pages/' % (len(decls), len(mods)))
