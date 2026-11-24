"""HTML pages of the informalized modules, in mathlib-informath's format
(build-html.py): one page per module in pages/, and index.html.

    python3 scripts/build-pages.py <index.json> ...
"""
import html, importlib.util, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..'))
MI = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
PROJECT = os.environ.get('RIEMANN', os.path.abspath(os.path.join(MI, '..', 'riemann-hypothesis-original')))
COMMIT = 'e4ed6533e67aaf71e918c97ccf1ed4d5458a0b23'
REPO = 'https://github.com/homeowmorphism/riemann-hypothesis-original'
TITLE = 'The Riemann hypothesis submission informalized'
os.environ['MATHLIB'] = os.path.join(PROJECT, 'src')
sys.path.insert(0, MI)                  # build-html.py imports worded.py beside it
spec = importlib.util.spec_from_file_location('build_html', os.path.join(MI, 'build-html.py'))
bh = importlib.util.module_from_spec(spec)
argv = sys.argv; sys.argv = [argv[0]]
spec.loader.exec_module(bh)
sys.argv = argv
bh.MATHLIB = os.path.join(PROJECT, 'src')
bh.GITHUB = REPO + '/blob/%s/src/%s#L%d'

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


def used(text):
    """The macros that a page uses, with the macros that theirs use: one page
    with all the macros of the 2,500 readings would be 300 KB of them."""
    import re
    seen, todo = {}, set(re.findall(r'\\([A-Za-z]+)', text))
    while todo:
        n = todo.pop()
        if n in macros and n not in seen:
            seen[n] = macros[n]
            todo |= set(re.findall(r'\\([A-Za-z]+)', json.dumps(macros[n]).replace('\\\\', '\\')))
    return seen


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
    head = ('<p><a href="../index.html">%s</a></p><h1>%s</h1>'
            '<p><a href="%s/blob/%s/src/%s">src/%s</a>, %d declarations.</p>'
            % (TITLE, html.escape(m), REPO, COMMIT, path, path, len(ds)))
    open(os.path.join(ROOT, 'pages', page_of(m)), 'w').write(bh.page(m + ' informalized', head, body, used(head + body)))

# the index: the modules in groups, from the claims down to the notions
P = 'Development.AutomorphicArithmetic.'
GROUPS = [
    ('The claims',
     'The five theorems as <code>Challenge.lean</code> states them, importing only Mathlib. '
     'Comparator checks that <code>Main.lean</code> proves exactly these statements.',
     ['Challenge']),
    ('From the claims to the statement of the proof',
     'All five follow from <code>UpperTheory.EveryCharacter</code>: no Dirichlet L-function vanishes for '
     'Re s &gt; 1/2, except L(1, s) at s = 1 (<code>Supplements/Kernels/MainTheorems.lean</code>). '
     '<code>Claim.HalfPlane</code> is the same statement under another name.',
     [P + 'CharacterBoxes.HalfPlane', 'Formalism.GammaFactorNonvanishing.RhOfRight',
      'Formalism.GammaFactorNonvanishing.CritLine', P + 'CharacterBoxes.EveryCharacter']),
    ('The hypotheses of the last step',
     'The proof derives <code>EveryCharacter</code> from three propositions, each proved elsewhere in the '
     'submission (<code>CharacterBoxes/MainConclusion.lean</code>): <code>Row0b</code> of <code>IsRecT</code> '
     '(Galois representations attached to the regular algebraic polarized cusp representations of GL_a over '
     'CM fields, with local-global compatibility), <code>RecTExists</code> (a local Langlands correspondence '
     'with given laws at every place of every number field) and <code>VWin</code> (a bound on the lengths of '
     'the Tate-Shafarevich groups of the twists Q_l/Z_l(e) over subfields of cyclotomic fields), which the proof derives from <code>Row0b</code>.',
     [P + 'CharacterBoxes.ExistsPageN', P + 'Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis',
      P + 'Foundations.LocalLanglands.IsRecTOfIsRec', P + 'Foundations.UnitarySphericalFixing.SatakeParameters.RecT']),
]
grouped = [m for _, _, ms in GROUPS for m in ms]
GROUPS.append(('The notions these use',
               'The modules that declare the notions of the definitions above, one level down.',
               [m for m in mods if m not in grouped]))
count = lambda m: sum(1 for d in decls if d['module'] == m)
sections = ''.join(
    '<h2>%s</h2><p>%s</p><ul>%s</ul>' % (t, txt, ''.join(
        '<li><a href="pages/%s">%s</a> (%d)</li>' % (page_of(m), html.escape(m), count(m)) for m in ms if m in mods))
    for t, txt, ms in GROUPS)
skipped = os.path.join(ROOT, 'work', 'skipped.txt')
left = ['GlobalTwisting.APerTw (<code>GlobalTheory.Fc.Hyps</code>)', 'GlobalTwisting.DRS (<code>GlobalTheory.Fc.DRS</code>)']
head = ('<h1>%s</h1>'
        '<p>Levent Alp\u00f6ge\'s Lean submission claiming proofs of the Riemann hypothesis and of the '
        'generalized Riemann hypothesis for Dirichlet L-functions, as preserved in '
        '<a href="%s/tree/%s">riemann-hypothesis-original</a> (commit <code>%s</code>). '
        'Its definitions and theorem statements are translated to Dedukti and read in English '
        'by <a href="https://github.com/GrammaticalFramework/informath">Informath</a>, with the symbol tables of '
        'mathlib-informath and of this example (<code>riemann.dkgf</code>). '
        'The proofs are not read. The submission has 175,187 modules and about a million declarations: '
        'these are %d declarations of the %d modules at the top of the proof. '
        'See <a href="comparison.html">the comparison with the announcement</a>: the claims, the statement the proof proves, and its last step.</p>'
        '<p>Two modules of the notions are left out, because the exporter does not finish them: '
        'Development.AbelianVarietyTheory.Definitions.%s. '
        'They declare the 50-field structure of hypotheses that <code>plugWin</code> takes and one of its parameters.</p>'
        '%s' % (TITLE, REPO, COMMIT, COMMIT[:7], len(decls), len(mods), ' and '.join(left), sections))
open(os.path.join(ROOT, 'index.html'), 'w').write(bh.page(TITLE, head, '', used(head)))
print('%d declarations of %d modules -> index.html, pages/' % (len(decls), len(mods)))
