"""comparison.html: the examples of "Navier-Stokes lost in translation" (Bastounis, Circelli
et al.), each with the statement of OpenAI's paper and Informath's readings of
the Lean declarations it is compared with, and what the readings show.

    python3 scripts/build-comparison.py <index.json>

The facts about which declarations the main theorems use come from
exporter/checks/Uses.lean (lake env lean checks/Uses.lean in exporter/).
"""
import html, importlib.util, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..'))
MI = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
PROJECT = os.environ.get('NAVIER_STOKES', os.path.abspath(os.path.join(MI, '..', 'NavierStokesAndEuler')))
COMMIT = 'f9e8bc5b38b6e212696e8a30e3e91517af887bbd'
PAPER = 'https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf'
os.environ['MATHLIB'] = PROJECT
spec = importlib.util.spec_from_file_location('build_html', os.path.join(MI, 'build-html.py'))
bh = importlib.util.module_from_spec(spec)
argv = sys.argv; sys.argv = [argv[0]]
spec.loader.exec_module(bh)
sys.argv = argv
bh.MATHLIB = PROJECT
bh.GITHUB = 'https://github.com/openai/NavierStokesAndEuler/blob/%s/%s#L%d'

ix = json.load(open(sys.argv[1]))
decls = {d['lean']: d for d in ix['declarations']}
page_of = lambda m: 'pages/' + m.replace('.', '-') + '.html'
where = {n: page_of(d['module']) for n, d in decls.items()}


def entries(names):
    out = []
    for n in names:
        if n not in decls:
            sys.exit('not in the index: ' + n)
        out.append(bh.entry_html(decls[n], ['Eng'], COMMIT, where))
    return '\n'.join(out)


def paper(label, page, tex):
    return ('<div class="paper"><div class="src">OpenAI, <i>Finite time blowup for Navier&ndash;Stokes</i>, '
            '<a href="%s#page=%d">%s, p. %d</a></div>%s</div>' % (PAPER, page, label, page, tex))


S = []
S.append(('intro', 'The question', r"""
<p>Lean has checked every proof of <code>openai/NavierStokesAndEuler</code> (no <code>sorry</code>, only the
axioms <code>propext</code>, <code>Classical.choice</code>, <code>Quot.sound</code>). What Lean cannot check is
whether the statements say what they are meant to say. There are two such questions:</p>
<ol>
<li><b>Is the main theorem the intended one?</b> Do the theorem and the definitions it rests on state the Clay
problem, Fefferman's alternatives (C) and (D)? If they do, the result is proved, whatever the proofs look like.</li>
<li><b>Is the formalization the paper's argument?</b> Do the intermediate lemmas say what the paper's lemmas say?
This is what <i>Navier&ndash;Stokes lost in translation</i> doubts. It matters for trusting the paper, not the
theorem.</li>
</ol>
<p>Below, the Lean declarations are shown as Informath reads them: translated to Dedukti by the exporter of
mathlib-informath, and read in English and as formulas with Mathlib's symbol tables and a table of this
project's notions (<code>navier-stokes.dkgf</code>, {ENTRIES} entries, each citing its Lean definition; the other
notions are shown by their Lean names). No language model takes part in the readings: they are produced by a
grammar, and the same Lean always gives the same text.</p>
<p>Open <b>Lean</b> or <b>Dedukti</b> at an entry to see what the reading is made from; the name of an entry
links to its module page.</p>
"""))

S.append(('main', '1. The main theorem and its definitions', r"""
<p>The theorem of option (C), and the definitions it rests on, as Informath reads them. They come from Google
DeepMind's <i>Formal Conjectures</i> statement of the Clay problem, and Comparator checks that the submission
uses them unchanged. These are the declarations a reader has to check; the rest is checked by Lean.</p>
""" + entries([
    'NavierStokes.Comparator.navier_stokes_breakdown_R3',
    'NavierStokes.Comparator.NavierStokesExistenceAndSmoothness.mk',
    'NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn.mk',
    'NavierStokes.Comparator.InitialVelocityCondition.mk',
    'NavierStokes.Comparator.InitialVelocityConditionDecay.mk',
    'NavierStokes.Comparator.ForceCondition.mk',
    'NavierStokes.Comparator.ForceConditionDecay.mk',
    'NavierStokes.Comparator.divergence',
]) + r"""
<p class="note"><b>Reading.</b> A solution is a pair $(v, p)$ of smooth functions on
$\mathbb{R}^n \times [0, \infty)$ with $\partial_t v + (Dv)\,v = \nu \Delta v - \nabla p + f$,
$\operatorname{div} v = 0$ and $v(\cdot, 0) = u_0$, of bounded energy ($\int |v(x,t)|^2\,dx < E$ for all
$t \geq 0$). The data are smooth, divergence-free and decay with all derivatives faster than any power of
$1 + |x|$ (and of $1 + |x| + t$ for the force). The theorem says that for every $\nu > 0$ there are such data
with no such solution. This is Fefferman's (C), which can be checked against his statement without reading
Lean.</p>
"""))

S.append(('lemma86', '2. Lemma 8.6: m + 4 or m + 5 derivatives', paper('Lemma 8.6', 95, r"""
<p>Let $N=v_{t} \cdot \partial_{y}$ on $\mathbb{T}^{2}$, with $v_{t}$ as in (6.2), and let $F$ be a smooth
function of zero Haar mean. Then $N \varphi=F$ has a unique smooth zero-mean solution $\varphi=N^{-1} F$. This
solution is given by the following Fourier series and satisfies the displayed norm bound for every integer
$m \geq 0$:
$$N^{-1} F=\sum_{k \in \mathbb{Z}^{2} \backslash\{0\}} \frac{\widehat{F}(k)}{2 \pi i v_{t} \cdot k} e^{2 \pi i k
\cdot y}, \quad\left\|N^{-1} F\right\|_{C_{y}^{m}} \leq C_{m}\|F\|_{C_{y}^{m+4}} . \qquad (8.19)$$</p>
<p><i>Proof (beginning).</i> The divisor bound (6.7) gives $|v_t\cdot k|^{-1}\leq C(1+|k|)$. Four more
derivatives of $F$ than the requested output leave a summable $(1+|k|)^{-3}$ bound on the Fourier series in
two dimensions.</p>""") + r"""
<p>The article compares (8.19) with <code>norm_derivativeWord_inverse_le</code> and mentions
<code>inverse_finiteJets</code> and <code>mixedJet_inverse_bound</code>. Their readings, and the readings of
the lemma their proofs use and of the definitions in them:</p>
""" + entries([
    'NavierStokes.SmoothFamilyTorusInverse.inverse_finiteJets',
    'NavierStokes.SmoothFamilyTorusInverse.norm_derivativeWord_inverse_le',
    'NavierStokes.SmoothFourierData.coefficient_seminorm_bound',
    'NavierStokes.TorusInverse.inverseCoeff_seminorm_le',
    'NavierStokes.SmoothFamilyTorusInverse.JetBound',
    'NavierStokes.TorusInverse.coeffSeminorm',
    'NavierStokes.TorusInverse.weight',
]) + r"""
<p class="note"><b>What the readings show.</b></p>
<ul class="note">
<li>The discrepancy is visible in the readings without reading Lean: <code>inverse_finiteJets</code> reads
"if $\|f\|_{C^{n+5}(S \times \mathbb{R}^2)} \leq C$, then $\|N_d^{-1} f\|_{C^{n}(S \times \mathbb{R}^2)} \leq K
\times C$". That is (8.19) with $m + 5$ for $m + 4$, and with the norm of all derivatives, in the parameter
too, where the paper has the torus derivatives only.</li>
<li>The readings also show where the fifth derivative comes from. <code>coefficient_seminorm_bound</code>
bounds the weighted Fourier norm $\|\widehat{f}\|_{\ell^1_p}$ by $p + 4$ derivatives in each coordinate, summed
against $(1 + |k_1| + |k_2|)^{-4}$; inverting $N$ costs one weight more
(<code>inverseCoeff_seminorm_le</code>: $\|m_d a\|_{\ell^1_p} \leq 6 \|(2\pi i)^{-1}\| \|a\|_{\ell^1_{p+1}}$).
The paper sums $(1+|k|)^{-3}$, which converges in two dimensions too. So the exponent 4 is a choice of the
formalization, not a need.</li>
<li>Which of these the main theorem depends on is a question Lean answers exactly (the constants its proof
uses, transitively; <code>exporter/checks/Uses.lean</code>). Both main theorems use
<code>inverse_finiteJets</code> and <code>coefficient_seminorm_bound</code>. Neither uses
<code>norm_derivativeWord_inverse_le</code>, the lemma the article prints, or either
<code>mixedJet_inverse_bound</code>. The theorem is therefore proved with the weaker estimate (m + 5): what
Lean has verified is the paper's argument with this lemma weakened, and Lean has checked that the weaker
lemma suffices.</li>
</ul>
"""))

S.append(('flux', '3. The pressure flux (10.19)', paper('(10.19)', 123, r"""
<p>Since $\left|\nabla \chi_{R}\right| \leq C R^{-1} \varphi_{R}^{7}$, the two terms in (10.18) pair with
$C R^{-1} \varphi_{R}^{3}|w|$. Interpolation yields
$$\left\|\varphi_{R}^{3} w\right\|_{3} \leq\left\|\varphi_{R}^{2} w\right\|_{3} \leq B_{R}^{1 / 2}\|w\|_{2}^{1 /
2}, \quad\left\|\varphi_{R}^{3} w\right\|_{4} \leq B_{R}^{3 / 4}\|w\|_{2}^{1 / 4} .$$
Consequently
$$\left|\int \pi w \cdot \nabla \chi_{R}\right| \leq C_{T} R^{-1}\left[\left(B_{R}+1\right) B_{R}^{1 /
2}+R^{-3 / 4} B_{R}^{3 / 4}\right] . \qquad (10.19)$$</p>""") + r"""
<p>Here $\chi_R = \varphi_R^8$, $w = u - v$, $\pi = p - q$, and, in the article's notation,
$A_R = (\int \chi_R |\nabla w|^2)^{1/2}$ and $B_R = \|\varphi_R^4 w\|_{L^6}$. The Lean declaration the article
compares with, and the definitions in its statement:</p>
""" + entries([
    'NavierStokesR3.PressureFlux.exists_uniform_actual_pressure_flux_bound',
    'NavierStokesR3.Comparison.cutoffL6',
    'NavierStokesR3.Comparison.dissipationRoot',
    'NavierStokesR3.Comparison.comparisonLpNorm',
    'NavierStokesR3.ComparisonCutoffs.weight',
]) + r"""
<p class="note"><b>What the readings show.</b></p>
<ul class="note">
<li>With the entries for $\varphi_R$, $\chi_R$ and the two norms, the reading of the Lean statement is the
article's formula for it: the flux is at most
$\mathrm{CP} \times \bigl((B_R^{1/2} + 1)(A_R/R + 1/R^2) + R^{-7/4} B_R^{3/4}\bigr)$, for $R \geq 1$ and every
$t \in (0, T)$. The term $A_R/R$, which (10.19) does not have, is in plain sight.</li>
<li>The readings show the statements, not the arguments: that the Lean proof goes by H&ouml;lder with exponents
6 and 6/5 instead of the paper's $L^{3/2}$ bound is in the proof, which this sample does not read yet
(Section 5).</li>
<li>The main theorems use <code>exists_uniform_actual_pressure_flux_bound</code> (Lean's dependency check
again). So the uniqueness argument of Lemma 10.5 is verified with this bound, not with (10.19).</li>
</ul>
"""))

S.append(('answer', '4. Does symbolic informalization help?', r"""
<p>On this evidence, yes, in three ways:</p>
<ol>
<li><b>The statement.</b> The main theorem and its definitions read as a mathematician would write them
(Section 1). Whether the result is what it claims to be can be checked by someone who does not read Lean, on
about ten declarations instead of 641,000 lines.</li>
<li><b>The deviations.</b> Both of the article's examples are visible in the readings: $C^{n+5}$ against the
paper's $C^{m+4}$, and the term with $A_R$ against (10.19). Readers who put the readings beside the paper's
lemmas would find them without reading Lean. Because the readings are made by a grammar from the formal
statement, a deviation cannot be smoothed over by a fluent paraphrase, which is the risk of an informalization
by a language model.</li>
<li><b>Whether it matters.</b> The formal side answers questions that the text cannot: which lemmas the main
theorem actually uses. The lemma the article prints is not used; the ones that are used are proved with the
extra derivative and the extra term, and Lean has checked that the argument closes with them.</li>
</ol>
<p>What it does not do:</p>
<ul>
<li><b>Match lemmas to the paper.</b> The Lean code does not say which declaration formalizes which lemma of
the paper; the article had to find "the closest" one. The readings make the comparison possible, not
automatic.</li>
<li><b>Judge the deviations.</b> Whether $m + 5$ for $m + 4$ is harmless is a mathematical judgement.
Informalization shows the deviation; it does not weigh it.</li>
<li><b>Vouch for the symbol table.</b> A reading is as faithful as the symbol table it uses. The {ENTRIES} entries of
<code>navier-stokes.dkgf</code> were written for this sample, each from its Lean definition, which is
quoted beside it in the table; they too must be checked. That is a short list, against the whole
formalization.</li>
</ul>
"""))

S.append(('status', '5. What this sample covers', r"""
<p>{MODULES} modules of the 2,659: the definitions and main theorems of the Navier&ndash;Stokes and Euler
Comparator challenges, and the modules of the article's two examples, {DECLS} declarations in all
(<a href="index.html">module pages</a>). Their statements are all read, in English and as formulas; {RAW} of
them still show some Mathlib or project notion by its Lean name. The proofs are not read: most of them are
tactic proofs, which mathlib-informath's tactic replay could give, to compare arguments as well as
statements.</p>
<p>Built with: mathlib-informath's <code>Export.lean</code> (on Lean 4.34.0-rc2 and the project's Mathlib),
extended to name partial and over-applied functions, $\mathbb{R}^n$ and pointwise operations on functions;
Informath, with a fix to the definienda of constants with hidden arguments; and mathlib-informath's
<code>build-html.py</code>.</p>
"""))

STYLE = """<style>
.paper{border-left:4px solid #b08a3e;background:#fbf7ee;padding:.5em 1em;margin:1em 0}
.paper .src{font-size:85%;color:#7a5c1e;margin-bottom:.3em}
.note{background:#eef4fb;padding:.3em 1em;margin:.6em 0}
ul.note{padding-left:2.2em}
nav.toc a{margin-right:1em}
</style>"""
toc = '<nav class="toc">' + ''.join('<a href="#%s">%s</a>' % (k, html.escape(t)) for k, t, _ in S) + '</nav>'
head = ('<p><a href="index.html">NavierStokesAndEuler informalized</a></p>'
        '<h1>Navier&ndash;Stokes, lost in translation? Read by Informath</h1>' + toc)
body = ''.join('<h2 id="%s">%s</h2>%s' % (k, html.escape(t), b) for k, t, b in S)
# the counts, from the table and the index
import re
table = open(os.path.join(ROOT, 'navier-stokes.dkgf')).read()
counts = {'ENTRIES': len(re.findall(r'^[A-Za-z_][A-Za-z0-9_]* : ', table, re.M)),
          'DECLS': len(ix['declarations']),
          'MODULES': len({d['module'] for d in ix['declarations']}),
          'RAW': sum(1 for d in ix['declarations']
                     if re.search(r'\\mathrm\{[A-Za-z0-9]+\\_\\_', d['readings'].get('Eng') or ''))}
for k, v in counts.items():
    body = body.replace('{%s}' % k, str(v))
open(os.path.join(ROOT, 'comparison.html'), 'w').write(
    bh.page('Navier-Stokes lost in translation? Read by Informath', STYLE + head, body, ix['macros']))
print('comparison.html')
