"""comparison.html: the claims and the top of the proof of the Riemann hypothesis
submission, as Informath reads them, beside Alpöge's announcement and the
standard statements, and what the readings show.

    python3 scripts/build-comparison.py <index.json>

Which declarations the proof uses is read from the Lean sources
(Supplements/Kernels/MainTheorems.lean, CharacterBoxes/MainConclusion.lean,
VwinOfRow.lean, RowSrc.lean, RecTExists.lean), cited in the text.
"""
import html, importlib.util, json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..'))
MI = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
PROJECT = os.environ.get('RIEMANN', os.path.abspath(os.path.join(MI, '..', 'riemann-hypothesis-original')))
COMMIT = 'e4ed6533e67aaf71e918c97ccf1ed4d5458a0b23'
REPO = 'https://github.com/homeowmorphism/riemann-hypothesis-original'
SRC = REPO + '/blob/' + COMMIT + '/src/'
REMARK = 'https://alpo.ge/remark.pdf'
os.environ['MATHLIB'] = os.path.join(PROJECT, 'src')
sys.path.insert(0, MI)
spec = importlib.util.spec_from_file_location('build_html', os.path.join(MI, 'build-html.py'))
bh = importlib.util.module_from_spec(spec)
argv = sys.argv; sys.argv = [argv[0]]
spec.loader.exec_module(bh)
sys.argv = argv
bh.MATHLIB = os.path.join(PROJECT, 'src')
bh.GITHUB = REPO + '/blob/%s/src/%s#L%d'

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


def src(path, text=None):
    return '<a href="%s%s"><code>%s</code></a>' % (SRC, path, html.escape(text or path.split('/')[-1]))


def remark(page, tex, label=None):
    return ('<div class="paper"><div class="src">L. Alp&ouml;ge, <i>announcement</i>, '
            '<a href="%s#page=%d">%sp. %d</a></div>%s</div>' % (REMARK, page, label + ', ' if label else '', page, tex))


def lean(code, path):
    return ('<div class="leansrc"><div class="src">%s</div><pre>%s</pre></div>'
            % (src(path, path), html.escape(code.strip('\n'))))


S = []
S.append(('intro', 'The question', r"""
<p>The submission claims the Riemann hypothesis and the generalized Riemann hypothesis for Dirichlet
L-functions, with a Lean proof of 175,187 modules and about a million declarations, without comments. There is
no paper: the announcement says "It being obviously inappropriate to attempt to post some massive unreadable
travesty of "slop", I decided to only present Lean" (p. 2). Comparator checks that the proof uses only the
standard axioms and that the five theorems are those of <code>Challenge.lean</code>. What Lean cannot check is
whether those statements say what they are meant to say, and, for understanding the proof, what its parts
state. With no paper, the questions are:</p>
<ol>
<li><b>Are the claims the Riemann hypothesis and GRH?</b> If they are, the result is proved, whatever the
proof looks like (Section 1).</li>
<li><b>What does the proof rest on?</b> The step from the claims down to the statement that the proof
proves (Section 2), and the three propositions from which the proof's last step derives it (Sections 3 and 4).
These are where a reader can start to understand the argument, and to compare it with the announcement's
outline and with the literature.</li>
</ol>
<p>Below, the Lean declarations are shown as Informath reads them: translated to Dedukti by the exporter of
mathlib-informath, and read in English and as formulas with Mathlib's symbol tables and a table of this
submission's notions (<code>riemann.dkgf</code>, {ENTRIES} entries, each citing its Lean definition; the other
notions are shown by their Lean names). No language model takes part in the readings: they are produced by a
grammar, and the same Lean always gives the same text.</p>
<p>Open <b>Lean</b> or <b>Dedukti</b> at an entry to see what the reading is made from; the name of an entry
links to its module page.</p>
"""))

S.append(('claims', '1. The claims', remark(1, r"""
<p>I believe I have, working with Claude, discovered a proof of the Riemann Hypothesis. In fact, the method
easily extends much further, resolving the so-called Generalized Riemann Hypothesis [&hellip;] Claude and I have
also formalized the arguments without assumptions.</p>""") + r"""
<p>The five theorems as <code>Challenge.lean</code> states them, importing only Mathlib (Comparator checks
that <code>Main.lean</code> proves exactly these):</p>
""" + entries([
    'riemannHypothesis', 'RiemannZetaZerosOnLine', 'riemannZeta_eq_zero_re',
    'DirichletLNonvanishingRightOfHalf', 'LFunction_ne_zero_of_half_lt_re',
    'DirichletLZerosOnLine', 'LFunction_eq_zero_re',
    'PrimitiveDirichletLZerosOnLine', 'LFunction_eq_zero_re_of_isPrimitive',
]) + r"""
<p class="note"><b>Reading.</b> The five theorems state their propositions by name only
(<code>RiemannHypothesis</code>, <code>RiemannZetaZerosOnLine</code>, &hellip;); their statements are read
with these definitions unfolded, and the unfolded Lean is shown beside the source (<code>#UNFOLD_STATEMENT</code>
of the exporter). The first is Mathlib's <code>RiemannHypothesis</code>, and the second states the same
proposition word for word: every zero $s$ of $\zeta$ that is not $-2(n+1)$ and not $1$ has real part
$\frac12$. The exception $s = 1$ is there because
Mathlib's $\zeta$ has a value at its pole. The other three are GRH for Dirichlet L-functions: for every
modulus $N$ and every Dirichlet character $\chi$ modulo $N$, imprimitive ones included,
$L(\chi, s) \neq 0$ for $\operatorname{Re} s > \frac12$ (except $\chi = 1$ at $s = 1$), and the zeros with
$0 < \operatorname{Re} s < 1$ are on the line $\frac12$. These are the standard statements, readable without
Lean; the remarks of the submission's own
<a href="%sverification/NOTES.md#statements">verification notes</a> (trivial zeros, $s = 1$, imprimitive
characters, real $\frac12$) can all be checked on the readings. The announcement's "Extended Riemann
Hypothesis" (for Dedekind zeta functions) is not claimed.</p>
""".replace('%s', REPO + '/blob/' + COMMIT + '/')))

S.append(('statement', '2. The statement the proof proves', r"""
<p>All five theorems are derived, by the functional equation and Mathlib's lemmas, from one statement,
<code>UpperTheory.EveryCharacter</code>
(""" + src('Supplements/Kernels/MainTheorems.lean') + r"""):</p>
""" + lean("""
theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter
theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi
theorem critAll ... := Formalism.VW.critLine allChi N χ hχ s h0 h1 hz
""", 'Supplements/Kernels/MainTheorems.lean') + entries([
    'UpperTheory.EveryCharacter', 'Formalism.VW.rh_of_right', 'Formalism.VW.critLine',
]) + r"""
<p class="note"><b>Reading.</b> <code>EveryCharacter</code> is the half-plane statement: no Dirichlet
L-function vanishes for $\operatorname{Re} s > \frac12$, except $L(1, s)$ at $s = 1$. It is the same
proposition as <code>DirichletLNonvanishingRightOfHalf</code> of the claims (and as
<code>Claim.HalfPlane</code>), word for word in the readings. <code>rh_of_right</code> and
<code>critLine</code> are the standard steps from it: RH from the non-vanishing of $\zeta$ to the right of
$\frac12$, and the zeros in the strip from the functional equation of a primitive character. So everything
rests on <code>EveryCharacter</code>, which is GRH itself in its half-plane form: the reduction does not
weaken the problem, and the whole weight is in the proof of <code>EveryCharacter</code>.</p>
"""))

S.append(('laststep', '3. The last step: Galois representations and local Langlands', lean("""
theorem UpperTheory.FinalTheorems.everyCharacter_of_row
    (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) : UpperTheory.EveryCharacter :=
  UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin
    ⟨h, UpperTheory.Zero.LLC.recTExists, h⟩ (UpperTheory.One.vwin_of_row h)

theorem UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter :=
  UpperTheory.FinalTheorems.everyCharacter_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
""", 'Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean') + r"""
<p>The last step derives <code>EveryCharacter</code> from three propositions: <code>Row0b</code> of
<code>IsRecT</code>, <code>RecTExists</code> and <code>VWin</code>, the last of which the proof derives from
the first (""" + src('Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean', 'VwinOfRow.lean') + r"""). The structure
that bundles the first two is called <code>OpenLiteratureStatements</code>, and the theorem
<code>every_character_of_literature_of_vWin</code>: they stand for results of the literature, but the
submission proves them (<code>galoisLocalGlobalStrong_recParameter</code>,
""" + src('Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean', 'RowSrc.lean') + r""";
<code>recTExists</code>, """ + src('Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean', 'RecTExists.lean') + r"""),
as the announcement's "without assumptions" says. The announcement does not mention them.</p>
<h3>Row0b: Galois representations of polarized cusp representations</h3>
""" + entries([
    'UpperTheory.GalStar.Row0b', 'GlobalTheory.ContraPair.PolarizedPair.mk', 'GlobalTheory.CuspRep.CG.IsRegAlg',
    'UpperTheory.GalStar.PropsB.mk',
]) + r"""
<p class="note"><b>Reading.</b> <code>Row0b</code> says: for every CM field $E$, prime $l$, isomorphism
$\iota : \overline{\mathbb{Q}}_l \cong \mathbb{C}$ and $a \geq 1$, every cusp representation $\pi$ of
degree $a$ over $E$ that is regular algebraic and has a polarization $\chi$ (a Hecke character of $E^+$
with the sign $(-1)^a$ at the infinite places, such that the twist of $\pi$ by $(\chi \circ \mathrm{N})^{-1}$
is paired with $\pi$ through complex conjugation: <code>DualIsConjBy</code>) has a continuous
semisimple Galois representation $r : \mathrm{Gal}(\overline{E}/E) \to \mathrm{GL}_a(\overline{\mathbb{Q}}_l)$
with Hodge&ndash;Tate weights given by the infinitesimal character, and compatible with the local components
of $\pi$ through the local correspondence <code>Rc</code> (<code>PropsB</code>: <code>away</code> at the
places not above $l$, <code>above</code> crystalline and de Rham at the places above $l$). This is the shape
of the theorems of Harris&ndash;Taylor, Shin, Chenevier&ndash;Harris and Caraiani on the Galois
representations of regular algebraic polarized cuspidal representations, with a weakened local-global
compatibility (<code>AwayB</code>, <code>AboveB</code>: only in the cases listed there). That this is what
the definitions say is visible in the readings; that the submission proves it, inside Lean, is a claim of
the size of that literature.</p>
<h3>RecTExists: a local Langlands correspondence</h3>
""" + entries([
    'UpperTheory.Zero.LLC.RecTExists', 'UpperTheory.Zero.LLC.IsRecT', 'UpperTheory.Zero.LLC.LawsT.mk',
]) + r"""
<p class="note"><b>Reading.</b> <code>RecTExists</code> says that at every finite place $w$ of every number
field there is a map <code>rc</code> from the irreducible smooth representations of the groups
$\mathrm{GL}_n(E_w)$ to Weil&ndash;Deligne representations satisfying the laws of <code>LawsT</code>: dimension,
characters by local class field theory (a local Artin map), the Langlands classification by segments,
cuspidal to irreducible, twists, central characters, duals, injectivity, depth zero to tame, and the type law
(<code>TypeLaw</code>: the tame cuspidal types match Green's characters of $\mathrm{GL}_n(\mathbb{F}_q)$).
This is the local Langlands correspondence for $\mathrm{GL}_n$ (Harris&ndash;Taylor, Henniart, Scholze), with
part of its characterization. The readings also show how much is required: twists, central characters, duals,
injectivity and depth are required only for the "good" representations (<code>Good</code>,
<code>GoodCusp</code>: those whose cuspidal support consists of characters, or, when $E_w \cong
\mathbb{Q}_g$, of twists of depth-zero cuspidal representations), and only the dimension, the characters, the
classification by segments, irreducibility of cuspidals, unramified twists and the absolute value of the
central character for all of them.</p>
"""))

S.append(('vwin', '4. VWin and the announcement\'s step 17', remark(4, r"""
<p>17. 11/15/26: for the classes in $H^1\bigl(\mathfrak{o}_E[\frac1\ell], \mathbb{Q}_\ell/\mathbb{Z}_\ell(-e)\bigr)$
that we couldn't kill by twisting, fight for a significant weakening of Vandiver.<sup>6</sup></p>
<p>19. 10/19/26: precise choice of the Iwasawa tower, specifically using Behrend!!</p>
<p><sup>6</sup>This is still pretty strong!! I believe vanishing of a number of K-groups of $\mathbb{Z}$
follows [&hellip;]</p>""", 'timeline') + r"""
<p>The third proposition of the last step, and the definitions it rests on:</p>
""" + entries([
    'UpperTheory.Top.VWin', 'UpperTheory.Top.VWinAt', 'UpperTheory.Top.VAt', 'UpperTheory.Top.VVle',
    'Formalism.GaloisCohomology.shaLen', 'Formalism.GaloisCohomology.qzTw',
    'UpperTheory.Top.IsChiField', 'UpperTheory.Top.WinPair.mk', 'UpperTheory.Top.PageN',
]) + r"""
<p class="note"><b>What the readings show.</b></p>
<ul class="note">
<li><b>Step 17 is <code>VVle</code>.</b> <code>shaLen</code> is the $\mathbb{Z}_l$-length of the
Tate&ndash;Shafarevich group <code>Sha</code> of $H^1$ of $\mathbb{Q}_l/\mathbb{Z}_l$ twisted by
$\chi_{\mathrm{cyc}}^{-e}$ (<code>qzTw</code>), unramified outside $l$: the announcement's
$H^1(\mathfrak{o}_E[\frac1\ell], \mathbb{Q}_\ell/\mathbb{Z}_\ell(-e))$, with the same sign of the twist.
<code>VVle E t B</code> says that these lengths are finite for $0 < e < t$ and that
$\sum_{l \in S} \log l \sum_{1 \leq e < t} \operatorname{len} Ш^1(E, \mathbb{Q}_l/\mathbb{Z}_l(-e)) \leq B$ for
every finite set $S$ of primes. The announcement calls this a weakening of Vandiver's conjecture (that $p$ does not divide
the class number of $\mathbb{Q}(\zeta_p)^+$): in the Lean statement the classes are not required to vanish,
but their lengths are bounded, weighted by $\log l$ and summed over the primes and twists.</li>
<li><b>Step 19 is <code>IsChiField</code>.</b> The fields $E$ are subfields of cyclotomic fields:
$E \subseteq \mathbb{Q}(\zeta_N)$ is the field fixed by the $a$ with $a \equiv \pm 1 \pmod{2^{e+2}}$,
$\psi(a) = 1$ and the Jacobi symbols $(\frac{a}{q}) = (\frac{a}{d}) = 1$, that is the $e$-th layer of the
cyclotomic $\mathbb{Z}_2$-tower joined with the field of the character $\psi$ and two quadratic fields. The
tower is the announcement's "Iwasawa tower". The primes of <code>WinPair</code> are $q \equiv 3 \pmod 8$ with
$\log q \in (\frac12 Y^{\varepsilon/5}, Y^{\varepsilon/5}]$ and $d \equiv 7 \pmod{16}$ with
$\log d \in (\frac12 Y^{\varepsilon/5} \log^2 Y, Y^{\varepsilon/5} \log^2 Y]$, such that $q$ and every odd
prime up to $Y^{\varepsilon/5}$ divide $d + 1$; whether this is the announcement's "Behrend" is not visible in the
statements.</li>
<li><b>The bound.</b> <code>VWin</code> asks, for every primitive character $\psi$ and $\varepsilon <
\frac1{52}$, for $x$ in a window $[Y, Y^2]$ and $2^e \approx x^{2 + 8\varepsilon}$ (<code>PageN</code>), the
bound <code>VVle</code> with $t = \lfloor x^{401} \rfloor$ and $B = \sqrt{\exp(x^{\varepsilon})}$. These
constants (401, 52, the windows) are in the readings, and in no text of the announcement.</li>
<li><b>Its status.</b> <code>VWin</code> is not a theorem of the literature: it is a new arithmetic input,
which the proof derives from <code>Row0b</code> (<code>vwin_of_row</code>). The derivation is in the modules
below <code>VwinOfRow.lean</code>, whose closure is most of the submission; this sample does not read
them.</li>
</ul>
"""))

S.append(('answer', '5. Does symbolic informalization help?', r"""
<p>On this sample, in the same three ways as for <a href="../navier-stokes/comparison.html">Navier&ndash;Stokes</a>,
but with a different weight, since here there is no paper to compare with:</p>
<ol>
<li><b>The statement.</b> The five claims read as RH and GRH for Dirichlet L-functions (Section 1), and the
statement the proof proves is GRH in its half-plane form (Section 2). This can be checked by someone who does
not read Lean, on a dozen declarations.</li>
<li><b>The structure of the proof.</b> The proof rests on three propositions whose readings make them
recognizable: two theorems of the shape of the literature on Galois representations and local Langlands, and
a new bound on Tate&ndash;Shafarevich groups over a cyclotomic tower (Sections 3, 4). That is the outline a
mathematician would want first, and the announcement does not give it in these terms. Its step 17 is
identified with a Lean definition, and the details (twist, fields, windows, constants) are read from it.</li>
<li><b>Exactness.</b> Because the readings are made by a grammar from the formal statements, they cannot
smooth over a condition or a constant, which matters here more than anywhere: the announcement's own
summaries are, in its words, "a 'slop' summary, which might make zero sense".</li>
</ol>
<p>What it does not do:</p>
<ul>
<li><b>Read the argument.</b> The proofs, and the 175,000 modules below this sample, are not read; whether
the derivation of <code>VWin</code> from <code>Row0b</code> is an argument a mathematician can follow is
not touched. Lean and its independent kernels are what check it.</li>
<li><b>Name the literature.</b> That <code>Row0b</code> has the shape of the theorems of Harris&ndash;Taylor,
Chenevier&ndash;Harris and Caraiani is a mathematician's identification, made here by reading; the code names
them only as "literature".</li>
<li><b>Vouch for the symbol table.</b> A reading is as faithful as its table. The {ENTRIES} entries of
<code>riemann.dkgf</code> were written for this sample from the Lean definitions, which they cite, since the
source has no comments; they too must be checked.</li>
</ul>
"""))

S.append(('status', '6. What this sample covers', r"""
<p>{MODULES} modules of the 175,187: the claims, the step to <code>EveryCharacter</code>, the modules of
the last step's hypotheses and one level of the modules declaring their notions, {DECLS} declarations in all
(<a href="index.html">module pages</a>). Their statements are all read, in English and as formulas; {RAW} of
them still show some notion by its Lean name. The modules <code>GlobalTwisting.APerTw</code> and
<code>.DRS</code> (the 50 hypotheses of <code>GlobalTheory.Fc.Hyps</code>) are left out, because the
exporter does not finish them. The announcement is <a href="%s">remark.pdf</a> (sha256 3fc97784&hellip;,
as in the submission's notes).</p>
""".replace('%s', REMARK)))

STYLE = """<style>
.paper{border-left:4px solid #b08a3e;background:#fbf7ee;padding:.5em 1em;margin:1em 0}
.paper .src,.leansrc .src{font-size:85%;color:#7a5c1e;margin-bottom:.3em}
.leansrc{border-left:4px solid #8a9bb8;background:#f6f8fb;padding:.5em 1em;margin:1em 0}
.leansrc pre{margin:0;font-size:85%;white-space:pre-wrap}
.note{background:#eef4fb;padding:.3em 1em;margin:.6em 0}
ul.note{padding-left:2.2em}
nav.toc a{margin-right:1em}
</style>"""
toc = '<nav class="toc">' + ''.join('<a href="#%s">%s</a>' % (k, html.escape(t)) for k, t, _ in S) + '</nav>'
head = ('<p><a href="index.html">The Riemann hypothesis submission informalized</a></p>'
        '<h1>The Riemann hypothesis submission, read by Informath</h1>' + toc)
body = ''.join('<h2 id="%s">%s</h2>%s' % (k, html.escape(t), b) for k, t, b in S)
table = open(os.path.join(ROOT, 'riemann.dkgf')).read()
counts = {'ENTRIES': len(re.findall(r'^[A-Za-z_][A-Za-z0-9_]* : ', table, re.M)),
          'DECLS': len(ix['declarations']),
          'MODULES': len({d['module'] for d in ix['declarations']}),
          'RAW': sum(1 for d in ix['declarations']
                     if re.search(r'\\mathrm\{[A-Za-z0-9]+(\\_)+[A-Za-z0-9_\\]+\}', d['readings'].get('Eng') or ''))}
for k, v in counts.items():
    body = body.replace('{%s}' % k, str(v))


def used(text):
    seen, todo = {}, set(re.findall(r'\\([A-Za-z]+)', text))
    while todo:
        n = todo.pop()
        if n in ix['macros'] and n not in seen:
            seen[n] = ix['macros'][n]
            todo |= set(re.findall(r'\\([A-Za-z]+)', json.dumps(ix['macros'][n]).replace('\\\\', '\\')))
    return seen


open(os.path.join(ROOT, 'comparison.html'), 'w').write(
    bh.page('The Riemann hypothesis submission, read by Informath', STYLE + head, body, used(head + body)))
print('comparison.html')
