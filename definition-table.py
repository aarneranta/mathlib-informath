#!/usr/bin/env python3
"""A verbal symbol table for all of Mathlib's definitions, in English.

    lake exe export --definitions          # -> out/definitions.jsonl
    python3 definition-table.py            # -> definitions.dkgf, out/definition-table.tsv
    python3 definition-table.py -lexicon   # also new words in Informath's Mathlib.gf, MathlibEng.gf

For each definition of out/definitions.jsonl (a def, structure, class, field
or inductive type of Mathlib, but not a theorem, an instance or a tactic)
that mathlib.dkgf and mapping.tsv do not cover, candidate wordings are made
from its docstring (by the patterns of suggest-entries.py) and from its name,
split at its capitals with Mathlib's abbreviations spelled out
(Nat.minFac: "the minimal factor of #1", IsPrimePow: "#1 is a prime power").
All candidates are parsed in one call of RunInformath -parse-example; the
first one whose parse has the constant's category (Exp, Kind or Prop) and its
number of arguments is its entry in definitions.dkgf.  out/definition-table.tsv
has every constant with its candidates, and the words of the candidates that
the grammar does not know, which out/unknown-words.tsv counts.
"""
import collections, importlib.util, json, os, re, subprocess, sys

spec = importlib.util.spec_from_file_location('suggest', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'suggest-entries.py'))
suggest = importlib.util.module_from_spec(spec)
spec.loader.exec_module(suggest)
RUN = suggest.RUN

# the parts of Mathlib that define no mathematical concepts
SKIP_MODULES = ('Mathlib.Tactic', 'Mathlib.Lean', 'Mathlib.Util', 'Mathlib.Testing', 'Mathlib.Deprecated',
                'Mathlib.Control', 'Mathlib.Std', 'Mathlib.Mathport')

# Mathlib's abbreviations in names, spelled out
ABBREVIATIONS = {
    'add': 'sum', 'mul': 'product', 'sub': 'difference', 'div': 'quotient', 'neg': 'negation',
    'inv': 'inverse', 'pow': 'power', 'zpow': 'integer power', 'npow': 'natural power',
    'smul': 'scalar multiple', 'nsmul': 'natural multiple', 'zsmul': 'integer multiple',
    'vadd': 'vector sum', 'vsub': 'vector difference', 'sq': 'square', 'sqrt': 'square root',
    'abs': 'absolute value', 'dist': 'distance', 'edist': 'extended distance', 'nndist': 'distance',
    'nnnorm': 'norm', 'enorm': 'extended norm', 'deriv': 'derivative', 'fderiv': 'derivative',
    'card': 'cardinality', 'ncard': 'cardinality', 'encard': 'extended cardinality',
    'dvd': 'divisibility', 'gcd': 'greatest common divisor', 'lcm': 'least common multiple',
    'fac': 'factor', 'succ': 'successor', 'pred': 'predecessor', 'min': 'minimum', 'max': 'maximum',
    'inf': 'infimum', 'sup': 'supremum', 'bot': 'bottom', 'comp': 'composition', 'id': 'identity',
    'equiv': 'equivalence', 'iso': 'isomorphism', 'hom': 'homomorphism', 'mono': 'monomorphism',
    'epi': 'epimorphism', 'endo': 'endomorphism', 'aut': 'automorphism', 'fst': 'first component',
    'snd': 'second component', 'prod': 'product', 'coprod': 'coproduct', 'nat': 'natural number',
    'int': 'integer', 'rat': 'rational number', 'eval': 'evaluation', 'deg': 'degree',
    'coeff': 'coefficient', 'mem': 'membership', 'supp': 'support', 'tsum': 'sum',
    'finsum': 'finite sum', 'iter': 'iterate', 'repr': 'representation', 'val': 'value',
    'num': 'numerator', 'den': 'denominator', 'coe': 'coercion', 'ext': 'extension',
    'char': 'characteristic', 'det': 'determinant', 'tr': 'trace', 'adj': 'adjoint',
    'diag': 'diagonal', 'vec': 'vector', 'mat': 'matrix', 'poly': 'polynomial', 'seq': 'sequence',
    'fn': 'function', 'func': 'function', 'rel': 'relation', 'ord': 'order', 'ker': 'kernel',
    'coker': 'cokernel', 'im': 'imaginary part', 're': 'real part', 'exp': 'exponential',
    'log': 'logarithm', 'cpow': 'complex power', 'rpow': 'real power', 'obj': 'object',
    'app': 'application', 'cfg': 'configuration', 'config': 'configuration', 'nhds': 'neighbourhood filter',
    'lim': 'limit', 'colim': 'colimit', 'fin': 'finite', 'finset': 'finite set', 'multiset': 'multiset',
    'emb': 'embedding', 'incl': 'inclusion', 'proj': 'projection', 'sym': 'symmetric power',
    'opp': 'opposite', 'op': 'opposite', 'cocone': 'cocone', 'prim': 'primitive', 'bij': 'bijection',
    'inj': 'injection', 'surj': 'surjection', 'cl': 'closure', 'int': 'integer', 'pos': 'positive part',
    'compl': 'complement', 'symm': 'inverse', 'trans': 'composition', 'refl': 'identity',
    'pi': 'product', 'alg': 'algebra', 'comm': 'commutative', 'cat': 'category', 'mon': 'monoid',
    'grp': 'group', 'ab': 'abelian group', 'clm': 'continuous linear map', 'homeomorph': 'homeomorphism',
    'diffeomorph': 'diffeomorphism', 'const': 'constant', 'fun': 'function', 'assoc': 'associator',
    'trunc': 'truncation', 'quot': 'quotient', 'elim': 'eliminator', 'inl': 'left injection',
    'inr': 'right injection', 'finsupp': 'finitely supported function', 'dom': 'domain',
    'conj': 'conjugate', 'distrib': 'distributive', 'indep': 'independent', 'ulift': 'lift',
    'unop': 'unopposite', 'cont': 'continuous', 'lin': 'linear', 'subtype': 'subtype',
    'nnreal': 'nonnegative real number', 'ennreal': 'extended nonnegative real number',
    'ereal': 'extended real number', 'zmod': 'integers modulo', 'padic': 'p-adic number',
    'bdd': 'bounded', 'nonneg': 'nonnegative', 'nonpos': 'nonpositive', 'iso': 'isomorphism',
    'cocone': 'cocone', 'hom': 'homomorphism', 'mul': 'product', 'gen': 'generator', 'gens': 'generators',
    'irred': 'irreducible', 'mvpolynomial': 'multivariate polynomial', 'charpoly': 'characteristic polynomial',
    'minpoly': 'minimal polynomial', 'spec': 'spectrum', 'tendsto': 'limit', 'cdf': 'cumulative distribution function',
    'pdf': 'probability density function', 'pmf': 'probability mass function', 'ae': 'almost everywhere',
}

# words of names that no wording uses: Mathlib's markers of variants and of
# constructions
DROP = {'mk', 'of', 'to', 'aux', 'core', 'impl', 'def', 'pre', 'mk\'', 'v', 'u', 'r', 'l', 'x', 'y', 'z'}

# words that no new lexical item is made of
STOP = set('''the of and is a an in to at on by for with from into onto over under as when where if
then all any some each every this these those it its they we one two which that such its their be are
was were has have not or but so than via along within sending given called also only same other more
most least can may must there here what who how whose being been let said note see using used define
defines defined gives give given returns return induced obtained corresponding associated respect
respectively namely i.e e.g etc'''.split())

# words that Mathlib writes with a capital: proper names and their adjectives
PROPER = {w.lower(): w for w in '''Galois Noether Noetherian Artin Artinian Hilbert Banach Lebesgue
Riemann Cauchy Euclid Euclidean Gauss Gaussian Lie Jacobson Dedekind Krull Hausdorff Borel Fourier
Frobenius Sylow Bernoulli Chebyshev Legendre Jacobi Mobius Möbius Haar Radon Nikodym Stieltjes Bochner
Hahn Schwartz Sobolev Lipschitz Holder Hölder Kähler Kahler Witt Teichmuller Zariski Grothendieck Yoneda
Kan Ore Bezout Bézout Kummer Dirichlet Eisenstein Fermat Pell Wilson Lagrange Taylor Laurent Puiseux
Hensel Weierstrass Stone Cech Čech Tychonoff Urysohn Baire Polish Alexandrov Alexandroff Kuratowski
Zorn Cantor Schroder Bernstein Ramsey Hall Konig König Turán Turan Euler Hamilton Hamiltonian Abel
Abelian Cayley Jordan Hölder Wedderburn Schur Brauer Maschke Burnside Cohen Macaulay Gorenstein
Lindelöf Lindelof Moore Smith Vitali Fubini Tonelli Fatou Markov Kolmogorov Poisson Bochner Hilbertian
Minkowski Gram Schmidt Sturm Liouville Laplace Laplacian Green Stokes Gelfand Mazur Krein Milman
Choquet Steinitz Hamel Wiener Riesz Fréchet Frechet Arzela Ascoli Dini Heine Bolzano Ostrowski Mordell
Clifford Grassmann Plücker Plucker Pontryagin Bohr Dynkin Coxeter Weyl Killing Cartan Chevalley
Picard Néron Severi Bott Frattini Hopf Poincaré Poincare Dold Kan Ext Tor Seifert Whitehead
Mahler Liouvillian Pochhammer Stirling Catalan Fibonacci Lucas Wythoff Beatty Zeckendorf Hasse Weil
Selmer Mersenne Wieferich Ramanujan Gamma Beta Zeta'''.split()}

# categories of the lexical items that a parse can start with, by its value category
CATS = {
    'Exp': ('Fun', 'Fun2', 'Fun3', 'FunC', 'Name', 'Const', 'Oper', 'Oper2'),
    'Kind': ('Noun', 'Fam', 'Fam2', 'Dep', 'Dep2', 'DepC'),
    'Prop': ('Adj', 'Adj2', 'Adj3', 'AdjC', 'AdjC3', 'AdjE', 'Noun1', 'Noun2', 'Noun3', 'NounC',
             'Verb', 'Verb2', 'VerbC', 'NegNoun2'),
}


def fun_cats():
    """GF function -> its value category, from the English grammar."""
    pgf = os.path.join(os.environ['INFORMATH_ROOT'], 'share', 'InformathEng.pgf')
    r = subprocess.run(['gf', '-run', pgf], input='pg -funs\n', capture_output=True, text=True)
    out = {}
    for l in r.stdout.split('\n'):
        m = re.match(r'\s*(\S+) : (.*) ;', l)
        if m:
            out[m.group(1)] = m.group(2).split('->')[-1].strip()
    return out


def covered():
    """The constants that mathlib.dkgf, Informath's base table or mapping.tsv cover."""
    out = set()
    share = os.path.join(os.environ['INFORMATH_ROOT'], 'share', 'baseconstants.dkgf')
    for f in ('mathlib.dkgf', share):
        for l in open(f):
            m = re.match(r"^([A-Za-z_0-9']+) : ", l)
            if m and '"' in l:
                out.add(m.group(1))
    for l in open('mapping.tsv'):
        if l.strip() and not l.startswith('#'):
            out.add(suggest_mangle(l.split('\t')[0].strip()))
    return out


def suggest_mangle(lean):
    return lean.replace('.', '__')


def wanted(d):
    if d['module'].startswith(SKIP_MODULES):
        return False
    last = d['lean'].split('.')[-1]
    if d['kind'] == 'constructor' and (last == 'mk' or d['lean'].rsplit('.', 1)[0] in STRUCTURES):
        return False
    if re.search(r'(^_|Aux$|aux$|Impl$|^go$|^loop$|_def$|^proof_|^match_|^rec$|^ctorIdx$|^noConfusionType$'
                 r'|^toCtorIdx$|^sizeOf$|[Dd]elab|[Uu]nexpand|Simps|^instDecidable|^decEq)', last):
        return False
    if re.search(r'\.(Simps|Delaborator|Meta|Tactic)\.', d['lean']):
        return False
    if re.match(r'\s*(An? )?[Aa]uxiliary', d['doc']) or re.match(r'\s*[Ii]mplementation', d['doc']):
        return False
    return True


STRUCTURES = set()


def words_of_name(lean, doc):
    """The words of the last part of a name, abbreviations spelled out and
    proper names capitalized: minFac -> ['minimum', 'factor']."""
    parts = lean.split('.')
    last = parts[-1]
    if last in ('app', 'toFun', 'apply') and len(parts) > 1:
        last = parts[-2]
    ws = re.findall(r'[A-Z]?[a-z]+|[A-Z]+(?![a-z])|\d+', last.replace('_', ' '))
    out = []
    for w in ws:
        lw = w.lower()
        if lw in ABBREVIATIONS:
            out += ABBREVIATIONS[lw].split()
        elif lw in PROPER:
            out.append(PROPER[lw])
        else:
            out.append(lw)
    return out


def singular(w):
    if w.endswith(('us', 'is', 'ss', 'as', 'ics', 'ous', 'series', 'ness')) or len(w) <= 3:
        return w
    return suggest.singular(w)


def from_name(lean, nargs, cat, value, doc):
    ws = [w for w in words_of_name(lean, doc) if w not in DROP]
    if not ws or any(w.isdigit() for w in ws):
        return []
    sg = lambda w: singular(w) if w.islower() else w
    out = []
    if cat == 'Prop':
        if ws[0] in ('is', 'has'):
            rest = ' '.join(ws[1:])
            if rest:
                out += ['#1 is a %s' % rest, '#1 is %s' % rest] if ws[0] == 'is' else ['#1 has a %s' % rest]
        else:
            out += ['#1 is %s' % ' '.join(ws), '#1 is a %s' % ' '.join(ws)]
    elif cat == 'Kind':
        out += [' '.join(sg(w) for w in ws) + suggest.args_phrase(nargs)]
    elif cat == 'Exp':
        if ws[0] in ('to', 'of') and len(ws) > 1:
            ws = ws[1:]
        collection = re.match(r'Elem \((Finset|List|Multiset|Set)\b', value)
        if collection and ws[-1].endswith('s') and ws[-1] != 'list':
            kind = 'list' if collection.group(1) == 'List' else 'set'
            out += ['the %s of %s%s' % (kind, ' '.join([sg(w) for w in ws[:-1]] + [ws[-1]]), suggest.args_phrase(nargs))]
        np = ' '.join([sg(w) for w in ws])
        out += ['the %s%s' % (np, suggest.args_phrase(nargs))]
        if nargs == 0:
            out += [np]
    return out


def parse_all(cands):
    """candidate -> its parses, as (GF tree, profile), in one call."""
    r = subprocess.run([RUN, '-parse-example'], input='\n'.join(cands) + '\n', capture_output=True, text=True)
    # each candidate's parses, one per line, end with an empty line
    blocks, cur = [], []
    for l in r.stdout.split('\n'):
        if l.strip():
            m = re.match(r'(.*?)\s*(\[[\d,]*\])?$', l.strip())
            cur.append((m.group(1), m.group(2) or ''))
        else:
            blocks.append(cur)
            cur = []
    if len(blocks) < len(cands):
        sys.exit('-parse-example gave %d answers to %d candidates' % (len(blocks), len(cands)))
    return dict(zip(cands, blocks))


def known_words(words):
    r = subprocess.run([RUN, '-find-gf'], input='\n'.join(words) + '\n', capture_output=True, text=True)
    out = {}
    for line in r.stdout.split('\n'):
        if ' :' in line:
            w, fs = line.split(' :', 1)
            out[w.strip()] = bool(fs.strip())
    return out


ADJ_SUFFIXES = ('al', 'ic', 'ive', 'ous', 'able', 'ible', 'ary', 'ian', 'ant', 'ent', 'less', 'ful',
                'ar', 'ed', 'ile', 'oid', 'ish', 'wise')
NOUN_EXCEPTIONS = ('ideal', 'interval', 'integral', 'functional', 'normal', 'radical', 'residual', 'potential',
                   'differential', 'rational', 'polynomial', 'monomial', 'binomial', 'arrival', 'total',
                   'element', 'component', 'segment', 'argument', 'quotient', 'coefficient', 'gradient',
                   'determinant', 'invariant', 'variant', 'constant', 'agent', 'tangent', 'exponent',
                   'equivalent', 'idempotent', 'nilpotent', 'unipotent', 'pullback', 'field', 'embed')

IRREGULAR_PLURALS = [('matrix', 'matrices'), ('vertex', 'vertices'), ('index', 'indices'), ('simplex', 'simplices'),
                     ('basis', 'bases'), ('axis', 'axes'), ('radius', 'radii'), ('locus', 'loci'), ('torus', 'tori'),
                     ('nucleus', 'nuclei'), ('spectrum', 'spectra'), ('maximum', 'maxima'), ('minimum', 'minima'),
                     ('supremum', 'suprema'), ('infimum', 'infima'), ('extremum', 'extrema'), ('series', 'series'),
                     ('criterion', 'criteria'), ('polyhedron', 'polyhedra'), ('datum', 'data')]

GENERATED = ('-- BEGIN words generated by mathlib-informath/definition-table.py',
             '-- END words generated by mathlib-informath/definition-table.py')


def dict_eng():
    """word -> {'N': plural, 'A': True}: the nouns and adjectives of the RGL's DictEng."""
    path = os.path.join(os.environ.get('GF_RGL', os.path.expanduser('~/GF/gf-rgl')), 'src', 'english', 'DictEng.gf')
    out = collections.defaultdict(dict)
    for l in open(path):
        m = re.match(r'lin ([a-z]+)_N = mkN "([a-z]+)" "([a-z]+)"', l)
        if m and m.group(1) == m.group(2):
            out[m.group(2)]['N'] = m.group(3)
        m = re.match(r'lin ([a-z]+)_A = (?:compoundA \()?mkA "([a-z]+)"', l)
        if m and m.group(1) == m.group(2):
            out[m.group(2)]['A'] = True
        m = re.match(r'lin ([a-z]+)_V2? = ', l)
        if m:
            out[m.group(1)]['V'] = True
    return out


def lexical_item(w, dic, adj_role, doc_count):
    """(GF function, its English linearization) for a new word, or None: a
    noun or an adjective as DictEng has it (an adjective if the candidates use
    it as one, when it is both), a proper name as a noun, and a word that
    DictEng lacks, if docstrings use it thrice, by its ending."""
    ident = re.sub(r"[^A-Za-z0-9]", '_', w)
    e = dic.get(w.lower(), {})
    plural = None
    for sg, pl in IRREGULAR_PLURALS:
        if w.endswith(sg):
            plural = w[:-len(sg)] + pl
    if 'A' in e and ('N' not in e or adj_role):
        return ident + '_Adj', 'mkAdj "%s"' % w
    if 'N' in e:
        plural = plural or e['N']
    elif w.lower() in PROPER:
        return ident + '_Noun', 'mkNoun "%s"' % w
    elif e or doc_count < 3:
        return None                     # a verb, or a word of names only
    elif w.lower().endswith(ADJ_SUFFIXES) and w.lower() not in NOUN_EXCEPTIONS:
        return ident + '_Adj', 'mkAdj "%s"' % w
    if plural and plural != w + 's':
        return ident + '_Noun', 'mkNoun (mkN "%s" "%s")' % (w, plural)
    return ident + '_Noun', 'mkNoun "%s"' % w


def write_block(path, lines):
    """Replace the generated block of a grammar module (or add it before its final }) by lines."""
    s = open(path).read()
    block = GENERATED[0] + '\n' + ''.join(l + '\n' for l in lines) + GENERATED[1] + '\n'
    if GENERATED[0] in s:
        s = re.sub(re.escape(GENERATED[0]) + '.*?' + re.escape(GENERATED[1]) + '\n', lambda _: block, s, flags=re.S)
    else:
        i = s.rstrip().rfind('}')
        s = s[:i] + block + '\n' + s[i:]
    open(path, 'w').write(s)


def make_lexicon(name_words, doc_words, adj_words, funs):
    """New English words for Mathlib.gf and MathlibEng.gf: the unknown words of
    the candidates from names that come twice or more, and those of the
    candidates from docstrings that come three times or more, that look like
    content words; a word that the grammar has as a function already is not made."""
    grammars = os.path.join(os.environ['INFORMATH_ROOT'], 'grammars')
    words = sorted(w for w in set(name_words) | set(doc_words)
                   if (name_words[w] >= 2 or doc_words[w] >= 3) and w.lower() not in STOP
                   and re.fullmatch(r"[A-Za-zÀ-ÿ]{4,}", w) and w.lower() not in ABBREVIATIONS)
    absl, cncl = [], []
    dic = dict_eng()
    for w in words:
        item = lexical_item(w, dic, adj_words[w] * 2 > name_words[w] + doc_words[w], doc_words[w])
        if not item:
            continue
        f, lin = item
        if f in funs:
            continue
        absl.append('fun %s : %s ;' % (f, f.rsplit('_', 1)[1]))
        cncl.append('lin %s = %s ;' % (f, lin))
    write_block(os.path.join(grammars, 'Mathlib.gf'), absl)
    write_block(os.path.join(grammars, 'MathlibEng.gf'), cncl)
    print('%d words -> Mathlib.gf, MathlibEng.gf' % len(absl))


def main():
    defs = [json.loads(l) for l in open('out/definitions.jsonl')]
    STRUCTURES.update(d['lean'] for d in defs if d['structure'])
    have = covered()
    cats = fun_cats()
    rows = []
    for d in defs:
        if d['dk'] in have or not wanted(d):
            continue
        names, nargs, cat = suggest.signature(d['type'])
        value = suggest.VALUE[0]
        if cat == 'Proof':
            continue
        cands = [(c, 'doc') for c in suggest.from_doc(d['dk'], d['doc'], names, nargs, cat)] + \
                [(c, 'name') for c in from_name(d['lean'], nargs, cat, value, d['doc'])]
        seen, cs = set(), []
        for c, src in cands:
            if c not in seen:
                seen.add(c)
                cs.append((c, src))
        rows.append((d, cat, nargs, cs))
    allc = sorted({c for _, _, _, cs in rows for c, _ in cs})
    print('%d definitions, %d candidates' % (len(rows), len(allc)), file=sys.stderr)
    parses = parse_all(allc)

    def fits(c, cat, nargs):
        for tree, prof in parses.get(c, []):
            head = tree.lstrip('(').split()[0]
            k = len(re.findall(r'\d+', prof))
            if cats.get(head) in CATS[cat] and k == nargs:
                return tree
        return None

    words = collections.Counter()
    name_words, doc_words, adj_words = collections.Counter(), collections.Counter(), collections.Counter()
    got = 0
    table, tsv = [], []
    for d, cat, nargs, cs in rows:
        ok = [(c, src, fits(c, cat, nargs)) for c, src in cs]
        good = [(c, src, t) for c, src, t in ok if t]
        bad = [(c, src) for c, src, t in ok if not t]
        for c, src in bad:
            for w in re.findall(r"[A-Za-zÀ-ÿ][A-Za-zÀ-ÿ'-]*", c):
                words[w] += 1
                (name_words if src == 'name' else doc_words)[w] += 1
                if re.match(r'#1 is (?!an? )', c):
                    adj_words[w] += 1
        if good:
            got += 1
            c, src, t = good[0]
            table.append((d, c, src))
        tsv.append((d, cat, nargs, good, bad))
    known = known_words(sorted(words))
    unknown = collections.Counter({w: n for w, n in words.items() if not known.get(w, True)})

    with open('definitions.dkgf', 'w') as f:
        f.write('# verbal entries for Mathlib definitions, made by definition-table.py from their\n'
                '# docstrings and names (do not edit: improve mathlib.dkgf, which overrides it)\n\n')
        for d, c, src in table:
            f.write('%s : "%s"\n' % (d['dk'], c))
    with open('out/definition-table.tsv', 'w') as f:
        f.write('constant\tmodule\tcategory\targuments\tentry\tsource\tother parsing\tnot parsing (unknown words)\n')
        for d, cat, nargs, good, bad in tsv:
            f.write('%s\t%s\t%s\t%d\t%s\t%s\t%s\t%s\n' % (
                d['dk'], d['module'], cat, nargs, good[0][0] if good else '', good[0][1] if good else '',
                ' | '.join(c for c, _, _ in good[1:]),
                ' | '.join('%s (%s) [%s]' % (c, src, ' '.join(w for w in re.findall(r"[A-Za-zÀ-ÿ][A-Za-zÀ-ÿ'-]*", c) if w in unknown))
                           for c, src in bad)))
    with open('out/unknown-words.tsv', 'w') as f:
        for w, n in unknown.most_common():
            f.write('%s\t%d\n' % (w, n))
    print('%d definitions, %d with an entry -> definitions.dkgf; %d unknown words -> out/unknown-words.tsv'
          % (len(rows), got, len(unknown)))
    if '-lexicon' in sys.argv[1:]:
        make_lexicon(collections.Counter({w: n for w, n in name_words.items() if w in unknown}),
                     collections.Counter({w: n for w, n in doc_words.items() if w in unknown}), adj_words, set(cats))
    by = collections.Counter(cat for _, cat, _, _ in rows)
    byok = collections.Counter(cat for _, cat, _, good, _ in tsv if good)
    print('  ' + ', '.join('%s %d/%d' % (k, byok[k], by[k]) for k in by))


if __name__ == '__main__':
    main()
