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
    'unop': 'opposite', 'cont': 'continuous', 'lin': 'linear', 'subtype': 'subtype',
    'nnreal': 'nonnegative real number', 'ennreal': 'extended nonnegative real number',
    'ereal': 'extended real number', 'zmod': 'integers modulo', 'padic': 'p-adic number',
    'bdd': 'bounded', 'nonneg': 'nonnegative', 'nonpos': 'nonpositive', 'iso': 'isomorphism',
    'cocone': 'cocone', 'hom': 'homomorphism', 'mul': 'product', 'gen': 'generator', 'gens': 'generators',
    'irred': 'irreducible', 'mvpolynomial': 'multivariate polynomial', 'charpoly': 'characteristic polynomial',
    'minpoly': 'minimal polynomial', 'spec': 'spectrum', 'tendsto': 'limit', 'cdf': 'cumulative distribution function',
    'pdf': 'probability density function', 'pmf': 'probability mass function', 'ae': 'almost everywhere',
    'congr': 'congruence', 'comap': 'preimage', 'diff': 'difference', 'lex': 'lexicographic',
    'cond': 'conditional', 'precomp': 'precomposition', 'postcomp': 'postcomposition',
    'reindex': 'reindexing', 'uncurry': 'uncurrying', 'cod': 'codomain', 'res': 'restriction',
    'restr': 'restriction', 'inter': 'intersection', 'bialg': 'bialgebra', 'coalg': 'coalgebra',
    'fg': 'finitely generated', 'coind': 'coinduction', 'homeo': 'homeomorphism', 'elem': 'element',
    'univ': 'universal set', 'coord': 'coordinate', 'mv': 'multivariate', 'fintype': 'finite type',
    'biprod': 'biproduct', 'rep': 'representation', 'bilin': 'bilinear', 'nn': 'nonnegative',
    'meas': 'measurable', 'comon': 'comonoid', 'idx': 'index', 'vcomp': 'vertical composition',
    'finrank': 'finite rank', 'var': 'variable', 'vert': 'vertex', 'decomp': 'decomposition',
    'noncomm': 'noncommutative', 'triv': 'trivial', 'aeval': 'algebra evaluation', 'unif': 'uniform',
    'dim': 'dimension', 'ess': 'essential', 'cmp': 'comparison', 'dbl': 'double', 'subst': 'substitution',
    'icc': 'closed interval', 'ioo': 'open interval', 'postcompose': 'postcomposition',
    'precompose': 'precomposition', 'sheafify': 'sheafification', 'unopposite': 'opposite',
    'lie': 'Lie', 'cof': 'cofinality', 'lequiv': 'linear equivalence', 'liequiv': 'linear isometric equivalence',
}

# words of names that no wording uses: Mathlib's markers of variants and of
# constructions
DROP = {'mk', 'aux', 'core', 'impl', 'def', 'pre'}

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
    if '«' in d['lean'] or last.startswith('term'):
        return False                    # notations
    if re.search(r'\.(Simps|Delaborator|Meta|Tactic)\.', d['lean']):
        return False
    if re.match(r'\s*(An? )?[Aa]uxiliary', d['doc']) or re.match(r'\s*[Ii]mplementation', d['doc']):
        return False
    return True


STRUCTURES = set()
DICT = {}


# words before another word in a name, as modifiers: AddMonoidHom, MulEquiv
MODIFIERS = {'add': 'additive', 'mul': 'multiplicative', 'nat': 'natural', 'int': 'integer',
             'comm': 'commutative', 'lin': 'linear', 'alg': 'algebra', 'cont': 'continuous',
             'rel': 'relative'}

# pairs of words of names that are one term
PAIRS = {('nat', 'trans'): 'natural transformation', ('nat', 'iso'): 'natural isomorphism',
         ('nat', 'degree'): 'natural degree', ('mon', 'cat'): 'monoid category',
         ('grp', 'cat'): 'group category', ('top', 'cat'): 'topological category',
         ('ring', 'cat'): 'ring category', ('mod', 'cat'): 'module category',
         ('add', 'equiv'): 'additive equivalence', ('mul', 'equiv'): 'multiplicative equivalence',
         ('linear', 'equiv'): 'linear equivalence', ('ring', 'equiv'): 'ring isomorphism',
         ('alg', 'equiv'): 'algebra isomorphism', ('order', 'iso'): 'order isomorphism',
         ('nhds', 'within'): 'neighbourhood filter within', ('is', 'o'): 'is little o',
         ('is', 'big', 'o'): 'is big o', ('l', 'i'): 'linear isometric',
         ('rel', 'iso'): 'relation isomorphism', ('rel', 'hom'): 'relation homomorphism',
         ('rel', 'embedding'): 'relation embedding', ('rel', 'series'): 'relation series'}

# adjectives of relations: "#1 is Brauer equivalent to #2"
RELATIONAL = set('''equivalent isomorphic equal coprime disjoint orthogonal similar conjugate homotopic
adjacent comparable parallel related independent congruent associated dual complementary
codisjoint perpendicular cofinal subordinate homeomorphic equinumerous'''.split())

# Greek letters that Mathlib names maps by
GREEK = {'ι': 'inclusion', 'π': 'projection'}


def words_of_name(lean, module):
    """The words of the last part of a name, abbreviations spelled out and
    proper names capitalized: minFac -> ['minimum', 'factor'],
    AddMonoidHom -> ['additive', 'monoid', 'homomorphism']; an inner "of" is
    kept (PartitionOfUnity), a first "of" or "to" (ofList, toFun) is not."""
    parts = lean.split('.')
    last = parts[-1]
    if last in ('app', 'toFun', 'apply') and len(parts) > 1:
        last = parts[-2]
    last = re.sub('[ιπ]', lambda m: ' %s ' % GREEK[m.group(0)].capitalize(), last)
    ws = [w.lower() for w in re.findall(r'[A-Z]?[a-z]+|[A-Z]+(?![a-z])|\d+', last.replace('_', ' '))]
    while ws and ws[0] in ('of', 'to') and len(ws) > 1:
        ws = ws[1:]
    out, i = [], 0
    while i < len(ws):
        w, nxt = ws[i], (ws[i + 1] if i + 1 < len(ws) else None)
        if (w, nxt) in PAIRS:
            out += PAIRS[(w, nxt)].split()
            i += 2
            continue
        if nxt and w in MODIFIERS:
            out.append(MODIFIERS[w])
        elif w in ('mono', 'anti') and 'CategoryTheory' not in module:
            out.append('monotone' if w == 'mono' else 'antitone')
        elif w in ABBREVIATIONS:
            out += ABBREVIATIONS[w].split()
        elif w in PROPER:
            out.append(PROPER[w])
        else:
            out.append(w)
        i += 1
    return out


def singular(w):
    if w.endswith(('us', 'is', 'ss', 'as', 'ics', 'ous', 'series', 'ness')) or len(w) <= 3:
        return w
    return suggest.singular(w)


def main_args(typ, nargs):
    """The numbers of the arguments that a reading names: the ones that are
    not types (Set), at most two, the last ones."""
    parts, depth, cur = [], 0, ''
    for ch in typ:
        depth += ch == '('
        depth -= ch == ')'
        cur += ch
        if depth == 0 and cur.endswith('->'):
            parts.append(cur[:-2].strip())
            cur = ''
    objs = [i + 1 for i, p in enumerate(parts[:nargs])
            if not re.fullmatch(r'\(\S+ : (Set|Prop)\)|Set|Prop', p) and not re.match(r'(\(\S+ : )?\(*Proof\b', p)]
    return (objs or list(range(1, nargs + 1)))[-2:]


def arg_types(typ, ks):
    """The types of the arguments ks of a Dedukti type, as strings."""
    parts, depth, cur = [], 0, ''
    for ch in typ:
        depth += ch == '('
        depth -= ch == ')'
        cur += ch
        if depth == 0 and cur.endswith('->'):
            parts.append(cur[:-2].strip())
            cur = ''
    return [parts[k - 1] if k <= len(parts) else '' for k in ks]


def parameter(doc, names, types):
    """Which of two arguments (0 or 1) the docstring names after "relative
    to", "with respect to", "for", "over" or "w.r.t.", by its name or by the
    words of its type (a Grothendieck topology: CategoryTheory__GrothendieckTopology),
    or None."""
    for m in re.finditer(r'\b(?:relative to|with respect to|w\.r\.t\.?|for|over|along)\s+([^.,;:]{1,60})', doc):
        phrase = m.group(1)
        hits = []
        for i, (n, t) in enumerate(zip(names, types)):
            heads = re.findall(r'__([A-Z][A-Za-z]+)|\b([A-Z][A-Za-z]+)\b', t.split(':')[-1])
            words = {w.lower() for h in heads for part in h if part
                     for w in re.findall(r'[A-Z][a-z]+', part)} - {'elem', 'proof', 'set', 'opposite'}
            if (n and re.search(r'`%s`' % re.escape(n), phrase)) or \
                    (words and all(w in phrase.lower() for w in words)):
                hits.append(i)
        if len(hits) == 1:
            return hits[0]
    return None


def of_args(ks):
    if not ks:
        return ''
    return ' of #%d' % ks[0] if len(ks) == 1 else ' of #%d and #%d' % tuple(ks[-2:])


def head_words(lean, module, cat):
    """The words that a reading of a name is made of: a constructor ofX
    names its namespace's type (Bicone.ofLimitCone: "bicone"), a function
    XOfY its X (pointOfClosedPoint: "point"), but a type keeps its "of"
    (PartitionOfUnity); a final left or right comes first (compRight: "right
    composition")."""
    parts = lean.split('.')
    last = parts[-1]
    if cat == 'Exp' and re.match(r'of[A-Z]', last) and len(parts) > 1:
        return [w for w in words_of_name('.'.join(parts[:-1]), module) if w not in DROP and len(w) > 1]
    ws = [w for w in words_of_name(lean, module) if w not in DROP and len(w) > 1]
    if cat == 'Exp' and 'of' in ws[1:]:
        ws = ws[:ws.index('of', 1)]
    if len(ws) > 1 and ws[-1] in ('left', 'right'):
        ws = [ws[-1]] + ws[:-1]
    return ws


def stems(ws):
    return {w[:4].lower() for w in ws if len(w) >= 3}


def from_name(lean, module, nargs, cat, value, doc='', typ='', argnames=()):
    ws = head_words(lean, module, cat)
    if not ws or any(w.isdigit() for w in ws) or ws[-1] == 'of':
        return []
    sg = lambda w: singular(w) if w.islower() else w
    ks = main_args(typ, nargs) if nargs > 2 or cat == 'Prop' else list(range(1, nargs + 1))
    first = '#%d' % ks[0] if ks else '#1'
    out = []
    if cat == 'Prop' and len(ks) == 2:
        # a predicate of two objects is binary, with no argument left out, and
        # its subject is the argument that the docstring does not name after
        # "relative to", "for" etc.; without such a clue there is no reading,
        # as the wrong subject would make a false one
        x, y = ks
        p = parameter(doc, [argnames[k - 1] if len(argnames) >= k else '' for k in ks], arg_types(typ, ks))
        if p is None and ws[-1] not in RELATIONAL:
            return []
        if p == 0:
            x, y = y, x
        rest = ' '.join(ws[1:] if ws[0] == 'is' else ws)
        if ws[-1] in RELATIONAL or re.search(r'\b%s (to|with)\b' % re.escape(ws[-1]), doc):
            out += ['#%d is %s to #%d' % (x, rest, y), '#%d is %s with #%d' % (x, rest, y)]
        adj = adjectival(ws[-1]) or (len(ws) > 2 and ws[-2].endswith('ly'))
        forms = ['#%d is %s with respect to #%d' % (x, rest, y), '#%d is a %s with respect to #%d' % (x, rest, y)]
        out += forms if adj else forms[::-1]
    elif cat == 'Prop':
        if ws[0] in ('is', 'has'):
            rest = ' '.join(ws[1:])
            if rest:
                adj = adjectival(ws[-1]) or (len(ws) > 2 and ws[-2].endswith('ly')) or \
                    re.search(r'\bis %s\b' % re.escape(rest), doc) and not re.search(r'\bis an? %s\b' % re.escape(rest), doc)
                out += (['%s is %s' % (first, rest), '%s is a %s' % (first, rest)] if adj else
                        ['%s is a %s' % (first, rest), '%s is %s' % (first, rest)]) if ws[0] == 'is' else ['%s has a %s' % (first, rest)]
        else:
            out += ['%s is %s' % (first, ' '.join(ws)), '%s is a %s' % (first, ' '.join(ws))]
    elif cat == 'Kind':
        out += [' '.join(sg(w) for w in ws) + (suggest.args_phrase(nargs) if nargs <= 2 else of_args(list(range(1, nargs + 1))))]
    elif cat == 'Exp':
        collection = re.match(r'Elem \((Finset|List|Multiset|Set)\b', value)
        if collection and ws[-1].endswith('s') and ws[-1] != 'list':
            kind = 'list' if collection.group(1) == 'List' else 'set'
            out += ['the %s of %s%s' % (kind, ' '.join([sg(w) for w in ws[:-1]] + [ws[-1]]), of_args(ks))]
        np = ' '.join([sg(w) for w in ws])
        out += ['the %s%s' % (np, of_args(ks))]
        if len(ks) == 2:
            out += ['the %s of #%d' % (np, ks[-1])]
        if nargs == 0:
            out += [np]
    return out


def adjectival(w):
    e = DICT.get(w, {})
    return ('A' in e and 'N' not in e) or (not e and w.endswith(ADJ_SUFFIXES) and not w.endswith(NOUN_EXCEPTIONS))


def cut_generic(c):
    """A docstring's noun phrase without a phrase about any object: "the
    cofinality on an ordinal of #1" -> "the cofinality of #1"."""
    cut = re.sub(r' (?:on|in|for|of|over|from|of all) (?:an?|any|some|every|each) [a-z -]+?(?= of #| on #| in #|$)', '', c)
    return [cut] if cut != c else []


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


def known_words(words, generated=()):
    """word -> whether the grammar has it, other than as a generated word."""
    r = subprocess.run([RUN, '-find-gf'], input='\n'.join(words) + '\n', capture_output=True, text=True)
    out = {}
    for line in r.stdout.split('\n'):
        if ' :' in line:
            w, fs = line.split(' :', 1)
            out[w.strip()] = any(f not in generated for f in fs.split())
    return out


def generated_functions():
    """The functions of the generated block of Mathlib.gf."""
    s = open(os.path.join(os.environ['INFORMATH_ROOT'], 'grammars', 'Mathlib.gf')).read()
    m = re.search(re.escape(GENERATED[0]) + '(.*?)' + re.escape(GENERATED[1]), s, re.S)
    return set(re.findall(r'fun (\S+) :', m.group(1))) if m else set()


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
        m = re.match(r'lin ([a-z]+)_Adv = ', l)
        if m:
            out[m.group(1)]['Adv'] = True
        m = re.match(r'lin ([a-z]+)_V2? = ', l)
        if m:
            out[m.group(1)]['V'] = True
    return out


def lexical_item(w, dic, adj_role, doc_count):
    """(GF function, its English linearization) for a new word, or None: a
    noun or an adjective as DictEng has it (an adjective if the candidates use
    it as one, when it is both), an adverb in -ly, a proper name as a noun,
    and a word that DictEng lacks, if three docstrings use it, by its ending."""
    ident = re.sub(r"[^A-Za-z0-9]", '_', w)
    e = dic.get(w.lower(), {})
    plural = None
    for sg, pl in IRREGULAR_PLURALS:
        if w.endswith(sg):
            plural = w[:-len(sg)] + pl
    if w.endswith('ly') and ('Adv' in e or 'N' not in e):
        return ident + '_Adverb', 'ParadigmsEng.mkAdv "%s"' % w
    if w.endswith('est') and len(w) > 5 and w[:-3] in dic:
        return None                     # a superlative
    if 'A' in e and ('N' not in e or adj_role):
        return ident + '_Adj', 'mkAdj "%s"' % w
    if 'N' in e:
        plural = plural or e['N']
    elif w.lower() in PROPER:
        return ident + '_Noun', 'mkNoun "%s"' % w
    elif e or doc_count < 3:
        return None                     # a verb, or a word of names only
    elif w.lower().endswith(ADJ_SUFFIXES) and not w.lower().endswith(NOUN_EXCEPTIONS):
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


# words of docstrings that are no mathematical terms: function words that
# DictEng lacks, everyday words, and the words of Lean and its tools
JUNK = set('''because while them without will until against another everything itself during just
five four sorry weird stupid young brown nightly weekly bird banana church bell machine fund ghost
store stream tape load float token info meta mathlib namespace tactic simp simproc typeclass defeq
formatter parenthesizer caching emulator discharger peek lookup insert reorder select trim paste
squash shrink move raise pull push yield seen made known written built chosen considered described
needed required provided proposed referred regarded registered viewed involved implemented
guaranteed specified expressed exhibited fudge junk guess intent clog blur slash sect stereo
auto away back down after near together outside inside forall prop prod perm frac conv con quasi
beck krull bernoulli clifford dirac serre levy reedy bourbaki yoneda coyoneda candidate package
packaged success priority precedence proxy wrapped upgraded unsound undefined lawful literal
plot spread synonym them dfinsupp finset fpqc proetale lapply subfamily boxes epis simplices
bicomplexes coalgebras subcomplexes nuclei continuants select halt anchor arch foot leg horn
rack shelf spine site coming going making showing turning plot cast chunk con prod perm finset
foldl foldr yield spread discard compress linearize parametrize preserve bigger larger largest
coarsest smaller higher automorphize binder datum couple corner shadow contract tilt sober
accidental actual based carried changed combined composed constructed contained continued
covered determined divided followed formed identified included inherited joined listed mapped
modified placed presented pulled realized reconstructed removed represented restricted shifted
sorted stopped tagged transferred transported valued forbidden external incident trailing walking
going typically possibly necessarily finally immediately initially frequently effectively
theoretically virtually'''.split())

# words in -ing that are terms of mathematics
ING_TERMS = set('''braiding gluing currying thickening coarsening grading labelling scaling tensoring
coupling branching doubling reindexing classifying connecting representing corepresenting stopping
hitting halting walking localizing colimiting normalizing separating reflecting intertwining
trailing'''.split())

DOC_COUNTS = collections.Counter()


def count_doc_words(defs):
    """How many docstrings use each word in their prose (not in code)."""
    for d in defs:
        prose = re.sub(r'`[^`]*`|\$[^$]*\$|\[[^\]]*\]\([^)]*\)', ' ', d['doc'])
        DOC_COUNTS.update(set(re.findall(r"[A-Za-z][a-z]+", prose)))


TRANSLATIONS = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'translations.tsv')
OTHER_LANGUAGES = [('Fre', 'MathlibFre.gf'), ('Ger', 'MathlibGer.gf'), ('Swe', 'MathlibSwe.gf'),
                   ('Cze', 'next/MathlibCze.gf')]
GENDERS = {
    'Fre': {'m': 'masculine', 'f': 'feminine'},
    'Ger': {'m': 'masculine', 'f': 'feminine', 'n': 'neuter'},
    'Swe': {'u': 'utrum', 'n': 'neutrum'},
    'Cze': {'ma': 'mascAnimate', 'mi': 'mascInanimate', 'f': 'feminine', 'n': 'neuter'},
}


def read_translations():
    """function -> {language: cell} from translations.tsv."""
    out = {}
    if not os.path.exists(TRANSLATIONS):
        return out
    for l in open(TRANSLATIONS):
        if l.startswith('#') or not l.strip():
            continue
        cols = l.rstrip('\n').split('\t')
        cols += [''] * (6 - len(cols))
        out[cols[0]] = dict(zip(['Eng'] + [lang for lang, _ in OTHER_LANGUAGES], cols[1:6]))
    return out


def cell_lin(lang, cat, cell):
    """The linearization of a word from its cell in translations.tsv: the
    forms separated by /, for a noun followed by its gender (French m f,
    German m f n, Swedish u n, Czech ma mi f n)."""
    q = lambda xs: ' '.join('"%s"' % x.strip() for x in xs)
    if cat == 'Adverb':
        return 'Paradigms%s.mkAdv "%s"' % (lang, cell.strip())
    if cat == 'Adj':
        return 'mkAdj (mkA %s)' % q(cell.split('/'))
    words = cell.split()
    gender = GENDERS[lang].get(words[-1]) if len(words) > 1 else None
    forms = ' '.join(words[:-1] if gender else words).split('/')
    return 'mkNoun (mkN %s%s)' % (q(forms), ' ' + gender if gender else '')


def translate_lexicon(items, grammars):
    """The generated words in the other languages, from translations.tsv
    (written by hand and to be reviewed); a proper name as it is in English.
    A word without a translation in a language has no linearization there,
    and the readings that need it fall back to the ones without the generated
    table (build-index.py). The words that the table lacks are added to it
    with empty cells."""
    table = read_translations()
    new = [(f, w) for f, w in items if f not in table and not w[0].isupper()]
    if new:
        with open(TRANSLATIONS, 'a') as out:
            for f, w in new:
                out.write('%s\t%s\t\t\t\t\n' % (f, w))
    for lang, module in OTHER_LANGUAGES:
        block, got = [], 0
        for f, w in items:
            cat = f.rsplit('_', 1)[1]
            cell = table.get(f, {}).get(lang, '').strip()
            if w[0].isupper():
                block.append('lin %s = %s "%s" ;' % (f, 'mkNoun' if cat == 'Noun' else 'mkAdj', w))
            elif cell:
                block.append('lin %s = %s ;' % (f, cell_lin(lang, cat, cell)))
            else:
                continue
            got += 1
        write_block(os.path.join(grammars, module), block)
        print('  %s: %d of %d words -> %s' % (lang, got, len(items), module))


def make_lexicon(name_words, doc_words, adj_words, funs):
    """New English words for Mathlib.gf and MathlibEng.gf: the unknown words of
    the candidates from names that come twice or more, and those of the
    candidates from docstrings that come three times or more, that look like
    content words; a word that the grammar has as a function already is not made."""
    grammars = os.path.join(os.environ['INFORMATH_ROOT'], 'grammars')
    dic = dict_eng()
    words = sorted(w for w in set(name_words) | set(doc_words)
                   if (name_words[w] >= 2 or doc_words[w] >= 3 or DOC_COUNTS[w] >= 3) and w.lower() not in STOP
                   and re.fullmatch(r"[A-Za-zÀ-ÿ]{4,}", w) and not re.search(r'[a-z][A-Z]', w)
                   and (w.islower() or w.lower() in PROPER) and w not in JUNK
                   and (not w.endswith('ing') or 'N' in dic.get(w, {}) or w in ING_TERMS)
                   and w.lower() not in ABBREVIATIONS)
    absl, cncl, items = [], [], []
    # a plural as its singular, if that is a word too: cocones -> cocone
    lemmas = []
    for w in words:
        sg = singular(w) if w.islower() else w
        if sg != w and (sg in dic or DOC_COUNTS[sg] or sg in words):
            w = sg
        if w in JUNK or len(w) < 4:
            continue
        if w not in lemmas:
            lemmas.append(w)
    for w in lemmas:
        item = lexical_item(w, dic, adj_words[w] * 2 > name_words[w] + doc_words[w], DOC_COUNTS[w])
        if not item:
            continue
        f, lin = item
        if f in funs:
            continue
        absl.append('fun %s : %s ;' % (f, f.rsplit('_', 1)[1]))
        cncl.append('lin %s = %s ;' % (f, lin))
        items.append((f, w))
    write_block(os.path.join(grammars, 'Mathlib.gf'), absl)
    write_block(os.path.join(grammars, 'MathlibEng.gf'), cncl)
    translate_lexicon(items, grammars)
    print('%d words -> Mathlib.gf, MathlibEng.gf' % len(absl))


def main():
    DICT.update(dict_eng())
    defs0 = [json.loads(l) for l in open('out/definitions.jsonl')]
    count_doc_words(defs0)
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
        # a docstring's wording, if it shares a word with the name
        name_stems = stems(words_of_name(d['lean'], d['module'])) | stems(head_words(d['lean'], d['module'], cat))
        docs = [c for c in suggest.from_doc(d['dk'], d['doc'], names, nargs, cat)
                if any(a.startswith(b) or b.startswith(a) for a in stems(re.findall(r'[A-Za-z]+', c)) for b in name_stems)]
        cands = [(c2, 'doc') for c in docs for c2 in cut_generic(c)]
        cands += [(c, 'doc') for c in docs] + \
                [(c, 'name') for c in from_name(d['lean'], d['module'], nargs, cat, value, d['doc'], d['type'], names)]
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
        """The first parse of the right category that uses arguments of the
        constant, all if it has two or fewer, the others left out of the reading,
        as Eqt's "#2 is equal to #3" leaves out the type #1."""
        for tree, prof in parses.get(c, []):
            head = tree.lstrip('(').split()[0]
            used = [int(i) for i in re.findall(r'\d+', prof)]
            if cats.get(head) not in CATS[cat] or any(i > nargs for i in used) or len(set(used)) < len(used):
                continue
            if len(used) == nargs or (nargs > 2 and used) or (nargs == 2 and len(used) == 1 and cat == 'Prop'):
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
        # the words of all candidates count, as the generated words are made
        # again each time
        for c, src in cs:
            for w in re.findall(r"[A-Za-zÀ-ÿ][A-Za-zÀ-ÿ'-]*", c):
                words[w] += 1
                (name_words if src == 'name' else doc_words)[w] += 1
                if re.match(r'#\d+ is (?!an? )', c):
                    adj_words[w] += 1
        if good:
            got += 1
            c, src, t = good[0]
            table.append((d, c, src))
        tsv.append((d, cat, nargs, good, bad))
    known = known_words(sorted(words), generated_functions())
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
                     collections.Counter({w: n for w, n in doc_words.items() if w in unknown}), adj_words, set(cats) - generated_functions())
    by = collections.Counter(cat for _, cat, _, _ in rows)
    byok = collections.Counter(cat for _, cat, _, good, _ in tsv if good)
    print('  ' + ', '.join('%s %d/%d' % (k, byok[k], by[k]) for k in by))


if __name__ == '__main__':
    main()
