#!/usr/bin/env python3
"""Second-round candidates for the definitions that definition-table.py
leaves without an entry: the words of a name that Informath's grammar does
not have as a noun, an adjective or a proper name are replaced by words of
its lexicon, and the candidates are made again.

    python3 definition-table.py            # uses this module; -> out/lexicon-repairs.tsv

A word of a name is replaced

* by its nominalization, if the lexicon has it as a noun (restrict ->
  restriction, iterate -> iteration, normalize -> normalization); a
  nominalization before the nouns of its object comes after them
  (restrictScalars: "the scalar restriction of #1");
* by the lexicon's word with its capitals and accents (kronecker -> Kronecker);
* as an abbreviation, by a word of the lexicon that it abbreviates (a prefix,
  or the letters in order with the same first two: semigrp -> semigroup),
  if the constant's docstring uses that word and no other such word, or if the
  docstrings of the other definitions whose names have the abbreviation use
  it at least three times and twice as often as any other such word
  (denom -> denominator, coeq -> coequalizer).

A predicate named X On, X At or X Within with two main arguments, whose X
is an adjective, is read "#1 is X on #2". out/lexicon-repairs.tsv lists
every replacement with its evidence and the number of entries that use it:
it is what to review, rather than the entries.
"""
import collections, json, os, re, subprocess, unicodedata

# nominalizations that the rules below do not make, and words that are not
# replaced although the rules would make a noun of them (induce is not induction)
NOMINALS = {'extend': 'extension', 'include': 'inclusion', 'decompose': 'decomposition',
            'compose': 'composition', 'reduce': 'reduction', 'choose': 'choice', 'apply': 'application',
            'remove': 'removal', 'deduce': 'deduction', 'expand': 'expansion', 'divide': 'division',
            'solve': 'solution', 'describe': 'description', 'embed': 'embedding', 'lift': 'lift'}
NOT_NOMINAL = {'induce', 'act', 'find', 'get', 'take', 'bind', 'cancel', 'fix', 'move', 'pull', 'push',
               'drop', 'halt', 'like', 'exists', 'paste', 'kill', 'build', 'read', 'write', 'grade', 'couple',
               'tilt', 'except', 'braid', 'choose', 'generate', 'opt'}

# words with a meaning of their own in Mathlib, replaced only as the head of a
# name: IsColimit.desc is the morphism that a colimit induces, forget the
# forgetful functor
HEADS = {'desc': 'induced morphism', 'forget': 'forgetful functor'}

# words that name what kind of map a definition is (domRestrictHom: the
# restriction as a homomorphism), not the object of a verb before them
TYPE_WORDS = {'homomorphism', 'equivalence', 'isomorphism', 'congruence', 'identity', 'map', 'functor',
              'structure', 'embedding', 'hom', 'equiv', 'iso', 'morphism', 'linear', 'continuous'}

# abbreviations of Mathlib that the lexicon's words do not spell out by themselves
SPELLED = {'fract': 'fractional part'}

# abbreviations that are not replaced: their words differ from one part of
# Mathlib to another (List.cons, MulOpposite.mop), or they are no words (simp)
NOT_ABBREVIATIONS = {'cons', 'simp', 'non', 'prop', 'mop', 'unmop', 'mod', 'std', 'str', 'stx', 'nat', 'int'}

# words replaced by adjectives only in the names of predicates and types
# (RightCancelMonoid), as they are verbs in the names of functions (cancelBaseChange)
ADJECTIVAL = {'cancel'}

# words of names that are no content words: they are never replaced
FUNCTION_WORDS = set('''is to on of at has with from over by as under within along below above in for or
and not no all some iff up down out away against thru via into onto'''.split())


def fold(w):
    """A word without its accents, as names write it: Kähler -> kahler, kaehler."""
    return ''.join(c for c in unicodedata.normalize('NFD', w) if unicodedata.category(c) != 'Mn').lower()


class Lexicon:
    """The English words of Informath's lexical functions, by their category:
    word (lower case, without accents) -> {category: the word as written}."""

    CATEGORIES = ('Noun', 'Adj', 'ProperName', 'Adverb')

    def __init__(self, pgf, cache):
        if os.path.exists(cache) and os.path.getmtime(cache) > os.path.getmtime(pgf):
            funs = json.load(open(cache))
        else:
            funs = self.read(pgf)
            json.dump(funs, open(cache, 'w'), ensure_ascii=False)
        self.words = collections.defaultdict(dict)
        for f, (cat, forms) in funs.items():
            if forms and forms[0]:
                w = forms[0]
                for key in {fold(w), fold(w).replace('ä', 'ae')} | {fold(w.replace('ä', 'ae').replace('ö', 'oe').replace('ü', 'ue'))}:
                    self.words[key].setdefault(cat, w)
                if cat == 'Noun' and len(forms) > 1:
                    self.words[fold(forms[1])].setdefault('Plural', w)

    @staticmethod
    def read(pgf):
        """function -> (category, its English forms), by gf."""
        r = subprocess.run(['gf', '-run', pgf], input='pg -funs\n', capture_output=True, text=True)
        cats = {}
        for l in r.stdout.split('\n'):
            m = re.match(r'\s*(\S+) : (\w+) ;', l)
            if m and m.group(2) in Lexicon.CATEGORIES:
                cats[m.group(1)] = m.group(2)
        cmds = ''.join('l -treebank -list -lang=InformathEng %s\n' % f for f in cats)
        r = subprocess.run(['gf', '-run', pgf], input=cmds, capture_output=True, text=True)
        out, cur = {}, None
        for l in r.stdout.split('\n'):
            m = re.match(r'Informath: (\S+)', l)
            if m:
                cur = m.group(1)
                continue
            m = re.match(r'InformathEng: (.*)', l)
            if m and cur in cats:
                out[cur] = (cats[cur], [x.strip() for x in m.group(1).split(',')])
        return out

    def get(self, w, *cats):
        e = self.words.get(fold(w), {})
        for c in cats:
            if c in e:
                return e[c]
        return None

    def content(self, w):
        """The word as a noun, an adjective or a proper name of the lexicon, or None."""
        return self.get(w, 'Noun', 'Adj', 'ProperName', 'Plural')

    def lemmas(self):
        return {k: e for k, e in self.words.items() if any(c in e for c in ('Noun', 'Adj', 'ProperName'))}


def nominal(w, lex):
    """The noun of the lexicon that names the action of a verb, or None."""
    if w in NOT_NOMINAL:
        return None
    if w in NOMINALS:
        return lex.get(NOMINALS[w], 'Noun')
    forms = [w + 'ion', w[:-1] + 'ion', w + 'ation', w[:-1] + 'ation', w + 'ment', w + 'al', w[:-1] + 'al',
             w[:-1] + 'ure', w + 'ing', w[:-1] + 'ing', w + 'ure']
    if w.endswith('ize'):
        forms.insert(0, w[:-3] + 'ization')
    if w.endswith('ify'):
        forms.insert(0, w[:-3] + 'ification')
    for f in forms:
        if f != w and lex.get(f, 'Noun'):
            return lex.get(f, 'Noun')
    return None


def abbreviates(a, lemma):
    """Whether a is a prefix of lemma, or its letters in order with the same first two."""
    l = fold(lemma)
    if len(l) <= len(a):
        return False
    if l.startswith(a):
        return True
    if l[:2] != a[:2] or len(l) > 3 * len(a):
        return False
    i = 0
    for c in l:
        if i < len(a) and c == a[i]:
            i += 1
    return i == len(a)


def doc_words(doc):
    prose = re.sub(r'`[^`]*`|\$[^$]*\$|\[[^\]]*\]\([^)]*\)', ' ', doc)
    return {fold(w) for w in re.findall(r"[A-Za-zÀ-ÿ][a-zà-ÿ]+", prose)}


class Repairer:
    """The replacements of the words of names, with their evidence."""

    def __init__(self, lex, defs, words_of, dic, proper):
        self.lex = lex
        self.dic = dic                              # DictEng: word -> {'N': plural, 'A', 'V', 'Adv'}
        self.proper = proper                        # lower case -> a proper name as written
        self.lemmas = lex.lemmas()
        self.uses = collections.Counter()           # (word, replacement) -> entries that use it
        self.evidence = {}
        # abbreviation -> lemma -> how many docstrings of definitions whose names
        # have it use the lemma
        self.assoc = collections.defaultdict(collections.Counter)
        self.docs = {}
        self.unknown = set()
        for d in defs:
            ws = {w for w in words_of(d) if w.isalpha() and not lex.content(w) and w not in FUNCTION_WORDS}
            self.unknown |= ws
            dw = doc_words(d['doc'])
            self.docs[d['dk']] = dw
            for w in ws:
                for l in dw:
                    if l in self.lemmas and abbreviates(w, l):
                        self.assoc[w][l] += 1
        self.cands = {w: sorted(l for l in self.lemmas if abbreviates(w, l)) for w in self.unknown if len(w) >= 3}

    def lemma(self, l):
        e = self.lemmas[l]
        w = e.get('Noun') or e.get('Adj') or e.get('ProperName')
        return self.proper.get(w.lower(), w)

    def word(self, w, dk, cat, head):
        """(replacement, how it was found) for a word of a name, or None."""
        if w in FUNCTION_WORDS or not w.isalpha() or w[0].isupper():
            return None
        if w in HEADS:
            return (HEADS[w], 'Mathlib') if head else None
        if w in SPELLED:
            return SPELLED[w], 'Mathlib'
        if w in ADJECTIVAL and cat == 'Exp':
            return None
        if self.lex.get(w, 'Plural'):
            return None                             # from_name makes it singular
        c = self.lex.content(w)
        if c:
            c = self.proper.get(c.lower(), c)
            return (c, 'lexicon') if c != w else None
        n = nominal(w, self.lex) if 'V' in self.dic.get(w, {}) else None
        if n:
            return n, 'nominalization'
        if len(w) < 3 or w in NOT_ABBREVIATIONS:
            return None
        counts = self.assoc.get(w, collections.Counter())
        top = counts.most_common(2)
        if top and top[0][1] >= 3 and (len(top) == 1 or top[0][1] >= 2 * top[1][1]):
            return self.lemma(top[0][0]), 'docstrings (%s)' % ', '.join('%s %d' % (self.lemma(l), n) for l, n in top)
        here = [l for l in self.cands.get(w, []) if l in self.docs.get(dk, ())]
        if len(here) == 1 and len(w) >= 4 and not top[1:]:
            return self.lemma(here[0]), 'docstring'
        return None

    def repair(self, ws, dk, cat):
        """The words of a name with replacements, and the replacements made;
        no replacements in a name of more than two words, whose reading word
        by word is too often wrong, nor where a nominalization or an induced
        morphism comes before a word of TYPE_WORDS."""
        out, made = [], []
        if len(ws) > 2:
            return ws, []
        for i, w in enumerate(ws):
            r = self.word(w, dk, cat, i == len(ws) - 1)
            if r:
                out += r[0].split()
                made.append((w, r[0], r[1]))
            else:
                out.append(w)
        firsts = [ws.index(w) for w, r, how in made if how in ('nominalization', 'Mathlib')]
        if firsts and any(w in TYPE_WORDS for w in ws[min(firsts) + 1:]):
            return ws, []
        # Over.mapForget is no forgetful functor of a map
        if any(w in HEADS and ws.index(w) > 0 and ws[ws.index(w) - 1] in TYPE_WORDS for w, r, how in made):
            return ws, []
        # a nominalization before its object comes after it: restrict scalars -> scalar restriction
        for i, (w, r, how) in enumerate(made):
            if how == 'nominalization':
                k = len(out) - 1 - out[::-1].index(r)
                obj = out[k + 1:]
                if obj and all(self.lex.get(o, 'Noun', 'Plural') for o in obj):
                    out = out[:k] + [self.lex.get(o, 'Noun', 'Plural') for o in obj] + [r]
                break
        return out, made

    def used(self, made):
        for w, r, how in made:
            self.uses[(w, r)] += 1
            self.evidence[(w, r)] = how

    def write(self, path):
        with open(path, 'w') as f:
            f.write('word\treplacement\tfound by\tentries\n')
            for (w, r), n in sorted(self.uses.items(), key=lambda x: (-x[1], x[0])):
                f.write('%s\t%s\t%s\t%d\n' % (w, r, self.evidence[(w, r)], n))


def adjective_prep(ws, lex):
    """(adjective, preposition) of a predicate named X On, X At, X Within, or None."""
    if len(ws) >= 2 and ws[-1] in ('on', 'at', 'within'):
        adj = ' '.join(ws[:-1])
        if all(lex.get(w, 'Adj', 'Adverb') for w in ws[:-1]):
            return adj, ws[-1]
    return None
