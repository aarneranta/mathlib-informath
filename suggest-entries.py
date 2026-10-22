#!/usr/bin/env python3
"""Suggest verbal symbol table entries for Mathlib constants, from their
docstrings and their names, keeping those that Informath's grammar parses.

    python3 suggest-entries.py               # -> suggestions.tsv, and a summary
    python3 suggest-entries.py -all          # also constants that have a verbal entry

For each constant used by the exported statements (out/*.dk) that has no
verbal form in mathlib.dkgf, candidates are made

* from its docstring, by patterns such as "`f n` is the X of `n`", "The X of
  `m` and `n` is ...", "Returns the X of ...", "A set is bounded above if ..."
  and "`n` is a prime power if ...", with the argument names in backticks
  replaced by #1, #2, ... after the constant's binders;
* from its name, which Mathlib's naming conventions make a noun phrase for a
  function (primeFactorsList: "the prime factor list of #1") and a predicate
  for a proposition (IsPrimePow: "#1 is a prime pow");

and each is tried with RunInformath -parse-example.  suggestions.tsv has, for
each constant, its type, the candidates that parse with their source, and the
ones that do not.  The first that parses is the suggestion.
"""
import glob, json, os, re, subprocess, sys


def informath():
    root = os.environ.get('INFORMATH_ROOT')
    built = glob.glob(os.path.join(root or '', '.stack-work', 'dist', '*', '*', 'build', 'RunInformath', 'RunInformath'))
    return max(built, key=os.path.getmtime) if built else 'RunInformath'


RUN = informath()


def constants():
    """name -> (Dedukti type, docstring) for the constants of out/*.dk."""
    out, docs = {}, {}
    for f in sorted(glob.glob('out/*.json')):
        for d in json.load(open(f)):
            if d['doc']:
                docs[d['dk']] = d['doc']
    for f in sorted(glob.glob('out/*.dk')):
        doc = None
        for line in open(f):
            m = re.match(r'\(; doc: (.*) ;\)$', line.strip())
            if m:
                doc = m.group(1)
                continue
            if line.startswith('(; //LEAN:'):
                continue                   # the tag between the docstring and the declaration
            m = re.match(r'(?:def )?([A-Za-z_0-9\']+) : (.*?)( :=)?\.?$', line.rstrip())
            if m and m.group(1) not in out:
                out[m.group(1)] = (m.group(2), doc or docs.get(m.group(1), ''))
            doc = None
    return out


def verbal_entries():
    out = set()
    for l in open('mathlib.dkgf'):
        m = re.match(r'^([A-Za-z_0-9\']+) : (.*)$', l)
        if m and '"' in m.group(2):
            out.add(m.group(1))
    return out


def used_constants():
    used = set()
    for f in glob.glob('out/*.dk'):
        if f.endswith('-deps.dk'):
            continue
        used |= set(re.findall(r'[A-Za-z][A-Za-z_0-9\']*', open(f).read()))
    return used


def signature(typ):
    """(argument names, value category) of a Dedukti type: Exp, Prop or Kind."""
    names, depth, i = [], 0, 0
    for m in re.finditer(r'\((\w+) : ', typ):
        names.append(m.group(1))
    # the value: what follows the last top-level ->
    parts, depth, cur = [], 0, ''
    for ch in typ:
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        cur += ch
        if depth == 0 and cur.endswith('->'):
            parts.append(cur[:-2])
            cur = ''
    value = cur.strip()
    VALUE[0] = value
    nargs = len(parts)
    cat = 'Prop' if value in ('Prop',) else 'Kind' if value == 'Set' else 'Exp'
    if value.startswith('Proof'):
        cat = 'Proof'
    return names[:nargs], nargs, cat


VALUE = ['']


def words_of_name(dk):
    """primeFactorsList -> ['prime', 'factors', 'list']: the last part of the
    name, split at its capitals and underscores."""
    last = dk.split('__')[-1]
    if last == 'app' and '__' in dk:
        last = dk.split('__')[-2]
    ws = re.findall(r'[A-Z]?[a-z]+|[A-Z]+(?![a-z])|\d+', last.replace('_', ' '))
    return [w.lower() for w in ws]


def singular(w):
    for a, b in [('ies', 'y'), ('sses', 'ss'), ('ors', 'or'), ('ers', 'er'), ('es', 'e'), ('s', '')]:
        if w.endswith(a) and len(w) > len(a) + 2 and not w.endswith('ss'):
            return w[:-len(a)] + b
    return w


def args_phrase(k):
    return {0: '', 1: ' of #1', 2: ' of #1 and #2'}.get(k, ' of ' + ', '.join('#%d' % i for i in range(1, k)) + ' and #%d' % k)


def from_name(dk, nargs, cat):
    ws = words_of_name(dk)
    if not ws:
        return []
    out = []
    if cat == 'Prop':
        if ws[0] == 'is':
            rest = ws[1:]
            if rest:
                out += ['#1 is a %s' % ' '.join(rest), '#1 is %s' % ' '.join(rest)]
        else:
            out += ['#1 is %s' % ' '.join(ws)]
    elif cat == 'Kind':
        out += [' '.join(singular(w) for w in ws) + args_phrase(nargs).replace(' and ', ' and ')]
    elif cat == 'Exp':
        collection = re.match(r'Elem \((Finset|List|Multiset|powerset)\b', VALUE[0])
        if collection and ws[-1].endswith('s') and ws[-1] != 'list':
            # a set of elements, named in the plural: the set of divisors of n
            np = ' '.join([singular(w) for w in ws[:-1]] + [ws[-1]])
            kind = 'list' if collection.group(1) == 'List' else 'set'
            out += ['the %s of %s%s' % (kind, np, args_phrase(nargs))]
        np = ' '.join([singular(w) for w in ws[:-1]] + [singular(ws[-1])])
        out += ['the %s%s' % (np, args_phrase(nargs))]
    return out


def strip_md(s):
    return re.sub(r'\s+', ' ', s).strip()


def from_doc(dk, doc, names, nargs, cat):
    """Candidates from the patterns of the docstring, with the backticked
    argument names replaced by #1, #2, ..."""
    if not doc:
        return []
    d = strip_md(doc)
    first = re.split(r'(?<=[a-z0-9`)])\. ', d)[0]
    pos = {n: '#%d' % (i + 1) for i, n in enumerate(names)}
    if not any('`%s`' % n in d for n in names):
        # the docstring names the arguments otherwise: in the order they come
        order = []
        for m in re.finditer(r'`([a-z][A-Za-z0-9_\']*)`', d):
            if m.group(1) not in order and m.group(1) != dk.split('__')[-1]:
                order.append(m.group(1))
        pos = {n: '#%d' % (i + 1) for i, n in enumerate(order[:nargs])}

    def args(s):
        s = re.sub(r'`([^`]*)`', lambda m: pos.get(m.group(1).strip(), '`' + m.group(1) + '`'), s)
        return s
    out = []
    if cat in ('Exp', 'Kind'):
        pats = [r'^`[^`]*` is the (.+?)(?:[,.;]|$)',
                r'^`[^`]*` is (?:an?|the) (.+?)(?:[,.;]|$)',
                r'^[Tt]he (.+?) (?:of a|of an|is|are|as)\b',
                r'^Returns the (.+?)(?:[,.;]|$)',
                r'^[Tt]he (.+?)\.?$']
        for p in pats:
            m = re.search(p, first)
            if m:
                np = args(m.group(1)).strip()
                np = re.sub(r'\s*`[^`]*`.*$', '', np)          # cut at leftover code
                if not np:
                    continue
                np = re.sub(r'\s+(of|in|at|to)$', r' \1 #1', np) if '#' not in np and nargs else np
                if cat == 'Exp':
                    c = 'the ' + np if not np.startswith('the ') else np
                    if '#' not in c and nargs:
                        c += args_phrase(nargs)
                else:
                    c = np
                out.append(c)
    if cat == 'Prop':
        pats = [r'^`[^`]*` is (an? [a-z -]+?) if\b', r'^`[^`]*` is ([a-z -]+?) if\b',
                r'^(?:A|An) [^`]*? is (?:called )?\*?(an? [a-z -]+?)\*? if\b',
                r'^(?:A|An) [^`]*? is (?:called )?\*?([a-z -]+?)\*? if\b',
                r'^(?:A|An) [a-z ]+ (holds [a-z]+) if\b',
                r'^(?:A|An) ([a-z -]+?) is (?:an?|the) ']
        for p in pats:
            m = re.search(p, first)
            if m:
                w = m.group(1).strip()
                if p.endswith("is (?:an?|the) '"):
                    w = ('an ' if w[0] in 'aeiou' else 'a ') + w
                out.append(('#1 ' + w) if w.startswith('holds') else ('#1 is ' + w))
    return [c for c in out if len(c) < 80]


KNOWN = {}


def unknown_words(ex):
    ws = [w for w in re.findall(r"[a-z][a-z'-]*", ex) if w not in ('the', 'of', 'and', 'is', 'a', 'an')]
    ask = [w for w in ws if w not in KNOWN]
    if ask:
        r = subprocess.run([RUN, '-find-gf'], input=' '.join(ask) + '\n', capture_output=True, text=True)
        for line in r.stdout.split('\n'):
            if ' :' in line:
                w, fs = line.split(' :', 1)
                KNOWN[w.strip()] = bool(fs.strip())
    return [w for w in ws if not KNOWN.get(w, True)]


def parses(ex):
    r = subprocess.run([RUN, '-parse-example'], input=ex + '\n', capture_output=True, text=True)
    return bool(r.stdout.strip())


def main():
    allc = '-all' in sys.argv[1:]
    cs = constants()
    have = verbal_entries()
    used = used_constants()
    rows, got = [], 0
    names = sorted(c for c in cs if c in used and (allc or c not in have))
    for dk in names:
        typ, doc = cs[dk]
        argnames, nargs, cat = signature(typ)
        if cat == 'Proof':
            continue                       # theorems need no entry
        cands = [(c, 'doc') for c in from_doc(dk, doc, argnames, nargs, cat)] + \
                [(c, 'name') for c in from_name(dk, nargs, cat)]
        seen, ok, bad = set(), [], []
        for c, src in cands:
            if c in seen:
                continue
            seen.add(c)
            (ok if parses(c) else bad).append((c, src))
        got += bool(ok)
        rows.append((dk, cat, nargs, ok, bad))
    with open('suggestions.tsv', 'w') as f:
        f.write('constant\tcategory\targuments\tsuggestion\tsource\tother parsing\tnot parsing (unknown words)\n')
        for dk, cat, nargs, ok, bad in rows:
            f.write('%s\t%s\t%d\t%s\t%s\t%s\t%s\n' % (
                dk, cat, nargs, ok[0][0] if ok else '', ok[0][1] if ok else '',
                ' | '.join(c for c, _ in ok[1:]),
                ' | '.join('%s (%s) [%s]' % (c, src, ' '.join(unknown_words(c))) for c, src in bad)))
    print('%d constants, %d with a suggestion that parses -> suggestions.tsv' % (len(rows), got))
    for dk, cat, nargs, ok, bad in rows:
        if ok:
            shown = '"%s" (%s)' % ok[0]
        else:
            docs = [(c, unknown_words(c)) for c, src in bad if src == 'doc']
            shown = '-- ' + ' | '.join('%s [%s]' % (c, ' '.join(u)) for c, u in docs[:2]) if docs \
                else '-- ' + ' | '.join(c for c, _ in bad[:1])
        print('%-30s %-5s %s' % (dk, cat, shown))


if __name__ == '__main__':
    main()
