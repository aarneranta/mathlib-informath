#!/usr/bin/env python3
"""The concepts of the informalized part of Mathlib, with their wordings and
how often they occur, as a table to view as a spreadsheet.

    python3 concept-table.py          # -> concepts.tsv

The part is the Mathlib modules of modules.txt (the undergraduate core and
the first pages; not the generated Structures pages). A concept is a constant
of their Dedukti translation: a Mathlib constant, or one of Informath's own
that mapping.tsv maps Mathlib's to (plus for HAdd.hAdd). Its occurrences are
counted in out/<Module>.dk, in the statements and in the definientia (term
proofs and definitions), and in the steps of the tactic proofs
(out/<Module>-tactic-units.json); a declaration's own name is not counted.
The rows are in descending order of all occurrences.

The columns: the Lean name(s), a link to Mathlib's documentation, the Dedukti
name, the kind of constant, its entry in the symbol tables (the last of
definitions.dkgf, mathlib.dkgf, structures.dkgf that has one; Informath's
share/baseconstants.dkgf for its own constants), where the entry comes from,
the occurrences, and the number of declarations whose statement uses it.
"""
import collections, glob, json, os, re

INFORMATH = os.environ.get('INFORMATH_ROOT', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'informath'))
DOCS = 'https://leanprover-community.github.io/mathlib4_docs/'
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")
# the words of the Dedukti syntax and of Informath's framework, not concepts
FRAMEWORK = {'def', 'thm', 'Set', 'Elem', 'Prop', 'Proof', 'Type'}
# Informath's constants that Export.lean writes for Lean's logic and equality
# itself, not by mapping.tsv
SPECIAL = {'Eqt': 'Eq', 'Eq': 'Eq (on numbers)', 'forall': '∀ (dependent function type)',
           'if': '→ (implication)', 'exists': 'Exists', 'not': 'Not',
           'ifI': 'fun (proof of an implication)', 'forallI': 'fun (proof of a ∀)',
           'ifE': 'application (of an implication)', 'forallE': 'application (of a ∀)'}


def category(ty):
    """What a constant is, by its Dedukti type: the codomain after its arrows."""
    depth, last = 0, 0
    for i, ch in enumerate(ty):
        depth += {'(': 1, ')': -1}.get(ch, 0)
        if depth == 0 and ty.startswith('->', i):
            last = i + 2
    cod = ty[last:].strip()
    if cod.startswith('Proof'):
        return 'theorem'
    if cod == 'Prop':
        return 'predicate'
    if cod in ('Set', 'Type'):
        return 'type'
    return 'function or constant'


def modules():
    return [l.split()[0] for l in open('modules.txt')
            if l.strip() and not l.startswith('#') and l.split()[0].startswith('Mathlib.')]


def blocks(path):
    """(Lean name, Dedukti name, type, definiens) of each declaration of a .dk file."""
    out = []
    for b in open(path).read().split('\n\n'):
        m = re.search(r'\(; //LEAN:(\S+) ;\)\n(def )?(\S+) : (.*?)(?: :=\n(.*))?\.\s*$', b, re.S)
        if m:
            out.append((m.group(1), m.group(3), m.group(4), m.group(5) or ''))
    return out


def table_entries(path):
    """Dedukti name -> the text of its entry in a .dkgf file."""
    out = {}
    if not os.path.exists(path):
        return out
    for l in open(path):
        if l.startswith('#') or ':' not in l:
            continue
        name, entry = l.split(':', 1)
        if name.strip() and ' ' not in name.strip():
            out[name.strip()] = entry.strip()
    return out


def main():
    ms = modules()
    lean_of, kind_of, module_of, type_of = {}, {}, {}, {}
    # the declarations of the modules and their dependencies
    for m in ms:
        for f in ['out/%s.json' % m]:
            if os.path.exists(f):
                for d in json.load(open(f)):
                    lean_of.setdefault(d['dk'], d['lean'])
                    kind_of.setdefault(d['dk'], d.get('kind', ''))
                    module_of.setdefault(d['dk'], m)
        for lean, dk, ty, _ in blocks('out/%s-deps.dk' % m):
            lean_of.setdefault(dk, lean)
            type_of.setdefault(dk, ty)
        for lean, dk, ty, _ in blocks('out/%s.dk' % m):
            type_of.setdefault(dk, ty)
    for l in open('out/definitions.jsonl'):
        d = json.loads(l)
        if d['dk'] in lean_of or True:
            module_of.setdefault(d['dk'], d['module'])
            kind_of.setdefault(d['dk'], d['kind'])
            lean_of.setdefault(d['dk'], d['lean'])
    # Informath's own constants, and the Lean constants mapped to them
    base, rules = set(), set()
    for f in [os.path.join(INFORMATH, 'share', 'baseconstants.dk'), 'nd.dk']:
        for l in open(f):
            m = re.match(r"(?:def |thm |injective )?([A-Za-z_][A-Za-z0-9_']*)\s*:", l)
            if m:
                base.add(m.group(1))
                if f == 'nd.dk':
                    rules.add(m.group(1))
    mapped = collections.defaultdict(list)
    for l in open('mapping.tsv'):
        if l.startswith('#') or not l.strip():
            continue
        cols = l.rstrip('\n').split('\t')
        if len(cols) >= 2:
            mapped[cols[1]].append(cols[0])
    # the entries, the later tables overriding the earlier ones, and their sources
    entries, source = {}, {}
    gen = {}
    for l in open('out/definition-table.tsv').readlines()[1:]:
        c = l.rstrip('\n').split('\t')
        if c[4]:
            gen[c[0]] = c[5]
    names = {'name': 'name (camel case)', 'doc': 'docstring', 'lexicon': 'name with lexicon words'}
    for dk, e in table_entries('definitions.dkgf').items():
        entries[dk] = e
        source[dk] = names.get(gen.get(dk), 'Lean notation' if e.startswith('$') else 'generated')
        if gen.get(dk) and '|' in e:
            source[dk] += ' + Lean notation'
    for dk, e in table_entries('mathlib.dkgf').items():
        entries[dk], source[dk] = e, 'hand-written (mathlib.dkgf)'
    for dk, e in table_entries('structures.dkgf').items():
        entries[dk], source[dk] = e, 'structures (structures.dkgf)'
    for dk, e in table_entries(os.path.join(INFORMATH, 'share', 'baseconstants.dkgf')).items():
        if dk in base and dk not in entries:
            entries[dk], source[dk] = e, 'Informath base (baseconstants.dkgf)'
    declared = set(lean_of) | base | set(mapped)

    # the occurrences
    stmt, proof, tactic = collections.Counter(), collections.Counter(), collections.Counter()
    using = collections.Counter()
    def count(text, counter, own=None):
        found = set()
        for t in IDENT.findall(text):
            if t in declared and t not in FRAMEWORK and t != own:
                counter[t] += 1
                found.add(t)
        return found
    for m in ms:
        for _, dk, ty, defn in blocks('out/%s.dk' % m):
            for c in count(ty, stmt, dk):
                using[c] += 1
            count(defn, proof, dk)
        units = 'out/%s-tactic-units.json' % m
        if os.path.exists(units):
            for p in json.load(open(units)):
                for st in p['steps']:
                    texts = [st.get('prop', ''), st.get('goal', '')] + [t for _, t in st.get('hypos', [])]
                    for t in texts:
                        if isinstance(t, str):
                            count(t, tactic)

    rows = []
    for c in set(stmt) | set(proof) | set(tactic):
        total = stmt[c] + proof[c] + tactic[c]
        if c in base or c in mapped:
            leans = mapped.get(c, []) or ([SPECIAL[c]] if c in SPECIAL else
                                          [lean_of[c]] if c in lean_of else [])
            lean = ', '.join(leans) if leans else '(Informath)'
            first = leans[0].split(' ')[0] if leans else ''
            url = (DOCS + 'find/?pattern=%s#doc' % first) if first and first[0].isalpha() and first != 'fun' and first != 'application' else ''
            kind = 'natural deduction rule' if c in rules else 'Informath base'
        else:
            lean = lean_of.get(c, c)
            if c.endswith('__app') and c not in lean_of:
                lean = lean_of.get(c[:-5], c[:-5].replace('__', '.')) + ' (applied by coercion)'
            mod = module_of.get(c)
            name = lean.split(' ')[0]
            url = DOCS + (mod.replace('.', '/') + '.html#' + name if mod else 'find/?pattern=%s#doc' % name)
            kind = kind_of.get(c) or ('function applied by coercion' if c.endswith('__app') else '')
            cat = category(type_of[c]) if c in type_of else ''
            kind = (kind + ', ' + cat if kind and cat and cat not in kind else kind or cat or 'unknown')
        none = ('proof rule (nd.dk), read as the structure of a proof' if c in rules
                else 'theorem (cited by name)' if 'theorem' in kind and c not in entries
                else 'none (shown as the Lean name)')
        rows.append((total, lean, url, c, kind, entries.get(c, ''), source.get(c, none),
                     stmt[c], proof[c], tactic[c], using[c]))
    rows.sort(key=lambda r: (-r[0], r[1]))
    with open('concepts.tsv', 'w') as f:
        f.write('\t'.join(['rank', 'Mathlib id', 'documentation', 'Dedukti id', 'kind', 'Informath entry', 'source',
                           'occurrences', 'in statements', 'in term proofs and definitions',
                           'in tactic proof steps', 'statements using it']) + '\n')
        for i, r in enumerate(rows, 1):
            f.write('\t'.join([str(i), r[1], r[2], r[3], r[4], r[5], r[6]] + [str(x) for x in (r[0],) + r[7:]]) + '\n')
    print('%d concepts in %d modules -> concepts.tsv; %d occurrences' % (len(rows), len(ms), sum(r[0] for r in rows)))
    by = collections.Counter(r[6] for r in rows)
    occ = collections.Counter()
    for r in rows:
        occ[r[6]] += r[0]
    for s, n in by.most_common():
        print('  %-40s %6d concepts %8d occurrences' % (s, n, occ[s]))


if __name__ == '__main__':
    main()
