"""Statistics of an informalized project, for the tables of the paper: the
size of its Lean code (characters, declarations), the size without proofs,
the size of the generated English, the concepts it uses and defines, and the
concepts with and without symbol table entries.

    python3 examples/stats.py <example dir> <project source dir> [--latex]

The whole project is every .lean file under the source dir (not .lake); the
informalized part is the modules of <example>/work/index.json. A declaration
is a line starting with one of DECL (after attributes and modifiers); its
text runs to the next declaration or command at the start of a line. "Without
proofs": a theorem or lemma up to the := (or the where, or |) that ends its
statement, any other declaration whole; comments and commands (import, open,
namespace, ...) are not counted. A concept defined is a declaration that is
not a theorem, lemma, instance or example. The concepts used, and their
entries, are those of <example>/constants.tsv (the constants that the readings
show).
"""
import csv, collections, json, os, re, sys

DECL = r'(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|example|opaque|axiom)'
START = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*(' + DECL + r')\b')
COMMAND = re.compile(r'^(?:import|open|namespace|end|section|variable|universe|set_option|attribute|noncomputable section|#|/-|--|@\[)')
PROOF_KINDS = {'theorem', 'lemma'}
CONCEPT_KINDS = {'def', 'abbrev', 'structure', 'class', 'inductive', 'opaque', 'axiom'}


def strip_comments(text):
    text = re.sub(r'/-.*?-/', '', text, flags=re.S)
    return re.sub(r'--[^\n]*', '', text)


def statement_part(text):
    """A theorem up to the := (or where, or the first | of equations) at depth 0."""
    depth, i = 0, 0
    while i < len(text):
        c = text[i]
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        elif depth == 0 and text.startswith(':=', i):
            return text[:i]
        elif depth == 0 and (text.startswith('\n  |', i) or text.startswith(' where', i)):
            return text[:i]
        i += 1
    return text


def declarations(path):
    """(kind, text) of the declarations of a file."""
    lines = open(path, encoding='utf8').read().split('\n')
    out, cur = [], None
    for l in lines:
        m = START.match(l)
        if m:
            if cur:
                out.append(cur)
            cur = [m.group(1), [l]]
        elif cur and (l.strip() == '' or l[0].isspace() or l.startswith('|') or l.startswith('where')) and not COMMAND.match(l):
            cur[1].append(l)
        elif cur and not COMMAND.match(l) and not l[0].isspace():
            cur[1].append(l)      # a continuation at column 0 (rare)
        else:
            if cur:
                out.append(cur)
            cur = None
    if cur:
        out.append(cur)
    return [(k, strip_comments('\n'.join(t)).rstrip()) for k, t in out]


def measure(files):
    chars = sum(os.path.getsize(f) for f in files)
    n = noproof = concepts = 0
    for f in files:
        for kind, text in declarations(f):
            n += 1
            noproof += len(statement_part(text) if kind in PROOF_KINDS else text)
            concepts += kind in CONCEPT_KINDS
    return {'files': len(files), 'chars': chars, 'decls': n, 'noproof': noproof, 'concepts': concepts}


def main():
    ex, src = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])
    allfiles = [os.path.join(d, f) for d, ds, fs in os.walk(src) for f in fs
                if f.endswith('.lean') and '.lake' not in d]
    ix = json.load(open(os.path.join(ex, 'work', 'index.json')))
    mods = sorted({d['module'] for d in ix['declarations']})
    sample = [os.path.join(src, *m.split('.')) + '.lean' for m in mods]
    sample = [f for f in sample if os.path.exists(f)]
    whole, part = measure(allfiles), measure(sample)
    decls = ix['declarations']
    part['exported'] = len(decls)
    part['english'] = sum(len(d['readings'].get('Eng') or '') for d in decls)
    part['formula'] = sum(len(d['readings'].get('formula') or '') for d in decls)
    part['concepts_exported'] = sum(1 for d in decls if d['kind'] not in ('theorem', 'instance'))
    rows = list(csv.DictReader(open(os.path.join(ex, 'constants.tsv')), delimiter='\t'))
    own = {r['defined in'] for r in rows} - {'Mathlib', 'Lean', '?', ''}
    def entry_kind(r):
        t = r['table']
        if not r['entry']:
            return 'none'
        if t.startswith('examples/') and t.endswith('-names.dkgf'):
            return 'generated name'
        if t.startswith('examples/'):
            return 'hand-written (project)'
        if t == 'definitions.dkgf':
            return 'generated (Mathlib)'
        return 'hand-written (Mathlib, Informath)'
    used = collections.Counter()
    for r in rows:
        origin = 'project' if r['defined in'] in own else r['defined in']
        used[(origin, entry_kind(r))] += 1
    out = {'whole': whole, 'part': part, 'used': {'%s/%s' % k: v for k, v in sorted(used.items())},
           'used_by_origin': dict(collections.Counter('project' if r['defined in'] in own else r['defined in'] for r in rows))}
    json.dump(out, sys.stdout, indent=1, ensure_ascii=False)
    print()


if __name__ == '__main__':
    main()
