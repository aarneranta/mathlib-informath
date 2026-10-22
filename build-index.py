#!/usr/bin/env python3
"""Build index.json: for each exported Mathlib declaration, its Dedukti
translation and Informath's informalizations, in English, in French and as a
LaTeX formula, with the proof texts of the theorems in English and French.
build-html.py makes the pages from it.

    lake exe export $(grep -v '^#' modules.txt)   # -> out/<Module>.dk, .json, -deps.dk
    python3 build-index.py                        # -> index.json
    python3 build-html.py                         # -> mathlib-informath.html, pages/*.html

RunInformath loads its grammar of English and French (share/InformathFull.pgf)
in a few seconds, so the statements of all modules are read in one call, which
gives both languages (-json -languages=Eng,Fre), and so are the proofs
(-proof-text -languages=Eng,Fre), with a new call after a proof that Informath
cannot render.  The formulas are read in another call, with the English
grammar only and the full symbol table.  RunInformath is the newest one built
in $INFORMATH_ROOT (stack build), or the one on the PATH.
"""
import difflib, glob, json, os, re, subprocess, sys

MATHLIB = os.environ.get('MATHLIB', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'mathlib4'))
TABLE = 'mathlib.dkgf'
INDEX = 'index.json'
LANGUAGES = ['Eng', 'Fre']        # the verbal readings; build-html.py shows them in this order
PROOF_TIMEOUT = 300               # seconds for one call of -proof-text
TMP = '.index-'                   # prefix of the temporary files


def informath():
    root = os.environ.get('INFORMATH_ROOT')
    if not root:
        sys.exit('INFORMATH_ROOT is not set')
    built = glob.glob(os.path.join(root, '.stack-work', 'dist', '*', '*', 'build', 'RunInformath', 'RunInformath'))
    return max(built, key=os.path.getmtime) if built else 'RunInformath'


RUN = None


def run(*args):
    r = subprocess.run([RUN] + list(args), capture_output=True, text=True)
    if r.returncode:
        sys.exit('RunInformath failed: %s\n%s' % (' '.join(args), r.stderr[-1500:]))
    return [l for l in r.stdout.split('\n') if l.strip()]


def write(name, text):
    path = TMP + name
    open(path, 'w').write(text)
    return path


# ---------------------------------------------------------------- the export

PAGE = {}   # module -> its page, from the "# page: X" lines of modules.txt


def read_modules():
    """The modules of modules.txt, in its order; a "# page: X" line puts the
    modules after it on page X, "# page:" alone ends that."""
    modules, page = [], None
    for l in open('modules.txt'):
        l = l.strip()
        if l.startswith('# page:'):
            page = l[len('# page:'):].strip() or None
        elif l and not l.startswith('#'):
            modules.append(l)
            if page:
                PAGE[l] = page
    return modules


def group_of(module):
    """The page of a module: the one given in modules.txt, or else its
    directory, Mathlib.Data.Nat.Prime for Mathlib.Data.Nat.Prime.Defs."""
    return PAGE.get(module) or module.rsplit('.', 1)[0]


def dk_blocks(path):
    """Lean name -> its Dedukti declaration, from the //LEAN tags."""
    out, name, block = {}, None, []
    for line in open(path).read().split('\n') + ['']:
        m = re.match(r'\(; //LEAN:(.*) ;\)$', line)
        if m:
            name, block = m.group(1), []
        elif name and line.strip():
            block.append(line)
        elif name and not line.strip():
            out[name] = '\n'.join(block)
            name = None
    return out


def is_theorem(d):
    """A theorem is labelled with its name, anything else with "Definition"."""
    return d['kind'] == 'theorem'


def statements(m, decls):
    """out/<m>.dk with the proofs of its theorems dropped (definitions keep
    their definiens): what the readings are made from, and the module's part
    of the base of the proof texts."""
    text = open('out/%s.dk' % m).read()
    theorems = {d['dk'] for d in decls if is_theorem(d)}

    def one(mt):
        name = mt.group(1)
        return '%s : %s.' % (name, mt.group(2)) if name in theorems else mt.group(0)
    return re.sub(r'^def ([^ ]+) : (.*?) :=\n  .*?\.$', one, text, flags=re.S | re.M)


def drop_instances(text):
    """The hypotheses (_ : Proof (...)) -> of the declarations left out."""
    out, i = [], 0
    while True:
        k = text.find('(_ : Proof (', i)
        if k < 0:
            break
        depth, j = 0, k
        while j < len(text):
            depth += {'(': 1, ')': -1}.get(text[j], 0)
            if depth == 0:
                break
            j += 1
        out.append(text[i:k])
        i = j + 1
        if text.startswith(' -> ', i):
            i += 4
    out.append(text[i:])
    return ''.join(out)


# ---------------------------------------------------------------- the readings

# Lean names written as notation, $\operatorname{primeFactors}(#1)$, are what
# formulas can do; English uses the words of the entry instead
PSEUDO = re.compile(r'\s*\|\s*\$\\operatorname\{[A-Za-z]+\}\([^$]*\)\$|\$\\operatorname\{[A-Za-z]+\}\([^$]*\)\$\s*\|\s*')
STANDARD = 'lcm|gcd|max|min|supp|deg|card|ord'


def verbal_table():
    """mathlib.dkgf without the pseudo-notations of the entries that have
    words, for the verbal readings (English and French: Informath parses the
    verbal forms in English and linearizes the trees in each language)."""
    out = []
    for l in open(TABLE):
        if not l.startswith('#') and '"' in l and '\\operatorname{' in l:
            def drop(m):   # the operator names of mathematics are notation, not Lean
                return m.group(0) if re.search(r'operatorname\{(%s)\}' % STANDARD, m.group(0)) else ' | '
            l = PSEUDO.sub(drop, l).replace('|  |', '|').rstrip(' |\n') + '\n'
        out.append(l)
    return write('verbal.dkgf', ''.join(out))


LABEL = re.compile(r'^\S+\.\s+')    # Nat__Prime__pos. / Definition. / Définition.


def verbal_readings(dk, table, force=False):
    """Dedukti name -> language -> reading, all languages in one call."""
    lines = run('-json', '-no-back-to-dedukti', '-languages=' + ','.join(LANGUAGES),
                '-add-symboltables=' + table, *(['-force-symbolic'] if force else []), dk)
    out = {}
    for l in lines:
        r = json.loads(l)
        ws = r['originalDedukti'].split()
        name = ws[1] if ws[0] == 'def' else ws[0]
        for lang in LANGUAGES:
            ranks = r['nlgResults'].get('Informath' + lang)
            if ranks:
                out.setdefault(name, {})[lang] = LABEL.sub('', ranks[0]['lin'], count=1)
    return out


def formulas(dk, decls, force=False):
    """Lean name -> formula, aligned with the declarations by their labels."""
    lines = run('-add-symboltables=' + TABLE, '-to-symbolic-latex', *(['-force-symbolic'] if force else []), dk)
    lab = re.compile(r'^\\textbf\{(\w+)\}(?: \\texttt\{\\detokenize\{([^}]*)\}\})?\.\s*')
    # a theorem is labelled with its name, a definition with "Definition", and
    # a constant without a definiens (a structure's constructor) as an axiom
    # with its name, which counts as "Definition" here
    others = {d['dk'] for d in decls if not is_theorem(d)}
    labels = [(lambda m: (m.group(2) or m.group(1)) if m else '?')(lab.match(l)) for l in lines]
    labels = ['Definition' if x in others else x for x in labels]
    expected = [d['dk'] if is_theorem(d) else 'Definition' for d in decls]
    out = {}
    sm = difflib.SequenceMatcher(a=expected, b=labels, autojunk=False)
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal':
            for k in range(i2 - i1):
                out[decls[i1 + k]['lean']] = lab.sub('', lines[j1 + k]).strip()
    return out


def proof_texts(base, proofs):
    """Dedukti blocks of proved theorems -> language -> the rows (number,
    sentence, justification) of each proof text; a proof that Informath
    cannot render stops its call, and the next call starts after it."""
    out, failed, i = [], [], 0
    while i < len(proofs):
        rest = write('proofs.dk', '\n\n'.join(proofs[i:]) + '\n')
        try:
            r = subprocess.run([RUN, '-proof-text', '-languages=' + ','.join(LANGUAGES), '-base=' + base,
                                '-add-symboltables=' + TABLE, rest],
                               capture_output=True, text=True, timeout=PROOF_TIMEOUT)
            stdout, error = r.stdout, r.returncode != 0
        except subprocess.TimeoutExpired as e:
            stdout, error = e.stdout or '', True
            stdout = stdout.decode() if isinstance(stdout, bytes) else stdout
        for sec in re.split(r'\\subsection\*', stdout)[1:]:
            tables = re.findall(r'\\begin\{tabular\}\{[^\n]*\}\n(.*?)\\end\{tabular\}', sec, re.S)
            if len(tables) < len(LANGUAGES):
                break
            out.append({lang: rows(t) for lang, t in zip(LANGUAGES, tables)})
            i += 1
        if not error:
            break
        if i < len(proofs):
            failed.append(i)
            out.append(None)
            i += 1
    return out, failed


def rows(table):
    out = []
    for row in re.split(r'\\\\\s*\n', table):
        mt = re.match(r'\s*(\d+\.)\s*&(.*)&(.*)$', row, re.S)
        if mt:
            out.append([g.strip() for g in mt.groups()])
    return out


def macros(modules, verbal):
    """MathJax macros: those of mathlib.dkgf's LaTeX forms, and Informath's own."""
    base = write('base.dk', ''.join(open('out/%s-deps.dk' % m).read() + '\n' + open('out/%s.dk' % m).read() + '\n'
                                    for m in modules))
    # the macros are numbered after their position in the table, so the verbal
    # table, which has fewer LaTeX forms, names them otherwise: both sets are needed
    lines = run('-base=' + base, TABLE) + run('-base=' + base, verbal)
    share = os.path.join(os.environ['INFORMATH_ROOT'], 'share', 'baseconstants.dkgf')
    lines += [l[len('#MACRO '):] for l in open(share) if l.startswith('#MACRO ')]
    out = {}
    for l in lines:
        m = re.match(r'\\newcommand\{\\(\w+)\}(?:\[(\d+)\])?\{(.*)\}\s*$', l.strip())
        if m:
            d = [m.group(3), int(m.group(2))] if m.group(2) else m.group(3)
            if m.group(1) in out and out[m.group(1)] != d:
                print('MACRO CLASH: \\%s is %s in one table and %s in the other' % (m.group(1), out[m.group(1)], d))
            out[m.group(1)] = d
    return out


# ---------------------------------------------------------------- the index

def main():
    global RUN
    RUN = informath()
    modules = read_modules()
    decls, blocks, stmts, base = [], {}, [], []
    root = os.environ['INFORMATH_ROOT']
    base += [open(os.path.join(root, 'share', 'baseconstants.dk')).read(), open('nd.dk').read()]
    for m in modules:
        ds = json.load(open('out/%s.json' % m))
        for d in ds:
            d['module'] = m
        decls += ds
        blocks.update(dk_blocks('out/%s.dk' % m))
        s = statements(m, ds)
        stmts.append(s)
        # the lemmas are rules without their type class instances (Export.lean
        # writes those hypotheses (_ : Proof (C x)) and drops them in proofs)
        base += [drop_instances(open('out/%s-deps.dk' % m).read()), drop_instances(s)]
    verbal = verbal_table()
    all_stmts = write('statements.dk', '\n'.join(stmts))

    verb = verbal_readings(all_stmts, verbal)
    form = formulas(all_stmts, decls)
    texts = {d['lean']: dict(verb.get(d['dk'], {}), formula=form.get(d['lean'])) for d in decls}
    # a declaration without a reading is read with -force-symbolic, which writes
    # \mathrm{c}(...) where a constant has no form that fits
    forced = {}
    for modes in [LANGUAGES, ['formula']]:
        missing = [d for d in decls if d['lean'] in blocks and any(not texts[d['lean']].get(k) for k in modes)]
        if not missing:
            continue
        one = write('forced.dk', '\n\n'.join(blocks[d['lean']] for d in missing) + '\n')
        got = (lambda v: {d['lean']: v.get(d['dk'], {}) for d in missing})(verbal_readings(one, verbal, True)) \
            if modes == LANGUAGES else {k: {'formula': v} for k, v in formulas(one, missing, True).items()}
        for d in missing:
            for k in modes:
                if not texts[d['lean']].get(k) and got.get(d['lean'], {}).get(k):
                    texts[d['lean']][k] = got[d['lean']][k]
                    forced.setdefault(d['lean'], []).append(k)

    proved = [d for d in decls if is_theorem(d) and d.get('definiens') and d['lean'] in blocks]
    texts_of_proofs, failed = proof_texts(write('proof-base.dk', '\n'.join(base) + '\n'),
                                          [blocks[d['lean']] for d in proved])
    proofs = {d['lean']: p for d, p in zip(proved, texts_of_proofs) if p}

    commit = lambda path: subprocess.run(['git', '-C', path, 'rev-parse', 'HEAD'],
                                         capture_output=True, text=True).stdout.strip()
    index = {
        'mathlib': commit(MATHLIB),
        'informath': commit(root),
        'languages': LANGUAGES,
        'pages': [[g, [m for m in modules if group_of(m) == g]] for g in dict.fromkeys(map(group_of, modules))],
        'macros': macros(modules, verbal),
        'proofsFailed': [proved[i]['lean'] for i in failed],
        'declarations': [dict(d, dedukti=blocks.get(d['lean']), readings=texts[d['lean']],
                              forced=forced.get(d['lean'], []), proof=proofs.get(d['lean']))
                         for d in decls],
    }
    json.dump(index, open(INDEX, 'w'), ensure_ascii=False, indent=1)
    for f in glob.glob(TMP + '*'):
        os.remove(f)
    n = len(decls)
    print('%d declarations of %d modules -> %s: readings %s, %d formulas, %d proof texts (RunInformath: %s)'
          % (n, len(modules), INDEX,
             ', '.join('%d %s' % (sum(bool(texts[d['lean']].get(l)) for d in decls), l) for l in LANGUAGES),
             sum(bool(texts[d['lean']].get('formula')) for d in decls), len(proofs), RUN))
    if failed:
        print('%d proofs without a proof text: %s' % (len(failed), ' '.join(index['proofsFailed'])))


if __name__ == '__main__':
    main()
