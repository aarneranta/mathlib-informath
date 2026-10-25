#!/usr/bin/env python3
"""Build index.json: for each exported Mathlib declaration, its Dedukti
translation and Informath's informalizations, in English, in French and as a
LaTeX formula, with the proof texts of the theorems in English and French.
build-html.py makes the pages from it.

    lake exe export $(grep -v '^#' modules.txt)   # -> out/<Module>.dk, .json, -deps.dk
    python3 build-index.py                        # -> index.json
    python3 build-index.py --reuse-slow           # the same, German taken from index.json
    python3 build-html.py                         # -> mathlib-informath.html, pages/*.html

RunInformath loads its grammar of English and French (share/InformathFull.pgf)
in a few seconds, so the statements of all modules are read in one call, which
gives both languages (-json -languages=Eng,Fre), and so are the proofs
(-proof-text -languages=Eng,Fre), with a new call after a proof that Informath
cannot render.  The formulas are read in another call, with the English
grammar only and the full symbol table.  RunInformath is the newest one built
in $INFORMATH_ROOT (stack build), or the one on the PATH.

The symbol table is mathlib.dkgf, written by hand, on top of definitions.dkgf,
made by definition-table.py for all of Mathlib's definitions; the grammar must
have the words that definition-table.py -lexicon generated (make
full_grammar in Informath).
"""
import difflib, glob, json, os, re, subprocess, sys, time

MATHLIB = os.environ.get('MATHLIB', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'mathlib4'))
# the symbol tables, the later overriding the earlier: the generated entries of
# all Mathlib definitions (definition-table.py) and the hand-written ones
TABLES = ['definitions.dkgf', 'mathlib.dkgf']
TABLE = None                      # the two in one file, written by main
# a reading that the generated entries spoil in some language, as there is no
# word for them in it, is made with the hand-written table only
GENERATED_TABLES = ['definitions.dkgf']
PLACEHOLDER = re.compile(r"\[[A-Za-z0-9_']+_[A-Z][A-Za-z0-9]*\]")   # a function without a linearization
INDEX = 'index.json'
LANGUAGES = ['Eng', 'Fre', 'Cze', 'Ger', 'Swe']  # the verbal readings; build-html.py shows them in this order
# German linearization can take minutes on nested noun phrases (GF, RGL), so
# German is read apart, in chunks with a time limit of PER_ITEM seconds per
# statement or proof, on top of the time RunInformath takes to load; a slow
# statement gets no German
SLOW_LANGUAGES = ['Ger']
FAST_LANGUAGES = [l for l in LANGUAGES if l not in SLOW_LANGUAGES]
PER_ITEM = 1
CHUNK = 12
PROOF_TIMEOUT = 300               # seconds for one call of -proof-text in the fast languages
TACTIC_LANGUAGES = ['Eng', 'Fre', 'Cze', 'Ger', 'Swe']  # the languages of the proof texts of tactic proofs
TMP = '.index-'                   # prefix of the temporary files
OUT = 'out'                       # the directory of the exported modules


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
    text = open(OUT + '/%s.dk' % m).read()
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


def verbal_table(table=None, name='verbal.dkgf'):
    """The symbol table without the pseudo-notations of the entries that have
    words, for the verbal readings (English and French: Informath parses the
    verbal forms in English and linearizes the trees in each language)."""
    out = []
    for l in open(table or TABLE):
        if not l.startswith('#') and '"' in l and '\\operatorname{' in l:
            def drop(m):   # the operator names of mathematics are notation, not Lean
                return m.group(0) if re.search(r'operatorname\{(%s)\}' % STANDARD, m.group(0)) else ' | '
            l = PSEUDO.sub(drop, l).replace('|  |', '|').rstrip(' |\n') + '\n'
        out.append(l)
    return write(name, ''.join(out))


LABEL = re.compile(r'^\S+\.\s+')    # Nat__Prime__pos. / Definition. / Définition.


def verbal_readings(dk, table, langs, force=False, timeout=None):
    """Dedukti name -> language -> reading, the languages in one call; with
    a timeout, subprocess.TimeoutExpired if the call takes longer."""
    r = subprocess.run([RUN, '-json', '-no-back-to-dedukti', '-languages=' + ','.join(langs),
                        '-add-symboltables=' + table] + (['-force-symbolic'] if force else []) + [dk],
                       capture_output=True, text=True, timeout=timeout)
    if r.returncode:
        raise RuntimeError(r.stderr[-500:])
    out = {}
    for l in r.stdout.split('\n'):
        if not l.strip():
            continue
        j = json.loads(l)
        ws = j['originalDedukti'].split()
        name = ws[1] if ws[0] == 'def' else ws[0]
        for lang in langs:
            ranks = j['nlgResults'].get('Informath' + lang)
            if ranks:
                out.setdefault(name, {})[lang] = LABEL.sub('', ranks[0]['lin'], count=1)
    return out


def load_time(lang):
    """The seconds RunInformath takes to read nothing in lang: loading the grammar."""
    one = write('load.dk', 'loadTest : Prop.\n')
    t = time.time()
    subprocess.run([RUN, '-to-lang=' + lang, one], capture_output=True, text=True)
    return time.time() - t


def bisected(items, call, load):
    """call(items) on chunks of CHUNK items, with a time limit of PER_ITEM
    seconds per item on top of load; a chunk that runs over the limit or fails
    is split in halves, down to the items that are too slow (or fail) alone.
    Returns the merged results and the items given up."""
    results, given_up = {}, []

    def go(chunk):
        try:
            results.update(call(chunk, load + PER_ITEM * len(chunk)))
        except (subprocess.TimeoutExpired, RuntimeError):
            if len(chunk) == 1:
                given_up.append(chunk[0])
            else:
                go(chunk[:len(chunk) // 2])
                go(chunk[len(chunk) // 2:])
    for i in range(0, len(items), CHUNK):
        go(items[i:i + CHUNK])
    return results, given_up


def slow_readings(blocks, names, table, lang, load, force=False):
    """Lean name -> reading in lang, statement by statement within the time
    limit, and the names given up."""
    def call(chunk, timeout):
        f = write('slow.dk', '\n\n'.join(blocks[n][1] for n in chunk) + '\n')
        got = verbal_readings(f, table, [lang], force, timeout)
        return {n: got[blocks[n][0]][lang] for n in chunk if lang in got.get(blocks[n][0], {})}
    return bisected(names, call, load)


# the label of a formula: \textbf{Definition}. or \textbf{Theorem} \texttt{\detokenize{name}}.
FORMULA_LABEL = re.compile(r'^\\textbf\{(\w+)\}(?: \\texttt\{\\detokenize\{([^}]*)\}\})?\.\s*')


def formulas(dk, decls, force=False):
    """Lean name -> formula, aligned with the declarations by their labels."""
    lines = run('-add-symboltables=' + TABLE, '-to-symbolic-latex', *(['-force-symbolic'] if force else []), dk)
    lab = FORMULA_LABEL
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


def proof_texts(base, proofs, langs):
    """Dedukti blocks of proved theorems -> language -> the rows (number,
    sentence, justification) of each proof text; a proof that Informath
    cannot render stops its call, and the output buffered before the error
    is lost, so the proofs before it may be cut off too. The next call
    starts at the first proof without its tables; a call that gives nothing
    is tried with its first proof alone, and only if that fails too does
    the proof count as failed."""
    out, failed, i, alone = [], [], 0, False
    while i < len(proofs):
        stdout, error = call_proof_text(base, proofs[i:i + 1] if alone else proofs[i:], langs)
        texts = proof_tables(stdout, langs)
        out += texts
        i += len(texts)
        if alone:
            if not texts:          # it fails alone too
                failed.append(i)
                out.append(None)
                i += 1
            alone = False
        elif error:
            alone = not texts      # nothing came: try the first proof alone
        else:
            break
    return out, failed


def call_proof_text(base, proofs, langs, timeout=PROOF_TIMEOUT):
    """RunInformath -proof-text on the proofs: its output, and whether it failed."""
    rest = write('proofs.dk', '\n\n'.join(proofs) + '\n')
    try:
        r = subprocess.run([RUN, '-proof-text', '-languages=' + ','.join(langs), '-base=' + base,
                            '-add-symboltables=' + TABLE, rest],
                           capture_output=True, text=True, timeout=timeout)
        return r.stdout, r.returncode != 0
    except subprocess.TimeoutExpired as e:
        stdout = e.stdout or ''
        return (stdout.decode() if isinstance(stdout, bytes) else stdout), True


def proof_tables(stdout, langs):
    """The proof texts of an output, as long as each has a table in every language."""
    out = []
    for sec in re.split(r'\\subsection\*', stdout)[1:]:
        tables = re.findall(r'\\begin\{tabular\}\{[^\n]*\}\n(.*?)\\end\{tabular\}', sec, re.S)
        if len(tables) < len(langs):
            break
        out.append({lang: rows(t) for lang, t in zip(langs, tables)})
    return out


def slow_proofs(base, proofs, names, lang, load):
    """Lean name -> proof text rows in lang, proof by proof within the time
    limit, and the names given up."""
    def call(chunk, timeout):
        stdout, error = call_proof_text(base, [proofs[n] for n in chunk], [lang], timeout)
        texts = proof_tables(stdout, [lang])
        if error or len(texts) < len(chunk):
            raise RuntimeError('proof text failed')
        return {n: t[lang] for n, t in zip(chunk, texts)}
    return bisected(names, call, load)


def rows(table):
    out = []
    for row in re.split(r'\\\\\s*\n', table):
        mt = re.match(r'\s*(\d+\.)\s*&(.*)&(.*)$', row, re.S)
        if mt:
            out.append([g.strip() for g in mt.groups()])
    return out


def macros(modules, verbal):
    """MathJax macros: those of mathlib.dkgf's LaTeX forms, and Informath's own."""
    base = write('base.dk', ''.join(open(OUT + '/%s-deps.dk' % m).read() + '\n' + open(OUT + '/%s.dk' % m).read() + '\n'
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
    global RUN, TABLE
    RUN = informath()
    TABLE = write('table.dkgf', ''.join(open(t).read() + '\n' for t in TABLES if os.path.exists(t)))
    modules = read_modules()
    decls, blocks, stmts, base = [], {}, [], []
    root = os.environ['INFORMATH_ROOT']
    base += [open(os.path.join(root, 'share', 'baseconstants.dk')).read(), open('nd.dk').read()]
    for m in modules:
        ds = json.load(open(OUT + '/%s.json' % m))
        for d in ds:
            d['module'] = m
        decls += ds
        blocks.update(dk_blocks(OUT + '/%s.dk' % m))
        s = statements(m, ds)
        stmts.append(s)
        # the lemmas are rules without their type class instances (Export.lean
        # writes those hypotheses (_ : Proof (C x)) and drops them in proofs)
        base += [drop_instances(open(OUT + '/%s-deps.dk' % m).read()), drop_instances(s)]
    verbal = verbal_table()
    all_stmts = write('statements.dk', '\n'.join(stmts))

    verb = verbal_readings(all_stmts, verbal, FAST_LANGUAGES)
    form = formulas(all_stmts, decls)
    texts = {d['lean']: dict(verb.get(d['dk'], {}), formula=form.get(d['lean'])) for d in decls}
    # the slow languages statement by statement, the statements without proofs
    stmt_blocks = dk_blocks(all_stmts)
    sblocks = {d['lean']: (d['dk'], stmt_blocks[d['lean']]) for d in decls if d['lean'] in stmt_blocks}
    # --reuse-slow: the slow languages' readings, proofs and time-outs as they
    # are in the existing index, which saves their many calls
    reuse = '--reuse-slow' in sys.argv[1:] and os.path.exists(INDEX)
    old = {d['lean']: d for d in json.load(open(INDEX))['declarations']} if reuse else {}
    timed_out, loads = {}, {lang: (0 if reuse else load_time(lang)) for lang in SLOW_LANGUAGES}
    for lang in ([] if reuse else SLOW_LANGUAGES):
        got, given_up = slow_readings(sblocks, list(sblocks), verbal, lang, loads[lang])
        for n, t in got.items():
            texts[n][lang] = t
        for n in given_up:
            timed_out.setdefault(n, []).append(lang)
    # the readings that a generated entry spoils in a language, with no reading
    # at all or a word that the language lacks ([cocone_Noun]), made again
    # with the hand-written tables only, which read the constant symbolically
    old_tables = [t for t in TABLES if os.path.basename(t) not in GENERATED_TABLES]
    old_verbal = verbal_table(write('old-table.dkgf', ''.join(open(t).read() + '\n' for t in old_tables
                                                             if os.path.exists(t))), 'old-verbal.dkgf')
    spoiled = lambda t: not t or PLACEHOLDER.search(t)
    worse = {lang: [n for n in sblocks if spoiled(texts[n].get(lang)) and lang not in timed_out.get(n, [])]
             for lang in LANGUAGES}
    older = {}
    names = sorted({n for lang in FAST_LANGUAGES for n in worse[lang]})
    if names and len(old_tables) < len(TABLES):
        try:
            got = verbal_readings(write('older.dk', '\n\n'.join(sblocks[n][1] for n in names) + '\n'),
                                  old_verbal, FAST_LANGUAGES)
        except RuntimeError:
            got = {}
        for n in names:
            for lang in FAST_LANGUAGES:
                t = got.get(sblocks[n][0], {}).get(lang)
                if n in worse[lang] and t and not spoiled(t):
                    texts[n][lang] = t
                    older.setdefault(n, []).append(lang)
    for lang in ([] if reuse or len(old_tables) == len(TABLES) else SLOW_LANGUAGES):
        if worse[lang]:
            got, _ = slow_readings(sblocks, worse[lang], old_verbal, lang, loads[lang])
            for n, t in got.items():
                if not spoiled(t):
                    texts[n][lang] = t
                    older.setdefault(n, []).append(lang)
    # a declaration without a reading is read with -force-symbolic, which writes
    # \mathrm{c}(...) where a constant has no form that fits
    forced = {}
    for n, d in old.items():
        if n in texts:
            for lang in SLOW_LANGUAGES:
                if d['readings'].get(lang):
                    texts[n][lang] = d['readings'][lang]
            timed_out[n] = [t for t in d.get('timedOut', []) if t.split()[0] in SLOW_LANGUAGES]
            if not timed_out[n]:
                del timed_out[n]
    for modes in [FAST_LANGUAGES, ['formula']] + [[lang] for lang in ([] if reuse else SLOW_LANGUAGES)]:
        missing = [d for d in decls if d['lean'] in blocks and any(not texts[d['lean']].get(k) for k in modes)
                   and not any(k in timed_out.get(d['lean'], []) for k in modes)]
        if not missing:
            continue
        one = write('forced.dk', '\n\n'.join(blocks[d['lean']] for d in missing) + '\n')
        if modes == FAST_LANGUAGES:
            got = (lambda v: {d['lean']: v.get(d['dk'], {}) for d in missing})(
                verbal_readings(one, verbal, FAST_LANGUAGES, True))
        elif modes == ['formula']:
            got = {k: {'formula': v} for k, v in formulas(one, missing, True).items()}
        else:
            lang = modes[0]
            fb = {d['lean']: (d['dk'], blocks[d['lean']]) for d in missing}
            r, given_up = slow_readings(fb, list(fb), verbal, lang, loads[lang], True)
            got = {n: {lang: t} for n, t in r.items()}
            for n in given_up:
                timed_out.setdefault(n, []).append(lang)
        for d in missing:
            for k in modes:
                if not texts[d['lean']].get(k) and got.get(d['lean'], {}).get(k):
                    texts[d['lean']][k] = got[d['lean']][k]
                    forced.setdefault(d['lean'], []).append(k)

    proved = [d for d in decls if is_theorem(d) and d.get('definiens') and d['lean'] in blocks]
    proof_base = write('proof-base.dk', '\n'.join(base) + '\n')
    texts_of_proofs, failed = proof_texts(proof_base, [blocks[d['lean']] for d in proved], FAST_LANGUAGES)
    proofs = {d['lean']: p for d, p in zip(proved, texts_of_proofs) if p}
    # the proof texts that a generated entry spoils, likewise
    bad_rows = lambda rows: not rows or any(PLACEHOLDER.search(t) for _, t, _ in rows)
    redo = [d['lean'] for d in proved if d['lean'] not in proofs or
            any(bad_rows(proofs[d['lean']].get(lang)) for lang in FAST_LANGUAGES)]
    if redo and len(old_tables) < len(TABLES):
        table, TABLE = TABLE, write('old-table.dkgf', ''.join(open(t).read() + '\n' for t in old_tables
                                                             if os.path.exists(t)))
        try:
            again, _ = proof_texts(proof_base, [blocks[n] for n in redo], FAST_LANGUAGES)
        finally:
            TABLE = table
        for n, p in zip(redo, again):
            for lang in FAST_LANGUAGES:
                if p and not bad_rows(p.get(lang)) and bad_rows((proofs.get(n) or {}).get(lang)):
                    proofs.setdefault(n, {})[lang] = p[lang]
                    older.setdefault(n, []).append(lang + ' proof')
    for n, p in proofs.items():
        for lang in SLOW_LANGUAGES:
            if reuse and (old.get(n, {}).get('proof') or {}).get(lang):
                p[lang] = old[n]['proof'][lang]
    for lang in ([] if reuse else SLOW_LANGUAGES):
        got, given_up = slow_proofs(proof_base, {n: blocks[n] for n in proofs}, list(proofs), lang, loads[lang])
        for n, rows_ in got.items():
            proofs[n][lang] = rows_
        for n in given_up:
            timed_out.setdefault(n, []).append(lang + ' proof')

    # the tactic proofs of the modules exported with lake exe export --tactics:
    # their steps as proof units (tactic-units.py), read by -tactic-proof
    tactic_by = {}
    for m in modules:
        if not os.path.exists(OUT + '/%s-tactics.json' % m):
            continue
        subprocess.run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tactic-units.py'), m, OUT],
                       check=True, capture_output=True)
        units_file = OUT + '/%s-tactic-units.json' % m
        units = json.load(open(units_file))
        r = subprocess.run([RUN, '-tactic-proof', '-languages=' + ','.join(TACTIC_LANGUAGES),
                            '-add-symboltables=' + TABLE, units_file], capture_output=True, text=True)
        tactic_texts = proof_tables(r.stdout, TACTIC_LANGUAGES)
        for p, t in zip(units, tactic_texts):
            # the justification is the tactic as written, for the page to show as code
            for lang in t:
                t[lang] = [[n, text, 'TACTIC:' + u['by']] for (n, text, _), u in zip(t[lang], p['steps'])]
            proofs[p['lean']] = t
            tactic_by[p['lean']] = True

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
                              forced=forced.get(d['lean'], []), proof=proofs.get(d['lean']),
                              timedOut=timed_out.get(d['lean'], []), tactics=d['lean'] in tactic_by,
                              older=older.get(d['lean'], []))
                         for d in decls],
    }
    json.dump(index, open(INDEX, 'w'), ensure_ascii=False, indent=1)
    for f in glob.glob(TMP + '*'):
        os.remove(f)
    n = len(decls)
    print('%d declarations of %d modules -> %s: readings %s, %d formulas, %d proof texts, %d with older readings (RunInformath: %s)'
          % (n, len(modules), INDEX,
             ', '.join('%d %s' % (sum(bool(texts[d['lean']].get(l)) for d in decls), l) for l in LANGUAGES),
             sum(bool(texts[d['lean']].get('formula')) for d in decls), len(proofs), len(older), RUN))
    if failed:
        print('%d proofs without a proof text: %s' % (len(failed), ' '.join(index['proofsFailed'])))
    for lang in SLOW_LANGUAGES:
        r = [n for n, ls in timed_out.items() if lang in ls]
        p = [n for n, ls in timed_out.items() if lang + ' proof' in ls]
        print('%s%s over %d s per item: %d readings, %d proofs left out: %s'
              % (lang, ' (reused)' if reuse else '', PER_ITEM, len(r), len(p), ' '.join(r + p)))


if __name__ == '__main__':
    main()
