#!/usr/bin/env python3
"""The round trip of NLG and semantics (Informath's doc/nlg-and-semantics.md)
for all of mathlib-informath's statements and definitions: for each Dedukti
judgement, each of its MathCore trees t and each NLG variant t', whether the
semantics of t' includes t (exact), does so with the same hypotheses or up to
normalization (equivalent), or not (lost).

    INFORMATH_ROOT=~/claude/informath python3 roundtrip-check.py [-part=statements|definitions] [-workers=8] [-limit=N] [-safe]
        [-names=FILE] [-out=DIR]

-names=FILE checks only the judgements named in FILE (one Dedukti name per
line), -out=DIR writes the results there instead of out/roundtrip.

It reads what is saved, without exporting from Lean again:
  * statements: the Dedukti judgements of index.json, with the symbol table of
    build-index.py (mathlib.dkgf, definitions.dkgf, structures.dkgf and the
    modules' #HIDE lines);
  * definitions: the declarations of out/definitions.jsonl as
    build-definitions.py makes them, with its symbol table.
Each chunk of judgements is one call of RunInformath -check-nlg-semantics -tsv,
within a time limit; a chunk that runs over it or fails is split in halves,
down to the judgements given up alone.

Output: out/roundtrip/<part>.tsv (one line per variant: name, tree, stage,
verdict, difference, words, first normalization step that matches), out/roundtrip/<part>-given-up.txt, and the
summary roundtrip-check.md.
"""
import collections, concurrent.futures, importlib.util, json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
CHUNK = 40          # judgements per call
PER_ITEM = 20       # seconds per judgement, on top of loading


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, file))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def arg(name, default):
    return ([a.split('=', 1)[1] for a in sys.argv[1:] if a.startswith('-%s=' % name)] or [default])[0]


OUTDIR = os.path.join(HERE, arg('out', os.path.join('out', 'roundtrip')))
BI = load('build_index', 'build-index.py')
BI.RUN = BI.informath()
os.makedirs(OUTDIR, exist_ok=True)
BI.TMP = os.path.join(OUTDIR, '.tmp-')
SAFE = ['-roundtrip-safe'] if '-safe' in sys.argv[1:] else []


# ---------------------------------------------------------------- the judgements

def statements():
    """(name, Dedukti text) of the declarations of index.json, and the table."""
    modules = BI.read_modules()
    hides = [BI.OUT + '/%s-hide.dkgf' % m for m in modules]
    BI.TABLE = BI.write('statements-table.dkgf', ''.join(open(os.path.join(HERE, t)).read() + '\n'
                                                         for t in BI.TABLES + hides if os.path.exists(t)))
    table = BI.verbal_table(None, 'statements-verbal.dkgf')
    decls = json.load(open(os.path.join(HERE, 'index.json')))['declarations']
    items = [(d['dk'], d['dedukti'], d['module'], d['kind']) for d in decls if d.get('dedukti')]
    return items, table


def definitions():
    """(name, Dedukti text) of the definitions as build-definitions.py reads
    them, and its table."""
    BD = load('build_definitions', 'build-definitions.py')
    dt = load('definition_table', 'definition-table.py')
    defs = [json.loads(l) for l in open(os.path.join(HERE, 'out', 'definitions.jsonl'))]
    dt.STRUCTURES.update(d['lean'] for d in defs if d['structure'])
    hand = BD.wordings(os.path.join(HERE, 'mathlib.dkgf'))
    made = BD.wordings(os.path.join(HERE, 'definitions.dkgf'))
    tables = {**made, **hand, **BD.wordings(os.path.join(HERE, 'structures.dkgf'))}
    nouns = BD.class_nouns(defs, tables)
    tables.update(nouns)
    items = []
    for d in defs:
        if not dt.wanted(d) or dt.suggest.signature(d['type'])[2] == 'Proof':
            continue
        kind = 'class' if d['class'] else 'structure' if d['structure'] else d['kind']
        for e in BD.class_decls(d, tables):
            items.append((e['dk'], BD.declaration(e), d['module'], kind))
    BI.TABLE = BI.write('definitions-table.dkgf', ''.join(open(os.path.join(HERE, t)).read() + '\n' for t in BI.TABLES)
                        + ''.join('%s : "%s"\n' % kv for kv in nouns.items()))
    table = BI.verbal_table(None, 'definitions-verbal.dkgf')
    return items, table


# ---------------------------------------------------------------- the check

def check(job):
    """The TSV lines of a chunk, and the names given up."""
    k, chunk, table, load_time = job
    lines, given_up = [], []

    def go(c):
        f = BI.TMP + 'chunk-%d-%d.dk' % (os.getpid(), k)
        open(f, 'w').write('\n\n'.join(t for _, t, _, _ in c) + '\n')
        try:
            r = subprocess.run([BI.RUN, '-check-nlg-semantics', '-tsv', '-add-symboltables=' + table] + SAFE + [f],
                               capture_output=True, text=True, timeout=load_time + PER_ITEM * len(c))
            if r.returncode:
                raise RuntimeError(r.stderr[-300:])
            lines.extend(l for l in r.stdout.split('\n') if l.strip())
        except (subprocess.TimeoutExpired, RuntimeError):
            if len(c) == 1:
                given_up.append(c[0][0])
            else:
                go(c[:len(c) // 2])
                go(c[len(c) // 2:])
    go(chunk)
    return lines, given_up


def run(part, items, table, workers):
    t0 = time.time()
    load_time = BI.load_time('Eng') + 5
    chunks = [items[i:i + CHUNK] for i in range(0, len(items), CHUNK)]
    print('%s: %d judgements in %d chunks, %d workers' % (part, len(items), len(chunks), workers), flush=True)
    lines, given_up = [], []
    with concurrent.futures.ProcessPoolExecutor(workers) as pool:
        for k, (ls, gs) in enumerate(pool.map(check, [(k, c, table, load_time) for k, c in enumerate(chunks)]), 1):
            lines += ls
            given_up += gs
            if k % 20 == 0 or k == len(chunks):
                print('  %d of %d chunks, %d variants, %d given up, %.0f s'
                      % (k, len(chunks), len(lines), len(given_up), time.time() - t0), flush=True)
    open(os.path.join(OUTDIR, part + '.tsv'), 'w').write('\n'.join(lines) + '\n')
    open(os.path.join(OUTDIR, part + '-given-up.txt'), 'w').write('\n'.join(given_up) + '\n')
    meta = {n: (m, kind) for n, _, m, kind in items}
    json.dump(meta, open(os.path.join(OUTDIR, part + '-meta.json'), 'w'))


# ---------------------------------------------------------------- the summary

VERDICTS = ['Exact', 'SameHypotheses', 'Equivalent', 'Lost']


def summary(part):
    path = os.path.join(OUTDIR, part + '.tsv')
    if not os.path.exists(path):
        return []
    meta = json.load(open(os.path.join(OUTDIR, part + '-meta.json')))
    given_up = [l for l in open(os.path.join(OUTDIR, part + '-given-up.txt')).read().split('\n') if l]
    rows = [l.rstrip('\n').split('\t') for l in open(path) if l.strip()]
    rows = [r + [''] * (8 - len(r)) for r in rows]
    notree = sorted({r[0] for r in rows if r[3] == 'NoTree'})
    var = [r for r in rows if r[3] != 'NoTree']
    names = {r[0] for r in var}
    stages = list(dict.fromkeys(r[2] for r in var))
    by = collections.Counter((r[2], r[3]) for r in var)
    lost = [r for r in var if r[3] == 'Lost']
    lost_names = sorted({r[0] for r in lost})
    default_lost = sorted({r[0] for r in lost if r[2].startswith('letDeclared')})
    out = ['## %s' % part.capitalize(), '',
           '%d judgements: %d with MathCore trees, %d without (no annotation), %d given up (time limit or failure).'
           % (len(meta), len(names), len(notree), len(given_up)), '',
           '%d variants; %d lost, in %d judgements (%d of them in the default output).'
           % (len(var), len(lost), len(lost_names), len(default_lost)), '',
           '| stage | variants | exact | same hypotheses | equivalent | lost |', '|---|---:|---:|---:|---:|---:|']
    for s in stages:
        out.append('| %s | %d | %s |' % (s, sum(by[(s, v)] for v in VERDICTS), ' | '.join(str(by[(s, v)]) for v in VERDICTS)))
    tot = collections.Counter(r[3] for r in var)
    out.append('| **all** | %d | %s |' % (len(var), ' | '.join(str(tot[v]) for v in VERDICTS)))
    steps = collections.Counter(r[7] or 'lost' for r in var)
    out += ['', '### By the first normalization step that makes t and the semantics of t\' equal', '',
            '| step | variants |', '|---|---:|'] + ['| %s | %d |' % (k, v) for k, v in steps.items()]
    out += ['', '### Where the lost ones differ', '',
            'The head functions of the smallest subtrees where the normalized t and the normalized '
            'semantics of t\' differ, with the variants, judgements and an example.', '',
            '| t | semantics of t\' | variants | judgements | example |', '|---|---|---:|---:|---|']
    causes = collections.defaultdict(list)
    for r in lost:
        causes[(r[4], r[5])].append(r)
    for (a, b), rs in sorted(causes.items(), key=lambda x: -len(x[1]))[:40]:
        out.append('| `%s` | `%s` | %d | %d | %s |' % (a, b, len(rs), len({r[0] for r in rs}), rs[0][0]))
    mods = collections.Counter(meta.get(n, ['?'])[0] for n in lost_names)
    out += ['', '### Modules with most judgements with lost variants', '',
            '| module | judgements |', '|---|---:|'] + ['| %s | %d |' % kv for kv in mods.most_common(15)]
    out += ['', '### Examples of lost variants', '']
    seen = set()
    for r in lost:
        if (r[4], r[5]) in seen:
            continue
        seen.add((r[4], r[5]))
        out.append('* `%s` (%s; `%s` / `%s`): %s' % (r[0], r[2], r[4], r[5], r[6][:400]))
        if len(seen) >= 25:
            break
    out.append('')
    return out


def main():
    workers = int(arg('workers', 8))
    limit = int(arg('limit', 0))
    parts = [arg('part', '')] if arg('part', '') else ['statements', 'definitions']
    if '-summary' not in sys.argv[1:]:
        for part in parts:
            items, table = statements() if part == 'statements' else definitions()
            if arg('names', ''):
                wanted = set(open(arg('names', '')).read().split())
                items = [i for i in items if i[0] in wanted]
            run(part, items[:limit] if limit else items, table, workers)
    for f in os.listdir(OUTDIR):
        if f.startswith('.tmp-'):
            os.remove(os.path.join(OUTDIR, f))
    text = ['# The round trip of NLG and semantics over mathlib-informath', '',
            'Made by roundtrip-check.py with RunInformath -check-nlg-semantics%s '
            '(Informath doc/nlg-and-semantics.md, doc/nlg-semantics-check.md).' % (' -roundtrip-safe' if SAFE else ''), '']
    for part in ['statements', 'definitions']:
        text += summary(part)
    open(os.path.join(HERE, 'roundtrip-check.md') if OUTDIR.endswith(os.path.join('out', 'roundtrip')) else os.path.join(OUTDIR, 'summary.md'), 'w').write('\n'.join(text) + '\n')
    print('-> roundtrip-check.md')


if __name__ == '__main__':
    main()
