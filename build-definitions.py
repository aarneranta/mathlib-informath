#!/usr/bin/env python3
"""Build the pages of all of Mathlib's definitions in English: static pages
definitions/<Part>-<k>.html of a few hundred definitions each, and
definitions.html, which searches them all and lists the pages.

    lake exe export --definitions      # -> out/definitions.jsonl
    python3 definition-table.py        # -> definitions.dkgf, out/definition-table.tsv
    python3 build-definitions.py       # -> definitions.html, definitions-data.js, definitions/*.html

Each definition (as definition-table.py selects them: no theorems, instances,
tactics or auxiliary declarations) has its Lean name, kind, category (a
function or constant, a type, a predicate), module, the wording of the symbol
table (from mathlib.dkgf, written by hand, or from definitions.dkgf, made from
the docstring or the name), and its reading in English: its statement, with its
definiens where it has one, read by Informath as build-index.py reads the
statements of the other pages, within a time limit. The readings are cached in
out/definition-readings.json, so that only new definitions are read again
(-reread reads them all); they are read by several RunInformath processes at
once (-workers=N, 8 by default).
"""
import collections, concurrent.futures, glob, html, importlib.util, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
DOCS = 'https://leanprover-community.github.io/mathlib4_docs/%s.html#%s'
CACHE = os.path.join(HERE, 'out', 'definition-readings.json')
PAGES = 'definitions'          # the directory of the static pages
PER_PAGE = 400                 # at most, unless a module has more
CHUNK = 200                    # definitions per call of a worker
CATEGORIES = {'Exp': 'function or constant', 'Kind': 'type', 'Prop': 'predicate'}
SOURCES = {'hand': 'by hand', 'doc': 'from the docstring', 'name': 'from the name'}


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, file))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def wordings(path):
    """Dedukti name -> the first verbal form of its entry in a .dkgf table."""
    out = {}
    for l in open(path):
        m = re.match(r'^([A-Za-z_0-9\']+) : "([^"]*)"', l)
        if m and m.group(1) not in out:
            out[m.group(1)] = m.group(2)
    return out


def declaration(d):
    """The Dedukti declaration of a definition, with its definiens if it has one."""
    if d.get('definiens'):
        return '(; //LEAN:%s ;)\ndef %s : %s :=\n  %s.\n' % (d['lean'], d['dk'], d['type'], d['definiens'])
    return '(; //LEAN:%s ;)\n%s : %s.\n' % (d['lean'], d['dk'], d['type'])


# ---------------------------------------------------------------- the readings

BI = None


def informath():
    """build-index.py, set up in this process to read with the full symbol table."""
    global BI
    if BI is None:
        os.environ.setdefault('INFORMATH_ROOT', os.path.join(HERE, '..', 'informath'))
        BI = load('build_index', 'build-index.py')
        BI.RUN = BI.informath()
        BI.TMP = os.path.join(HERE, '.defs-%d-' % os.getpid())
        BI.TABLE = BI.write('table.dkgf', ''.join(open(os.path.join(HERE, t)).read() + '\n' for t in BI.TABLES))
        BI.VERBAL = BI.verbal_table()
        BI.LOAD = BI.load_time('Eng')
    return BI


def read_chunk(decls):
    """Lean name -> English reading of a chunk of definitions, None for one over
    the time limit; -force-symbolic for one without a reading otherwise."""
    bi = informath()
    blocks = {d['lean']: (d['dk'], declaration(d)) for d in decls}
    got, given_up = bi.slow_readings(blocks, list(blocks), bi.VERBAL, 'Eng', bi.LOAD)
    missing = [n for n in blocks if n not in got and n not in given_up]
    if missing:
        more, _ = bi.slow_readings(blocks, missing, bi.VERBAL, 'Eng', bi.LOAD, True)
        got.update(more)
    out = {n: got.get(n, '') for n in blocks}
    out.update({n: None for n in given_up})
    return out


def all_readings(decls, workers, reread):
    """The readings of all definitions, from the cache and from new calls."""
    cache = {} if reread or not os.path.exists(CACHE) else json.load(open(CACHE))
    todo = [d for d in decls if d['lean'] not in cache]
    chunks = [todo[i:i + CHUNK] for i in range(0, len(todo), CHUNK)]
    if chunks:
        print('%d definitions to read, in %d chunks, %d workers' % (len(todo), len(chunks), workers), flush=True)
    with concurrent.futures.ProcessPoolExecutor(workers) as pool:
        for k, got in enumerate(pool.map(read_chunk, chunks), 1):
            cache.update(got)
            if k % 10 == 0 or k == len(chunks):
                json.dump(cache, open(CACHE, 'w'), ensure_ascii=False)
                print('  %d of %d chunks' % (k, len(chunks)), flush=True)
    for f in glob.glob(os.path.join(HERE, '.defs-*')):
        os.remove(f)
    return cache


# ---------------------------------------------------------------- the pages

def paginate(rows, modules):
    """Pages of consecutive modules of one part of Mathlib (Mathlib.Algebra), at
    most PER_PAGE definitions each, unless one module has more: (part, k, rows)."""
    by_part = collections.OrderedDict()
    for r in sorted(rows, key=lambda r: (modules[r[3]], r[0])):
        by_part.setdefault('.'.join(modules[r[3]].split('.')[:2]), []).append(r)
    pages = []
    for part, rs in by_part.items():
        cur, k = [], 1
        for m, group in _by_module(rs, modules):
            if cur and len(cur) + len(group) > PER_PAGE:
                pages.append((part, k, cur))
                cur, k = [], k + 1
            cur += group
        if cur:
            pages.append((part, k, cur))
    return pages


def _by_module(rs, modules):
    out = collections.OrderedDict()
    for r in rs:
        out.setdefault(modules[r[3]], []).append(r)
    return out.items()


def page_file(part, k):
    return '%s/%s-%d.html' % (PAGES, part, k)


def entry(bh, r, modules, reading):
    name, kind, cat, mi, w, src = r[:6]
    m = modules[mi]
    wording = (html.escape(w).replace('\x01', '<i>').replace('\x02', '</i>') +
               ' <span class=forced>(%s)</span>' % SOURCES.get(src, src)
               if w else '<span class=missing>no wording</span>')
    text = ('<div class=text>%s</div>' % bh.reading_html(reading) if reading else
            '<div class="text missing">%s</div>' % ('generation took over the time limit'
                                                    if reading is None else 'no reading'))
    return ('<div class=entry id="%s"><a class=name href="%s">%s</a><span class="k %s">%s</span>'
            '<span class=src>%s, %s</span>'
            '<div class=row><div class=lab>Wording</div><div class=text>%s</div></div>'
            '<div class=row><div class=lab>English</div>%s</div></div>'
            % (html.escape(name), DOCS % (m.replace('.', '/'), name), html.escape(name), kind, kind,
               html.escape(m), CATEGORIES[cat], wording, text))


def write_pages(pages, modules, readings, macros):
    bh = load('build_html', 'build-html.py')
    os.makedirs(os.path.join(HERE, PAGES), exist_ok=True)
    for f in glob.glob(os.path.join(HERE, PAGES, '*.html')):
        os.remove(f)
    count = collections.Counter(part for part, _, _ in pages)
    for i, (part, k, rs) in enumerate(pages):
        mods = list(dict.fromkeys(modules[r[3]] for r in rs))
        body = []
        for m, group in _by_module(rs, modules):
            body.append('<h2 id="%s">%s</h2>' % (html.escape(m), html.escape(m)))
            body += [entry(bh, r, modules, readings.get(r[0], '')) for r in group]
        prev = '<a href="%s">&lsaquo; previous</a>' % os.path.basename(page_file(*pages[i - 1][:2])) if i else ''
        nxt = ('<a href="%s">next &rsaquo;</a>' % os.path.basename(page_file(*pages[i + 1][:2]))
               if i + 1 < len(pages) else '')
        title = '%s%s' % (part, ', part %d of %d' % (k, count[part]) if count[part] > 1 else '')
        head = ('<nav><a href="../mathlib-informath.html">Mathlib informalized</a> &rsaquo; '
                '<a href="../definitions.html">definitions</a> &rsaquo; %s</nav>'
                '<h1>Definitions: %s</h1><p>%d definitions of %d modules, %s to %s. %s %s</p>'
                % (html.escape(title), html.escape(title), len(rs), len(mods), html.escape(mods[0]),
                   html.escape(mods[-1]), prev, nxt))
        open(os.path.join(HERE, page_file(part, k)), 'w').write(
            bh.page('Definitions: ' + title, head, '\n'.join(body) +
                    '<p class=pager>%s %s</p>' % (prev, nxt), macros).replace('href="pages/', 'href="../pages/'))


# ---------------------------------------------------------------- main

def main():
    workers = int(([a.split('=')[1] for a in sys.argv[1:] if a.startswith('-workers=')] or [8])[0])
    reread = '-reread' in sys.argv[1:]
    limit = int(([a.split('=')[1] for a in sys.argv[1:] if a.startswith('-limit=')] or [0])[0])
    dt = load('definition_table', 'definition-table.py')
    defs = [json.loads(l) for l in open(os.path.join(HERE, 'out', 'definitions.jsonl'))]
    dt.STRUCTURES.update(d['lean'] for d in defs if d['structure'])
    hand = wordings(os.path.join(HERE, 'mathlib.dkgf'))
    made = wordings(os.path.join(HERE, 'definitions.dkgf'))
    source = {}
    for l in open(os.path.join(HERE, 'out', 'definition-table.tsv')):
        cols = l.rstrip('\n').split('\t')
        if len(cols) > 5 and cols[4]:
            source[cols[0]] = cols[5]
    modules, mod_index, rows, decls = [], {}, [], []
    counts = collections.Counter()
    for d in defs:
        if not dt.wanted(d):
            continue
        names, nargs, cat = dt.suggest.signature(d['type'])
        if cat == 'Proof':
            continue
        if d['dk'] in hand:
            w, src = hand[d['dk']], 'hand'
        elif d['dk'] in made:
            w, src = made[d['dk']], source.get(d['dk'], 'name')
        else:
            w, src = '', ''
        # the arguments by their names: "the cofinality of #1" -> "... of o"
        w = re.sub(r'#(\d+)', lambda m: '\x01%s\x02' % (names[int(m.group(1)) - 1]
                                                         if int(m.group(1)) <= len(names) else m.group(0)), w)
        m = d['module']
        if m not in mod_index:
            mod_index[m] = len(modules)
            modules.append(m)
        kind = 'class' if d['class'] else 'structure' if d['structure'] else d['kind']
        rows.append([d['lean'], kind, cat, mod_index[m], w, src])
        decls.append(d)
        counts[cat] += 1
        counts[cat + ' worded'] += bool(w)
        if limit and len(rows) >= limit:      # for testing
            break

    readings = all_readings(decls, workers, reread)
    macros = informath().macros(BI.read_modules(), BI.VERBAL)
    for f in glob.glob(os.path.join(HERE, '.defs-*')):
        os.remove(f)
    pages = paginate(rows, modules)
    write_pages(pages, modules, readings, macros)
    page_of = {r[0]: i for i, (_, _, rs) in enumerate(pages) for r in rs}
    data = {'modules': modules, 'pages': [page_file(p, k) for p, k, _ in pages],
            'rows': [r + [page_of[r[0]]] for r in rows]}
    # a script, not JSON to fetch, so that the page works from a file too
    open(os.path.join(HERE, 'definitions-data.js'), 'w').write(
        'const DATA = %s;\n' % json.dumps(data, ensure_ascii=False, separators=(',', ':')))
    if os.path.exists(os.path.join(HERE, 'definitions-data.json')):
        os.remove(os.path.join(HERE, 'definitions-data.json'))
    worded = sum(bool(r[4]) for r in rows)
    read = sum(bool(readings.get(r[0])) for r in rows)
    toc = []
    for part in dict.fromkeys(p for p, _, _ in pages):
        ps = [(i, k, rs) for i, (p, k, rs) in enumerate(pages) if p == part]
        n = sum(len(rs) for _, _, rs in ps)
        toc.append('<tr><td>%s</td><td>%s</td><td>%s</td></tr>' % (
            html.escape(part), '{:,}'.format(n), ' '.join('<a href="%s">%d</a>' % (page_file(part, k), k)
                                                          for i, k, _ in ps)))
    open(os.path.join(HERE, 'definitions.html'), 'w').write(PAGE % {
        'n': '{:,}'.format(len(rows)), 'w': '{:,}'.format(worded), 'r': '{:,}'.format(read),
        'p': '{:,}'.format(len(pages)),
        'cov': ' · '.join('%s %s of %s' % (label, '{:,}'.format(counts[c + ' worded']), '{:,}'.format(counts[c]))
                          for c, label in (('Exp', 'functions and constants'), ('Kind', 'types'),
                                           ('Prop', 'predicates'))),
        'toc': '\n'.join(toc)})
    print('%d definitions, %d worded, %d with a reading -> definitions.html, %d pages in %s/'
          % (len(rows), worded, read, len(pages), PAGES))


PAGE = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Mathlib's definitions in English</title>
<style>
 body{font-family:-apple-system,Segoe UI,Roboto,Helvetica,Arial,sans-serif;margin:0 auto;max-width:1150px;padding:1.5rem;line-height:1.5;color:#222;background:#fff}
 header{border-bottom:1px solid #ddd;margin-bottom:1rem}
 nav{font-size:.9em;margin-bottom:.4rem}
 .bar{position:sticky;top:0;background:#fff;padding:.6rem 0;border-bottom:1px solid #ddd;display:flex;flex-wrap:wrap;gap:.6rem;align-items:center;z-index:2}
 .bar input[type=search]{flex:1 1 18rem;font:inherit;padding:.35rem .6rem;border:1px solid #c8d3e6;border-radius:4px}
 .bar select{font:inherit;padding:.3rem;border:1px solid #c8d3e6;border-radius:4px;background:#fff}
 .count{color:#666;font-size:.9em}
 .entry{padding:.45rem 0;border-bottom:1px solid #eee}
 .name{font-weight:700;font-family:ui-monospace,Menlo,monospace;color:#0645ad;text-decoration:none;word-break:break-all}
 .name:hover{text-decoration:underline}
 .k{font-size:.72em;padding:0 .35rem;border-radius:3px;background:#eef;color:#335;margin-left:.4rem}
 .k.Prop{background:#e6f4ea;color:#1e6b34}.k.Kind{background:#fdf0e1;color:#7a4a08}
 .mod{color:#888;font-size:.8em;margin-left:.6rem;font-family:ui-monospace,Menlo,monospace}
 .w{margin:.15rem 0 0;font-size:1.0em}
 .w i{font-family:ui-monospace,Menlo,monospace;font-style:normal;color:#7a2a8a}
 .w.none{color:#999;font-style:italic;font-size:.9em}
 .src{color:#999;font-size:.75em;margin-left:.4rem}
 .pages{margin:1rem 0;display:flex;gap:.4rem;align-items:center;flex-wrap:wrap}
 .pages button{font:inherit;padding:.2rem .6rem;border:1px solid #c8d3e6;border-radius:3px;background:#f4f6fb;color:#0645ad;cursor:pointer}
 .pages button:disabled{color:#aaa;cursor:default}
 table.toc{border-collapse:collapse;margin:.6rem 0;font-size:.9em}
 table.toc td,table.toc th{border:1px solid #ddd;padding:.2rem .6rem;vertical-align:top}
 table.toc td:nth-child(2){text-align:right}
 table.toc a{margin-right:.35rem}
</style></head><body>
<header>
<nav><a href="mathlib-informath.html">Mathlib informalized</a> &rsaquo; definitions</nav>
<h1>Mathlib's definitions in English</h1>
<p>All %(n)s definitions of Mathlib (its functions, constants, types, structures,
classes and predicates; not its theorems, instances or tactics), on %(p)s pages by part of Mathlib.
Each has the <b>wording</b> that the symbol table gives it, %(w)s of them (%(cov)s), written by
hand in <code>mathlib.dkgf</code> or made by <code>definition-table.py</code> from the definition's
docstring or name, with the arguments shown by their names; and its <b>reading</b> in English, %(r)s
of them: the statement of the definition, with its definiens where it has one, read by Informath
as the statements on the other pages are, where a constant without a wording is shown symbolically.
Search below to find a definition's page; each name there links to Mathlib's documentation, which
has the docstring.</p>
</header>
<div class=bar>
 <input type=search id=q placeholder="search names and wordings" autofocus>
 <select id=area><option value="">all of Mathlib</option></select>
 <select id=cat><option value="">all kinds</option><option value="Exp">functions and constants</option>
  <option value="Kind">types</option><option value="Prop">predicates</option></select>
 <select id=wd><option value="">worded or not</option><option value="y">worded</option>
  <option value="n">not worded</option><option value="hand">by hand</option>
  <option value="doc">from the docstring</option><option value="name">from the name</option></select>
 <span class=count id=count></span>
</div>
<div id=list></div>
<div class=pages id=pages></div>
<h2>The pages</h2>
<table class=toc><tr><th>part of Mathlib</th><th>definitions</th><th>pages</th></tr>
%(toc)s
</table>
<script src="definitions-data.js"></script>
<script>
const PER = 50;
let D = null, hits = [], page = 0;
const $ = id => document.getElementById(id);
const esc = s => s.replace(/[&<>"]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
function wording(w) {
  return esc(w).replace(/\\x01([^\\x02]*)\\x02/g, '<i>$1</i>');
}
function area(m) { return m.split('.').slice(0, 2).join('.'); }
function filter() {
  const q = $('q').value.trim().toLowerCase().split(/\\s+/).filter(x => x);
  const a = $('area').value, c = $('cat').value, wd = $('wd').value;
  hits = [];
  if (!q.length && !a && !c && !wd) { show(); return; }
  for (const r of D.rows) {
    if (a && area(D.modules[r[3]]) !== a) continue;
    if (c && r[2] !== c) continue;
    if (wd === 'y' && !r[4] || wd === 'n' && r[4] || ['hand','doc','name'].includes(wd) && r[5] !== wd) continue;
    if (q.length) {
      const text = (r[0] + ' ' + r[4].replace(/[\\x01\\x02]/g, '')).toLowerCase();
      if (!q.every(x => text.includes(x))) continue;
    }
    hits.push(r);
  }
  page = 0;
  show();
}
function show() {
  const from = page * PER, rows = hits.slice(from, from + PER);
  $('count').textContent = hits.length ? hits.length.toLocaleString() + ' definitions' : '';
  $('list').innerHTML = rows.map(r => {
    const m = D.modules[r[3]];
    const url = D.pages[r[6]] + '#' + encodeURIComponent(r[0]);
    return '<div class=entry><a class=name href="' + url + '">' + esc(r[0]) + '</a>' +
      '<span class="k ' + r[2] + '">' + esc(r[1]) + '</span><span class=mod>' + esc(m) + '</span>' +
      (r[4] ? '<div class=w>' + wording(r[4]) + '<span class=src>' + r[5] + '</span></div>'
            : '<div class="w none">no wording</div>') + '</div>';
  }).join('');
  const n = Math.ceil(hits.length / PER);
  $('pages').innerHTML = n > 1 ? '<button id=prev' + (page ? '' : ' disabled') + '>&lsaquo; previous</button>' +
    '<span class=count>' + (page + 1) + ' of ' + n.toLocaleString() + '</span>' +
    '<button id=next' + (page + 1 < n ? '' : ' disabled') + '>next &rsaquo;</button>' : '';
  if (n > 1) {
    $('prev').onclick = () => { page--; show(); };
    $('next').onclick = () => { page++; show(); };
  }
}
(d => {
  D = d;
  const areas = [...new Set(d.modules.map(area))].sort();
  $('area').innerHTML += areas.map(a => '<option>' + esc(a) + '</option>').join('');
  for (const id of ['q', 'area', 'cat', 'wd']) $(id).addEventListener('input', filter);
  filter();
})(DATA);
</script>
</body></html>
"""


if __name__ == '__main__':
    main()
