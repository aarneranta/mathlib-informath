#!/usr/bin/env python3
"""Build definitions.html, a browsable page of all of Mathlib's definitions
with their English wordings, and definitions-data.json, its data.

    lake exe export --definitions      # -> out/definitions.jsonl
    python3 definition-table.py        # -> definitions.dkgf, out/definition-table.tsv
    python3 build-definitions.py       # -> definitions.html, definitions-data.json

Each definition (as definition-table.py selects them: no theorems, instances,
tactics or auxiliary declarations) has its Lean name, kind, category (a
function or constant, a type, a predicate), module, wording (from
mathlib.dkgf, written by hand, or from definitions.dkgf, made from the
docstring or the name), and the first sentence of its docstring; the page
searches and filters them in the browser, and links each to Mathlib's
documentation.
"""
import collections, html, importlib.util, json, os, re

HERE = os.path.dirname(os.path.abspath(__file__))
DOCS = 'https://leanprover-community.github.io/mathlib4_docs/%s.html#%s'


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


def first_sentence(doc):
    d = re.sub(r'\s+', ' ', re.sub(r'\[([^\]]*)\]\([^)]*\)', r'\1', doc)).strip()
    s = re.split(r'(?<=[a-z0-9`)\]])\.(?:\s|$)', d)[0]
    return (s[:220] + '…') if len(s) > 220 else s


def main():
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
    modules, mod_index, rows = [], {}, []
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
        rows.append([d['lean'], kind, cat, mod_index[m], w, src, first_sentence(d['doc'])])
        counts[cat] += 1
        counts[cat + ' worded'] += bool(w)
    data = {'modules': modules, 'rows': rows}
    json.dump(data, open(os.path.join(HERE, 'definitions-data.json'), 'w'), ensure_ascii=False,
              separators=(',', ':'))
    worded = sum(bool(r[4]) for r in rows)
    open(os.path.join(HERE, 'definitions.html'), 'w').write(PAGE % {
        'n': '{:,}'.format(len(rows)), 'w': '{:,}'.format(worded),
        'cov': ' · '.join('%s %s of %s' % (label, '{:,}'.format(counts[c + ' worded']), '{:,}'.format(counts[c]))
                          for c, label in (('Exp', 'functions and constants'), ('Kind', 'types'),
                                           ('Prop', 'predicates'))),
        'docs': DOCS})
    print('%d definitions, %d worded -> definitions.html, definitions-data.json' % (len(rows), worded))
    return len(rows), worded


PAGE = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Mathlib definitions in English</title>
<style>
 body{font-family:-apple-system,Segoe UI,Roboto,Helvetica,Arial,sans-serif;margin:0 auto;max-width:1150px;padding:1.5rem;line-height:1.5;color:#222;background:#fff}
 header{border-bottom:1px solid #ddd;margin-bottom:1rem}
 nav{font-size:.9em;margin-bottom:.4rem}
 .bar{position:sticky;top:0;background:#fff;padding:.6rem 0;border-bottom:1px solid #ddd;display:flex;flex-wrap:wrap;gap:.6rem;align-items:center;z-index:2}
 .bar input[type=search]{flex:1 1 18rem;font:inherit;padding:.35rem .6rem;border:1px solid #c8d3e6;border-radius:4px}
 .bar select{font:inherit;padding:.3rem;border:1px solid #c8d3e6;border-radius:4px;background:#fff}
 .count{color:#666;font-size:.9em}
 .entry{padding:.55rem 0;border-bottom:1px solid #eee}
 .name{font-weight:700;font-family:ui-monospace,Menlo,monospace;color:#0645ad;text-decoration:none;word-break:break-all}
 .name:hover{text-decoration:underline}
 .k{font-size:.72em;padding:0 .35rem;border-radius:3px;background:#eef;color:#335;margin-left:.4rem}
 .k.Prop{background:#e6f4ea;color:#1e6b34}.k.Kind{background:#fdf0e1;color:#7a4a08}
 .mod{color:#888;font-size:.8em;margin-left:.6rem;font-family:ui-monospace,Menlo,monospace}
 .w{margin:.2rem 0 .1rem;font-size:1.02em}
 .w i{font-family:ui-monospace,Menlo,monospace;font-style:normal;color:#7a2a8a}
 .w.none{color:#999;font-style:italic;font-size:.9em}
 .src{color:#999;font-size:.75em;margin-left:.4rem}
 .doc{color:#555;font-size:.88em}
 .pages{margin:1rem 0;display:flex;gap:.4rem;align-items:center;flex-wrap:wrap}
 .pages button{font:inherit;padding:.2rem .6rem;border:1px solid #c8d3e6;border-radius:3px;background:#f4f6fb;color:#0645ad;cursor:pointer}
 .pages button:disabled{color:#aaa;cursor:default}
</style></head><body>
<header>
<nav><a href="mathlib-informath.html">Mathlib informalized</a> &rsaquo; definitions</nav>
<h1>Mathlib's definitions in English</h1>
<p>All %(n)s definitions of Mathlib (its functions, constants, types, structures,
classes and predicates; not its theorems, instances or tactics), %(w)s of them with an English
wording that Informath's grammar parses: %(cov)s. The wordings marked <b>hand</b> are
written by hand in <code>mathlib.dkgf</code>; the others are made by
<code>definition-table.py</code> from the definition's docstring (<b>doc</b>) or from its name
(<b>name</b>), and are in <code>definitions.dkgf</code>. In a wording, the arguments are shown by
their names. Each name links to Mathlib's documentation.</p>
</header>
<div class=bar>
 <input type=search id=q placeholder="search names, wordings and docstrings" autofocus>
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
<script>
const PER = 100;
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
  for (const r of D.rows) {
    if (a && area(D.modules[r[3]]) !== a) continue;
    if (c && r[2] !== c) continue;
    if (wd === 'y' && !r[4] || wd === 'n' && r[4] || ['hand','doc','name'].includes(wd) && r[5] !== wd) continue;
    if (q.length) {
      const text = (r[0] + ' ' + r[4] + ' ' + r[6]).toLowerCase();
      if (!q.every(x => text.includes(x))) continue;
    }
    hits.push(r);
  }
  page = 0;
  show();
}
function show() {
  const from = page * PER, rows = hits.slice(from, from + PER);
  $('count').textContent = hits.length.toLocaleString() + ' definitions';
  $('list').innerHTML = rows.map(r => {
    const m = D.modules[r[3]];
    const url = '%(docs)s'.replace('%%s', m.replace(/\\./g, '/')).replace('%%s', encodeURIComponent(r[0]));
    return '<div class=entry><a class=name href="' + url + '">' + esc(r[0]) + '</a>' +
      '<span class="k ' + r[2] + '">' + esc(r[1]) + '</span><span class=mod>' + esc(m) + '</span>' +
      (r[4] ? '<div class=w>' + wording(r[4]) + '<span class=src>' + r[5] + '</span></div>'
            : '<div class="w none">no wording</div>') +
      (r[6] ? '<div class=doc>' + esc(r[6]) + '</div>' : '') + '</div>';
  }).join('');
  const n = Math.max(1, Math.ceil(hits.length / PER));
  $('pages').innerHTML = '<button id=prev' + (page ? '' : ' disabled') + '>&lsaquo; previous</button>' +
    '<span class=count>page ' + (page + 1) + ' of ' + n.toLocaleString() + '</span>' +
    '<button id=next' + (page + 1 < n ? '' : ' disabled') + '>next &rsaquo;</button>';
  $('prev').onclick = () => { page--; show(); scrollTo(0, 0); };
  $('next').onclick = () => { page++; show(); scrollTo(0, 0); };
}
fetch('definitions-data.json').then(r => r.json()).then(d => {
  D = d;
  const areas = [...new Set(d.modules.map(area))].sort();
  $('area').innerHTML += areas.map(a => '<option>' + esc(a) + '</option>').join('');
  for (const id of ['q', 'area', 'cat', 'wd']) $(id).addEventListener('input', filter);
  filter();
});
</script>
</body></html>
"""


if __name__ == '__main__':
    main()
