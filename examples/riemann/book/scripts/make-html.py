#!/usr/bin/env python3
r"""The informalization of grh-lean (compact edition) as web pages: index.html
(the main theorems, the preface, the contents) and one page per chapter,
pages/chNNN.html.

    python3 scripts/make-html.py [-sample]

The declarations are those that the five theorems of src/Main.lean depend on
(work/deps.json, made by exporter/Deps.lean), in the order of work/order.json
(scripts/order.py): every module after the modules it imports, and in each
module Lean's own order, so that nothing is used before it is stated. A
chapter is a maximal run of the modules of one folder of the source; a folder
can come back in a later chapter ("continued"). Each declaration has
Informath's reading of its statement (work/index.json,
scripts/read-modules.py), or Lean's own statement where there is no reading;
the comment of the source, if any; and, for a theorem, a proof of one line:
the declarations of the project that the proof uses, linked to their
statements, and in a fold the theorems of Mathlib it applies, linked to
their place in mathlib4 (those of Mathlib's tactics left out). Each
declaration is linked to its place in grh-lean.
"""
import html, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
BOOK = os.path.abspath(os.path.join(HERE, '..'))
WORK = os.path.join(BOOK, 'work')
PAGES = os.path.join(BOOK, 'pages')
SAMPLE = '-sample' in sys.argv

GRH_COMMIT = '72fead1'
GRH_URL = 'https://github.com/lsernau/grh-lean/blob/%s/grh-compact/src/%%s.lean#L%%d' % GRH_COMMIT
MATHLIB_COMMIT = '56a005855ea17e0b0958f73ec801ae140b0a1679'
MATHLIB_URL = 'https://github.com/leanprover-community/mathlib4/blob/%s/%%s.lean#L%%d' % MATHLIB_COMMIT

KINDS = {'theorem': 'Theorem', 'def': 'Definition', 'axiom': 'Axiom', 'opaque': 'Definition',
         'structure': 'Structure', 'class': 'Class', 'inductive': 'Definition', 'instance': 'Instance'}
SKIP = {'constructor', 'recursor', 'quot'}
TITLES = {'Statements': 'The statements', 'Main': 'The five theorems', 'New.Main': 'The main inequality and GRH'}
MAIN = [('riemannHypothesis', 'The Riemann hypothesis'),
        ('riemannZeta_eq_zero_re', 'The zeros of the zeta function'),
        ('LFunction_ne_zero_of_half_lt_re', 'GRH for Dirichlet L-functions, half-plane form'),
        ('LFunction_eq_zero_re', 'GRH for Dirichlet L-functions'),
        ('LFunction_eq_zero_re_of_isPrimitive', 'GRH for primitive Dirichlet characters')]

STYLE = """
body{font-family:-apple-system,Segoe UI,Roboto,Helvetica,Arial,sans-serif;margin:0 auto;max-width:960px;
 padding:1.5rem;line-height:1.55;color:#222;background:#fff}
h1{font-size:1.7em;margin-bottom:.2em}h2{border-bottom:1px solid #ddd;margin-top:1.8em;font-size:1.2em}
a{color:#0645ad;text-decoration:none}a:hover{text-decoration:underline}
nav{font-size:.9em;margin:.4em 0}nav a{margin-right:1.2em}
.decl{margin:1.1em 0;padding:.1em 0 .1em .8em;border-left:3px solid #c9d6e8}
.decl.theorem{border-left-color:#1F4E79}
.head{font-size:.95em}.head b{margin-right:.5em}.src{font-family:Menlo,monospace;font-size:.8em}
.reading{margin:.3em 0}.unread{color:#777;font-style:italic;font-size:.85em}
.lean{font-family:Menlo,monospace;font-size:.8em;white-space:pre-wrap;color:#444}
.comment{background:#f5f5f5;border:1px solid #ddd;border-radius:3px;padding:.3em .6em;font-size:.85em;
 color:#333;white-space:pre-wrap;margin:.3em 0}
.proof{font-size:.88em}.proof code,.m code{font-size:.92em}
details{display:inline}summary{cursor:pointer;color:#555;display:inline}
.thm{border-left:3px solid #1F4E79;padding:.3em .9em;margin:1em 0;background:#f7f9fc}
.m{color:#777;font-size:.85em}li{margin:.2em 0}
"""


def mathjax(index):
    mj = {}
    for k, v in index.get('macros', {}).items():
        body, arity = (v[0], int(v[1])) if isinstance(v, list) else (v, 0)
        mj[k] = [body, arity] if arity else body
    return 'window.MathJax={tex:{macros:%s},options:{ignoreHtmlClass:"lean|src|comment"}};\n' % json.dumps(mj)


def head(title, depth):
    up = '../' * depth
    return ('<!DOCTYPE html><html lang=en><head><meta charset=utf-8><meta name=viewport '
            'content="width=device-width, initial-scale=1"><title>%s</title><link rel=stylesheet href="%sstyle.css">'
            '<script src="%smacros.js"></script><script defer '
            'src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml-full.js"></script></head><body>\n'
            % (html.escape(title), up, up))


def anchor(name):
    return re.sub(r"[^A-Za-z0-9_.'-]", lambda m: '_%x_' % ord(m.group(0)), name)


def main():
    deps = {d['name']: d for d in json.load(open(os.path.join(WORK, 'deps.json')))}
    order = json.load(open(os.path.join(WORK, 'order.json')))
    index = json.load(open(os.path.join(WORK, 'index.json')))
    readings = {d['lean']: d for d in index['declarations']}
    mloc = json.load(open(os.path.join(WORK, 'mathlib-locations.json')))
    if SAMPLE:
        have = {d['module'] for d in index['declarations']}
        order = [o for o in order if o['module'] in have]
    chapters = []
    for o in order:
        if chapters and chapters[-1]['folder'] == o['folder']:
            chapters[-1]['modules'].append(o)
        else:
            chapters.append({'folder': o['folder'], 'modules': [o]})
    where = {}
    for ci, ch in enumerate(chapters, 1):
        for m in ch['modules']:
            for x in m['decls']:
                where[x] = ci
    os.makedirs(PAGES, exist_ok=True)
    open(os.path.join(BOOK, 'macros.js'), 'w').write(mathjax(index))
    open(os.path.join(BOOK, 'style.css'), 'w').write(STYLE)
    seen, toc, total, unread = set(), [], 0, 0
    for ci, ch in enumerate(chapters, 1):
        f = ch['folder']
        title = TITLES.get(f, f) + (' (continued)' if f in seen else '')
        seen.add(f)
        nav = '<nav><a href="../index.html">Contents</a>%s%s</nav>' % (
            '<a href="ch%03d.html">&larr; previous</a>' % (ci - 1) if ci > 1 else '',
            '<a href="ch%03d.html">next &rarr;</a>' % (ci + 1) if ci < len(chapters) else '')
        out = [head('GRH: ' + title, 1), nav, '<h1>%d. %s</h1>' % (ci, html.escape(title))]
        num = 0
        for m in ch['modules']:
            path = m['module'].replace('.', '/')
            out.append('<h2 id="%s"><code>%s</code></h2>' % (anchor(m['module']), html.escape(m['module'])))
            for x in m['decls']:
                d = deps[x]
                if d['kind'] in SKIP:
                    continue
                num += 1
                total += 1
                rd = (readings.get(x) or {}).get('readings', {})
                e = ['<div class="decl %s" id="%s"><div class=head><b>%s %d.%d</b>'
                     '<a class=src href="%s">src/%s.lean: %s</a></div>'
                     % (d['kind'], anchor(x), KINDS.get(d['kind'], 'Definition'), ci, num,
                        GRH_URL % (path, d['line'] or 1), html.escape(path), html.escape(x))]
                if rd.get('Eng'):
                    e.append('<div class=reading>%s</div>' % html.escape(rd['Eng'], quote=False))
                else:
                    unread += 1
                    st = (readings.get(x) or {}).get('statement') or ''
                    e.append('<div class=reading><span class=unread>not read; the Lean statement:</span> '
                             '<span class=lean>%s</span></div>' % html.escape(st))
                if d.get('doc', '').strip():
                    e.append('<div class=comment>%s</div>' % html.escape(d['doc'].strip()))
                if d['kind'] == 'theorem':
                    cites = []
                    for u in d['uses']:
                        if u in deps and deps[u]['kind'] not in SKIP and u in where:
                            href = ('#%s' if where[u] == ci else 'ch%03d.html#%%s' % where[u]) % anchor(u)
                            cites.append('<a href="%s"><code>%s</code></a>' % (href, html.escape(u)))
                    ml = []
                    for u in d['mathlib']:
                        if u.startswith(('Mathlib.', 'Lean.', 'Std.', 'Batteries.Tactic')):
                            continue
                        loc = mloc.get(u)
                        ml.append('<a href="%s"><code>%s</code></a>' % (MATHLIB_URL % (loc[0].replace('.', '/'), loc[1] or 1), html.escape(u))
                                  if loc else '<code>%s</code>' % html.escape(u))
                    p = []
                    if cites:
                        p.append('By ' + ', '.join(cites))
                    if ml:
                        p.append('<details><summary>%s %d lemma%s of Mathlib</summary> %s</details>'
                                 % ('and' if cites else 'By', len(ml), '' if len(ml) == 1 else 's', ', '.join(ml)))
                    e.append('<div class=proof><i>Proof.</i> %s. &#8718;</div>'
                             % (' '.join(p) if p else 'By the definitions'))
                e.append('</div>')
                out.append(''.join(e))
        out.append(nav + '</body></html>')
        open(os.path.join(PAGES, 'ch%03d.html' % ci), 'w').write('\n'.join(out) + '\n')
        toc.append((ci, title, [m['module'] for m in ch['modules']], num))
    # the index page
    out = [head('The Generalized Riemann Hypothesis, read by Informath', 0),
           '<h1>The Generalized Riemann Hypothesis</h1>',
           '<p>The Lean proof <a href="https://github.com/lsernau/grh-lean/tree/%s/grh-compact">grh-lean</a> '
           '(compact edition), read in English by Informath: %d declarations in %d chapters.</p>'
           % (GRH_COMMIT, total, len(chapters)),
           '<h2>The main theorem</h2>']
    for name, title in MAIN:
        d, rd = deps.get(name, {}), (readings.get(name) or {}).get('readings', {})
        out.append('<div class=thm><b>%s.</b> %s<div class=src><a href="%s">src/Main.lean: %s</a> &middot; '
                   '<a href="pages/ch%03d.html#%s">in the book</a></div></div>'
                   % (title, html.escape(rd.get('Eng', ''), quote=False), GRH_URL % ('Main', d.get('line') or 1),
                      html.escape(name), where.get(name, 0), anchor(name)))
    out.append(open(os.path.join(BOOK, 'preface.html')).read())
    out.append('<h2>Contents</h2>')
    part = None
    for ci, title, mods, num in toc:
        p = 'Background results (src/Lib)' if mods[0].startswith('Lib.') else \
            'The argument (src/New)' if mods[0].startswith('New.') else 'The statements and the theorems'
        if p != part:
            out.append(('</ol>' if part else '') + '<h3>%s</h3><ol start=%d>' % (p, ci))
            part = p
        out.append('<li><a href="pages/ch%03d.html">%s</a> <span class=m>%d declarations: %s</span></li>'
                   % (ci, html.escape(title), num,
                      html.escape(', '.join(x.split('.', 2)[-1] for x in mods[:4]) + (' …' if len(mods) > 4 else ''))))
    out.append('</ol></body></html>')
    open(os.path.join(BOOK, 'index.html'), 'w').write('\n'.join(out) + '\n')
    print('%d chapters, %d declarations (%d not read) -> index.html, pages/' % (len(chapters), total, unread))


if __name__ == '__main__':
    main()
