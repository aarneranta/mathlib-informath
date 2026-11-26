#!/usr/bin/env python3
r"""The informalization of grh-lean (compact edition) as web pages: index.html
(the main theorems and the main steps of the proof, the preface, the
contents) and one page per Lean file of grh-lean, pages/<Module>.html.

    python3 scripts/make-html.py [-sample]

The declarations are those that the five theorems of src/Main.lean depend on
(work/deps.json, made by exporter/Deps.lean), in the order of work/order.json
(scripts/order.py): every module after the modules it imports, and in each
module Lean's own order, so that nothing is used before it is stated. The
contents list the files under the folders of the source, a folder coming back
("continued") where the order requires it. Each declaration has
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
.reading,.thm{overflow-x:auto;overflow-y:hidden}
"""


def mathjax(index):
    mj = {}
    for k, v in index.get('macros', {}).items():
        body, arity = (v[0], int(v[1])) if isinstance(v, list) else (v, 0)
        mj[k] = [body, arity] if arity else body
    # the readings write inline formulas as $...$, which MathJax 3 does not take by default
    return ('window.MathJax={tex:{inlineMath:[["$","$"],["\\\\(","\\\\)"]],processEscapes:true,macros:%s},'
            'options:{ignoreHtmlClass:"lean|src|comment"}};\n' % json.dumps(mj))


def head(title, depth):
    up = '../' * depth
    return ('<!DOCTYPE html><html lang=en><head><meta charset=utf-8><meta name=viewport '
            'content="width=device-width, initial-scale=1"><title>%s</title><link rel=stylesheet href="%sstyle.css">'
            '<script src="%smacros.js"></script><script defer '
            'src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml-full.js"></script></head><body>\n'
            % (html.escape(title), up, up))


SRC = os.path.expanduser('~/claude/grh-lean/grh-compact/src/')
_src = {}
TOKEN = re.compile(r"[^\W\d][\w'.!?]*")


def named(d):
    """The constants of d's proof that its source names: d['uses'] and
    d['mathlib'] have all the constants of the proof term, also those that
    tactics (simp, instances, elaboration) put there. A name counts as named
    when it, or its last component, is one of the components of an identifier
    of the proof's text (P.foo.choose_spec names foo; h.le names le)."""
    m = d['module']
    if m not in _src:
        try:
            _src[m] = open(SRC + m.replace('.', '/') + '.lean').read().split('\n')
        except OSError:
            _src[m] = []
    text = '\n'.join(_src[m][(d['line'] or 1) - 1:d['endLine'] or 0])
    text = re.sub(r'/-.*?-/', ' ', text, flags=re.S)
    text = re.sub(r'--[^\n]*', ' ', text)
    i = text.find(':=')
    toks = set(TOKEN.findall(text[i:] if i >= 0 else text))
    parts = toks | {p for t in toks for p in t.split('.')}
    keep = lambda c: c in toks or c.split('.')[-1] in parts
    return [c for c in d['uses'] if keep(c)], [c for c in d['mathlib'] if keep(c)]


def source_head(d):
    """The declaration as the source has it, up to its := or where (without
    the doc comment): shown for the declarations that are not exported, the
    instances."""
    lines = _src.get(d['module']) or []
    text = '\n'.join(lines[(d['line'] or 1) - 1:d['endLine'] or 0])
    text = re.sub(r'/-.*?-/', '', text, flags=re.S).strip()
    m = re.search(r':=|\swhere\b|\|', text)
    return (text[:m.start()] if m else text).strip()


def anchor(name):
    return re.sub(r"[^A-Za-z0-9_.'-]", lambda m: '_%x_' % ord(m.group(0)), name)


# the spine of the proof, as New/Main.lean describes it, in logical order
STEPS = [('exists_data', 'Admissible data exist'),
         ('Data.short_forms', 'Theorem A: short forms'),
         ('Data.enough_forms', 'Theorem B: enough forms'),
         ('Data.exists_family_covolumeSq_le', 'Theorems A and B together: a family of rows of small covolume'),
         ('exists_isFitFamily', 'Twists with congruence bounds'),
         ('Data.crude_rows', 'Cruder forms'),
         ('Data.integral_forms_long', 'Theorem C: integral forms are long'),
         ('star_inequality', 'The main inequality (⋆)'),
         ('eventually_primeError_le_rpow', 'The one-sided bound for the prime sums'),
         ('entireL_ne_zero_of_primeError_le', 'The one-sided criterion'),
         ('New.grh', 'GRH in half-plane form'),
         ('New.zeros_on_line', 'The zeros of Dirichlet L-functions on the critical line'),
         ('New.zeta_zeros_on_line', 'The zeros of the zeta function on the critical line')]
FOLDERS = {'Statements': 'The statements', 'Main': 'The five theorems'}


def page(module):
    return module + '.html'


def module_summary(module):
    """The first sentence of the module's doc comment (/-! ... -/)."""
    lines = _src.get(module)
    if lines is None:
        try:
            lines = _src[module] = open(SRC + module.replace('.', '/') + '.lean').read().split('\n')
        except OSError:
            lines = _src[module] = []
    m = re.search(r'/-!(.*?)-/', '\n'.join(lines), flags=re.S)
    if not m:
        return ''
    text = ' '.join(m.group(1).split())
    s = re.match(r'(.+?[.!?])(\s|$)', text)
    return (s.group(1) if s else text)[:300]


def claim(name, title, deps, readings, where, prefix=''):
    d, rd = deps.get(name, {}), (readings.get(name) or {}).get('readings', {})
    path = (d.get('module') or 'Main').replace('.', '/')
    return ('<div class=thm><b>%s.</b> %s<div class=src><a href="%s">src/%s.lean: %s</a> &middot; '
            '<a href="%spages/%s#%s">in the book</a></div></div>'
            % (html.escape(title), html.escape(rd.get('Eng', ''), quote=False), GRH_URL % (path, d.get('line') or 1),
               html.escape(path), html.escape(name), prefix, page(where.get(name, '')), anchor(name)))


def main():
    deps = {d['name']: d for d in json.load(open(os.path.join(WORK, 'deps.json')))}
    order = json.load(open(os.path.join(WORK, 'order.json')))
    index = json.load(open(os.path.join(WORK, 'index.json')))
    readings = {d['lean']: d for d in index['declarations']}
    mloc = json.load(open(os.path.join(WORK, 'mathlib-locations.json')))
    if SAMPLE:
        have = {d['module'] for d in index['declarations']}
        order = [o for o in order if o['module'] in have]
    where = {x: o['module'] for o in order for x in o['decls']}
    os.makedirs(PAGES, exist_ok=True)
    for old in os.listdir(PAGES):
        if old.endswith('.html'):
            os.remove(os.path.join(PAGES, old))
    open(os.path.join(BOOK, 'macros.js'), 'w').write(mathjax(index))
    open(os.path.join(BOOK, 'style.css'), 'w').write(STYLE)
    toc, total, unread = [], 0, 0
    for mi, o in enumerate(order, 1):
        mod = o['module']
        path = mod.replace('.', '/')
        nav = '<nav><a href="../index.html#%s">Contents</a>%s%s</nav>' % (
            anchor(mod), '<a href="%s">&larr; %s</a>' % (page(order[mi - 2]['module']), html.escape(order[mi - 2]['module']))
            if mi > 1 else '',
            '<a href="%s">%s &rarr;</a>' % (page(order[mi]['module']), html.escape(order[mi]['module']))
            if mi < len(order) else '')
        summary = module_summary(mod)
        out = [head('GRH: ' + mod, 1), nav,
               '<h1>%d. <code>%s</code></h1>' % (mi, html.escape(mod)),
               '<p class=m><a href="%s">src/%s.lean</a></p>' % (GRH_URL.replace('#L%d', '') % path, html.escape(path))]
        if summary:
            out.append('<div class=comment>%s</div>' % html.escape(summary))
        num = 0
        for x in o['decls']:
            d = deps[x]
            # what Lean generates (congr_simp, hcongr) has no place in the source
            if d['kind'] in SKIP or not d['line']:
                continue
            named(d)  # loads the source of the module
            num += 1
            total += 1
            rd = (readings.get(x) or {}).get('readings', {})
            inst = x not in readings  # not exported: the instances
            kind = 'Instance' if inst else KINDS.get(d['kind'], 'Definition')
            e = ['<div class="decl %s" id="%s"><div class=head><b>%s %d.%d</b>'
                 '<a class=src href="%s">src/%s.lean: %s</a></div>'
                 % (d['kind'], anchor(x), kind, mi, num,
                    GRH_URL % (path, d['line'] or 1), html.escape(path), html.escape(x))]
            if rd.get('Eng'):
                e.append('<div class=reading>%s</div>' % html.escape(rd['Eng'], quote=False))
            elif inst:
                e.append('<div class=reading><span class=lean>%s</span></div>' % html.escape(source_head(d)))
            else:
                unread += 1
                st = (readings.get(x) or {}).get('statement') or ''
                e.append('<div class=reading><span class=unread>not read; the Lean statement:</span> '
                         '<span class=lean>%s</span></div>' % html.escape(st))
            if d.get('doc', '').strip():
                e.append('<div class=comment>%s</div>' % html.escape(d['doc'].strip()))
            if d['kind'] == 'theorem' and not inst:
                cites = []
                uses, mathlib = named(d)
                for u in uses:
                    if u in deps and deps[u]['kind'] not in SKIP and u in where and deps[u]['line']:
                        href = ('#%s' if where[u] == mod else page(where[u]) + '#%s') % anchor(u)
                        cites.append('<a href="%s"><code>%s</code></a>' % (href, html.escape(u)))
                ml = []
                for u in mathlib:
                    if u.startswith(('Mathlib.', 'Lean.', 'Std.', 'Batteries.Tactic')):
                        continue
                    loc = mloc.get(u)
                    ml.append('<a href="%s"><code>%s</code></a>' % (MATHLIB_URL % (loc[0].replace('.', '/'), loc[1] or 1), html.escape(u))
                              if loc else '<code>%s</code>' % html.escape(u))
                p = []
                if cites:
                    p.append('By ' + ', '.join(cites))
                if ml:
                    # the end of the proof in the summary: a fold ends its line
                    p.append('<details><summary>%s %d lemma%s of Mathlib. &#8718;</summary> %s</details>'
                             % ('and' if cites else 'By', len(ml), '' if len(ml) == 1 else 's', ', '.join(ml)))
                    e.append('<div class=proof><i>Proof.</i> %s</div>' % ' '.join(p))
                else:
                    e.append('<div class=proof><i>Proof.</i> %s. &#8718;</div>'
                             % (' '.join(p) if p else 'By Lean\'s tactics, without named lemmas'))
            e.append('</div>')
            out.append(''.join(e))
        out.append(nav + '</body></html>')
        open(os.path.join(PAGES, page(mod)), 'w').write('\n'.join(out) + '\n')
        toc.append((mi, mod, o['folder'], num, summary))
    # the index page
    out = [head('The Generalized Riemann Hypothesis, read by Informath', 0),
           '<h1>The Generalized Riemann Hypothesis</h1>',
           '<p>The Lean proof <a href="https://github.com/lsernau/grh-lean/tree/%s/grh-compact">grh-lean</a> '
           '(compact edition), read in English by Informath: %d declarations in %d files, '
           '<a href="#contents">listed below</a> in an order where nothing is used before it is stated.</p>'
           % (GRH_COMMIT, total, len(order)),
           '<h2>The main theorem</h2>']
    out += [claim(n, t, deps, readings, where) for n, t in MAIN]
    out.append('<h2>The main steps</h2><p>The spine of the proof, as <code>src/New/Main.lean</code> describes it, '
               'from the admissible data to GRH.</p>')
    out += [claim(n, t, deps, readings, where) for n, t in STEPS if n in deps]
    out.append(open(os.path.join(BOOK, 'preface.html')).read())
    out.append('<h2 id=contents>Contents</h2>')
    folder, seen = None, set()
    for mi, mod, fo, num, summary in toc:
        if fo != folder:
            title = FOLDERS.get(fo, fo) + (' (continued)' if fo in seen else '')
            out.append(('</ol>' if folder else '') + '<h3>%s</h3><ol start=%d>' % (html.escape(title), mi))
            folder = fo
            seen.add(fo)
        out.append('<li id="%s"><a href="pages/%s"><code>%s</code></a> <span class=m>%d declaration%s%s</span></li>'
                   % (anchor(mod), page(mod), html.escape(mod), num, '' if num == 1 else 's',
                      (': ' + html.escape(summary)) if summary else ''))
    out.append('</ol></body></html>')
    open(os.path.join(BOOK, 'index.html'), 'w').write('\n'.join(out) + '\n')
    print('%d files, %d declarations (%d not read) -> index.html, pages/' % (len(order), total, unread))

if __name__ == '__main__':
    main()
