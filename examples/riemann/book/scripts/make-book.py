#!/usr/bin/env python3
r"""The informalization of grh-lean (compact edition) as a book in volumes,
with an index page.

    python3 scripts/make-book.py [-sample]   # -> book/index.html, book/volumes/volN.tex
    (cd volumes && latexmk -xelatex volN.tex)

The declarations are those that the five theorems of src/Main.lean depend on
(work/deps.json, made by exporter/Deps.lean), in the order of
work/order.json (scripts/order.py): every module after the modules it
imports, and in each module Lean's own order, so that nothing is used before
it is stated. The order is cut into volumes at the chapter boundaries
(maximal runs of the modules of one folder), of about VOLUME declarations
each. Each declaration has Informath's reading of its statement
(work/index.json, scripts/read-modules.py), the comment of the source if it
has one, and a proof of one line: the declarations of the project that the
proof uses, linked to their statements, and the theorems of Mathlib it
applies, linked to their place in mathlib4. Each declaration is linked to
its place in grh-lean.
"""
import html, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
BOOK = os.path.abspath(os.path.join(HERE, '..'))
WORK = os.path.join(BOOK, 'work')
VOLS = os.path.join(BOOK, 'volumes')
SAMPLE = '-sample' in sys.argv
VOLUME = 450                         # declarations per volume, about

GRH_COMMIT = '72fead1'
GRH_URL = 'https://github.com/lsernau/grh-lean/blob/%s/grh-compact/src/%%s.lean#L%%d' % GRH_COMMIT
MATHLIB_COMMIT = '56a005855ea17e0b0958f73ec801ae140b0a1679'
MATHLIB_URL = 'https://github.com/leanprover-community/mathlib4/blob/%s/%%s.lean#L%%d' % MATHLIB_COMMIT

KINDS = {'theorem': 'Theorem', 'def': 'Definition', 'axiom': 'Axiom', 'opaque': 'Definition',
         'structure': 'Structure', 'class': 'Class', 'inductive': 'Definition', 'instance': 'Instance'}
SKIP = {'constructor', 'recursor', 'quot'}

FOLDER_TITLES = {
    'Statements': 'The statements', 'Main': 'The five theorems', 'New.Main': 'The main inequality and GRH',
}


def esc(s):
    return (s.replace('\\', '\\textbackslash{}').replace('_', '\\_').replace('&', '\\&').replace('%', '\\%')
            .replace('#', '\\#').replace('{', '\\{').replace('}', '\\}').replace('$', '\\$')
            .replace('^', '\\^{}').replace('~', '\\~{}'))


def target(name):
    return 'd:' + re.sub(r"[^A-Za-z0-9.]", lambda m: '-%d-' % ord(m.group(0)), name)


DEF = re.compile(r'\\newcommand\{\\(\w+)\}(?:\[(\d+)\])?\{(.*)\}\s*$')
ROMAN = ['i', 'ii', 'iii', 'iv', 'v', 'vi', 'vii', 'viii', 'ix']
END = re.compile(r'\\(end\w*)')


def define(name, arity, body):
    """A macro definition (as godement-index/rocq/book/make-book.py)."""
    name = END.sub(lambda m: '\\X' + m.group(1), '\\' + name)[1:]
    body = re.sub(r'#(\d+)', r'{#\1}', body)
    if arity <= 9:
        return '\\providecommand{\\%s}%s{%s}' % (name, '[%d]' % arity if arity else '', body)
    store = ''.join('\\def\\%sArg%s{#%d}' % (name, ROMAN[i], i + 1) for i in range(9))
    rest = body
    for i in range(arity, 9, -1):
        rest = rest.replace('#%d' % i, '#@%d' % (i - 9))
    for i in range(9, 0, -1):
        rest = rest.replace('#%d' % i, '\\%sArg%s{}' % (name, ROMAN[i - 1]))
    rest = rest.replace('#@', '#')
    return ('\\providecommand{\\%s}[9]{%s\\%sRest}\n\\providecommand{\\%sRest}[%d]{%s}'
            % (name, store, name, name, arity - 9, rest))


def macros(index):
    out = []
    for k, v in index.get('macros', {}).items():
        body, arity = (v[0], int(v[1])) if isinstance(v, list) else (v, 0)
        out.append(define(k, arity, body))
    return '\n'.join(out)


PREAMBLE = r'''\documentclass[10pt,openany]{book}
\usepackage[english]{babel}
\usepackage[a4paper,margin=2.3cm]{geometry}
\usepackage{fontspec}
\usepackage{amsmath,amssymb,mathrsfs}
\usepackage{xcolor}
\usepackage[most]{tcolorbox}
\usepackage[hidelinks]{hyperref}
\setsansfont{Arial Unicode MS}
\setmonofont[Scale=0.9]{Menlo}
\definecolor{note}{HTML}{1F4E79}
\definecolor{lnk}{HTML}{0645AD}
\newtcolorbox{source}[1][]{breakable,colback=gray!4,colframe=gray!40,boxrule=0.4pt,arc=2pt,
  left=6pt,right=6pt,top=3pt,bottom=3pt,fontupper=\footnotesize\sffamily,#1}
\newcommand{\decl}[4]{\par\medskip\noindent\hypertarget{#3}{}\textbf{#1}\enspace
  {\footnotesize\href{#4}{\color{lnk}\texttt{#2}}}\par\nopagebreak\noindent}
\newcommand{\lcite}[2]{\hyperlink{#1}{\color{lnk}\texttt{#2}}}
\newcommand{\xcite}[2]{\href{#1}{\color{lnk}\texttt{#2}}}
\setlength{\parindent}{0pt}
\emergencystretch=3em
\sloppy
'''


def breakable(t):
    """A reading whose formulas may break after their commas and before their
    parentheses: the formulas that Informath leaves unread (forall(R, λv. ...))
    are long and would run into the margin."""
    def math(m):
        s = m.group(0)
        s = re.sub(r',\s', r',\\allowbreak ', s)
        s = re.sub(r'(?<=[A-Za-z}])\s*\(', r'\\allowbreak(', s)
        return s
    return re.sub(r'\$[^$]+\$', math, t)


def reading_tex(d, rd):
    """The statement: Informath's reading, or Lean's own statement."""
    t = (rd or {}).get('Eng')
    if t:
        return breakable(t)
    st = d.get('statement') or ''
    return '{\\small\\itshape (not read)} {\\footnotesize\\texttt{%s}}' % esc(st)


MAIN = [('riemannHypothesis', 'The Riemann hypothesis'),
        ('riemannZeta_eq_zero_re', 'The zeros of the zeta function'),
        ('LFunction_ne_zero_of_half_lt_re', 'GRH for Dirichlet L-functions, half-plane form'),
        ('LFunction_eq_zero_re', 'GRH for Dirichlet L-functions'),
        ('LFunction_eq_zero_re_of_isPrimitive', 'GRH for primitive Dirichlet characters')]

STYLE = """body{font-family:-apple-system,Segoe UI,Roboto,Helvetica,Arial,sans-serif;margin:0 auto;max-width:900px;
padding:1.5rem;line-height:1.55;color:#222}h1{font-size:1.8em}h2{border-bottom:1px solid #ddd;margin-top:2em}
.thm{border-left:3px solid #1F4E79;padding:.3em .9em;margin:1em 0;background:#f7f9fc}
.thm .src{font-size:.8em;color:#666}code{font-size:.9em}.m{color:#777;font-size:.85em}
li{margin:.2em 0}"""


def index_page(index, readings, deps, toc):
    mj = {}
    for k, v in index.get('macros', {}).items():
        body, arity = (v[0], int(v[1])) if isinstance(v, list) else (v, 0)
        mj[k] = [body, arity] if arity else body
    head = ('<!DOCTYPE html><html lang=en><head><meta charset=utf-8><title>The Generalized Riemann Hypothesis, '
            'read by Informath</title><style>%s</style><script>window.MathJax={tex:{macros:%s}};</script>'
            '<script defer src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml-full.js"></script></head><body>'
            % (STYLE, json.dumps(mj)))
    out = [head, '<h1>The Generalized Riemann Hypothesis</h1>',
           '<p>The Lean proof <a href="https://github.com/lsernau/grh-lean/tree/%s/grh-compact">grh-lean</a> '
           '(compact edition), read in English by Informath: %d declarations in %d volumes.</p>'
           % (GRH_COMMIT, sum(t[2] for t in toc), len(toc)),
           '<h2>The main theorem</h2>']
    for name, title in MAIN:
        d, rd = deps.get(name, {}), (readings.get(name) or {}).get('readings', {})
        url = GRH_URL % ('Main', d.get('line') or 1)
        out.append('<div class=thm><b>%s.</b> %s<div class=src><a href="%s">src/Main.lean: %s</a></div></div>'
                   % (title, rd.get('Eng', ''), url, html.escape(name)))
    out.append(open(os.path.join(BOOK, 'preface.html')).read())
    out.append('<h2>Contents</h2><ol>')
    for vi, vtoc, num in toc:
        chs = ''.join('<li>%s <span class=m>(%s)</span></li>'
                      % (html.escape(t), html.escape(', '.join(ms[:3]) + (' …' if len(ms) > 3 else '')))
                      for t, ms in vtoc)
        out.append('<li><a href="volumes/vol%d.pdf">Volume %d</a> <span class=m>(%d declarations)</span><ul>%s</ul></li>'
                   % (vi, vi, num, chs))
    out.append('</ol></body></html>')
    return '\n'.join(out)


def main():
    deps = {d['name']: d for d in json.load(open(os.path.join(WORK, 'deps.json')))}
    order = json.load(open(os.path.join(WORK, 'order.json')))
    index = json.load(open(os.path.join(WORK, 'index.json')))
    readings = {d['lean']: d for d in index['declarations']}
    mloc = json.load(open(os.path.join(WORK, 'mathlib-locations.json'))) \
        if os.path.exists(os.path.join(WORK, 'mathlib-locations.json')) else {}
    if SAMPLE:
        have = {d['module'] for d in index['declarations']}
        order = [o for o in order if o['module'] in have]
    # chapters: maximal runs of one folder; volumes: chapters up to about VOLUME declarations
    chapters = []
    for o in order:
        if chapters and chapters[-1]['folder'] == o['folder']:
            chapters[-1]['modules'].append(o)
        else:
            chapters.append({'folder': o['folder'], 'modules': [o]})
    volumes, cur, n = [], [], 0
    for ch in chapters:
        k = sum(len([x for x in m['decls'] if deps[x]['kind'] not in SKIP]) for m in ch['modules'])
        if cur and n + k > VOLUME:
            volumes.append(cur)
            cur, n = [], 0
        cur.append(ch)
        n += k
    if cur:
        volumes.append(cur)
    # where each declaration is: volume, for links across volumes
    where = {}
    for vi, vol in enumerate(volumes, 1):
        for ch in vol:
            for m in ch['modules']:
                for x in m['decls']:
                    where[x] = vi
    os.makedirs(VOLS, exist_ok=True)
    mac = macros(index)
    seen_folders = set()
    toc = []
    for vi, vol in enumerate(volumes, 1):
        out = [PREAMBLE, mac, '\\begin{document}',
               '\\begin{titlepage}\\centering\\vspace*{4cm}{\\Huge The Generalized Riemann Hypothesis}\\par'
               '\\vspace{1em}{\\Large grh-lean (compact edition), read by Informath}\\par\\vspace{2em}'
               '{\\LARGE Volume %d}\\par\\vspace{1em}{\\large %s}\\end{titlepage}'
               % (vi, ' -- '.join(sorted(set(esc(c['folder']) for c in vol), key=lambda f: f))),
               '\\tableofcontents']
        num = 0
        vtoc = []
        for ch in vol:
            f = ch['folder']
            title = FOLDER_TITLES.get(f, f)
            cont = f in seen_folders
            seen_folders.add(f)
            out.append('\\chapter{%s%s}' % (esc(title), ' (continued)' if cont else ''))
            vtoc.append((title + (' (continued)' if cont else ''), [m['module'] for m in ch['modules']]))
            for m in ch['modules']:
                out.append('\\section*{\\texttt{%s}}\\addcontentsline{toc}{section}{\\texttt{%s}}'
                           % (esc(m['module']), esc(m['module'])))
                for x in m['decls']:
                    d = deps[x]
                    if d['kind'] in SKIP:
                        continue
                    num += 1
                    rd = readings.get(x, {})
                    path = m['module'].replace('.', '/')
                    url = (GRH_URL % (path, d['line'] or 1)).replace('#', '\\#')
                    out.append('\\decl{%s %d.%d}{src/%s.lean: %s}{%s}{%s}'
                               % (KINDS.get(d['kind'], 'Definition'), vi, num, esc(path), esc(x), target(x), url))
                    out.append(reading_tex(d, rd.get('readings')))
                    if d.get('doc', '').strip():
                        out.append('\\begin{source}%s\\end{source}' % esc(d['doc'].strip()))
                    if d['kind'] == 'theorem':
                        cites = []
                        for u in d['uses']:
                            if u in deps and deps[u]['kind'] not in SKIP:
                                if where.get(u) == vi:
                                    cites.append('\\lcite{%s}{%s}' % (target(u), esc(u)))
                                elif u in where:
                                    cites.append('\\xcite{vol%d.pdf\\#%s}{%s}' % (where[u], target(u), esc(u)))
                        ml = []
                        # the lemmas of Mathlib's tactics (Mathlib.Tactic.Ring..., Mathlib.Meta.NormNum...)
                        # are left out: the tactics apply them, the proof does not cite them
                        for u in d['mathlib']:
                            if u.startswith(('Mathlib.', 'Lean.', 'Std.', 'Batteries.Tactic')):
                                continue
                            loc = mloc.get(u)
                            if loc:
                                ml.append('\\xcite{%s}{%s}' % ((MATHLIB_URL % (loc[0].replace('.', '/'), loc[1] or 1)).replace('#', '\\#'), esc(u)))
                            else:
                                ml.append('\\texttt{%s}' % esc(u))
                        parts = []
                        if cites:
                            parts.append(', '.join(cites))
                        if ml:
                            parts.append('Mathlib: ' + ', '.join(ml))
                        out.append('\\par\\smallskip{\\small\\raggedright\\textit{Proof.} %s.\\hfill$\\square$\\par}'
                                   % ('By ' + '; '.join(parts) if parts else 'By the definitions'))
        out.append('\\end{document}')
        open(os.path.join(VOLS, 'vol%d.tex' % vi), 'w').write('\n'.join(out) + '\n')
        toc.append((vi, vtoc, num))
    # the index page: the main theorems, the preface, the contents
    open(os.path.join(BOOK, 'index.html'), 'w').write(index_page(index, readings, deps, toc))
    print('%d volumes, %d declarations -> %s, index.html' % (len(volumes), sum(t[2] for t in toc), VOLS))


if __name__ == '__main__':
    main()
