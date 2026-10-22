#!/usr/bin/env python3
"""Build mathlib-informath.html, a table of contents, and pages/<Part>.html,
one page for each part of Mathlib in modules.txt, from index.json (made by
build-index.py): each exported Mathlib statement with its Lean source, its
Dedukti translation, and Informath's informalization in English, French,
Czech and as a formula, rendered by MathJax, and the proof texts of the theorems.

    lake exe export $(grep -v '^#' modules.txt)     # -> out/<Module>.dk, .json, -deps.dk
    python3 build-index.py                  # -> index.json
    python3 build-html.py                   # -> mathlib-informath.html, pages/*.html

The Lean source is read from the Mathlib checkout (../mathlib4, or $MATHLIB),
from the line where the declaration starts up to its ":=", without the
docstring, which is shown apart; each declaration links to its line on
GitHub, at the commit of the checkout.
"""
import html, json, os, re

MATHLIB = os.environ.get('MATHLIB', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'mathlib4'))
GITHUB = 'https://github.com/leanprover-community/mathlib4/blob/%s/%s#L%d'
OUT = 'mathlib-informath.html'
INDEX = 'index.json'
LANGUAGE_NAMES = {'Eng': 'English', 'Fre': 'French', 'Cze': 'Czech'}
SHOWN = ['Eng']     # the languages shown by default; the others are switched on in the page header
MATHJAX = 'https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml-full.js'


# ---------------------------------------------------------------- the pieces

def source(module, d):
    """The declaration as written in Mathlib, without its docstring and proof:
    up to its first := outside brackets (not the one of @[deprecated (since := ...)])."""
    path = os.path.join(MATHLIB, module.replace('.', '/') + '.lean')
    lines = open(path).read().split('\n')
    i, end = d['line'] - 1, d['endLine']
    if lines[i].lstrip().startswith('/--'):        # the docstring is shown apart
        while i < end and '-/' not in lines[i]:
            i += 1
        i += 1
    if d.get('definiens'):                          # the definiens is shown too
        return '\n'.join(lines[i:end]).rstrip()
    out, depth = [], 0
    while i < end:
        l = lines[i]
        if out and depth == 0 and re.match(r'\s*\|', l):   # equations of a definition by cases
            break
        cut = None
        for k, ch in enumerate(l):
            if ch in '([{':
                depth += 1
            elif ch in ')]}':
                depth -= 1
            elif ch == ':' and l[k:k + 2] == ':=' and depth == 0:
                cut = k + 2
                break
        if cut is not None:
            out.append(l[:cut])
            break
        out.append(l)
        if depth == 0 and re.search(r'\bwhere\s*$', l):
            break
        i += 1
    return '\n'.join(out).rstrip()


def justification_html(j, where, here):
    """The rule of a step, \\texttt{Nat\\_\\_Prime\\_\\_ne\\_zero} 2, 3: its Lean name,
    linked to its entry where it has one."""
    def one(mt):
        dk = mt.group(1).replace('\\_', '_')
        lean = dk.replace('__', '.')
        page = where.get(lean)
        if page:
            href = ('' if page == here else os.path.basename(page)) + '#' + lean
            return '<a href="%s"><code>%s</code></a>' % (html.escape(href), html.escape(lean))
        return '<code>%s</code>' % html.escape(lean)
    return re.sub(r'\\texttt\{([^{}]*)\}', one, html.escape(j, quote=False))


def proof_html(rows, where, here):
    body = ''.join('<tr><td class=n>%s</td><td>%s</td><td class=j>%s</td></tr>'
                   % (html.escape(n), reading_html(t), justification_html(j, where, here))
                   for n, t, j in rows)
    return ('<details%s><summary>%d lines</summary><table class=proof>%s</table></details>'
            % (' open' if len(rows) <= 12 else '', len(rows), body))


def doc_html(doc):
    """A Mathlib docstring: Markdown, with `code` and *emphasis*."""
    t = html.escape(doc.strip())
    t = re.sub(r'`([^`]*)`', r'<code>\1</code>', t)
    t = re.sub(r'\*([^*\s][^*]*)\*', r'<em>\1</em>', t)
    return re.sub(r'\n\s*\n', '<br>', t)


def reading_html(t):
    # a qualified constant without a form for its place in a formula,
    # \mathrm{Nat\_\_primeFactors}, is shown as an operator, primeFactors
    def operator(m):
        parts = m.group(1).split('\\_\\_')
        if parts[-1] == 'app' and len(parts) > 1:   # a constant applied as a function
            parts = parts[:-1]
        return '\\operatorname{%s}' % parts[-1].replace('\\_', '\\_')
    t = re.sub(r'\\mathrm\{((?:[A-Za-z0-9\']+\\_\\_)+[A-Za-z0-9\']+)\}', operator, t)
    t = html.escape(t, quote=False)
    t = t.replace('\\begin{itemize}', '<ul>').replace('\\end{itemize}', '</ul>')
    t = re.sub(r'\\item\b\s*', '<li>', t)
    return re.sub(r'\\textbf\{([^{}$]*)\}', r'<b>\1</b>', t)


# ---------------------------------------------------------------- the page

STYLE = """
 body{font-family:-apple-system,Segoe UI,Roboto,Helvetica,Arial,sans-serif;margin:0 auto;max-width:1150px;padding:1.5rem;line-height:1.5;color:#222;background:#fff}
 header{border-bottom:1px solid #ddd;margin-bottom:1rem}
 nav{font-size:.9em;margin-bottom:.4rem}
 h2{margin-top:2.4rem;border-bottom:2px solid #0645ad;padding-bottom:.2rem;font-size:1.25rem}
 h2 a{font-size:.7em;font-weight:400;margin-left:.6rem}
 .entry{padding:.8rem 0;border-bottom:1px solid #eee}
 .name{font-weight:700;font-family:ui-monospace,Menlo,monospace;color:#0645ad}
 .k{font-size:.72em;padding:0 .35rem;border-radius:3px;background:#eef;color:#335;margin-left:.4rem}
 .k.theorem{background:#e6f4ea;color:#1e6b34}
 .src{font-size:.8em;margin-left:.6rem}
 .doc{color:#444;font-size:.92em;margin:.3rem 0}
 .row{display:grid;grid-template-columns:6.5rem 1fr;gap:.6rem;margin:.25rem 0;align-items:start}
 .lab{color:#666;font-size:.75em;text-transform:uppercase;letter-spacing:.04em;padding-top:.35rem}
 pre{background:#f6f8fa;border:1px solid #e1e4e8;border-radius:6px;padding:.45rem .6rem;overflow:auto;font-size:.8em;white-space:pre-wrap;margin:0}
 pre.lean{background:#fbf8ef;border-color:#ece3c8}
 .text{font-size:.95em;padding-top:.2rem}
 .missing{color:#999;font-style:italic}
 .forced{color:#999;font-size:.75em}
 table.proof{border-collapse:collapse;font-size:.95em;margin:.1rem 0}
 table.proof td{padding:.1rem .5rem;vertical-align:top;border-bottom:1px solid #f0f0f0}
 table.proof td.n{color:#888;text-align:right;white-space:nowrap}
 table.proof td.j{color:#555;white-space:nowrap;font-size:.9em}
 summary{cursor:pointer;color:#0645ad;font-size:.85em}
 table.cov{border-collapse:collapse;margin:.6rem 0;font-size:.9em}
 table.cov td,table.cov th{border:1px solid #ddd;padding:.2rem .6rem;text-align:right}
 table.cov td:first-child,table.cov th:first-child{text-align:left}
 table.cov tr.group td{font-weight:700;background:#f4f6fb}
"""

INTRO = """<p>Statements of <a href="https://github.com/leanprover-community/mathlib4">Mathlib</a>
(commit <code>{COMMIT}</code>), each with its <b>Lean</b> source, its translation to
<b>Dedukti</b> by <code>Export.lean</code>, and its informalization by
<a href="https://github.com/GrammaticalFramework/informath">Informath</a>, in
<b>English</b>, as a <b>formula</b>, and in <b>French</b> and <b>Czech</b>,
which the buttons at each entry show there, and the check boxes above the entries everywhere. The Dedukti translation drops implicit and
instance arguments and maps Lean's arithmetic and logic to Informath's base
(<code>mapping.tsv</code>); the other Mathlib constants are worded by the symbol table
<code>mathlib.dkgf</code>, whose English wordings Informath also renders in the other languages. Constants without a wording appear as
$\\mathrm{name}$.</p>"""


def lang_switch(languages):
    """Check boxes for the languages hidden by default: a checked language
    shows its rows on every page, remembered in the browser."""
    hidden = [l for l in languages if l not in SHOWN]
    if not hidden:
        return ''
    boxes = ' '.join('<label><input type=checkbox data-lang="%s"> %s</label>' % (l, LANGUAGE_NAMES[l])
                     for l in hidden)
    return '<div class=langs>Show also: %s</div>' % boxes


LANG_SCRIPT = """
<script>
(function(){
  function get(l){try{return localStorage.getItem('lang-'+l)==='1';}catch(e){return false;}}
  function set(l,v){try{localStorage.setItem('lang-'+l,v?'1':'0');}catch(e){}}
  // a language's button in an entry shows or hides it in that entry only
  function show(entry,l,on){
    entry.classList.toggle('show-'+l,on);
    var b=entry.querySelector('.langlink[data-lang="'+l+'"]'); if(b) b.classList.toggle('on',on);
  }
  document.addEventListener('click',function(e){
    var b=e.target.closest('.langlink'); if(!b) return;
    var entry=b.closest('.entry'), l=b.dataset.lang;
    show(entry,l,!entry.classList.contains('show-'+l));
  });
  // a check box above the entries shows or hides the language in all of them
  function all(l,on){ document.querySelectorAll('.entry').forEach(function(e){show(e,l,on);}); }
  document.querySelectorAll('.langs input').forEach(function(box){
    var l=box.dataset.lang;
    box.checked=get(l);
    if(box.checked) all(l,true);
    box.addEventListener('change',function(){ all(l,box.checked); set(l,box.checked); });
  });
})();
</script>"""


def page(title, head, body, macros, extra=''):
    return """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>%s</title>
<script>
window.MathJax = {
  tex: { inlineMath: [['$','$']], displayMath: [['$$','$$']], macros: %s },
  options: { skipHtmlTags: ['script','noscript','style','textarea','pre','code'] }
};
</script>
<script async src="%s"></script>%s
<style>%s</style></head><body>
<header>%s</header>
%s%s
</body></html>
""" % (html.escape(title), json.dumps(macros), MATHJAX, extra, STYLE + lang_css(), head, body,
       LANG_SCRIPT if 'class=langs' in head else '')


def lang_css():
    hidden = [l for l in LANGUAGE_NAMES if l not in SHOWN]
    return ''.join(' .row.lang-%s{display:none}\n .entry.show-%s .row.lang-%s{display:grid}\n' % (l, l, l)
                   for l in hidden) + \
        ' .langlink{font:inherit;font-size:.8em;margin-left:.5rem;padding:0 .35rem;border:1px solid #c8d3e6;' \
        'border-radius:3px;background:#f4f6fb;color:#0645ad;cursor:pointer}\n' \
        ' .langlink.on{background:#0645ad;color:#fff;border-color:#0645ad}\n' \
        ' .langs{position:sticky;top:0;z-index:2;background:#fff;border-bottom:1px solid #ddd;' \
        'padding:.35rem 0;font-size:.9em}\n .langs label{margin-left:.8rem;cursor:pointer}\n'


def entry_html(d, languages, commit, where):
    """A declaration of the index, with its readings and proof texts."""
    name, m = d['lean'], d['module']
    path = m.replace('.', '/') + '.lean'

    def text(mode, what):
        t = d['readings'].get(mode)
        forced = (' <span class=forced>(forced symbolic: no wording found)</span>'
                  if mode in d['forced'] else '')
        return ('<div class=text>%s%s</div>' % (reading_html(t), forced) if t
                else '<div class="text missing">no %s</div>' % what)
    # rows: (language or None, label, content)
    rows = [
        (None, 'Lean', '<pre class=lean>%s</pre>' % html.escape(source(m, d))),
        (None, 'Dedukti', '<pre>%s</pre>' % html.escape(d['dedukti'] or '(not exported)')),
    ] + [(lang, LANGUAGE_NAMES[lang], text(lang, 'reading')) for lang in languages] + [
        (None, 'Formula', text('formula', 'formula')),
    ]
    for lang in languages:
        if d['proof'] and lang in d['proof']:
            rows.append((lang, 'Proof' if lang == 'Eng' else 'Proof, ' + LANGUAGE_NAMES[lang],
                         proof_html(d['proof'][lang], where, where[name])))
    toggles = ''.join('<button type=button class=langlink data-lang="%s" title="show or hide %s here">%s</button>'
                      % (l, LANGUAGE_NAMES[l], LANGUAGE_NAMES[l]) for l in languages if l not in SHOWN)
    return ('<div class=entry id="%s"><span class=name>%s</span><span class="k %s">%s</span>'
            '<a class=src href="%s">%s:%d</a>%s%s%s</div>' % (
                html.escape(name), html.escape(name), d['kind'], d['kind'],
                GITHUB % (commit, path, d['nameLine']), html.escape(path.split('/')[-1]), d['nameLine'],
                toggles,
                '<div class=doc>%s</div>' % doc_html(d['doc']) if d['doc'] else '',
                ''.join('<div class="row%s"><div class=lab>%s</div><div>%s</div></div>'
                        % (' lang-' + l if l else '', lab, c) for l, lab, c in rows)))


def cov_head(languages):
    return '<th>statements</th>' + ''.join(
        '<th>fully worded, %s</th>' % LANGUAGE_NAMES[l] if i == 0 else '<th>%s</th>' % LANGUAGE_NAMES[l]
        for i, l in enumerate(languages))


def cov_cells(ns, tag='td'):
    return ''.join('<%s>%d</%s>' % (tag, n, tag) for n in ns)


def worded(text):
    """No constant left verbatim: a variable may hold for arguments ($r$
    holds for $a$ and $b$), a \\mathrm{Constant} may not."""
    return bool(text) and '\\mathrm' not in text


def main():
    index = json.load(open(INDEX))
    commit, languages, ms = index['mathlib'], index['languages'], index['macros']
    decls = index['declarations']
    os.makedirs('pages', exist_ok=True)
    page_of = {m: g for g, mods in index['pages'] for m in mods}
    # every declaration's page, for the links of the proofs
    where = {d['lean']: 'pages/%s.html' % page_of[d['module']] for d in decls}
    head_cov = cov_head(languages)
    rows, total = [], [0] * (1 + len(languages))
    for g, mods in index['pages']:
        file = 'pages/%s.html' % g
        body, grows, gtot = [], [], [0] * (1 + len(languages))
        for m in mods:
            ds = [d for d in decls if d['module'] == m]
            body.append('<h2 id="%s">%s <a href="%s">source</a></h2>' % (
                html.escape(m), html.escape(m), GITHUB % (commit, m.replace('.', '/') + '.lean', 1)))
            body += [entry_html(d, languages, commit, where) for d in ds]
            ns = [len(ds)] + [sum(worded(d['readings'].get(lang)) for d in ds) for lang in languages]
            grows.append((m, ns))
            gtot = [a + b for a, b in zip(gtot, ns)]
        head = ('<nav><a href="../mathlib-informath.html">Mathlib informalized</a> &rsaquo; %s</nav>'
                '<h1>%s</h1>%s' % (html.escape(g), html.escape(g), INTRO.replace('{COMMIT}', commit[:10])) +
                '<table class=cov><tr><th>module</th>%s</tr>%s</table>'
                % (head_cov, ''.join('<tr><td><a href="#%s">%s</a></td>%s</tr>'
                                     % (html.escape(m), html.escape(m), cov_cells(ns)) for m, ns in grows)) +
                lang_switch(languages))
        open(file, 'w').write(page(g + ' informalized', head, '\n'.join(body), ms))
        rows.append('<tr class=group><td><a href="%s">%s</a></td>%s</tr>' % (file, html.escape(g), cov_cells(gtot)))
        rows += ['<tr><td>&nbsp;&nbsp;<a href="%s#%s">%s</a></td>%s</tr>'
                 % (file, html.escape(m), html.escape(m[len(g) + 1:]), cov_cells(ns)) for m, ns in grows]
        total = [a + b for a, b in zip(total, gtot)]
        print('%s: %d statements, fully worded: %s -> %s' % (
            g, gtot[0], ', '.join('%d %s' % (n, l) for n, l in zip(gtot[1:], languages)), file))
    toc = ('<table class=cov><tr><th>part of Mathlib</th>%s</tr>%s<tr><th>all</th>%s</tr></table>'
           % (head_cov, ''.join(rows), cov_cells(total, 'th')))
    # the declarations had anchors on this page before it was split
    forward = ('\n<script>\n(function(){var w=%s;var h=decodeURIComponent(location.hash.slice(1));'
               'if(w[h])location.replace(w[h]+"#"+encodeURIComponent(h));})();\n</script>' % json.dumps(where))
    head = '<h1>Mathlib informalized</h1>' + INTRO.replace('{COMMIT}', commit[:10]) + \
        '<p>One page for each part of Mathlib:</p>' + toc
    open(OUT, 'w').write(page('Mathlib informalized', head, '', {}, forward))
    print('%d statements in %d modules, fully worded: %s -> %s and %d pages' % (
        total[0], len(page_of), ', '.join('%d %s' % (n, l) for n, l in zip(total[1:], languages)),
        OUT, len(index['pages'])))


if __name__ == '__main__':
    main()
