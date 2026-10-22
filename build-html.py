#!/usr/bin/env python3
"""Build mathlib-informath.html, a table of contents, and pages/<Part>.html,
one page for each directory of Mathlib whose modules are in modules.txt
(pages/Mathlib.Data.Nat.Prime.html for Mathlib.Data.Nat.Prime.Defs, ...),
with each exported Mathlib statement, its
Lean source, its Dedukti translation, and Informath's informalization in
English and as a formula, rendered by MathJax.

    lake exe export $(cat modules.txt)     # -> out/<Module>.dk, .json, -deps.dk
    python3 build-html.py                  # -> mathlib-informath.html, pages/*.html

The modules are those of modules.txt, in its order.  The Lean source is read
from the Mathlib checkout (../mathlib4, or $MATHLIB), from the line where the
declaration starts up to its ":=", without the docstring, which is shown
apart; each declaration links to its line on GitHub, at the commit of the
checkout.  The readings are made with RunInformath and mathlib.dkgf: the
newest RunInformath built in $INFORMATH_ROOT (stack build), or the one on the
PATH.
"""
import difflib, glob, html, json, os, re, subprocess, sys

MATHLIB = os.environ.get('MATHLIB', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'mathlib4'))
GITHUB = 'https://github.com/leanprover-community/mathlib4/blob/%s/%s#L%d'
TABLE = 'mathlib.dkgf'
OUT = 'mathlib-informath.html'
MATHJAX = 'https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml-full.js'


def informath():
    root = os.environ.get('INFORMATH_ROOT')
    if not root:
        sys.exit('INFORMATH_ROOT is not set')
    built = glob.glob(os.path.join(root, '.stack-work', 'dist', '*', '*', 'build', 'RunInformath', 'RunInformath'))
    return max(built, key=os.path.getmtime) if built else 'RunInformath'


RUN = None
FORCED = set()   # (name, symbolic) of the readings made with -force-symbolic


def run(*args):
    r = subprocess.run([RUN] + list(args), capture_output=True, text=True)
    if r.returncode:
        sys.exit('RunInformath failed: %s\n%s' % (' '.join(args), r.stderr[-1500:]))
    return [l for l in r.stdout.split('\n') if l.strip()]


# ---------------------------------------------------------------- the pieces

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
    their definiens), as a temporary file: what the readings are made from,
    and the module's part of the base of the proof texts."""
    text = open('out/%s.dk' % m).read()
    theorems = {d['dk'] for d in decls if is_theorem(d)}

    def one(mt):
        name = mt.group(1)
        return '%s : %s.' % (name, mt.group(2)) if name in theorems else mt.group(0)
    text = re.sub(r'^def ([^ ]+) : (.*?) :=\n  .*?\.$', one, text, flags=re.S | re.M)
    path = '.html-%s-statements.dk' % m
    open(path, 'w').write(text)
    return path


# Lean names written as notation, $\operatorname{primeFactors}(#1)$, are what
# formulas can do; English uses the words of the entry instead
PSEUDO = re.compile(r'\s*\|\s*\$\\operatorname\{[A-Za-z]+\}\([^$]*\)\$|\$\\operatorname\{[A-Za-z]+\}\([^$]*\)\$\s*\|\s*')
ENGLISH_TABLE = '.html-english.dkgf'
STANDARD = 'lcm|gcd|max|min|supp|deg|card|ord'


def english_table():
    """mathlib.dkgf without the pseudo-notations of the entries that have words."""
    if not os.path.exists(ENGLISH_TABLE):
        out = []
        for l in open(TABLE):
            if not l.startswith('#') and '"' in l and '\\operatorname{' in l:
                def drop(m):   # the operator names of mathematics are notation, not Lean
                    return m.group(0) if re.search(r'operatorname\{(%s)\}' % STANDARD, m.group(0)) else ' | '
                l = PSEUDO.sub(drop, l).replace('|  |', '|').rstrip(' |\n') + '\n'
            out.append(l)
        open(ENGLISH_TABLE, 'w').write(''.join(out))
    return ENGLISH_TABLE


def readings(dk, decls, blocks, symbolic):
    """Lean name -> reading, aligned with the declarations by their labels."""
    flags = ['-add-symboltables=' + (TABLE if symbolic else english_table())] + \
        (['-to-symbolic-latex'] if symbolic else []) + [dk]
    lines = run(*flags)
    names = [d['lean'] for d in decls]
    if symbolic:
        lab = re.compile(r'^\\textbf\{(\w+)\}(?: \\texttt\{\\detokenize\{([^}]*)\}\})?\.\s*')
        labels = [(lambda m: (m.group(2) or m.group(1)) if m else '?')(lab.match(l)) for l in lines]
        expected = [d['dk'] if is_theorem(d) else 'Definition' for d in decls]
        strip = lambda l: lab.sub('', l).strip()
    else:
        lab = re.compile(r'^([A-Za-z0-9\\_\']+)\.\s')
        labels = [lab.match(l).group(1).replace('\\_', '_') if lab.match(l) else '?' for l in lines]
        expected = [(d['dk'][0].upper() + d['dk'][1:]) if is_theorem(d) else 'Definition'
                    for d in decls]
        strip = lambda l: lab.sub('', l)
    out = {}
    sm = difflib.SequenceMatcher(a=expected, b=labels, autojunk=False)
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal':
            for k in range(i2 - i1):
                out[names[i1 + k]] = strip(lines[j1 + k])
    # a declaration that got no reading is read alone with -force-symbolic,
    # which writes \mathrm{c}(...) where a constant has no form that fits
    for d in decls:
        if d['lean'] in out or d['lean'] not in blocks:
            continue
        tmp = '.html-one.dk'
        open(tmp, 'w').write(blocks[d['lean']] + '\n')
        ls = run('-force-symbolic', *flags[:-1], tmp)
        os.remove(tmp)
        if ls:
            out[d['lean']] = strip(ls[0])
            FORCED.add((d['lean'], symbolic))
    return out


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


def proof_texts(m, decls, blocks, stmts):
    """Lean name -> the rows (number, sentence, justification) of the proof
    text of each proved theorem: RunInformath -proof-text on the declaration
    alone, with Informath's base, nd.dk, the module's dependencies and its
    statements as the base, so that each lemma's premisses are known."""
    base = '.html-proof-base.dk'
    with open(base, 'w') as f:
        for path in [os.path.join(os.environ['INFORMATH_ROOT'], 'share', 'baseconstants.dk'), 'nd.dk']:
            f.write(open(path).read() + '\n')
        # the lemmas are rules without their type class instances (Export.lean
        # writes those hypotheses (_ : Proof (C x)) and drops them in proofs)
        for path in ['out/%s-deps.dk' % m, stmts]:
            f.write(drop_instances(open(path).read()) + '\n')
    out = {}
    for d in decls:
        if not (is_theorem(d) and d.get('definiens')):
            continue
        one = '.html-proof.dk'
        open(one, 'w').write(blocks[d['lean']] + '\n')
        r = subprocess.run([RUN, '-proof-text', '-base=' + base, '-add-symboltables=' + TABLE, one],
                           capture_output=True, text=True)
        os.remove(one)
        tables = re.findall(r'\\begin\{tabular\}\{[^\n]*\}\n(.*?)\\end\{tabular\}', r.stdout, re.S)
        if r.returncode or not tables:
            PROOF_FAILED.append(d['lean'])
            continue
        rows = []
        for row in re.split(r'\\\\\s*\n', tables[0]):
            mt = re.match(r'\s*(\d+\.)\s*&(.*)&(.*)$', row, re.S)
            if mt:
                rows.append(tuple(g.strip() for g in mt.groups()))
        out[d['lean']] = rows
    os.remove(base)
    return out


PROOF_FAILED = []


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


def macros(modules):
    """MathJax macros: those of mathlib.dkgf's LaTeX forms, and Informath's own."""
    base = '.html-base.dk'
    with open(base, 'w') as f:
        for m in modules:
            f.write(open('out/%s-deps.dk' % m).read() + '\n' + open('out/%s.dk' % m).read() + '\n')
    # the macros are numbered after their position in the table, so the English
    # table, which has fewer LaTeX forms, names them otherwise: both sets are needed
    lines = run('-base=' + base, TABLE) + run('-base=' + base, english_table())
    os.remove(base)
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
<b>English</b> and as a <b>formula</b>. The Dedukti translation drops implicit and
instance arguments and maps Lean's arithmetic and logic to Informath's base
(<code>mapping.tsv</code>); the other Mathlib constants are worded by the symbol table
<code>mathlib.dkgf</code>. Constants without a wording appear as
$\\mathrm{name}$.</p>"""


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
%s
</body></html>
""" % (html.escape(title), json.dumps(macros), MATHJAX, extra, STYLE, head, body)


def group_of(module):
    """The subfile of a module: its directory, Mathlib.Data.Nat.Prime for
    Mathlib.Data.Nat.Prime.Defs."""
    return module.rsplit('.', 1)[0]


def entry_html(m, d, blocks, english, formula, proofs, commit, where):
    name = d['lean']
    path = m.replace('.', '/') + '.lean'
    e, f = english.get(name), formula.get(name)
    rows = [
        ('Lean', '<pre class=lean>%s</pre>' % html.escape(source(m, d))),
        ('Dedukti', '<pre>%s</pre>' % html.escape(blocks.get(name, '(not exported)'))),
        ('English', '<div class=text>%s%s</div>' % (reading_html(e), forced(name, False)) if e
         else '<div class="text missing">no reading</div>'),
        ('Formula', '<div class=text>%s%s</div>' % (reading_html(f), forced(name, True)) if f
         else '<div class="text missing">no formula</div>'),
    ]
    if name in proofs:
        rows.append(('Proof', proof_html(proofs[name], where, 'pages/%s.html' % group_of(m))))
    return ('<div class=entry id="%s"><span class=name>%s</span><span class="k %s">%s</span>'
            '<a class=src href="%s">%s:%d</a>%s%s</div>' % (
                html.escape(name), html.escape(name), d['kind'], d['kind'],
                GITHUB % (commit, path, d['nameLine']), html.escape(path.split('/')[-1]), d['nameLine'],
                '<div class=doc>%s</div>' % doc_html(d['doc']) if d['doc'] else '',
                ''.join('<div class=row><div class=lab>%s</div><div>%s</div></div>' % r for r in rows)))


def forced(name, symbolic):
    return (' <span class=forced>(forced symbolic: no wording found)</span>'
            if (name, symbolic) in FORCED else '')


def worded(text):
    return bool(text) and '\\mathrm' not in text and 'holds for' not in text


def main():
    global RUN
    RUN = informath()
    modules = [l.strip() for l in open('modules.txt') if l.strip() and not l.startswith('#')]
    commit = subprocess.run(['git', '-C', MATHLIB, 'rev-parse', 'HEAD'],
                            capture_output=True, text=True).stdout.strip()
    ms = macros(modules)
    groups = []
    for m in modules:
        if not groups or groups[-1][0] != group_of(m):
            groups.append((group_of(m), []))
        groups[-1][1].append(m)
    os.makedirs('pages', exist_ok=True)
    where, rows, total = {}, [], [0, 0]
    for g, mods in groups:          # every declaration's page, for the links of the proofs
        for m in mods:
            for d in json.load(open('out/%s.json' % m)):
                where[d['lean']] = 'pages/%s.html' % g
    for g, mods in groups:
        file = 'pages/%s.html' % g
        body, grows, gtot = [], [], [0, 0]
        for m in mods:
            decls = json.load(open('out/%s.json' % m))
            blocks = dk_blocks('out/%s.dk' % m)
            stmts = statements(m, decls)
            english = readings(stmts, decls, blocks, False)
            formula = readings(stmts, decls, blocks, True)
            proofs = proof_texts(m, decls, blocks, stmts)
            os.remove(stmts)
            body.append('<h2 id="%s">%s <a href="%s">source</a></h2>' % (
                html.escape(m), html.escape(m), GITHUB % (commit, m.replace('.', '/') + '.lean', 1)))
            body += [entry_html(m, d, blocks, english, formula, proofs, commit, where) for d in decls]
            n, w = len(decls), sum(worded(english.get(d['lean'])) for d in decls)
            for d in decls:
                where[d['lean']] = file
            grows.append((m, n, w))
            gtot[0] += n
            gtot[1] += w
        head = ('<nav><a href="../mathlib-informath.html">Mathlib informalized</a> &rsaquo; %s</nav>'
                '<h1>%s</h1>%s' % (html.escape(g), html.escape(g), INTRO.replace('{COMMIT}', commit[:10])) +
                '<table class=cov><tr><th>module</th><th>statements</th><th>fully worded</th></tr>%s</table>'
                % ''.join('<tr><td><a href="#%s">%s</a></td><td>%d</td><td>%d</td></tr>'
                          % (html.escape(m), html.escape(m), n, w) for m, n, w in grows))
        open(file, 'w').write(page(g + ' informalized', head, '\n'.join(body), ms))
        rows.append('<tr class=group><td><a href="%s">%s</a></td><td>%d</td><td>%d</td></tr>'
                    % (file, html.escape(g), gtot[0], gtot[1]))
        rows += ['<tr><td>&nbsp;&nbsp;<a href="%s#%s">%s</a></td><td>%d</td><td>%d</td></tr>'
                 % (file, html.escape(m), html.escape(m.rsplit('.', 1)[1]), n, w) for m, n, w in grows]
        total[0] += gtot[0]
        total[1] += gtot[1]
        print('%s: %d statements, %d fully worded -> %s' % (g, gtot[0], gtot[1], file))
    toc = ('<table class=cov><tr><th>part of Mathlib</th><th>statements</th><th>fully worded</th></tr>%s'
           '<tr><th>all</th><th>%d</th><th>%d</th></tr></table>' % (''.join(rows), total[0], total[1]))
    # the declarations had anchors on this page before it was split
    forward = ('\n<script>\n(function(){var w=%s;var h=decodeURIComponent(location.hash.slice(1));'
               'if(w[h])location.replace(w[h]+"#"+encodeURIComponent(h));})();\n</script>' % json.dumps(where))
    head = '<h1>Mathlib informalized</h1>' + INTRO.replace('{COMMIT}', commit[:10]) + \
        '<p>One page for each part of Mathlib:</p>' + toc
    open(OUT, 'w').write(page('Mathlib informalized', head, '', {}, forward))
    print('%d statements in %d modules, %d fully worded -> %s and %d pages (RunInformath: %s)'
          % (total[0], len(modules), total[1], OUT, len(groups), RUN))
    if os.path.exists(ENGLISH_TABLE):
        os.remove(ENGLISH_TABLE)
    if PROOF_FAILED:
        print('%d proofs without a proof text: %s' % (len(PROOF_FAILED), ' '.join(PROOF_FAILED)))


if __name__ == '__main__':
    main()
