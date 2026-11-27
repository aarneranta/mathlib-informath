"""Two declarations of the book as a page for the paper's figure
(~/papers/mathlib/riemann-book.pdf): the Riemann hypothesis of src/Main.lean and
exists_data, the first of the main steps, each as its book page shows it, with
its Lean source above the reading and the proof cut to its first citations.

    python3 scripts/paper-figure.py fig.html
    "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" --headless \
        --no-pdf-header-footer --virtual-time-budget=20000 --print-to-pdf=out.pdf fig.html

The page size is in the @page rule."""
import html, os, re, sys
BOOK = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.expanduser('~/claude/grh-lean/grh-compact/src/')
ITEMS = [('Main', 'riemannHypothesis', 4, 4), ('New.Data.DataExist', 'exists_data', 49, 51)]
CITED = 4


def decl_div(module, name):
    page = open(os.path.join(BOOK, 'pages', module + '.html'), encoding='utf-8').read()
    i = page.index('id="%s"' % name)
    i = page.rindex('<div class="decl', 0, i)
    ends = [k for k in (page.find('<div class="decl', i + 1), page.find('<nav', i + 1), page.find('</body>', i)) if k > 0]
    return page[i:min(ends)].rstrip()


def cut_proof(div):
    m = re.search(r'(<div class=proof><i>Proof\.</i> By )(.*?)(\.?</div>)', div, re.S)
    if not m:
        return div
    links = re.findall(r'<a [^>]*>.*?</a>', m.group(2), re.S)
    if len(links) <= CITED + 1:
        return div
    short = ', '.join(links[:CITED]) + ', &hellip; (%d in all)' % len(links)
    return div[:m.start()] + m.group(1) + short + '.</div>' + div[m.end():]


def source(module, first, last):
    lines = open(SRC + module.replace('.', '/') + '.lean', encoding='utf-8').read().split('\n')
    return '\n'.join(lines[first - 1:last])


body = []
for module, name, first, last in ITEMS:
    div = cut_proof(decl_div(module, name))
    lean = '<pre class=lean>%s</pre>' % html.escape(source(module, first, last))
    div = div.replace('<div class=reading>', lean + '<div class=reading>', 1)
    body.append(div)
css = ('<style>@page{size:228mm 114mm;margin:0} body{margin:0;padding:3mm 5mm;max-width:none;font-size:13px} '
       'pre.lean{background:#f6f6f6;padding:.4em .6em;margin:.3em 0;font-size:12px;white-space:pre-wrap} '
       '.decl{padding:.4rem 0;border-bottom:1px solid #ddd} .decl:last-child{border-bottom:none} '
       'mjx-container{font-size:95% !important}</style>')
page = ('<!DOCTYPE html><html lang=en><head><meta charset=utf-8><title>Figure</title>'
        '<link rel=stylesheet href="%s/style.css"><script src="%s/macros.js"></script>%s'
        '<script defer src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml-full.js"></script></head>'
        '<body>\n%s\n</body></html>\n' % (BOOK, BOOK, css, '\n'.join(body)))
open(sys.argv[1], 'w', encoding='utf-8').write(page)
