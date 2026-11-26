#!/usr/bin/env python3
"""The order of the book: the modules of the closure (work/deps.json) in an
order where every module comes after the modules it imports, keeping the
modules of one folder together as far as the imports allow, and the
declarations of each module in their source order (Lean's own order, in
which nothing is used before it is declared).

    python3 scripts/order.py      # -> work/order.json

work/order.json: [{"module": M, "folder": F, "decls": [names in source order]}]
in book order. The imports are read from the sources (grh-compact/src).
"""
import collections, heapq, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
BOOK = os.path.join(HERE, '..')
SRC = os.environ.get('GRH_SRC', os.path.expanduser('~/claude/grh-lean/grh-compact/src'))


def folder(m):
    """The chapter of a module: its first two components (Lib.Weil, New.Selmer),
    or the module itself for the top ones (Statements, Main, New.Main)."""
    p = m.split('.')
    return '.'.join(p[:2]) if len(p) > 2 else m


def imports(m):
    path = os.path.join(SRC, *m.split('.')) + '.lean'
    out = []
    for l in open(path):
        mm = re.match(r'\s*(?:public\s+)?import\s+(\S+)', l)
        if mm:
            out.append(mm.group(1))
        elif l.strip() and not l.startswith(('--', '/-', 'module', 'prelude', 'public', ' ', '\t')) and 'import' not in l:
            break
    return out


def main():
    deps = json.load(open(os.path.join(BOOK, 'work', 'deps.json')))
    by_mod = collections.defaultdict(list)
    for d in deps:
        by_mod[d['module']].append(d)
    mods = set(by_mod)
    # the imports between the modules of the closure, transitively through the
    # others (a module of the closure may import one outside it that imports
    # one inside)
    direct = {}
    todo = list(mods)
    while todo:
        m = todo.pop()
        if m in direct:
            continue
        if not os.path.exists(os.path.join(SRC, *m.split('.')) + '.lean'):
            direct[m] = []
            continue
        direct[m] = [i for i in imports(m) if os.path.exists(os.path.join(SRC, *i.split('.')) + '.lean')]
        todo += direct[m]
    reach = {}

    def inside(m, seen=None):
        """The modules of the closure that m imports, looking through the others."""
        if m in reach:
            return reach[m]
        out = set()
        for i in direct.get(m, []):
            if i in mods:
                out.add(i)
            else:
                out |= inside(i)
        reach[m] = out
        return out
    preds = {m: inside(m) for m in mods}
    succs = collections.defaultdict(set)
    for m, ps in preds.items():
        for p in ps:
            succs[p].add(m)
    # Kahn's algorithm; among the ready modules, those of the folder being
    # written first, then by the folder's first appearance, then by name
    indeg = {m: len(preds[m]) for m in mods}
    ready = [m for m in mods if indeg[m] == 0]
    order, current = [], None

    def run_length(f, indeg, ready):
        """How many modules of folder f can be written in a row from here."""
        indeg, ready, n = dict(indeg), set(ready), 0
        while True:
            c = [m for m in ready if folder(m) == f]
            if not c:
                return n
            m = min(c)
            ready.discard(m)
            n += 1
            for s in succs[m]:
                indeg[s] -= 1
                if indeg[s] == 0:
                    ready.add(s)
    while ready:
        same = sorted(m for m in ready if folder(m) == current)
        if same:
            m = same[0]
        else:
            # Statements first (it imports only Mathlib); then the folder that
            # goes on longest, the background (Lib) before the argument (New)
            fs = sorted(set(folder(x) for x in ready))
            best = max(fs, key=lambda f: (f == 'Statements', f.startswith('Lib'), run_length(f, indeg, ready), -fs.index(f)))
            m = sorted(x for x in ready if folder(x) == best)[0]
        ready.remove(m)
        order.append(m)
        current = folder(m)
        for s in succs[m]:
            indeg[s] -= 1
            if indeg[s] == 0:
                ready.append(s)
    if len(order) != len(mods):
        sys.exit('import cycle among %d modules' % (len(mods) - len(order)))
    out = []
    for m in order:
        ds = sorted(by_mod[m], key=lambda d: (d['line'] or 10 ** 9, d['name']))
        out.append({'module': m, 'folder': folder(m), 'decls': [d['name'] for d in ds]})
    json.dump(out, open(os.path.join(BOOK, 'work', 'order.json'), 'w'), ensure_ascii=False, indent=0)
    # the chapters: maximal runs of one folder
    runs = []
    for o in out:
        if runs and runs[-1][0] == o['folder']:
            runs[-1][1] += len(o['decls'])
        else:
            runs.append([o['folder'], len(o['decls'])])
    print('%d modules, %d declarations, %d chapters (runs of a folder), %d folders'
          % (len(out), sum(len(o['decls']) for o in out), len(runs), len(set(o['folder'] for o in out))))


if __name__ == '__main__':
    main()
