#!/usr/bin/env python3
"""How much of each module index.json reads well, and what is missing most.

    python3 coverage.py            # -> coverage.md

For each module: its declarations, how many English readings are fully
worded (no constant shown as \\mathrm{C} because the symbol table lacks it),
how many needed -force-symbolic, and of its theorems how many have a proof
text, from a term or from tactics, and how many proof lines say only "It is
obvious".  Then the constants most often shown symbolically, over all the
modules: the symbol table entries most worth writing.
"""
import collections, json, re

SYMBOLIC = re.compile(r'\\mathrm\{([A-Za-z0-9_\\\']+)\}')
OBVIOUS = 'It is obvious.'


def constants(text):
    return [c.replace('\\_', '_') for c in SYMBOLIC.findall(text or '')
            if '\\_\\_' in c or c[:1].isupper()]


def main():
    index = json.load(open('index.json'))
    by = collections.defaultdict(list)
    for d in index['declarations']:
        by[d['module']].append(d)
    rows, missing = [], collections.Counter()
    seen = collections.defaultdict(set)
    for m, ds in by.items():
        theorems = [d for d in ds if d['kind'] == 'theorem']
        worded = sum(not constants(d['readings'].get('Eng')) for d in ds)
        forced = sum('Eng' in d['forced'] for d in ds)
        term = sum(bool(d['proof']) and not d['tactics'] for d in theorems)
        tactic = sum(bool(d['proof']) and d['tactics'] for d in theorems)
        lines = [r[1] for d in theorems if d['proof'] for r in d['proof'].get('Eng', [])]
        obvious = sum(OBVIOUS in l for l in lines)
        rows.append((m, len(ds), worded, forced, len(theorems), term, tactic, len(lines), obvious))
        for d in ds:
            for c in set(constants(d['readings'].get('Eng'))):
                missing[c] += 1
                seen[c].add(m)
    total = [sum(r[i] for r in rows) for i in range(1, 9)]
    pct = lambda a, b: '%d%%' % (100 * a // b) if b else '-'
    out = ['# Coverage of the English readings', '',
           'Made by `coverage.py` from `index.json`.', '',
           '| module | declarations | fully worded | forced | theorems | term proofs | tactic proofs | proof lines | "obvious" lines |',
           '|---|---|---|---|---|---|---|---|---|']
    for m, n, w, f, t, tp, tc, l, o in rows + [('**all**',) + tuple(total)]:
        out.append('| %s | %d | %d (%s) | %d | %d | %d | %d | %d | %d (%s) |'
                   % (m, n, w, pct(w, n), f, t, tp, tc, l, o, pct(o, l)))
    out += ['', '## Constants shown symbolically', '',
            'The constants without a wording, by the number of readings they occur in.', '',
            '| constant | readings | modules |', '|---|---|---|']
    for c, k in missing.most_common(150):
        out.append('| `%s` | %d | %d |' % (c, k, len(seen[c])))
    open('coverage.md', 'w').write('\n'.join(out) + '\n')
    print('%d declarations, %d fully worded, %d proof texts (%d term, %d tactic), %d of %d proof lines obvious -> coverage.md'
          % (total[0], total[1], total[4] + total[5], total[4], total[5], total[7], total[6]))


if __name__ == '__main__':
    main()
