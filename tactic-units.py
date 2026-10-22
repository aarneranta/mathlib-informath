#!/usr/bin/env python3
"""The tactic proofs of a module as proof units, for RunInformath -tactic-proof.

    lake exe export --tactics <Module>          # -> out/<Module>-tactics.json
    python3 tactic-units.py <Module>            # -> out/<Module>-tactic-units.json

out/<Module>-tactics.json has, for each step of a tactic proof (a tactic of a
tactic sequence), the main goal before it and the goals after it, with their
hypotheses and targets in Dedukti. A step becomes one or two proof units,
by comparing the goals:

* hypotheses that are there before the step without an earlier step having
  made them (the case hypotheses of by_cases, rcases, induction, at the
  beginning of a case) are assumed: "Assume that n = 1";
* new hypotheses after the step: assumed if the step introduces them (intro,
  rintro), "let n be ... such that ..." if they include variables (obtain,
  rcases), and stated if they are propositions only (have, rw at, simp at);
* a goal closed by the step is stated, justified by the step: "m = p";
* a changed goal is what is enough to show: "it is enough to show that ...",
  the conjunction of the goals if there are several;
* a step that splits the goal into cases (by_cases, rcases with |, cases,
  induction) is "we reason by cases" or "by induction".

Each unit has the step's tactic as its justification. The declaration of a
step is found by its line in out/<Module>.json.
"""
import json, re, sys

INTRO = ('intro', 'intros', 'rintro', 'introv')
# the tactics whose new hypotheses are derived facts, not assumptions; "at h"
# makes a rewriting or simplification one too
DERIVED = ('have', 'haveI', 'obtain', 'rcases', 'specialize', 'replace', 'choose', 'lift')
CASES = ('by_cases', 'byCases', 'cases', 'rcases', 'casesm', 'obtain', 'match', 'split')
INDUCTION = ('induction', 'induction\'')


def tactic_name(step):
    """The tactic's name: the first word of its text (rw for rw [...])."""
    m = re.match(r"[A-Za-z_][A-Za-z_0-9'?!]*|·|<;>", step['tactic'].strip())
    return m.group(0) if m else ''


HYGIENE = re.compile(r"([A-Za-z_][A-Za-z0-9_']*)\._@\.[A-Za-z0-9_.']*?_hyg\.\d+")


def clean(s):
    """Names with Lean's macro scopes (m._@.M._hyg.42, shown as m✝) as m'."""
    return HYGIENE.sub(lambda m: m.group(1) + "'", s)


def hyps(goal):
    """The accessible hypotheses of a goal, as (name, type) pairs."""
    return [(clean(h[0]), clean(h[1])) for h in (goal or {}).get('hyps', []) if not h[2]]


def target(goal):
    return clean(goal['target'])


def is_prop(ty):
    return ty.startswith('Proof ')


def conj(props):
    out = props[-1]
    for p in reversed(props[:-1]):
        out = 'and (%s) (%s)' % (p, out)
    return out


def split_if(target):
    """if A B -> (A, B), for a target in Dedukti, else None."""
    if not target.startswith('if '):
        return None
    args = top_args(target[3:])
    return (args[0], args[1]) if len(args) == 2 else None


def top_args(s):
    """The arguments of an application, as written: 'A (B C) D' -> ['A', 'B C', 'D']."""
    out, depth, cur = [], 0, ''
    for ch in s.strip():
        if ch == '(':
            depth += 1
            if depth == 1:
                continue
        elif ch == ')':
            depth -= 1
            if depth == 0:
                out.append(cur)
                cur = ''
                continue
        if ch == ' ' and depth == 0:
            if cur:
                out.append(cur)
            cur = ''
            continue
        cur += ch
    if cur:
        out.append(cur)
    return out


def first_line(tactic):
    """The justification: the tactic's first line, without a nested proof's "by"."""
    line = tactic.strip().split('\n')[0].strip()
    return re.sub(r'\s*:=\s*by$', '', line)


def units_of_proof(steps):
    """The proof units of the steps of one proof, in order."""
    units, seen = [], set()
    if steps and steps[0]['before']:
        seen = set(hyps(steps[0]['before']))
    for st in steps:
        before, after = st['before'], st['after']
        if not before or 'error' in before or any('error' in a for a in after):
            units.append({'unit': 'obvious', 'by': st['tactic']})
            continue
        name = tactic_name(st)
        hb = hyps(before)
        # hypotheses there without an earlier step's making them: a case's
        entered = [h for h in hb if h not in seen]
        if entered:
            units.append({'unit': 'hypos', 'hypos': entered, 'by': ''})
        seen |= set(hb)
        n_before = st.get('nBefore', 1)
        closed = len(after) < n_before
        new_goals = after[:max(0, len(after) - n_before + 1)]
        # the hypotheses a step makes count as seen, but not those of the cases
        # it splits the goal into: they are assumed where each case begins
        if len(new_goals) <= 1:
            for a in new_goals:
                seen |= set(hyps(a))
        if name == '·':
            continue
        main = new_goals[0] if new_goals else None
        new = [h for h in hyps(main) if h not in hb] if main else []
        if name in INDUCTION:
            units.append({'unit': 'induction', 'by': st['tactic']})
            continue
        if len(new_goals) > 1 and (name in CASES or '|' in st['tactic']):
            units.append({'unit': 'cases', 'by': st['tactic']})
            continue
        derived = name in DERIVED or ' at ' in st['tactic']
        if not derived:
            # a hypothesis whose type changes by a substitution (rintro rfl) is not new
            names_before = {n for n, _ in hb}
            new = [h for h in new if h[0] not in names_before]
        if new and name in ('have', 'haveI') and re.search(r':=\s*by\b', st['tactic']) \
                and all(is_prop(t) for _, t in new):
            # a fact proved by a nested proof, which follows
            units.append({'unit': 'verify', 'prop': conj([t[len('Proof '):] for _, t in new]),
                          'by': st['tactic']})
        elif new:
            if not derived:
                units.append({'unit': 'hypos', 'hypos': new, 'by': st['tactic']})
            elif all(is_prop(t) for _, t in new):
                units.append({'unit': 'conclusion', 'prop': conj([t[len('Proof '):] for _, t in new]),
                              'by': st['tactic']})
            else:
                units.append({'unit': 'hypos', 'hypos': new, 'by': st['tactic']})
        if closed:
            units.append({'unit': 'conclusion', 'prop': target(before), 'by': st['tactic']})
        elif main and target(main) != target(before) or len(new_goals) > 1:
            if name in INTRO:
                # an assumption that substitutes (rintro rfl) leaves no hypothesis
                ab = split_if(target(before))
                if not new and ab:
                    units.append({'unit': 'hypos', 'hypos': [['_h', 'Proof (%s)' % ab[0]]],
                                  'by': st['tactic']})
            else:
                targets = [target(g) for g in new_goals]
                units.append({'unit': 'enough', 'prop': conj(targets), 'by': st['tactic']})
    return units


def inside(s, c):
    """Whether step s is a part of the step c: another step that starts within it."""
    return s is not c and (s['line'], s['col']) >= (c['line'], c['col']) and s['line'] <= c['endLine']


def main():
    mod = sys.argv[1]
    decls = json.load(open('out/%s.json' % mod))
    steps = json.load(open('out/%s-tactics.json' % mod))
    proofs = []
    for d in decls:
        if d['kind'] != 'theorem' or d.get('definiens'):
            continue
        mine = [s for s in steps if d['line'] <= s['line'] <= d['endLine']]
        # the tactics inside t <;> u are told by the combination itself
        combined = [s for s in mine if '<;>' in s['kind']]
        mine = [s for s in mine if not any(inside(s, c) for c in combined)]
        if mine:
            units = units_of_proof(mine)
            for u in units:
                u['by'] = first_line(u['by'])
            proofs.append({'name': d['dk'], 'lean': d['lean'], 'steps': units})
    out = 'out/%s-tactic-units.json' % mod
    json.dump(proofs, open(out, 'w'), ensure_ascii=False, indent=1)
    print('%s: %d tactic proofs, %d units -> %s' % (mod, len(proofs), sum(len(p['steps']) for p in proofs), out))


if __name__ == '__main__':
    main()
