#!/usr/bin/env python3
"""Export the statements of the modules of work/modules.txt in batches: one
exporter process exports many modules, loading their imports once (a process
per module spends a minute or more on its imports). The exporter writes
out/<M>.json module by module, in the order given; when no module is finished
for STALL seconds, the module it is on is taken to hang the exporter: the
process is killed, that module is named in work/skipped.txt, and a new
process goes on with the rest. JOBS workers share the modules (each process
needs about 6-8 GB).

    python3 scripts/export-batches.py [JOBS] [STALL] [IMPORT]     # default 3, 60, 600

STALL is the limit between two modules of a batch; the first module of a
batch gets IMPORT seconds, which include the imports.
"""
import os, subprocess, sys, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
BOOK = os.path.join(HERE, '..')
EXP = os.path.join(BOOK, 'exporter')
OUT = os.path.join(EXP, 'out')
JOBS = int(sys.argv[1]) if len(sys.argv) > 1 else 3
STALL = int(sys.argv[2]) if len(sys.argv) > 2 else 60
IMPORT = int(sys.argv[3]) if len(sys.argv) > 3 else 600
BATCH = 40
NAMES = os.path.join(BOOK, 'grh-names.dkgf')

env = dict(os.environ)
env['STATEMENTS_ONLY'] = '1'  # the book shows no proof terms; translating them is 15x slower
env['MATHLIB'] = os.path.expanduser('~/claude/grh-lean/grh-compact/src')
env['ENTRY_TABLES'] = '../../../../mathlib.dkgf:../../../../structures.dkgf:../grh-names.dkgf:../grh.dkgf'
env['LEAN_PATH'] = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=EXP, capture_output=True,
                                  text=True).stdout.strip()
lock = threading.Lock()


def done(m):
    f = os.path.join(OUT, m + '.json')
    return os.path.exists(f) and os.path.getmtime(f) > os.path.getmtime(NAMES)


def skip(m):
    with lock:
        open(os.path.join(BOOK, 'work', 'skipped.txt'), 'a').write(m + '\n')
        print('skipped', m, flush=True)


def worker(mods):
    todo = [m for m in mods if not done(m)]
    while todo:
        batch = todo[:BATCH]
        p = subprocess.Popen([os.path.join(EXP, '.lake', 'build', 'bin', 'export')] + batch, cwd=EXP, env=env,
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        last, n = time.time(), 0
        while p.poll() is None:
            time.sleep(5)
            k = sum(1 for m in batch if done(m))
            if k > n:
                n, last = k, time.time()
            elif time.time() - last > (STALL if n else IMPORT):
                p.kill()
                p.wait()
                break
        left = [m for m in batch if not done(m)]
        if left and p.returncode != 0:
            # the first module not done is the one the exporter was on
            skip(left[0])
            left = left[1:]
        elif left:
            for m in left:
                skip(m)
            left = []
        todo = left + todo[BATCH:]


def main():
    mods = [l.strip() for l in open(os.path.join(BOOK, 'work', 'modules.txt')) if l.strip()]
    # the modules skipped before are not tried again (rm work/skipped.txt to retry them)
    sk = os.path.join(BOOK, 'work', 'skipped.txt')
    skipped = set(l.strip() for l in open(sk)) if os.path.exists(sk) else set()
    mods = [m for m in mods if m not in skipped]
    shards = [mods[i::JOBS] for i in range(JOBS)]
    ts = [threading.Thread(target=worker, args=(s,)) for s in shards]
    for t in ts:
        t.start()
    for t in ts:
        t.join()
    print('%d of %d modules exported' % (sum(1 for m in mods if done(m)), len(mods)))


if __name__ == '__main__':
    main()
