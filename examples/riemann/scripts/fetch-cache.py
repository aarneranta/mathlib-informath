#!/usr/bin/env python3
"""Fetch the compiled files of the given modules of riemann-hypothesis-original
and of all the modules they import, and nothing else: the full cache
(`lake exe cache get`) unpacks to about 105 GB, the import closure of the
modules read here to about 11 GB.

    python3 scripts/fetch-cache.py <project> <Module> ...

The files are the community cache that the project's scripts/restore-cache.py
restores (the same pinned list of archives, modules.jsonl.gz, with its sha256),
each archive checked against the sha256 that the list gives for it and unpacked
by Lean's leantar into <project>/.lake/build. Mathlib's files come first, by
`lake exe mathlib/cache get` in the project. A module that is not in the list
(Challenge, added after the submission) is compiled by `lake build <Module>`.
"""
import concurrent.futures as cf, gzip, hashlib, json, os, subprocess, sys, urllib.request
from pathlib import Path

LIST = 'https://rh-cache.taucetiproject.org/bootstrap/e50d09817ad81469f737e8f637561e6ccf86c670/modules.jsonl.gz'
LIST_SHA256 = '292caa386a620d935cfc736b56fcceaab9fe7073086693b62e899c1ee4725f04'
ARTIFACTS = 'https://rh-cache.taucetiproject.org/artifacts/leanprover-community/riemann-hypothesis/'
AGENT = {'User-Agent': 'RiemannHypothesisCache/1.0'}


def imports(src):
    """Module -> the modules it imports, from the import lines of src/."""
    out = {}
    for d, _, fs in os.walk(src):
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(d, f)
                ims = []
                for line in open(p, encoding='utf8'):
                    if line.startswith('import '):
                        ims.append(line.split()[1])
                    elif line.strip():
                        break
                out[os.path.relpath(p, src)[:-5].replace(os.sep, '.')] = ims
    return out


def main():
    root, mods = Path(sys.argv[1]).resolve(), sys.argv[2:]
    imp = imports(root / 'src')
    seen, todo = set(), list(mods)
    while todo:
        m = todo.pop()
        if m not in seen and m in imp:
            seen.add(m)
            todo += imp[m]
    cache = root / '.lake' / 'cache' / 'artifacts'
    cache.mkdir(parents=True, exist_ok=True)
    lst = cache.parent / 'modules.jsonl.gz'
    if not lst.exists() or hashlib.sha256(lst.read_bytes()).hexdigest() != LIST_SHA256:
        data = urllib.request.urlopen(urllib.request.Request(LIST, headers=AGENT), timeout=60).read()
        if hashlib.sha256(data).hexdigest() != LIST_SHA256:
            sys.exit('the list of archives has the wrong sha256')
        lst.write_bytes(data)
    rows = {r[0]: r for r in map(json.loads, gzip.decompress(lst.read_bytes()).splitlines()[1:])}
    missing = sorted(m for m in seen if m not in rows)
    wanted = sorted(m for m in seen if m in rows)

    def get(m):
        _, _, art, digest = rows[m]
        p = cache / art
        if p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest() == digest:
            return 0
        req = urllib.request.Request(ARTIFACTS + art[:-len('.ltar')] + '.art', headers=AGENT)
        for _ in range(3):
            try:
                data = urllib.request.urlopen(req, timeout=60).read()
            except OSError:
                continue
            if hashlib.sha256(data).hexdigest() == digest:
                p.write_bytes(data)
                return len(data)
        raise SystemExit('%s: no archive with the right sha256' % m)

    print('%d modules in the import closure; fetching...' % len(wanted), flush=True)
    with cf.ThreadPoolExecutor(64) as ex:
        n = sum(ex.map(get, wanted))
    print('%d bytes downloaded' % n, flush=True)
    jobs = []
    for m in wanted:
        _, dep_hash, art, _ = rows[m]
        rel = Path(*m.split('.')).parent
        bases = [str(root / '.lake/build/lib/lean' / rel), str(root / '.lake/build/ir' / rel)]
        for b in bases:
            Path(b).mkdir(parents=True, exist_ok=True)
        jobs.append({'file': str(cache / art), 'hash': dep_hash, 'base': bases})
    env = dict(os.environ, ELAN_TOOLCHAIN='leanprover/lean4:v4.33.1', RUST_MIN_STACK='8388608')
    lean = Path(subprocess.check_output(['elan', 'which', 'lean'], cwd=root, env=env, text=True).strip())
    subprocess.run([str(lean.with_name('leantar')), '--jobs', '16', '-f', '-x', '-j', '-'],
                   input=json.dumps(jobs), text=True, cwd=root, env=env, check=True)
    print('%d modules unpacked' % len(jobs))
    for m in missing:
        print('not in the cache, compiling:', m, flush=True)
        subprocess.run(['lake', 'build', m], cwd=root, env=dict(os.environ, LAKE_ARTIFACT_CACHE='false'), check=True)


if __name__ == '__main__':
    main()
