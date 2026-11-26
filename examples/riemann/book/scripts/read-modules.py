"""Informath's readings of exported riemann-hypothesis-original modules, with
mathlib-informath's build-index.py and its symbol tables (English only).

    python3 scripts/read-modules.py [--proofs] <index.json> <Module> ...

Informath is $INFORMATH_ROOT, by default ../informath beside mathlib-informath.
The proof texts of the term proofs are made only with --proofs.
"""
import importlib.util, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
MI = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
EXPORT = os.path.join(HERE, '..', 'exporter', 'out')
os.environ.setdefault('INFORMATH_ROOT', os.path.abspath(os.path.join(MI, '..', 'informath')))
os.environ['LANGUAGES'] = 'Eng'
proofs = '--proofs' in sys.argv[1:]
args = [a for a in sys.argv[1:] if a != '--proofs']
index, mods = os.path.abspath(args[0]), args[1:]
work = os.path.abspath(os.path.join(HERE, '..', 'work'))
os.makedirs(work, exist_ok=True)
spec = importlib.util.spec_from_file_location('build_index', os.path.join(MI, 'build-index.py'))
bi = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bi)
bi.OUT, bi.TMP, bi.INDEX = os.path.abspath(EXPORT), os.path.join(work, '.index-'), index
bi.LANGUAGES, bi.SLOW_LANGUAGES, bi.FAST_LANGUAGES, bi.TACTIC_LANGUAGES = ['Eng'], [], ['Eng'], ['Eng']
# the generated names first, the hand-written table after them (it overrides them)
extra = [os.path.abspath(os.path.join(HERE, '..', t)) for t in ['grh-names.dkgf', 'grh.dkgf']]
bi.TABLES = [os.path.join(MI, t) for t in bi.TABLES] + [t for t in extra if os.path.exists(t)]
bi.read_modules = lambda: mods
# the book's 12,000 statements take RunInformath over 20 minutes in one call: in chunks at once
bi.WHOLE_TIMEOUT = int(os.environ.get('WHOLE_TIMEOUT', '60'))
if not proofs:
    bi.proof_texts = lambda base, ps, langs: ([None] * len(ps), [])
sys.argv = [sys.argv[0]]
os.chdir(MI)
bi.main()
