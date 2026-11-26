# The GRH proof of grh-lean, read by Informath

A book-format informalization of [grh-lean](https://github.com/lsernau/grh-lean)
(compact edition, commit 72fead1): the five theorems of `src/Main.lean` and every
declaration they depend on, in an order where nothing is used before it is stated,
as HTML pages (`index.html`, `pages/chNNN.html`) linked to grh-lean and mathlib4 on GitHub.

Work in progress: the statements are being exported; the HTML is so far built for a sample.

Pipeline (grh-lean cloned to `~/claude/grh-lean`, built in `grh-compact`):

    cd exporter && lake build && lake exe deps          # work/deps.json, work/mathlib-locations.json
    python3 scripts/order.py                            # work/order.json, work/modules.txt
    RIEMANN=$HOME/claude/grh-lean/grh-compact python3 scripts/name-table.py   # grh-names.dkgf
    python3 scripts/export-batches.py 3 60 600          # exporter/out/*.json; hanging modules -> work/skipped.txt
    INFORMATH_ROOT=$HOME/claude/informath python3 scripts/read-modules.py work/index.json <modules>
    python3 scripts/make-html.py                        # index.html, pages/

`grh.dkgf` is the hand-written symbol table of the project's central notions;
`grh-names.dkgf` is generated from the names of the declarations. `preface.html` is
the hand-written preface included in `index.html`.
