# Atlas of Distributed Algorithms

**[florian-schager.github.io/atlas](https://florian-schager.github.io/atlas/)**

A curated database of known upper and lower bounds for the classical symmetry-breaking problems in distributed
graph algorithms, with the state of the art highlighted for every range of the maximum degree Δ:

- maximal matching
- maximal independent set (MIS)
- vertex coloring
- edge coloring
- network decomposition
- degree splitting (directed and undirected)

Every result records its runtime, the model (LOCAL or CONGEST), whether it is deterministic or randomized, the
graph class and assumptions it needs, the number of colors (for colorings), and the theorem in the paper it comes
from, with a link to it where possible. The site also lists the reductions between the problems and a
bibliography of all papers.

## How the state of the art is determined

Runtimes are functions of the number of nodes n and the maximum degree Δ, so whether one result beats another
depends on how large Δ is. The site evaluates every runtime at sample values of Δ as functions of n (from
constant through log\* n, polylogarithmic and quasi-polylogarithmic up to polynomial), simplifies it to a single
dominant term in n, and compares the results that match the current filters. A result is marked as state of the
art for the ranges of Δ where no other result is asymptotically faster, unless another result is at least as fast
for every Δ and faster for some Δ. Lower bounds are ranked the same way, with stronger bounds winning.

Results only compete when they solve the same problem in a comparable setting: an algorithm also counts for
stronger models (CONGEST → LOCAL) and for randomized algorithms, a lower bound for weaker models, deterministic
algorithms and superclasses of its graph class, and colorings only compete with colorings that use the same
number of colors. Since Δ is only sampled, the ranges shown are approximate.

## Corrections and missing results

Corrections are very welcome. On the site, every row of a results table and every bibliography entry has a
**Report an issue** button, and every table has a **Report missing algorithm / lower bound** button. Both open a
prefilled issue in this repository, which you can still edit before submitting.

You can also open a pull request that edits the files in `data/` directly (see below). Please run
`scripts/validate.py` before submitting.

## Data

All data lives in `data/` as one YAML file per entry; every entry's `id` equals its file name.

| Folder | Contents |
|---|---|
| `data/results/` | One file per bound (upper or lower), for one problem in one model |
| `data/reductions/` | One file per reduction from one problem to another |
| `data/papers/` | One file per work; conference, journal and arXiv versions are listed as `versions` |
| `data/authors/` | One file per author |
| `data/venues/` | Conferences, journals and preprint servers |
| `schema/` | JSON Schemas for the five entry types |

Conventions:

- `year` of a result is the year of its earliest publication, including arXiv preprints.
- `runtime.latex` is the display form; `runtime.expr` is a machine-readable form using the variables `n`, `Delta`
  and the functions `log`, `logstar`, `sqrt`, `O`, `Otilde`, `Omega`, `Theta`, `min`, e.g.
  `O(log(Delta)^2 * log(n))`. The schema lists everything the parser accepts.
- Coloring results give their number of colors in `colors`.
- Degree splitting results give their variant (`directed` or `undirected`) in `variant` and the maximum
  discrepancy at a node in `discrepancy`; a discrepancy of ε·deg(v) + O(1) is compared as `eps*Delta`.
- A result obtained from another one by a reduction names that result in `reduce_to` (e.g. a maximal matching
  algorithm from an MIS algorithm on the line graph, or a randomized algorithm from a deterministic one by
  shattering).
- A reduction solves `from` with an algorithm for `to`, run on `instance` (the input graph, its line graph or its
  product with K<sub>Δ+1</sub>; `n` and `Delta` give the instance's size in terms of the input graph). Its
  `runtime` uses `T` for the runtime of the algorithm for `to` on the instance, `c` for the colors of a given
  coloring and `C`, `D` for the colors and cluster diameter of a network decomposition. Reductions without
  `sources` are folklore.
- `public_url` on a paper points to a freely accessible version (preferably arXiv) and is left out if none is
  known.

## Running the site locally

The site in `site/` is static and needs no build tools. The Python scripts validate the data and bundle it for the
site:

```bash
python -m venv .venv
source .venv/bin/activate        # on Windows: .venv\Scripts\activate
pip install -r requirements.txt
python scripts/validate.py       # check every entry against its schema and the references between entries
python scripts/build_site.py     # bundle data/ into site/data.js
python scripts/serve.py          # serve the site at http://localhost:8765
```

When served by `scripts/serve.py`, the site shows **Edit** buttons instead of **Report an issue**: they open forms
that check the entry and write it back to `data/`. `scripts/link_theorems.py` adds links to theorems in the HTML
versions of papers on arXiv.

## Maintainer

Florian Schager
