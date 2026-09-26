# Standalone LaTeX editions

**Current P3 C5:** [complete PDF](cells/p3-c5.pdf), [standalone LaTeX](cells/p3-c5.tex), [submission Markdown](cells/p3-c5.md), and [fresh Astra audit](../../cagent/p3/c5/audit.md). This edition replaces the earlier partial C5 document. The combined `p3.pdf` is a historical snapshot; use the current C5 document for the complete upper bound.

The four problem editions typeset the published P1–P4 Markdown at repository commit [`212bba53b1818c08c40b8c4b48f636651eaf6410`](https://github.com/mpelteshki/climbing-to-the-frontier/tree/212bba53b1818c08c40b8c4b48f636651eaf6410). The P1 formalization appendix and 14 cell editions use their accompanying Markdown sources in this directory, assembled and audited for individual submission. They are presentation copies and retain each cell’s stated proof limits. `sources.json` records SHA-256 hashes of every Markdown input. For original `cagent/` sources, the builder uses the local file when its hash matches and otherwise reads it from the pinned commit with `git show`, then verifies the hash. Derived `p3-source.md` and cell Markdown must match their local hashes exactly.

| Edition | Source and scope |
| --- | --- |
| `p1.tex` | `cagent/p1/writeup.md`: written C1–C5 proofs; C6 excluded. |
| `p1-formalization.tex` | `p1-formalization.md`: the complete published P1 Lean module closure and replay instructions, with its stated formalization scope. |
| `p2.tex` | `cagent/p2/writeup.md`: published writeup and its explicit witness lists. |
| `p3.tex` | `p3-source.md`: assembled published C1–C4 proofs and C5 lower bound. Historical snapshot: its C5 section contains only the lower bound and is superseded by the complete `cells/p3-c5` edition; C6 is skipped. |
| `p4.tex` | `cagent/p4/SUBMISSION.md`: full published submission, including code appendix and stated limitations. |
| `cells/p1-c4.tex` and `cells/p1-c5.tex` | Matching `cells/*.md`: the complete published written C4/C5 arguments as individual submissions. |
| `cells/p3-c1.tex` through `cells/p3-c6.tex` | Matching `cells/*.md`: each P3 cell as a separate document, with C5 replaced by its complete Astra-audited submission; C6 remains a status-only document. |
| `cells/p4-c1.tex` through `cells/p4-c6.tex` | Matching `cells/*.md`: each P4 cell as a separate document, with formal evidence and stated limits. |

P3's assembled Markdown is included so its editorial introduction and precise C5/C6 status are reproducible. It retains all proof text from `c1/written-proof.md`, both C2 proofs, `c3/written-proof.md`, `c4/written-proof.md`, and `c5/lower-bound-proof.md`. The individual proof hashes in `sources.json` identify the published originals. The formalization appendix and cell Markdown are likewise retained beside their TeX outputs.

Build from the repository root with Python 3 and **Pandoc 3.11**:

```sh
PANDOC=/path/to/pandoc python3 docs/latex/build.py all
```

For one edition, replace `all` with `p1`, `p3-c2`, or another document name. The builder accepts `pandoc` on `PATH` and checks its exact version. Rebuilding original problem editions requires the pinned Git commit to be available locally if those source files have since changed; the builder never fetches from the network.

Each `.tex` file is a complete document, but compilation also needs the included `fonts/` directory. With a standard TeX installation, run `xelatex -interaction=nonstopmode p1.tex` from `docs/latex/`, or compile a cell from `docs/latex/cells/`; repeat for cross-references if needed. The built-in editor may not resolve relative font assets, so the PDFs in this package were verified with portable Tectonic. The documents use explicit Latin Modern font files, standard math/table packages, `hyperref`, and `fvextra`. Lean code uses the included [JuliaMono v0.63.2](https://github.com/cormullion/juliamono/releases/tag/v0.63.2) regular font under the SIL Open Font License. `sources.json` records the font and license hashes. Its cmap covers all 43 non-ASCII characters in the fenced code, including `∣`, `ᗮ`, and `𝕜`, so those glyphs can render and copy without substitution. Long code blocks use breakable `Verbatim`.

Conversion resolves relative Markdown links to GitHub URLs at the pinned source commit. Existing links to a specific earlier commit remain as written, preserving evidence provenance. Existing `blob/main` links in the same repository are pinned to the recorded commit. Standalone `\[` and `\]` display delimiters are normalized before Pandoc. Non-code Unicode math symbols and accented Latin letters are rendered with TeX commands; fenced code remains byte-for-byte intact.
