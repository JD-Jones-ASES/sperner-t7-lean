# Research note: a 7-vertex tournament whose capacity exceeds its transitive number

This folder holds the research note that accompanies the Lean development (`main.tex`, built as
`main.pdf`; rebuild with `pdflatex main.tex`, three passes). The note proves the general tools, shows
that the 7-vertex tournament `T₇` has `√18 ≤ C(T₇) ≤ 5` while `t(T₇) = 4`, shows that every tournament on at most six
vertices has `C = t` (in Lean too), and shows on paper that `T₇` is the only exception on seven.

The finite-data claims of the note are checked by standalone Python 3 programs (standard library
only, exact integers, no `assert` statements). Each prints its checks, runs forged-input controls
that are expected to fail, and ends with a line `VERDICT: PASS` or `VERDICT: FAIL`.

| Certificate | Claim | Re-run |
| --- | --- | --- |
| [0001](certificates/0001-t7-square-clique/) | the 18-point transitive clique of `T₇²`, `t(T₇) = 4`, the lift at `n = 118` and `n = 76` | `python note/certificates/0001-t7-square-clique/verify.py` |
| [0002](certificates/0002-t23-square-clique/) | the 29-point transitive clique of `Q₂₃²`, `t(Q₂₃) = 5`, the lift | `python note/certificates/0002-t23-square-clique/verify.py` |
| [0003](certificates/0003-t7-square-exact/) | `tr(T₇²) = 18` exactly: the 18 points and an exhaustive upper-bound search of its own (`--lower` checks the witness and the lift only) | `python note/certificates/0003-t7-square-exact/verify.py` (about ten minutes; `--lower` under a second) |
| [0004](certificates/0004-six-vertex-closure/) | `C = t` on at most six vertices: two independent class lists with rank-`t` matrices over GF(2), cross-checked | `python note/certificates/0004-six-vertex-closure/verify.py` (2 s) |
| [0005](certificates/0005-seven-vertex-uniqueness/) | 455 of the 456 seven-vertex classes have `C = t`; the remaining class is `T₇` (two independent lists, cross-checked) | `python note/certificates/0005-seven-vertex-uniqueness/verify.py` (40 s) |
| [0006](certificates/0006-t7-rank-bound/) | `C(T₇) ≤ 5`: the rank-5 matrix over ℚ and the Lean factors `T7A`, `T7B` over GF(2) | `python note/certificates/0006-t7-rank-bound/verify.py` (under a second) |
| [0007](certificates/0007-t7-interval-witnesses/) | `tr(T₇³) ≥ 75`, `w(T₇³) ≥ 16`, `w(T₇²) = 7` (the 7-set is the only one) | `python note/certificates/0007-t7-interval-witnesses/verify.py` (under a second) |
| [0008](certificates/0008-gf27-neighbour/) | `t = 5` for the Paley tournament on GF(27) and on its 26 nonzero elements; the 27- and 26-point anti-diagonal cliques | `python note/certificates/0008-gf27-neighbour/verify.py` (10 s) |

Every run is short except 0003, whose exhaustive search proves the upper bound 18 by itself. The count of 84 optimal
sets, the bound `w(T₇³) ≤ 19` and the exhaustive minrank searches are computations without a certificate; the note
labels them as such.

License: the note (`main.tex`, `main.pdf`) is [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/);
the `verify.py` programs are [MIT](../LICENSE), like the rest of the repository.
