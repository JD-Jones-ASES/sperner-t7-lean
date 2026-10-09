# Verification

All nineteen statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard, the
statement and definition checks, the certificates, the module-resolution check, the elaboration check and Palomar's
core-notation audit of the statements pass; `python scripts/verify.py` runs them all and ends with `VERIFY: PASS`.
The checks below were last run on the tree of the final commit; a build record is evidence for that tree only.
Theorems are numbered as in `comparator.json`, which is also their order in Challenge.lean. `comparator.json` lists no `definition_names`: a name there is a definition hole whose value the
Solution supplies; the nine definitions here are fully specified in the Challenge, so the comparator checks the
Solution's values against them.

## Formal scope

| # | Statement | Proved in |
| --- | --- | --- |
| 1 | `T7_isTournament` — `T₇` is a tournament | SpernerCapacity/T7.lean |
| 2 | `transitiveNumber_T7` — `t(T₇) = 4` | T7.lean (with Clique.lean) |
| 3 | `T7_square_witness` — 18 injective points of `T₇ × T₇`, each earlier one sending an arc to each later one in some coordinate | T7.lean |
| 4 | `T7_exists_clique_gt_four_pow` — some Sperner power of `T₇` has a clique larger than `4ⁿ` | T7.lean (with Lift.lean) |
| 5 | `four_lt_capacity_T7` — `4 < C(T₇)` | T7.lean (with Clique.lean) |
| 6 | `sqrt18_le_capacity_T7` — `√18 ≤ C(T₇)` | T7.lean (with Clique.lean) |
| 7 | `capacity_T7_le_five` — `C(T₇) ≤ 5` | T7.lean (with Rank.lean) |
| 8 | `transitiveNumber_lt_capacity_T7` — `t(T₇) < C(T₇)` | T7.lean |
| 9 | `lift_lemma` — the lift lemma for any digraph | Lift.lean |
| 10 | `rpow_le_capacity` — `N^{1/k} ≤ C(R)` from `N` such points of the `k`-th power | Clique.lean |
| 11 | `transitiveNumber_le_capacity` — `t(R) ≤ C(R)` | Clique.lean |
| 12 | `capacity_le_of_factorization` — the rank bound `C(R) ≤ r` | Rank.lean |
| 13 | `capacity_le_card` — `C(R) ≤ \|V\|` | Clique.lean |
| 14 | `paley_isTournament` — the Paley tournament on 23 vertices is a tournament | T23.lean |
| 15 | `transitiveNumber_paley` — its transitive number is 5 | T23.lean |
| 16 | `five_lt_capacity_paley` — `5 < C` | T23.lean |
| 17 | `sqrt29_le_capacity_paley` — `√29 ≤ C` | T23.lean |
| 18 | `capacity_eq_transitiveNumber_of_card_le_six` — every tournament on at most six vertices has `C = t` | Six.lean (with SixCover.lean, Rank.lean, Clique.lean) |
| 19 | `seven_le_card_of_transitiveNumber_lt_capacity` — a tournament with `t < C` has at least seven vertices | Six.lean |

Each statement is restated verbatim in Solution.lean and closed by the internal theorem of the same name with the
suffix `_internal` (theorems 18 and 19 by the theorems of `Six.lean` of the same names with the suffix). The capacity is `⨆ n, (w(R^{n+1}))^{1/(n+1)}` over the reals; the transitive number is the
supremum of the lengths of injective transitive chains; `T₇` is the induced subtournament of the Paley tournament on
`ZMod 23` through the residue map `W = ![0, 1, 2, 3, 9, 14, 18]`. PROOF.md names the lemma behind each step.

## Local checks

```sh
python scripts/verify.py --fetch-cache
```

runs, in order: the pins (`lean-toolchain` and the Mathlib revision of `lake-manifest.json` are the committed ones),
`scripts/check-source.py`, `scripts/check_definitions.py`, `scripts/check_statements.py`, the certificates under
`note/certificates/` (each must end `VERDICT: PASS`), `lake build` of the four targets `SpernerCapacity`, `Challenge`,
`Solution`, `Test`, `lake env python scripts/check_module_resolution.py`, the elaboration check (every compared
definition printed with `pp.all` from the Challenge and from `SpernerCapacity.Defs`; the outputs must be identical),
and Palomar's `scripts/core_notation_audit.lean` on the twenty-eight compared declarations of `comparator.json`; the
last line is `VERIFY: PASS` or `VERIFY: FAIL`. `--skip-build` leaves out the four Lean steps. The steps can also be
run one by one:

```sh
lake exe cache get
lake build
python scripts/check-source.py
python scripts/check_definitions.py
python scripts/check_statements.py
lake env python scripts/check_module_resolution.py
```

The `Test` target imports `Solution` and audits every constant of its environment whose name begins with
`SpernerCapacity.`, `_private.SpernerCapacity.` or `_private.Solution.` (229 constants, the public declarations
of the development; the audit fails below 200), permits only `propext`, `Classical.choice` and `Quot.sound`,
and fails if any of the nineteen compared theorems is missing. Under the module system the auxiliaries Lean
generates for proofs are not enumerated, but `collectAxioms` follows every private constant a public proof refers
to. A placeholder in a proof compiles with a warning; this audit is what fails the build. Challenge.lean
intentionally contains nineteen proof placeholders; Solution.lean and the modules it imports contain none, and
Solution.lean does not import Challenge.lean. The source guard rejects `sorry`, `sorryAx`, `admit`, `axiom`,
`unsafe`, `partial`, `native_decide`, `implemented_by`, `extern`, `Lean.ofReduceBool` and the kernel-bypass options
in SpernerCapacity.lean, `SpernerCapacity/`, Solution.lean, Test.lean and `Test/`, the same tokens except `sorry` in
Challenge.lean, and any `debug.` option in the `[leanOptions]` table of lakefile.toml. `check_definitions.py` compares
the nine definitions of Challenge.lean and SpernerCapacity/Defs.lean character for character and the two files'
import lines; `check_statements.py` compares every theorem header of Challenge.lean with Solution.lean. Palomar's
`scripts/core_notation_audit.lean` (an unmodified copy from github.com/PalomarRegistry/PalomarSubmission, fetched
2026-10-07 UTC) prints all twenty-eight declarations of the statement surface (the nineteen compared theorems and the nine definitions) with exit 0 (61 s; it takes about 4 GB of memory).

Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`) are pinned by
the committed manifest; `lake update` is never run. Every `.lean` file of the repository carries a `module` header.
`SpernerCapacity/Defs.lean` has exactly the six Mathlib imports of the Challenge, so that the nine definitions
elaborate to identical terms in both environments; printing each with `pp.all` from the Challenge and from
`SpernerCapacity.Defs` gives identical output. A build from an empty `.lake/build` after `lake exe cache get`, one target at a time, takes
about two minutes (129 s for the four targets) on a 16-core, 16 GB PC with the Mathlib cache in place; the two kernel checks of `SixCover.lean` (the data and the coverage bitset for
`n = 6`) take about a minute of kernel time between them, and every other module elaborates in under a minute, most of it
the Mathlib import.

## The finite computations

There is no `native_decide`. The kernel computations are: `decide` over the 49 vertex pairs of `T₇` (each `paley` test
searches the 23 square roots) and over the 529 pairs of `ZMod 23`; the pruned nested searches for the absence of a
transitive 5-chain in `T₇` and of a transitive 6-chain in the Paley tournament (each next vertex ranges over the common
out-neighbourhood of the previous ones; a plain `decide` over all maps `Fin 5 → Fin 7` is not used); the forward
property of the 18 points (153 pairs) and of the 29 points (406 pairs); the pigeonhole inequalities
`(4²)^59 · (17·59 + 1) < 18^59` and `(5²)^49 · (28·49 + 1) < 29^49` by `decide +kernel`; and the diagonal and arc
conditions of the `ZMod 2` factorization (49 sums over `Fin 5`); and, for the tournaments on at most six vertices,
the two checks of `SixCover.lean` for each `n ≤ 6` by `decide +kernel`: the data check (each of the 1, 1, 1, 2, 4, 12,
56 representatives is a tournament on the listed pairs, its `GF(2)` factorization has diagonal 1 and zeros on its arcs,
and its chain of length `t` is transitive) and the coverage bitset (the `or` of `1 <<< code` over every representative
and every one of the `n!` permutations equals `2^{2^{n(n-1)/2}} − 1`, so every orientation of the `n(n−1)/2` pairs is
the code of a relabelled representative; `Nat.lor`, `Nat.shiftLeft` and equality on literals are evaluated natively by
the kernel). A reflection lemma turns a set bit into a representative and a permutation; the factorization and the
chain are transported along it, and the capacity and the transitive number are invariant under relabelling. Everything else is finite-dimensional linear algebra
(the rank bound: Kronecker powers, a diagonal submatrix, the injectivity of a product), real arithmetic with `rpow`
and bounded suprema, and the counting of words by their index sum (the lift).

Mutation controls, each run once in a scratch copy and reverted: (a) the first two points of the 18-point witness
swapped — `T7pts_forward` fails (`decide` proves the proposition false); (b) a `1` placed at the arc position `(0, 1)`
of the right factor `T7B` — `T7AB_arc` fails the same way; (c) the Six module's coverage check with one representative
removed — the bitset is not all ones and `decide +kernel` fails (run by the lane that built the module).

## The certificates in `note/`

Independent of Lean, `note/certificates/` holds eight standard-library Python checkers (exact integers, no `assert`
statements, forged-input controls that fail as they must, a final `VERDICT` line): the 18-point witness with the lift
inequalities (0001); the 29-point witness of the Paley tournament on 23 vertices (0002); the exact square value 18 by an
exhaustive search (0003, about ten minutes); the equality `C = t` for every tournament on at most six vertices, by a
rank-`t` matrix over `GF(2)` per isomorphism class with the class lists checked complete (0004, a cross-check of theorem 18 by two independent class lists); the same for 455 of
the 456 classes on seven vertices with the exception identified as `T₇` (0005); the rank-5 matrix behind `C(T₇) ≤ 5`
and its `GF(2)` factorization (0006); the witnesses `tr(T₇³) ≥ 75`, `w(T₇³) ≥ 16`, `w(T₇²) = 7` (0007); and the Paley
tournament on `GF(27)` with its 27- and 26-point anti-diagonals (0008). They are cross-checks of the paper statements,
not premises of any Lean proof.

## Not checked here

- The exactness of the square value 18, the uniqueness of `T₇` on seven vertices and `C(Q₇) = 3` are certificates,
  not Lean theorems.
- The limit form of the capacity (that the supremum is a limit) is not formalized; the definition is the supremum, which
  Alon's paper states is equal to the limit.
- The Python checkers verify finite data and explicit matrices; the Lean development does not depend on them.
