# 0003 The square of T₇: the largest transitive clique has exactly 18 points

**Statement.** Let `T₇ = Q₂₃[W]`, `W = {0, 1, 2, 3, 9, 14, 18}`, with `x → y` iff `y − x` is a
nonzero square mod 23. The largest transitive clique of the second Sperner power of `T₇` (a list
of points of `W × W` in which every earlier point sends an arc to every later one in some
coordinate) has exactly 18 points: `tr(T₇²) = 18`. Because `T₇` is a tournament, these lists are
the acyclic sets of the strong square `T₇ ⊠ T₇` in topological order, so equivalently
`a(T₇ ⊠ T₇) = 18`. The 18 points of `witness.json` attain it (they are the points of certificate
0001 and of the Lean theorem `T7_square_witness`); no 19 points do. The lift then gives a clique of
the 118-th Sperner power with more than `4¹¹⁸` words (pigeonhole, `m = 59`) and one of the 76-th
power with more than `4⁷⁶` words (largest index-sum class, `m = 38`).

**Artifact.** `verify.py` (Python 3 standard library, exact integers) with `witness.json`. Steps:
(1) `T₇` is a tournament and `t(T₇) = 4`, by the score test on all 128 subsets and by a chain
search; (2) the lower bound: the 18 points are distinct, in order every earlier point
OR-dominates every later one, and Kahn's algorithm on the strong-square arcs empties the set;
(3) the upper bound by an exhaustive Russian-doll search of its own over the 49 vertices of the
strong square, with two valid prunings (heredity, and at most `t = 4` points in any row or column
of `W × W`, since such a line induces a copy of `T₇`); (4) the two lift exponents. `W`, `t = 4`,
the value 18 and the exponents 59 and 38 are pinned in the code.

**Re-run.** `python -O verify.py` (about 9 to 11 minutes; 533 s here, with another check running).
`python -O verify.py --lower` (under 1 s: steps 1, 2 and 4 only; it prints that the upper bound
was not checked). `python -O verify.py witness_FORGED_17max.json` (must end `VERDICT: FAIL`; 201 s).

**Honesty label.** Exact: an exhaustive search with valid prunings, 26,355,933 nodes. The value
18 is a fact about the square only.

**External dependencies.** None beyond the Python standard library. The step from the 18 points
to `√18 ≤ C(T₇)` is the lift lemma, proved in Lean (`lift_lemma`, `rpow_le_capacity`,
`sqrt18_le_capacity_T7`).

**Implication.** A green full run proves `tr(T₇²) = 18`; with the lift lemma it gives
`√18 ≤ C(T₇)`. It does not determine `C(T₇)`, which lies in `[√18, 5]` (certificate 0006), and
it says nothing about higher powers (certificate 0007). The 17-point set of the earlier bench
certificate is inclusion-maximal but not maximum.

**Independent verification.** During development three engines agreed on 18: a CP-SAT model
(OR-Tools, OPTIMAL 18, bound 18), a separate pure-Python Russian doll, and CaDiCaL through PySAT
with lazy cycle cuts ("at least 19" unsatisfiable); a census of all 456 seven-vertex classes with
two further engines (lazy-cut MaxSAT, then a SAT refutation of 19) found the same value. Two
enumerations found exactly 84 optimal 18-sets (not replayed here). The Lean kernel checks the
18 points (`T7_square_witness`).

**Forged controls.** Run automatically, each fails before the search: the first two points
swapped (no OR-arc forward); `t` claimed to be 3; vertex 18 replaced by 19; the value claimed to
be 19. The file `witness_FORGED_17max.json` claims that the 17-point bench set is a maximum; the
search refutes it at vertex 3.

**Last lines of a run.**

```
3. UPPER BOUND: Russian doll over 49 vertices, 26355933 nodes; g = [18, 18, 18, 18, 17, ...]; no acyclic set of size 19
PASS: tr(T7^2) = a(T7 [x] T7) = 18 exactly; sqrt(18) <= C(T7)
control (two points swapped): FAIL as expected -- no OR-arc from (1, 0) to (0, 0) (positions 0 < 1)
control (t claimed to be 3): FAIL as expected -- t(T7) is 4 (score test) and 4 (chain search); the file says 3
control (vertex 18 replaced by 19): FAIL as expected -- the file's constants (p, W) = (23, [0, 1, 2, 3, 9, 14, 19]) are not the statement's (23, [0, 1, 2, 3, 9, 14, 18])
control (value claimed to be 19): FAIL as expected -- the witness has 18 points, the claimed value is 19
VERDICT: PASS
```

The forged 17-point file:

```
FAIL: an acyclic set of size 18 exists inside vertices 3..48: the claimed maximum 17 is wrong
...
VERDICT: FAIL
```
