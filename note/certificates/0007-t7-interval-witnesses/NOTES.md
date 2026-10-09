# 0007 Witnesses for the small powers of T₇

**Statement.** For `T₇ = Q₂₃[{0, 1, 2, 3, 9, 14, 18}]`: a transitive clique of 18 points in the
second Sperner power (a second 18-set, found independently of certificate 0003's) and one of 75
words in the third, so `tr(T₇²) ≥ 18` and `tr(T₇³) ≥ 75`; a symmetric clique of 16 words in the
third power, so `w(T₇³) ≥ 16`; and `w(T₇²) = 7`, attained only by the graph of the
anti-automorphism `0 ↔ 3, 1 ↔ 18, 9 ↔ 14`, 2 fixed. Exact comparisons: `75² = 5625 < 5832 = 18³`,
so the cube does not improve `√18`; `16 < 4³` and `7 < 4²`, so no symmetric clique exceeds `4ⁿ`
at `n = 2, 3`; and the largest coefficient of `(1 + … + x¹⁷)³⁸` exceeds `16³⁸`, so the 18 points
lift to a symmetric clique of more than `4⁷⁶` words in `T₇⁷⁶`.

**Artifact.** `verify.py` (Python 3 standard library, exact integers) with `witnesses.json`.
Checks: `t(T₇) = 4`; each transitive clique by forward OR-domination in the listed order and,
independently, by the absence of backward strong-power arcs and by Kahn's algorithm; each
symmetric clique both ways for every ordered pair; `w(T₇²) ≤ 7` by checking that no two distinct
points of `W × W` sharing a coordinate carry OR-arcs in both directions (so a symmetric clique of
the square has distinct first coordinates), and that exactly one of the 5040 bijections of `W`
has a graph that is a symmetric clique, the listed 7-set; the comparisons and the lift exponent
38. The sizes 18, 75, 7, 16 and `W`, `t` are pinned.

**Re-run.** `python -O verify.py` (under 1 s).

**Honesty label.** Exact. Lower bounds by explicit witnesses, except `w(T₇²) = 7`, which is
exact: the injection argument on paper, with its one finite step checked by the code.

**External dependencies.** None beyond the Python standard library.

**Implication.** A green run proves the four statements above. The intervals they leave open are
not claimed: `tr(T₇³) ∈ [75, 125]` (125 by the rank bound of certificate 0006), `w(T₇³)` is at
least 16 (two SAT engines found no 20-word clique; not certified here), and the least `n` with
`w(T₇ⁿ) > 4ⁿ` lies in `[3, 76]` on the certified facts (the bench lanes narrow it to `[6, 76]`
using the uncertified bound `w(T₇³) ≤ 19`).

**Independent verification.** The witnesses were found by solvers (CP-SAT, CaDiCaL through
PySAT, simulated annealing); the bench checker of the same lane and this checker pass them. The
square value 18 is exact by certificate 0003.

**Forged controls.** Run automatically, each must fail: the first two words of the square clique
swapped; the word (0, 0, 0) added to the cube's symmetric clique; the square clique cut to 16
words; vertex 18 replaced by 19.

**Last lines of a run.**

```
2. transitive clique of T7^2: 18 words; OR-forward True; no backward strong arc True; Kahn acyclic True
2. transitive clique of T7^3: 75 words; OR-forward True; no backward strong arc True; Kahn acyclic True
3. symmetric clique of T7^2: 7 words; every ordered pair has a forward coordinate True
3. symmetric clique of T7^3: 16 words; every ordered pair has a forward coordinate True
4. w(T7^2) <= 7: pairs of distinct points sharing a coordinate with OR-arcs both ways: 0; bijections of W whose graph is a symmetric clique: 1; it is the listed 7-set: True
5. 18 > 16; 75^2 = 5625 < 5832 = 18^3 (the cube does not improve sqrt(18)); 16 < 64 and 7 < 16; the largest coefficient of (1+...+x^17)^38 exceeds 16^38 (more than 4^76 words in T7^76)
PASS: tr(T7^2) >= 18, tr(T7^3) >= 75, w(T7^3) >= 16, w(T7^2) = 7; C(T7) >= sqrt(18)
control (the first two words of the square clique swapped): FAIL as expected -- the transitive clique of power 2 fails
control (the word (0, 0, 0) added to the cube's symmetric clique): FAIL as expected -- the symmetric clique of power 3 fails; ...
control (the square clique cut to 16 words): FAIL as expected -- the transitive clique of power 2 has 16 words, the statement says 18; ...
control (vertex 18 replaced by 19): FAIL as expected -- the file's (p, W) are not the statement's (23, [0, 1, 2, 3, 9, 14, 18])
VERDICT: PASS
```
