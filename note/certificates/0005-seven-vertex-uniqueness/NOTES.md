# 0005 On seven vertices, T₇ is the only tournament with C > t

**Statement.** Of the 456 isomorphism classes of tournaments on 7 vertices, 455 have
`C(T) = t(T)`, and the remaining one is isomorphic to `T₇ = Q₂₃[{0, 1, 2, 3, 9, 14, 18}]`. Since
`C(T₇) > t(T₇) = 4` (certificates 0001 and 0003; the Lean theorem
`transitiveNumber_lt_capacity_T7`), `T₇` is, up to isomorphism, the only tournament on 7 vertices
with `C(T) > t(T)`; with certificate 0004 it is the unique tournament of least order with this
property.

**Artifact.** `verify.py` (Python 3 standard library, exact integers) with two independent forms,
each with its own checker, written by separate bench lanes. `census_A.json` (checker A): 456
entries whose relabellings are pairwise disjoint and cover all `2^21` labelled tournaments on 7
vertices; `t` by the score test; for 455 entries a GF(2) matrix with unit diagonal, zeros on the
arcs and rank `≤ t`; the one remaining entry has `t = 4` and an explicit relabelling onto `T₇`
(arcs rebuilt from the Paley rule). `closure_B.json` (checker B): every class on 1 to 7 vertices,
pairwise non-isomorphic with full orbit sums, each with a transitive witness and an upper bound of
one of three kinds (degree, deletion, GF(p) rank); one 7-vertex class is `T₇`, rebuilt from the
pinned `W`, with a 17-point transitive clique of its second Sperner power (17 > 16). A cross-check
matches the 456 classes of the two lists one to one, with equal `t` and the same exception. `W`,
`t(T₇) = 4` and the class counts are pinned.

**Re-run.** `python -O verify.py` (about 40 s).

**Honesty label.** Exact and exhaustive over the `2^21` labelled tournaments. Checker A uses the
rank lemma only; checker B also uses two more bounds (below).

**External dependencies.** The rank lemma, proved in Lean in this repository
(`capacity_le_of_factorization`; see certificate 0004). For checker B only: Alon's Theorem 1.2
(European J. Combin. 19 (1998) 1–5: `C ≤ min(Δ⁺, Δ⁻) + 1`) and the deletion lemma
`C(T) ≤ C(T − v) + 1` (group a clique of the `m`-th power by the coordinates that hold `v`; within
a group those coordinates agree, so deleting them leaves a clique of a lower power of `T − v`;
summing gives `w(Tᵐ) ≤ (C(T − v) + 1)ᵐ`). That `C(T₇) > 4` comes from certificates 0001 and 0003.

**Implication.** A green run, with the rank lemma, proves that every 7-vertex tournament not
isomorphic to `T₇` has `C(T) = t(T)`; with `C(T₇) > t(T₇)` it proves the uniqueness. Not
formalized in Lean.

**Independent verification.** The two forms come from different bench lanes (different class
generators, different proofs, different matrices) and are checked by separate code; both pass
and match one to one. The count 456 agrees with the known number of 7-vertex tournaments.

**Forged controls.** Run automatically, each must fail. Form A: a matrix entry moved onto an arc;
one class dropped; the `T₇` entry marked closed with the identity matrix (rank 7, not 4). Form B:
the 17 points in reverse order; a minrank matrix row set to all ones; the `T₇` class dropped
(orbit sum 2092112); the exceptional class naming another 7-subset of `Z/23`.

**Last lines of a run.**

```
  A: the one entry not closed (356) has t = 4; isomorphic to T7: True (vertex [0, 1, 2, 3, 9, 14, 18] of T7 is vertex [6, 5, 3, 2, 4, 0, 1] of the entry)
PASS (checker A, census_A.json)
  B: n = 7: 456 classes, orbit sum 2097152 of 2097152, C = t proven for 455
  B: the one class not closed, T7_388, is T7 = Q23[W] with t = 4 and a 17-point transitive clique of its second Sperner power
PASS (checker B, closure_B.json)
PASS (cross-check): the two lists hold the same 456 classes with the same t and the same exception
PASS: 455 of the 456 tournaments on 7 vertices have C(T) = t(T); the remaining class is T7
control (A: a matrix entry moved onto an arc): FAIL as expected -- entry 100: the matrix fails
control (A: one class dropped): FAIL as expected -- not one entry per class
control (A: the T7 entry marked closed with the identity matrix): FAIL as expected -- entry 356: the matrix fails; 0 entries are not closed, exactly one expected
control (B: the 17 points in reverse order): FAIL as expected -- T7_388: the order fails at pairs [(0, 1), (0, 2), (0, 3)]; ...
control (B: a minrank matrix row set to all ones): FAIL as expected -- T7_051: matrix nonzero on arcs [(0, 6)]; ...
control (B: the T7 class dropped): FAIL as expected -- n = 7: orbit sum 2092112 != 2097152 (class list incomplete); ...
control (B: the exceeds data naming another 7-subset of Q23): FAIL as expected -- T7_388: the exceeds data must name W = [0, 1, 2, 3, 9, 14, 18] on 7 vertices; ...
VERDICT: PASS
```
