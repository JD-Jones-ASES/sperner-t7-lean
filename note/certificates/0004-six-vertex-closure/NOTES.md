# 0004 Every tournament on at most six vertices has C = t

**Statement.** For every tournament `T` on at most 6 vertices, `C(T) = t(T)`. Each of the
1, 1, 2, 4, 12 and 56 isomorphism classes on 1 to 6 vertices has a 0/1 matrix over GF(2) with
nonzero diagonal, zeros at every arc `u → v`, and rank `t(T)`. By the rank lemma this gives
`C(T) ≤ t(T)`, and `t(T) ≤ C(T)` always. With `T₇` (certificate 0001), the least number of
vertices of a tournament with `C(T) > t(T)` is exactly 7.

**Artifact.** `verify.py` (Python 3 standard library, exact integers) with two independent forms
of the certificate, each with its own checker, written by separate bench lanes:
`classes_A.json` (checker A: the list is shown to hold exactly one tournament per class because
the relabellings of the listed tournaments are pairwise disjoint and cover all `2^(n choose 2)`
labelled tournaments; `t` by the score test and by an ordering search; rank `≤ t` by elimination
mod 2 and by all `(t+1) × (t+1)` minors vanishing mod 2) and `classes_B.json` (checker B:
pairwise non-isomorphic by a minimal arc code, orbit sums `Σ n!/|Aut| = 2^(n choose 2)`, a
transitive witness in order, `t` by exhaustive search, rank exactly `t` by elimination mod 2).
A cross-check matches the two lists class by class. The class counts and `p = 2` are pinned.

**Re-run.** `python -O verify.py` (about 1.5 s).

**Honesty label.** Exact and exhaustive over the labelled tournaments; the theorem rests on the
rank lemma below.

**External dependencies.** The rank lemma: if `M = A·B` over a field factors through `Fʳ`, with
nonzero diagonal and zeros on the arcs, then `C(T) ≤ r`. It is proved in this repository in Lean
(`capacity_le_of_factorization`); a rank-`t` matrix factors through `Fᵗ`. It is the rank method
of Haemers, used by Alon (1998, §2, through Blokhuis) and stated for Sperner capacity in
Kiviluoto–Östergård–Vaskelainen, Advances in Mathematics of Communications 3 (2009), no. 2,
125–133. No other result is used.

**Implication.** A green run, with the rank lemma, proves `C(T) = t(T)` for every tournament on
at most 6 vertices. The 6-vertex case is not formalized in Lean.

**Independent verification.** The two forms were built by different bench lanes with different
class generators and different matrices, and are checked by separate code in `verify.py`; both
pass and agree class by class. The 5-vertex case was reported by Alon with Szabó and Tardos (no
proof printed), and Kiviluoto–Östergård–Vaskelainen (2009) determine the capacity of every
digraph on at most 5 vertices except eight, none of which is a tournament.

**Forged controls.** Run automatically, each must fail. Form A: a matrix entry moved onto an arc;
one 6-vertex class dropped; `t` claimed one smaller; a class listed twice. Form B: a matrix entry
moved onto an arc; one 6-vertex class dropped (orbit sum 32048); a non-transitive witness for
`T6_55`; the matrix of `T6_55` replaced by the identity (rank 6, not 3).

**Last lines of a run.**

```
PASS (checker A, classes_A.json)
PASS (checker B, classes_B.json)
PASS (cross-check): both lists hold the same 76 classes with the same t
PASS: every tournament on at most 6 vertices has a GF(2) matrix of rank t(T) with nonzero diagonal and zeros on the arcs, so C(T) = t(T)
control (A: a matrix entry moved onto an arc): FAIL as expected -- k=6 entry 10: nonzero at arc 0->1
control (A: one 6-vertex class dropped): FAIL as expected -- n=6: the list is not one tournament per class; 75 entries, 76 expected
control (A: t claimed one smaller): FAIL as expected -- k=6 entry 21 has a transitive 4-set; k=6 entry 21: rank 4 > t = 3
control (A: a class listed twice): FAIL as expected -- k=6 entries 0 and 1 are isomorphic; n=6: the list is not one tournament per class
control (B: a matrix entry moved onto an arc): FAIL as expected -- T6_25: matrix nonzero on arcs [(0, 1)]; ...
control (B: one 6-vertex class dropped): FAIL as expected -- n = 6: orbit sum 32048 != 32768 (class list incomplete); ...
control (B: a non-transitive witness for T6_55): FAIL as expected -- T6_55: the witness is not transitive in the listed order; ...
control (B: the matrix of T6_55 replaced by the identity): FAIL as expected -- T6_55: rank 6 over GF(2), t = 3; ...
VERDICT: PASS
```
