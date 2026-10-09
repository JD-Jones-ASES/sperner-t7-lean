# 0006 C(T₇) ≤ 5 by a rank-5 matrix

**Statement.** Let `T₇ = Q₂₃[W]`, `W = (0, 1, 2, 3, 9, 14, 18)`. The integer matrix `M` of
`rank_certificate.json` (rows and columns in the `W` order) has nonzero diagonal, `M[a][b] = 0` at
every arc `a → b`, and rank 5 over `Q`. Over GF(2) it is the product `A·B` of the 7 × 5 matrix
`A` (rows 10000, 01000, 00100, 00010, 01110, 00001, 01100) and the 5 × 7 matrix `B` (rows
1000000, 0100001, 0110100, 0011001, 0000010), which are the factors `T7A`, `T7B` of the Lean
proof of `capacity_T7_le_five`. By the rank lemma, `w(T₇ⁿ) ≤ tr(T₇ⁿ) ≤ 5ⁿ` for every `n`, so
`C(T₇) ≤ 5`. This improves the bound `min(Δ⁺, Δ⁻) + 1 = 6` of Alon's Theorem 1.2.

**Artifact.** `verify.py` (Python 3 standard library, exact integers and fractions) with
`rank_certificate.json`. Checks: the 21 arcs from the Paley rule; the pattern of `M`; rank 5 over
`Q` by elimination and by minors (all 49 6 × 6 minors vanish, some 5 × 5 minor does not); `A·B`
mod 2 has 1 on the diagonal, 0 on every arc, and equals `M` mod 2; and, as a demonstration of the
lemma, the 18 × 18 block of `M ⊗ M` on the 18-point transitive clique of certificate 0003 is
triangular with diagonal ±1 over `Q` and 1 over GF(2). `W`, the rank 5 and the Lean factors are
pinned.

**Re-run.** `python -O verify.py` (under 1 s).

**Honesty label.** Exact.

**External dependencies.** The rank lemma (proved in Lean here as `capacity_le_of_factorization`;
the rank method of Haemers, as used by Alon 1998, §2). Over `Q` the factorization through `Q⁵`
comes from rank 5; over GF(2) it is the explicit `A·B`.

**Implication.** A green run, with the rank lemma, proves `C(T₇) ≤ 5`. The Lean theorem
`capacity_T7_le_five` proves the same bound in the kernel from `T7A` and `T7B`; this certificate
ties those factors to the integer matrix found at the bench. Since `tr(T₇²) ≥ 18 > 16`, no
admissible matrix of rank 4 exists over any field, so this method cannot go below 5.

**Independent verification.** Two bench searches found GF(2) minimum rank 5 independently (an
exhaustive row-by-row search with span pruning, also over GF(3), and an enumeration of all `2^21`
admissible 0/1 matrices); the Lean kernel checks the GF(2) factorization (`T7AB_diag`,
`T7AB_arc`).

**Forged controls.** Run automatically, each must fail: an entry on the arc 0 → 1; the last
diagonal entry changed to 2 (rank 6 over `Q`, and 0 mod 2); the rank claimed to be 4; one bit of
`A` flipped (row 01110 to 01111); vertex 18 replaced by 19.

**Last lines of a run.**

```
3. rank over Q: elimination 5; nonzero 6 x 6 minors: 0; a nonzero 5 x 5 minor exists: True
4. Lean factors over GF(2): A B mod 2 has diagonal 1: True; zeros on all 21 arcs: True; equals M mod 2: True
5. the 18-point transitive clique of the OR-square gives a triangular block of M (x) M with diagonal +-1 (and 1 through A B mod 2); 18 <= 25
PASS: a rank-5 matrix with nonzero diagonal and zeros on the arcs (over Q, and over GF(2) through the Lean factors): w(T7^n) <= tr(T7^n) <= 5^n for every n, so C(T7) <= 5
control (an entry on the arc 0 -> 1): FAIL as expected -- nonzero entry at the arc 0 -> 1; ...
control (the last diagonal entry set to 2): FAIL as expected -- rank over Q by elimination is 6, claimed 5; 12 nonzero (r+1)-minors
control (the rank claimed to be 4): FAIL as expected -- rank over Q by elimination is 5, claimed 4; 64 nonzero (r+1)-minors
control (one bit of A flipped): FAIL as expected -- A or B differs from the Lean factors T7A, T7B; ...
control (vertex 18 replaced by 19): FAIL as expected -- the file's (p, W) are not the statement's (23, [0, 1, 2, 3, 9, 14, 18])
VERDICT: PASS
```
