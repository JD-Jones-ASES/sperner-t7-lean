# 0008 The Paley tournament on GF(27): 27- and 26-vertex examples

**Statement.** Let `Q₂₇` be the Paley tournament on `GF(27) = F₃[x]/(x³ − x − 1)` (`a → b` iff
`b − a` is a nonzero square). Then `t(Q₂₇) = 5`, and the anti-diagonal `{(a, −a)}` is a symmetric
clique of 27 points of its second Sperner power: every ordered pair of distinct points has a
coordinate carrying an arc forward (`b − a` and `−(b − a)` are nonzero, and exactly one is a
square). So `w(Q₂₇²) ≥ 27 > 25 = t²` and `C(Q₂₇) ≥ √27 > 5 = t(Q₂₇)`. Without the point
`(0, 0)`, the 26 remaining points lie in the second power of the subtournament on the 26 nonzero
elements, which also has `t = 5`, so `C ≥ √26 > 5` on 26 vertices.

**Artifact.** `verify.py` (Python 3 standard library; no data file). Checks: the cubic has no
root in `F₃`, so it is irreducible; the implemented product is commutative, associative and
distributive on all `27³` triples, and every nonzero element is invertible; 13 nonzero squares,
`−1` a non-square, a tournament; `t = 5` by source peeling on bitmasks and by the no-3-cycle test
on all 5- and 6-subsets, and `t = 5` for the 26-vertex subtournament by source peeling; for each
anti-diagonal, distinct points, no strong-square arc inside, and every ordered pair with a
forward coordinate. The modulus, `t = 5` and the sizes 27 and 26 are pinned.

**Re-run.** `python -O verify.py` (about 10 s).

**Honesty label.** Exact.

**External dependencies.** None beyond the Python standard library. The construction is the one
Alon (European J. Combin. 19 (1998) 1–5, §4) gives for `Q_p` with `p ≡ 3 mod 4`, applied to the
field of 27 elements; `t(Q₂₇) = 5` is in print (Sanchez-Flores 1998) and recomputed here.

**Implication.** A green run proves `C(Q₂₇) > t(Q₂₇)`, and the same on 26 vertices. These
examples are implicit in print, but we found no place where they are stated. The smallest
example exhibited in print is Alon's `Q₆₇` (67 vertices); `T₇` has 7.

**Independent verification.** `t = 5` is computed by two unrelated routes (source peeling and
the no-3-cycle test). This is a port of a bench check from the same lane; the port repairs that
check's irreducibility test (which could not fail) and checks the field axioms on all triples
instead of a sample. No second implementation of the anti-diagonal check exists.

**Forged controls.** Run automatically, each must fail: the reducible modulus `x³ − x`; `t`
claimed to be 4; the diagonal `{(a, a)}` in place of the anti-diagonal; the point `(1, −1)` moved
to `(1, 0)`.

**Last lines of a run.**

```
3. t = 5 by source peeling (27 vertices; also the 26 nonzero elements) and by the no-3-cycle test (a transitive 5-set exists; none of the 6-subsets is transitive)
4. the 27-point anti-diagonal: no strong-square arc; every ordered pair has a forward coordinate; 27 > 25
4. the 26-point anti-diagonal: no strong-square arc; every ordered pair has a forward coordinate; 26 > 25
PASS: w(Q27^2) >= 27 > 25 = t(Q27)^2, so C(Q27) >= sqrt(27) > 5; on 26 vertices C >= sqrt(26) > 5 = t
control (the reducible modulus x^3 - x): FAIL as expected -- the modulus x^3 - (0 + 1 x) has a root in F_3, so it is reducible
control (t claimed to be 4): FAIL as expected -- source peeling gives t = 5 (27 vertices) and 5 (26 vertices); claimed 4
control (the diagonal in place of the anti-diagonal): FAIL as expected -- the 27-point set carries an arc of the strong square
control (the point (1, -1) moved to (1, 0)): FAIL as expected -- the 27-point set carries an arc of the strong square
VERDICT: PASS
```
