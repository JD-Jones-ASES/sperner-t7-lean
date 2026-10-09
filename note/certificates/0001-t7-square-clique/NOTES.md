# Certificate 0001 — the 18-point transitive clique of the second Sperner power of `T₇`, with the lift

**Statement.** Let `T₇ = Q₂₃[W]`, `W = {0, 1, 2, 3, 9, 14, 18}`, `x → y` iff `y − x` is a nonzero square mod 23. Then
`T₇` is a tournament, `t(T₇) = 4`, and the 18 points of `witness.json`, in the listed order, form a transitive clique
of the second Sperner power (every earlier point sends an arc to every later one in some coordinate; equivalently an
acyclic set of the strong square). Since `18 > 16 = t(T₇)²`, the lift gives `w(T₇¹¹⁸) > 4¹¹⁸` (pigeonhole at `m = 59`)
and `w(T₇⁷⁶) > 4⁷⁶` (the largest index-sum class at `m = 38`), so `C(T₇) ≥ √18 > 4 = t(T₇)`.

**Artifact.** `witness.json` (`p`, `W`, `t`, the 18 points in order, the two exponents); `verify.py` (standard library,
exact integers, no `assert`): the tournament property; `t(T₇) = 4` by two routes (an exhaustive chain search over
common out-neighbourhoods and the score-sequence test on every 5-subset); the forward property of the order and,
independently, that every strong-square arc inside the set runs forward; the two lift inequalities in exact integers.
Forged controls run automatically: the order reversed, `t` claimed one smaller, the last point dropped, a point
duplicated; each must FAIL.

    python note/certificates/0001-t7-square-clique/verify.py        # VERDICT: PASS (0.1 s)

**Label.** PROVEN-BY-CERTIFICATE. **External dependencies:** none (the lift lemma is proved in the note and in Lean).
**Implication:** a green run establishes every statement above; the capacity inequality follows by the lift lemma.
**Independent verification:** the same facts are kernel-checked in Lean (`T7_isTournament`, `transitiveNumber_T7`,
`T7_square_witness`, `T7_exists_clique_gt_four_pow`, `sqrt18_le_capacity_T7`), and the forward property was
re-derived by two further programs during the work. Certificate 0003 shows that 18 is the exact square value.

Last lines of a run:

    PASS: Q_23[[0, 1, 2, 3, 9, 14, 18]] is a tournament with t = 4 (chain search and score test); 18 distinct points form a transitive clique of the OR-square (acyclic in the strong square); 18 > 16; the pigeonhole lift holds at m = 59 (n = 118) and the middle coefficient at m = 38 (n = 76).
    control (order reversed): FAIL as expected -- no OR-arc from (18, 18) to (18, 2)
    control (t claimed one smaller): FAIL as expected -- the longest transitive chain has 4 vertices, not 3
    control (last point dropped): FAIL as expected -- pigeonhole inequality fails at m = 59
    control (a point duplicated): FAIL as expected -- repeated point in the order
    VERDICT: PASS
