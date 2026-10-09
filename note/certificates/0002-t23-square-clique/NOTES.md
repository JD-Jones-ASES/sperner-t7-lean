# Certificate 0002 — the 29-point transitive clique of the second Sperner power of the Paley tournament on 23 vertices

**Statement.** Let `Q₂₃` be the Paley tournament on `ℤ/23` (`x → y` iff `y − x` is a nonzero square). Then `Q₂₃` is a
tournament, `t(Q₂₃) = 5`, and the 29 points of `witness.json`, in the listed order, form a transitive clique of the
second Sperner power. Since `29 > 25 = t(Q₂₃)²`, the lift gives `w(Q₂₃⁹⁸) > 5⁹⁸` (pigeonhole at `m = 49`) and
`w(Q₂₃⁶⁶) > 5⁶⁶` (the largest index-sum class at `m = 33`), so `C(Q₂₃) ≥ √29 > 5 = t(Q₂₃)`.

**Artifact.** `witness.json`; `verify.py` (the same program as certificate 0001, standard library, exact integers, no
`assert`): the tournament property on all 23 residues; `t(Q₂₃) = 5` by the exhaustive chain search and by the score
test on every 6-subset (100,947 subsets); the forward property and the strong-square arcs; the lift inequalities.
Forged controls as in 0001.

    python note/certificates/0002-t23-square-clique/verify.py        # VERDICT: PASS (2.6 s)

**Label.** PROVEN-BY-CERTIFICATE. **External dependencies:** none; `t(Q₂₃) = 5` is also in print (Momihara–Suda 2017,
Table 2; Sanchez-Flores 1998). **Implication:** a green run establishes every statement above. **Independent
verification:** kernel-checked in Lean (`paley_isTournament`, `transitiveNumber_paley`, `five_lt_capacity_paley`,
`sqrt29_le_capacity_paley`); the acyclicity of the set was found by one program and re-checked by two others.

Last lines of a run:

    PASS: Q_23[[0, 1, ..., 22]] is a tournament with t = 5 (chain search and score test); 29 distinct points form a transitive clique of the OR-square (acyclic in the strong square); 29 > 25; the pigeonhole lift holds at m = 49 (n = 98) and the middle coefficient at m = 33 (n = 66).
    control (order reversed): FAIL as expected -- no OR-arc from (11, 8) to (21, 8)
    control (t claimed one smaller): FAIL as expected -- the longest transitive chain has 5 vertices, not 4
    control (last point dropped): FAIL as expected -- pigeonhole inequality fails at m = 49
    control (a point duplicated): FAIL as expected -- repeated point in the order
    VERDICT: PASS
