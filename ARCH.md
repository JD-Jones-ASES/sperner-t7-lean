# Architecture and lane protocol (working document; not part of the published repository)

## What this repository proves

Alon, *On the capacity of digraphs* (European J. Combin. 19 (1998) 1–5): for a digraph `R` on `V`,
`w(Rⁿ)` is the largest `S ⊆ Vⁿ` such that every ordered pair of distinct members has a coordinate `i`
with `R (u i) (v i)`; `C(R) = lim w(Rⁿ)^{1/n} = sup_n w(Rⁿ)^{1/n}` (we define `capacity` as the sup
over `n ≥ 1`). For a tournament `t(T)` = the order of its largest transitive subtournament; `t ≤ C`.
Conjecture 1.1 there (Körner–Simonyi, citing Körner, Graphs Combin. 14 (1998) 25–36): `C(T) = t(T)`
for every tournament. Alon disproves it (random tournaments; `Q₆₇` explicitly) and asks for the
smallest tournament for which it fails.

`T₇ = Q₂₃[{0, 1, 2, 3, 9, 14, 18}]`: `t(T₇) = 4`, an 18-point transitive clique of the second Sperner
power, so `√18 ≤ C(T₇)`; a rank-5 factorization over `ZMod 2` gives `C(T₇) ≤ 5`. On paper (the note,
with standard-library certificates): the square value 18 is exact; every tournament on ≤ 6 vertices has
`C = t` (rank-`t` matrices over `GF(2)` for all 1 + 1 + 2 + 4 + 12 + 56 classes); on 7 vertices `T₇` is the
only class with `C > t` (455 rank-`t` matrices); so **7 is the least order of a counterexample and `T₇`
is the unique one up to isomorphism**; `T₇` is self-converse with trivial automorphism group; every
proper subtournament of `T₇` has `C = t`.

Compared theorems (all in `Challenge.lean`; proved in `Solution.lean` through `_internal` theorems):

| # | Theorem | Content | Module |
| --- | --- | --- | --- |
| 1 | `T7_isTournament` | `T₇` is a tournament | T7 |
| 2 | `transitiveNumber_T7` | `t(T₇) = 4` | T7 |
| 3 | `T7_square_witness` | 18 forward-ordered injective points of `T₇²` | T7 |
| 4 | `T7_exists_clique_gt_four_pow` | some power has a clique `> 4ⁿ` | T7 (via Lift) |
| 5 | `four_lt_capacity_T7` | `4 < C(T₇)` | T7 (via Clique) |
| 6 | `sqrt18_le_capacity_T7` | `√18 ≤ C(T₇)` | T7 (via Clique) |
| 7 | `capacity_T7_le_five` | `C(T₇) ≤ 5` | T7 (via Rank) |
| 8 | `transitiveNumber_lt_capacity_T7` | `t(T₇) < C(T₇)` | T7 |
| 9 | `lift_lemma` | the general lift (ℕ form, no instances) | Lift |
| 10 | `rpow_le_capacity` | `N^{1/k} ≤ C(R)` | Clique |
| 11 | `transitiveNumber_le_capacity` | `t(R) ≤ C(R)` | Clique |
| 12 | `capacity_le_of_factorization` | the rank bound `C(R) ≤ r` | Rank |
| 13 | `capacity_le_card` | `C(R) ≤ |V|` | Clique |
| 14 | `paley_isTournament` | `Q₂₃` is a tournament | T23 |
| 15 | `transitiveNumber_paley` | `t(Q₂₃) = 5` | T23 |
| 16 | `five_lt_capacity_paley` | `5 < C(Q₂₃)` | T23 |
| 17 | `sqrt29_le_capacity_paley` | `√29 ≤ C(Q₂₃)` | T23 |

| 18 | `capacity_eq_transitiveNumber_of_card_le_six` | every tournament on ≤ 6 vertices has `C = t` | Six (with SixCover) |
| 19 | `seven_le_card_of_transitiveNumber_lt_capacity` | a tournament with `t < C` has ≥ 7 vertices | Six |

The stretch module `Six` closed in 33 minutes of lane time: a Mathlib-free leaf `SixCover.lean` holds the 77
representatives with their `GF(2)` factorizations and chains, and the kernel checks the data and the coverage bitset
(`2^(2^15) - 1` at `n = 6`, 60 s); theorems 18 and 19 were then added to the Challenge.

## Module map and owners

| Module | Lane | Imports | Contents |
| --- | --- | --- | --- |
| `Defs` | desk (done) | the Challenge's six Mathlib imports, identical | the nine definitions + two `Decidable` instances |
| `Lift` | **lift** | Defs, Equiv.Fin, BigOperators, Tactic | `liftWord`, `liftWord_injective`, `clique_of_equal_sums`, `lift_lemma_internal`, `lift_corollary` |
| `Clique` | **clique** | Lift, SpecificLimits.Normed | clique sizes, `spernerCliqueNumber_*`, `capacity_*`, `root_pow`, `lt_capacity_of_clique`, `capacity_le_of_forall`, the transitive number lemmas, `exists_pow_mul_lt`, `rpow_le_capacity_internal`, `transitive_le_capacity`, `transitiveNumber_le_capacity_internal`, `lt_capacity_of_forward` |
| `Rank` | **rank** | Clique, Matrix.Rank, Kronecker | `card_le_pow_of_factorization`, `spernerCliqueNumber_le_pow_of_factorization`, `capacity_le_of_factorization_internal` |
| `T7` | **t7** | Rank | the `T₇` facts, the 18 points, the factorization `T7A`, `T7B` |
| `T23` | **t23** | Clique | the `Q₂₃` facts, the 29 points |
| `Six`, `SixCover` | **six** (done) | Rank; the leaf imports nothing | the ≤ 6 closure by a kernel bitset; the seven-vertex corollary |
| `Main` | desk | all | glue; `Solution.lean` restates the Challenge |

Reference material, compiled at this pin on 2026-10-08 (read them; port freely): `.scratch/FullProbe.lean`
(the lift lemma, the clique/capacity lemmas, `T₇` with the 17-point set, the pruned chain search),
`.scratch/Lift.lean`, `.scratch/Capacity.lean`, `.scratch/T7Probe.lean`, `.scratch/T23Probe.lean` (the
`Q₂₃` facts with the 29 points; its namespace is `T23`). The pinned skeletons differ from the probes in
small ways (names, `Function.Injective` in the chain statements, no `[DecidableEq V]` in
`lift_lemma_internal`, the transitive number through `sSup`); the probe proofs adapt in minutes.

## The mathematics, module by module

**Lift.** `liftWord pts m w` concatenates the points `pts (w j)`; injective since `pts` is. Two distinct
words of equal index sum have `j` with `w j < w' j` (else `w' ≤ w` pointwise with equal sums forces
equality, `Finset.sum_eq_sum_iff_of_le`), and the forward property at block `j` gives the arc. The
largest fiber of the index sum (`Finset.exists_max_image` over `Finset.range ((N-1)m+1)`) has at least
`Nᵐ / ((N-1)m+1)` words (`Finset.card_eq_sum_card_fiberwise` with a `Set.MapsTo` hypothesis at this pin,
`Finset.sum_le_card_nsmul`). Without `[DecidableEq V]`: open `classical` inside the proof.

**Clique.** Clique sizes are bounded by `|V|ⁿ` (`Finset.card_le_univ`, `Fintype.card_fun`), nonempty
(`∅`), attained (`Nat.sSup_mem`). `capacity` is bounded by `|V|` (`Real.rpow_le_rpow`, then
`root_pow`: `(x^n)^(1/n) = x` from `Real.pow_rpow_inv_natCast` with `one_div`). `le_capacity` is
`le_ciSup`. `capacity_le_of_forall` is `ciSup_le`. The transitive number: bounded by `|V|`
(`Fintype.card_le_of_injective`), attained; `transitiveNumber_le` from the absence of a `(k+1)`-chain —
a longer chain restricts along `Fin.castLE`. `rpow_le_capacity_internal`: for every `r < N^{1/k}` with
`r ≥ 0`, `rᵏ < N`, `exists_pow_mul_lt` (from `tendsto_pow_const_mul_const_pow_of_abs_lt_one`) gives `m`
with `(rᵏ)ᵐ((N-1)m+1) < Nᵐ`, the lift gives a clique larger than `(rᵏ)ᵐ`, so `r < C`; conclude with
`le_of_forall_lt`. `transitiveNumber_le_capacity_internal`: the attained chain of length `t` is a
forward-ordered `t`-set of the first power.

**Rank.** See the module docstring. Suggested route: define `Mn u v := ∏ i, M (u i) (v i)` where
`M u v := ∑ i, A u i * B i v`; prove `Mn = An * Bn` as matrices (`Matrix.of`, `Matrix.mul_apply`,
`Finset.prod_univ_sum`); for a clique `S` the matrix `D := Mn.submatrix (Subtype.val : S → _) Subtype.val`
is `Matrix.diagonal d` with `d ≠ 0` (prove entrywise: off-diagonal zero by the clique property and
`Finset.prod_eq_zero`), so `D.rank = S.card` (`Matrix.rank_diagonal` or invertibility); and
`D = An.submatrix … * Bn.submatrix …`, so `D.rank ≤ (Bn.submatrix …).rank ≤ Fintype.card (Fin n → Fin r) = rⁿ`
(`Matrix.rank_mul_le_right`, `Matrix.rank_le_card_height`/`width`). Alternatively avoid `Matrix.rank`:
`D.mulVec` is injective (diagonal with nonzero entries), hence `(Bn.submatrix …).mulVec` is injective on
`S → F`, and `LinearMap.finrank_le_finrank_of_injective` gives `S.card ≤ rⁿ`. Then
`capacity_le_of_forall` with `root_pow` and `Real.rpow_le_rpow`.

**T7 / T23.** The module docstrings give every number. Never use plain `decide` over `Fin 5 → Fin 7`
or `Fin 6 → ZMod 23` (memory); use the pruned nested searches of the probes. `decide +kernel` for the
forward properties and the big inequality `(4 ^ 2) ^ 59 * (17 * 59 + 1) < 18 ^ 59`.

**Six.** The module docstring. A stretch; the kill criterion is binding.

## Rules (binding for every lane)

1. **Pinned statements.** Every statement in a skeleton file keeps its exact name, binders and
   conclusion. Add helper lemmas and definitions freely in your own file(s). If a pinned statement is
   wrong or unprovable as stated, do not edit it: prove the nearest correct version under a new name,
   leave the pinned one with its `sorry`, and say so in your report.
2. **Other lanes' files are black boxes.** Use their sorried statements as stated; never edit them,
   never prove them yourself. If you need a variant, prove an `aux_…` copy in your file and report it.
3. **Build only through** `bash scripts/lane-build.sh SpernerCapacity.<Module>` from your worktree
   root, one module per call (two machine-wide slots; waits for 2.5 GB free). Never `lake build` with no
   target, never `lake update`, never `lake exe cache get`. Scratch files go in `.scratch/` of your
   worktree (`lake env lean .scratch/<file>.lean` for small files importing at most your module's
   imports). Nothing detached, no background jobs. Never run the core-notation audit (it takes 4 GB).
4. **Kernel-only.** No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `partial`,
   `implemented_by`, `extern`, `ofReduceBool`, `debug.skipKernelTC`, `debug.byAsSorry` in the
   deliverable. If you raise `maxHeartbeats`, do it per declaration and report it. Keep the `module`
   header, `public import`s, `@[expose] public section … end`.
5. **Imports.** Targeted Mathlib imports only; never `import Mathlib`. `Defs.lean`'s imports are frozen
   (they must equal the Challenge's; the comparator compares elaborated terms).
6. **Lean 4.35.0-rc2 gotchas** (from the probes): `Finset.card_eq_sum_card_fiberwise` takes a
   `Set.MapsTo` hypothesis; `Real.pow_rpow_inv_natCast` uses `n⁻¹` (rewrite with `one_div`);
   `pow_lt_pow_left₀ (hab) (ha) (hn : n ≠ 0)`; `lt_of_mul_lt_mul_left (h) (a0 : 0 ≤ a)`;
   `le_of_forall_lt`; `Nat.sSup_mem (nonempty) (bdd)`; `Real.sqrt_eq_rpow`;
   `tendsto_pow_const_mul_const_pow_of_abs_lt_one`; `push Not` works; the `unusedSectionVars` linter
   fires on theorems in a `[Fintype V]` section that do not use the instance (`omit [Fintype V] in`).
   `le_or_lt` is `le_or_gt`. A section `variable` hypothesis is dropped from a theorem whose statement
   does not mention it (`include`).
7. **No names** of people or AI systems in the Lean; no "record" language anywhere.
8. **Done means:** your module builds through `lane-build.sh` with zero `sorry` warnings in your
   file(s) (other lanes' sorries show as warnings on replayed modules, which is fine); `git add` your
   files and `git commit -m "<one line>"` on your branch (never push, never checkout `main`); return the
   structured report (every pinned statement closed or open with the reason, helpers, `aux_`
   duplicates, heartbeats, the commit hash, the tail of the last build, anything the desk must know).

## Results on paper (for the note; every number has a certificate at the bench)

- `tr(T₇²) = 18` exactly (three engines; a standard-library exhaustive checker, 625 s); 84 optimal
  18-sets; cert 0039's 17-set is inclusion-maximal but not maximum. `w(T₇²) = 7` (the graph of the
  unique anti-automorphism `0↔3, 1↔18, 9↔14, 2` fixed); `Aut(T₇)` trivial; `T₇` self-converse.
- `√18 ≤ C(T₇) ≤ 5`; the degree bound gives 6; `tr(T₇³) ∈ [75, 125]`; `w(T₇³) ∈ [16, 19]`;
  no symmetric clique beats `4ⁿ` for `n ≤ 5`; the lift gives `n = 76` (largest index-sum class,
  `m = 38`) and `n = 118` (pigeonhole, `m = 59`).
- Every tournament on ≤ 6 vertices: `C = t` (rank-`t` `GF(2)` matrices; GF(2) minrank = `t` for every
  class). On 7 vertices: 455 classes closed, `T₇` the only exception; `C(Q₇) = 3`.
- Alon's ≤ 5 claim (with Szabó and Tardos) is a reported computation, no proof printed; KOV 2009
  (Adv. Math. Commun. 3(2) 125–133) settles every digraph on ≤ 5 vertices except eight non-tournaments.
- The 26- and 27-vertex examples implicit in print (Alon's anti-diagonal over `GF(27)`, `t = 5` by
  Sanchez-Flores 1998) are re-verified; the smallest previously exhibited example has 67 vertices.
