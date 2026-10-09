module

public import SpernerCapacity.Rank

/-!
# `T₇`

`T₇` is the subtournament of the Paley tournament on `ZMod 23` induced on `0, 1, 2, 3, 9, 14, 18`
(vertex `i : Fin 7` is the residue `W i`). Its 21 arcs, as pairs of indices into `W`
(residues in brackets): 0→1 [0→1], 0→2 [0→2], 0→3 [0→3], 0→4 [0→9], 0→6 [0→18], 1→2, 1→3, 1→4 [1→9],
1→5 [1→14], 2→3, 2→5 [2→14], 2→6 [2→18], 3→4 [3→9], 4→2 [9→2], 4→6 [9→18], 5→0 [14→0], 5→3 [14→3],
5→4 [14→9], 5→6 [14→18], 6→1 [18→1], 6→3 [18→3]. Out-degrees 5, 4, 3, 1, 2, 4, 2.

* A tournament: `decide` over the 49 pairs (each `paley` test searches the 23 square roots).
* `t(T₇) = 4`: the chain `0, 1, 2, 3` (indices) is transitive; there is no transitive 5-chain —
  use the pruned nested search `d1 … d5` (each next vertex ranges over the common out-neighbourhood
  of the previous ones), as in `.scratch/FullProbe.lean`; a plain `decide` over `Fin 5 → Fin 7`
  through the pi `Fintype` instance exhausts memory and must not be used. Then
  `transitiveNumber_T7` by `le_antisymm` from `transitiveNumber_le` (a chain of length `k ≥ 5`
  restricts, through `Fin.castLE`, to a transitive injective 5-chain) and `le_transitiveNumber`.
* The 18 points (indices into `W`), in order:
  (0,0) (1,0) (5,1) (0,1) (0,4) (1,4) (5,2) (0,2) (4,5) (2,5) (3,0) (4,0) (4,3) (2,3) (3,4) (4,4)
  (6,2) (6,6) — residues (0,0) (1,0) (14,1) (0,1) (0,9) (1,9) (14,2) (0,2) (9,14) (2,14) (3,0) (9,0)
  (9,3) (2,3) (3,9) (9,9) (18,2) (18,18). Forward property by `decide +kernel` (153 pairs); injectivity
  from the forward property and irreflexivity.
* The main theorem from `lift_corollary` with `t = 4`, `k = 2`, `N = 18`, `m = 59`:
  `(4 ^ 2) ^ 59 * (17 * 59 + 1) < 18 ^ 59` by `decide +kernel` (`n = 118`).
* `4 < C(T₇)` from `lt_capacity_of_clique`; `√18 ≤ C(T₇)` from `rpow_le_capacity_internal` at
  `k = 2` (`Real.sqrt_eq_rpow`); `t(T₇) < C(T₇)` by rewriting `transitiveNumber_T7`.
* `C(T₇) ≤ 5` from `capacity_le_of_factorization_internal` over `ZMod 2` with the explicit
  factorization below: `A : Fin 7 → Fin 5 → ZMod 2` with rows
  `1 0 0 0 0 / 0 1 0 0 0 / 0 0 1 0 0 / 0 0 0 1 0 / 0 1 1 1 0 / 0 0 0 0 1 / 0 1 1 0 0` and
  `B : Fin 5 → Fin 7 → ZMod 2` with rows `1 0 0 0 0 0 0 / 0 1 0 0 0 0 1 / 0 1 1 0 1 0 0 /
  0 0 1 1 0 0 1 / 0 0 0 0 0 1 0`; the product has diagonal `1` and vanishes on every arc (both by
  `decide`). (Lane: t7.)
-/

@[expose] public section

namespace SpernerCapacity

theorem T7_isTournament_internal : IsTournament T7 := by
  unfold IsTournament
  decide

theorem T7_transitive_four : ∃ f : Fin 4 → Fin 7, Function.Injective f ∧ IsTransitiveChain T7 f :=
  ⟨![0, 1, 2, 3], by decide, by unfold IsTransitiveChain; decide⟩

/-! The pruned nested search for a transitive 5-chain: each next vertex ranges over the common
out-neighbourhood of the previous ones. -/

/-- No fifth vertex beats `x0, x1, x2, x3`. -/
def noChainStep5 (x0 x1 x2 x3 : Fin 7) : Prop :=
  ∀ x4 : Fin 7, T7 x0 x4 → T7 x1 x4 → T7 x2 x4 → T7 x3 x4 → False
instance (x0 x1 x2 x3 : Fin 7) : Decidable (noChainStep5 x0 x1 x2 x3) := by
  unfold noChainStep5; infer_instance

/-- No transitive chain extends `x0, x1, x2` by two vertices. -/
def noChainStep4 (x0 x1 x2 : Fin 7) : Prop :=
  ∀ x3 : Fin 7, T7 x0 x3 → T7 x1 x3 → T7 x2 x3 → noChainStep5 x0 x1 x2 x3
instance (x0 x1 x2 : Fin 7) : Decidable (noChainStep4 x0 x1 x2) := by
  unfold noChainStep4; infer_instance

/-- No transitive chain extends `x0, x1` by three vertices. -/
def noChainStep3 (x0 x1 : Fin 7) : Prop := ∀ x2 : Fin 7, T7 x0 x2 → T7 x1 x2 → noChainStep4 x0 x1 x2
instance (x0 x1 : Fin 7) : Decidable (noChainStep3 x0 x1) := by unfold noChainStep3; infer_instance

/-- No transitive chain extends `x0` by four vertices. -/
def noChainStep2 (x0 : Fin 7) : Prop := ∀ x1 : Fin 7, T7 x0 x1 → noChainStep3 x0 x1
instance (x0 : Fin 7) : Decidable (noChainStep2 x0) := by unfold noChainStep2; infer_instance

/-- No transitive chain of five vertices. -/
def noChainStep1 : Prop := ∀ x0 : Fin 7, noChainStep2 x0
instance : Decidable noChainStep1 := by unfold noChainStep1; infer_instance

theorem noChainStep1_holds : noChainStep1 := by decide +kernel

theorem T7_no_transitive_five : ¬ ∃ f : Fin 5 → Fin 7, Function.Injective f ∧ IsTransitiveChain T7 f := by
  rintro ⟨f, -, hf⟩
  exact noChainStep1_holds (f 0) (f 1) (hf 0 1 (by decide)) (f 2) (hf 0 2 (by decide))
    (hf 1 2 (by decide)) (f 3) (hf 0 3 (by decide)) (hf 1 3 (by decide)) (hf 2 3 (by decide))
    (f 4) (hf 0 4 (by decide)) (hf 1 4 (by decide)) (hf 2 4 (by decide)) (hf 3 4 (by decide))

theorem transitiveNumber_T7_internal : transitiveNumber T7 = 4 := by
  obtain ⟨f, hinj, htr⟩ := T7_transitive_four
  exact le_antisymm (transitiveNumber_le T7 (k := 4) T7_no_transitive_five)
    (le_transitiveNumber T7 f hinj htr)

/-- The 18 points, as indices into `W`, in order. -/
def T7pts : Fin 18 → Fin 2 → Fin 7 := fun i => ![
  ![0, 0], ![1, 0], ![5, 1], ![0, 1], ![0, 4], ![1, 4], ![5, 2], ![0, 2], ![4, 5], ![2, 5],
  ![3, 0], ![4, 0], ![4, 3], ![2, 3], ![3, 4], ![4, 4], ![6, 2], ![6, 6]] i

theorem T7pts_forward : ∀ i j : Fin 18, i < j → ∃ c : Fin 2, T7 (T7pts i c) (T7pts j c) := by
  decide +kernel

theorem T7pts_injective : Function.Injective T7pts := by
  intro i j h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨c, hc⟩ := T7pts_forward i j hlt
    rw [h] at hc
    exact T7_isTournament_internal.1 _ hc
  · obtain ⟨c, hc⟩ := T7pts_forward j i hlt
    rw [h] at hc
    exact T7_isTournament_internal.1 _ hc

theorem T7_square_witness_internal : ∃ e : Fin 18 → Fin 2 → Fin 7, Function.Injective e ∧
    ∀ i j : Fin 18, i < j → ∃ c, T7 (e i c) (e j c) :=
  ⟨T7pts, T7pts_injective, T7pts_forward⟩

/-- The counting inequality of the lift at `t = 4`, `k = 2`, `N = 18`, `m = 59`. -/
theorem T7_lift_inequality : (4 ^ 2) ^ 59 * ((18 - 1) * 59 + 1) < 18 ^ 59 := by
  decide +kernel

theorem T7_exists_clique_gt_four_pow_internal :
    ∃ n : ℕ, ∃ S : Finset (Fin n → Fin 7), 4 ^ n < S.card ∧ IsSpernerClique T7 S :=
  ⟨_, lift_corollary T7 T7pts T7pts_injective T7pts_forward 4 59 T7_lift_inequality⟩

theorem four_lt_capacity_T7_internal : (4 : ℝ) < capacity T7 := by
  have := lt_capacity_of_forward T7 two_ne_zero T7pts T7pts_injective T7pts_forward
    (t := 4) (by norm_num)
  exact_mod_cast this

theorem sqrt18_le_capacity_T7_internal : Real.sqrt 18 ≤ capacity T7 := by
  rw [Real.sqrt_eq_rpow]
  have := rpow_le_capacity_internal T7 two_ne_zero T7pts T7pts_injective T7pts_forward
  simpa using this

/-- The rank-5 factorization over `ZMod 2`: the left factor. -/
def T7A : Fin 7 → Fin 5 → ZMod 2 := fun i => ![
  ![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 1, 1, 1, 0],
  ![0, 0, 0, 0, 1], ![0, 1, 1, 0, 0]] i

/-- The right factor. -/
def T7B : Fin 5 → Fin 7 → ZMod 2 := fun i => ![
  ![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 0, 1],
  ![0, 0, 0, 0, 0, 1, 0]] i

theorem T7AB_diag : ∀ v : Fin 7, ∑ i, T7A v i * T7B i v ≠ 0 := by
  decide

theorem T7AB_arc : ∀ u v : Fin 7, T7 u v → ∑ i, T7A u i * T7B i v = 0 := by
  decide

theorem capacity_T7_le_five_internal : capacity T7 ≤ 5 := by
  have := capacity_le_of_factorization_internal T7 T7A T7B T7AB_diag T7AB_arc
  exact_mod_cast this

theorem transitiveNumber_lt_capacity_T7_internal : (transitiveNumber T7 : ℝ) < capacity T7 := by
  rw [transitiveNumber_T7_internal]
  exact_mod_cast four_lt_capacity_T7_internal

end SpernerCapacity

end
