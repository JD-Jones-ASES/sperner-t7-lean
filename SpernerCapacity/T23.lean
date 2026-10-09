module

public import SpernerCapacity.Clique

/-!
# The Paley tournament on 23 vertices

`paley x y ↔ x ≠ y ∧ IsSquare (y - x)` on `ZMod 23`. It is a tournament (`−1` is not a square mod
23; `decide` over the 529 pairs). Its transitive number is 5: the chain `0, 1, 2, 3, 4` is transitive;
no transitive 6-chain exists — translate so that the first vertex is `0` (`paley (x + c) (y + c) ↔
paley x y`) and run the pruned nested search `c1 … c5` over the common out-neighbourhoods, exactly as
`.scratch/T23Probe.lean` does (compiled at this pin; port it). The 29 points of the second Sperner
power, in order (residues):
(22,7) (8,2) (8,3) (8,11) (1,13) (14,13) (1,6) (5,6) (17,22) (17,7) (3,22) (3,7) (12,19) (12,22)
(1,15) (5,15) (21,19) (14,2) (14,15) (9,0) (9,2) (17,0) (17,2) (7,4) (3,8) (7,6) (9,8) (21,8) (11,8);
forward property by `decide` (406 pairs). Then `5 < C` from `lt_capacity_of_forward` (`29 > 5²`) or
from `lift_corollary` at `m = 49`, and `√29 ≤ C` from `rpow_le_capacity_internal` at `k = 2`.
(Lane: t23.)
-/

@[expose] public section

namespace SpernerCapacity

theorem paley_isTournament_internal : IsTournament paley := by
  unfold IsTournament
  constructor
  · intro x; decide +revert
  · decide

theorem paley_translate (x y c : ZMod 23) : paley (x + c) (y + c) ↔ paley x y := by
  unfold paley
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 (by rw [h]), by simpa using h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 (add_right_cancel h), by simpa using h2⟩

theorem paley_transitive_five :
    ∃ f : Fin 5 → ZMod 23, Function.Injective f ∧ IsTransitiveChain paley f :=
  ⟨![0, 1, 2, 3, 4], by decide, by unfold IsTransitiveChain; decide⟩

/-- No `x5` extends the chain `0, x1, …, x4`. -/
def paleyC5 (x1 x2 x3 x4 : ZMod 23) : Prop :=
  ∀ x5 : ZMod 23, paley 0 x5 → paley x1 x5 → paley x2 x5 → paley x3 x5 → paley x4 x5 → False
instance (x1 x2 x3 x4 : ZMod 23) : Decidable (paleyC5 x1 x2 x3 x4) := by
  unfold paleyC5; infer_instance
def paleyC4 (x1 x2 x3 : ZMod 23) : Prop :=
  ∀ x4 : ZMod 23, paley 0 x4 → paley x1 x4 → paley x2 x4 → paley x3 x4 → paleyC5 x1 x2 x3 x4
instance (x1 x2 x3 : ZMod 23) : Decidable (paleyC4 x1 x2 x3) := by unfold paleyC4; infer_instance
def paleyC3 (x1 x2 : ZMod 23) : Prop :=
  ∀ x3 : ZMod 23, paley 0 x3 → paley x1 x3 → paley x2 x3 → paleyC4 x1 x2 x3
instance (x1 x2 : ZMod 23) : Decidable (paleyC3 x1 x2) := by unfold paleyC3; infer_instance
def paleyC2 (x1 : ZMod 23) : Prop := ∀ x2 : ZMod 23, paley 0 x2 → paley x1 x2 → paleyC3 x1 x2
instance (x1 : ZMod 23) : Decidable (paleyC2 x1) := by unfold paleyC2; infer_instance
def paleyC1 : Prop := ∀ x1 : ZMod 23, paley 0 x1 → paleyC2 x1
instance : Decidable paleyC1 := by unfold paleyC1; infer_instance

/-- No transitive 5-chain inside the out-neighbourhood of `0` (pruned kernel search). -/
theorem paley_no_chain : paleyC1 := by decide

theorem paley_no_transitive_six :
    ¬ ∃ f : Fin 6 → ZMod 23, Function.Injective f ∧ IsTransitiveChain paley f := by
  rintro ⟨f, -, hf⟩
  have h : ∀ i j : Fin 6, i < j → paley (f i - f 0) (f j - f 0) := by
    intro i j hij
    simpa [sub_eq_add_neg] using (paley_translate (f i) (f j) (-f 0)).2 (hf i j hij)
  have h0 : f 0 - f 0 = 0 := sub_self _
  refine paley_no_chain (f 1 - f 0) ?_ (f 2 - f 0) ?_ ?_ (f 3 - f 0) ?_ ?_ ?_ (f 4 - f 0) ?_ ?_ ?_ ?_
    (f 5 - f 0) ?_ ?_ ?_ ?_ ?_ <;>
  first
  | (rw [← h0]; exact h _ _ (by decide))
  | exact h _ _ (by decide)

theorem transitiveNumber_paley_internal : transitiveNumber paley = 5 := by
  obtain ⟨f, hinj, htr⟩ := paley_transitive_five
  exact le_antisymm (transitiveNumber_le paley paley_no_transitive_six)
    (le_transitiveNumber paley f hinj htr)

/-- The 29 points, in order. -/
def paleyPts : Fin 29 → Fin 2 → ZMod 23 := fun i => ![
  ![22, 7], ![8, 2], ![8, 3], ![8, 11], ![1, 13], ![14, 13], ![1, 6], ![5, 6], ![17, 22],
  ![17, 7], ![3, 22], ![3, 7], ![12, 19], ![12, 22], ![1, 15], ![5, 15], ![21, 19],
  ![14, 2], ![14, 15], ![9, 0], ![9, 2], ![17, 0], ![17, 2], ![7, 4], ![3, 8], ![7, 6],
  ![9, 8], ![21, 8], ![11, 8]] i

theorem paleyPts_forward :
    ∀ i j : Fin 29, i < j → ∃ c : Fin 2, paley (paleyPts i c) (paleyPts j c) := by
  decide

theorem paleyPts_injective : Function.Injective paleyPts := by
  intro i j h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨k, hk, _⟩ := paleyPts_forward i j hlt; exact hk (by rw [h])
  · obtain ⟨k, hk, _⟩ := paleyPts_forward j i hlt; exact hk (by rw [h])

theorem five_lt_capacity_paley_internal : (5 : ℝ) < capacity paley := by
  have := lt_capacity_of_forward paley (k := 2) (N := 29) (t := 5) (by decide) paleyPts
    paleyPts_injective paleyPts_forward (by decide)
  exact_mod_cast this

theorem sqrt29_le_capacity_paley_internal : Real.sqrt 29 ≤ capacity paley := by
  have := rpow_le_capacity_internal paley (k := 2) (N := 29) (by decide) paleyPts
    paleyPts_injective paleyPts_forward
  rw [Real.sqrt_eq_rpow]
  convert this using 2

end SpernerCapacity

end
