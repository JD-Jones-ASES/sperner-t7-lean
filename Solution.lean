module

public import SpernerCapacity

/-!
# Solution

Each statement of `Challenge.lean`, restated verbatim and closed by the internal theorem of the same
name with the suffix `_internal` (`SpernerCapacity/T7.lean`, `T23.lean`, `Clique.lean`, `Lift.lean`,
`Rank.lean`, `Six.lean`). This module does not import `Challenge.lean`; the definitions come from
`SpernerCapacity/Defs.lean`, which restates those of the Challenge character for character.
-/

@[expose] public section

namespace SpernerCapacity

/-! ### `T₇` -/

theorem T7_isTournament : IsTournament T7 := T7_isTournament_internal

theorem transitiveNumber_T7 : transitiveNumber T7 = 4 := transitiveNumber_T7_internal

theorem T7_square_witness : ∃ e : Fin 18 → Fin 2 → Fin 7, Function.Injective e ∧
    ∀ i j : Fin 18, i < j → ∃ c, T7 (e i c) (e j c) := T7_square_witness_internal

theorem T7_exists_clique_gt_four_pow :
    ∃ n : ℕ, ∃ S : Finset (Fin n → Fin 7), 4 ^ n < S.card ∧ IsSpernerClique T7 S :=
  T7_exists_clique_gt_four_pow_internal

theorem four_lt_capacity_T7 : (4 : ℝ) < capacity T7 := four_lt_capacity_T7_internal

theorem sqrt18_le_capacity_T7 : Real.sqrt 18 ≤ capacity T7 := sqrt18_le_capacity_T7_internal

theorem capacity_T7_le_five : capacity T7 ≤ 5 := capacity_T7_le_five_internal

theorem transitiveNumber_lt_capacity_T7 : (transitiveNumber T7 : ℝ) < capacity T7 :=
  transitiveNumber_lt_capacity_T7_internal

/-! ### General tools -/

theorem lift_lemma {V : Type*} (R : V → V → Prop) {k N : ℕ} (pts : Fin N → Fin k → V)
    (hinj : Function.Injective pts) (hfwd : ∀ i j : Fin N, i < j → ∃ c, R (pts i c) (pts j c))
    (m : ℕ) : ∃ S : Finset (Fin (k * m) → V), IsSpernerClique R S ∧
      N ^ m ≤ ((N - 1) * m + 1) * S.card := lift_lemma_internal R pts hinj hfwd m

theorem rpow_le_capacity {V : Type*} [Fintype V] (R : V → V → Prop) {k N : ℕ} (hk : k ≠ 0)
    (pts : Fin N → Fin k → V) (hinj : Function.Injective pts)
    (hfwd : ∀ i j : Fin N, i < j → ∃ c, R (pts i c) (pts j c)) :
    (N : ℝ) ^ ((1 : ℝ) / k) ≤ capacity R := rpow_le_capacity_internal R hk pts hinj hfwd

theorem transitiveNumber_le_capacity {V : Type*} [Fintype V] (R : V → V → Prop) :
    (transitiveNumber R : ℝ) ≤ capacity R := transitiveNumber_le_capacity_internal R

theorem capacity_le_of_factorization {V : Type*} [Fintype V] (R : V → V → Prop) {F : Type*}
    [Field F] {r : ℕ} (A : V → Fin r → F) (B : Fin r → V → F)
    (hdiag : ∀ v, ∑ i, A v i * B i v ≠ 0) (harc : ∀ u v, R u v → ∑ i, A u i * B i v = 0) :
    capacity R ≤ r := capacity_le_of_factorization_internal R A B hdiag harc

theorem capacity_le_card {V : Type*} [Fintype V] (R : V → V → Prop) :
    capacity R ≤ Fintype.card V := capacity_le_card_internal R

/-! ### The Paley tournament on 23 vertices -/

theorem paley_isTournament : IsTournament paley := paley_isTournament_internal

theorem transitiveNumber_paley : transitiveNumber paley = 5 := transitiveNumber_paley_internal

theorem five_lt_capacity_paley : (5 : ℝ) < capacity paley := five_lt_capacity_paley_internal

theorem sqrt29_le_capacity_paley : Real.sqrt 29 ≤ capacity paley :=
  sqrt29_le_capacity_paley_internal

/-! ### Tournaments on at most six vertices -/

theorem capacity_eq_transitiveNumber_of_card_le_six {V : Type*} [Fintype V] (R : V → V → Prop)
    (hT : IsTournament R) (hV : Fintype.card V ≤ 6) : capacity R = transitiveNumber R :=
  capacity_eq_transitiveNumber_of_card_le_six_internal R hT hV

theorem seven_le_card_of_transitiveNumber_lt_capacity {V : Type*} [Fintype V] (R : V → V → Prop)
    (hT : IsTournament R) (h : (transitiveNumber R : ℝ) < capacity R) : 7 ≤ Fintype.card V :=
  seven_le_card_of_transitiveNumber_lt_capacity_internal R hT h

end SpernerCapacity

end
