module

public import SpernerCapacity.Clique
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The rank bound

Let `F` be a field, `A : V → Fin r → F`, `B : Fin r → V → F`, and `M u v = ∑ i, A u i * B i v`.
Suppose `M v v ≠ 0` for every `v` and `M u v = 0` whenever `u → v`. Then `w(Rⁿ) ≤ rⁿ` for every `n`,
hence `C(R) ≤ r`.

Proof. For `u v : Fin n → V` put `Mₙ u v = ∏ i, M (u i) (v i)`; expanding each factor,
`Mₙ u v = ∑ j : Fin n → Fin r, (∏ i, A (u i) (j i)) * (∏ i, B (j i) (v i))`, that is
`Mₙ = Aₙ * Bₙ` with `Aₙ u j = ∏ i, A (u i) (j i)` and `Bₙ j v = ∏ i, B (j i) (v i)`
(`Finset.prod_univ_sum` / `Fintype.prod_sum`). If `S` is a clique of the `n`-th power, then for
distinct `u v ∈ S` some coordinate has `u i → v i`, so `M (u i) (v i) = 0` and `Mₙ u v = 0`, while
`Mₙ u u = ∏ i, M (u i) (u i) ≠ 0`: the submatrix of `Mₙ` on `S × S` is diagonal with nonzero diagonal,
hence invertible, so its rank is `|S|`; it equals the product of the `S × (Fin n → Fin r)` block of
`Aₙ` and the `(Fin n → Fin r) × S` block of `Bₙ`, whose rank is at most `|Fin n → Fin r| = rⁿ`
(`Matrix.rank_mul_le_left`, `Matrix.rank_le_card_width` or the injectivity of `mulVec`). So
`|S| ≤ rⁿ`, `w(Rⁿ) ≤ rⁿ`, and every term `w(Rⁿ)^{1/n} ≤ r`, so `C(R) ≤ r`
(`capacity_le_of_forall`). (Lane: rank.)
-/

@[expose] public section

namespace SpernerCapacity

variable {V : Type*} [Fintype V] (R : V → V → Prop) {F : Type*} [Field F] {r : ℕ}

omit [Fintype V] in
/-- The entry identity of the Kronecker factorization: `∏ᵢ (A B)(uᵢ, vᵢ) = ∑ⱼ Aₙ(u, j) Bₙ(j, v)`. -/
theorem rank_entry_identity (A : V → Fin r → F) (B : Fin r → V → F) {n : ℕ} (u v : Fin n → V) :
    ∑ j : Fin n → Fin r, (∏ i, A (u i) (j i)) * (∏ i, B (j i) (v i))
      = ∏ i, ∑ k, A (u i) k * B k (v i) := by
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.prod_mul_distrib.symm

set_option linter.unusedSectionVars false in
/-- A clique of the `n`-th Sperner power of `R` has at most `rⁿ` points when a matrix with nonzero
diagonal and zeros on the arcs factors through `Fʳ`. -/
theorem card_le_pow_of_factorization (A : V → Fin r → F) (B : Fin r → V → F)
    (hdiag : ∀ v, ∑ i, A v i * B i v ≠ 0) (harc : ∀ u v, R u v → ∑ i, A u i * B i v = 0)
    {n : ℕ} (S : Finset (Fin n → V)) (hS : IsSpernerClique R S) : S.card ≤ r ^ n := by
  classical
  let As : Matrix S (Fin n → Fin r) F := Matrix.of fun s j => ∏ i, A ((s : Fin n → V) i) (j i)
  let Bs : Matrix (Fin n → Fin r) S F := Matrix.of fun j s => ∏ i, B (j i) ((s : Fin n → V) i)
  have hprod : As * Bs = Matrix.diagonal fun s : S =>
      ∏ i, ∑ k, A ((s : Fin n → V) i) k * B k ((s : Fin n → V) i) := by
    ext s t
    rw [Matrix.mul_apply]
    simp only [As, Bs, Matrix.of_apply]
    rw [rank_entry_identity]
    by_cases hst : s = t
    · subst hst; simp
    · rw [Matrix.diagonal_apply_ne _ hst]
      obtain ⟨i, hi⟩ := hS s s.2 t t.2 (fun h => hst (Subtype.ext h))
      exact Finset.prod_eq_zero (Finset.mem_univ i) (harc _ _ hi)
  have hinj : Function.Injective Bs.mulVecLin := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [Matrix.mulVecLin_apply] at hx
    have h1 : Matrix.mulVec (As * Bs) x = 0 := by
      rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    rw [hprod] at h1
    funext s
    have h2 := congrFun h1 s
    rw [Matrix.mulVec_diagonal] at h2
    exact (mul_eq_zero.mp h2).resolve_left
      (Finset.prod_ne_zero_iff.mpr fun i _ => hdiag _)
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_fin] using h

/-- `w(Rⁿ) ≤ rⁿ`. -/
theorem spernerCliqueNumber_le_pow_of_factorization (A : V → Fin r → F) (B : Fin r → V → F)
    (hdiag : ∀ v, ∑ i, A v i * B i v ≠ 0) (harc : ∀ u v, R u v → ∑ i, A u i * B i v = 0)
    (n : ℕ) : spernerCliqueNumber R n ≤ r ^ n := by
  obtain ⟨S, hc, hS⟩ := spernerCliqueNumber_attained R n
  rw [← hc]
  exact card_le_pow_of_factorization R A B hdiag harc S hS

/-- The statement of `Challenge.lean`: `C(R) ≤ r`. -/
theorem capacity_le_of_factorization_internal (A : V → Fin r → F) (B : Fin r → V → F)
    (hdiag : ∀ v, ∑ i, A v i * B i v ≠ 0) (harc : ∀ u v, R u v → ∑ i, A u i * B i v = 0) :
    capacity R ≤ r := by
  refine capacity_le_of_forall R fun n hn => ?_
  have h : (spernerCliqueNumber R n : ℝ) ≤ (r : ℝ) ^ n := by
    exact_mod_cast spernerCliqueNumber_le_pow_of_factorization R A B hdiag harc n
  calc (spernerCliqueNumber R n : ℝ) ^ ((1 : ℝ) / n)
      ≤ ((r : ℝ) ^ n) ^ ((1 : ℝ) / n) := Real.rpow_le_rpow (Nat.cast_nonneg _) h (by positivity)
    _ = r := root_pow (Nat.cast_nonneg r) hn

end SpernerCapacity

end
