module

public import SpernerCapacity.Lift
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The clique number, the transitive number and the capacity

Basic facts: the set of clique sizes is nonempty and bounded (so `w(Rⁿ)` is attained and at most
`|V|ⁿ`), the capacity is a bounded supremum with `w(Rⁿ)^{1/n} ≤ C(R)` for every `n ≥ 1`, `C(R) ≤ |V|`,
a clique of the `n`-th power larger than `tⁿ` gives `t < C(R)`; the transitive number is attained
and at most `|V|`; the lift gives `N^{1/k} ≤ C(R)` and `t(R) ≤ C(R)`. (Lane: clique.)
-/

@[expose] public section

namespace SpernerCapacity

variable {V : Type*} (R : V → V → Prop)

theorem cliqueSizes_nonempty (n : ℕ) :
    {c | ∃ S : Finset (Fin n → V), S.card = c ∧ IsSpernerClique R S}.Nonempty :=
  ⟨0, ∅, rfl, by intro u hu; simp at hu⟩

theorem transitiveSizes_nonempty :
    {k | ∃ f : Fin k → V, Function.Injective f ∧ IsTransitiveChain R f}.Nonempty :=
  ⟨0, Fin.elim0, fun a => a.elim0, fun i => i.elim0⟩

section Finite

variable [Fintype V]

theorem cliqueSizes_bddAbove (n : ℕ) :
    BddAbove {c | ∃ S : Finset (Fin n → V), S.card = c ∧ IsSpernerClique R S} := by
  refine ⟨Fintype.card V ^ n, ?_⟩
  rintro c ⟨S, rfl, -⟩
  calc S.card ≤ Fintype.card (Fin n → V) := Finset.card_le_univ S
    _ = Fintype.card V ^ n := by rw [Fintype.card_fun, Fintype.card_fin]

theorem card_le_spernerCliqueNumber {n : ℕ} (S : Finset (Fin n → V))
    (hS : IsSpernerClique R S) : S.card ≤ spernerCliqueNumber R n :=
  le_csSup (cliqueSizes_bddAbove R n) ⟨S, rfl, hS⟩

theorem spernerCliqueNumber_attained (n : ℕ) :
    ∃ S : Finset (Fin n → V), S.card = spernerCliqueNumber R n ∧ IsSpernerClique R S :=
  Nat.sSup_mem (cliqueSizes_nonempty R n) (cliqueSizes_bddAbove R n)

theorem spernerCliqueNumber_le (n : ℕ) : spernerCliqueNumber R n ≤ Fintype.card V ^ n := by
  obtain ⟨S, hS, -⟩ := spernerCliqueNumber_attained R n
  rw [← hS]
  calc S.card ≤ Fintype.card (Fin n → V) := Finset.card_le_univ S
    _ = Fintype.card V ^ n := by rw [Fintype.card_fun, Fintype.card_fin]

theorem root_pow {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) :
    (x ^ n) ^ ((1 : ℝ) / n) = x := by
  rw [one_div]; exact Real.pow_rpow_inv_natCast hx hn

/-- Each term of the supremum is at most `|V|`. -/
theorem term_le_card (n : ℕ) :
    (spernerCliqueNumber R (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1)) ≤ Fintype.card V := by
  have hw : (spernerCliqueNumber R (n + 1) : ℝ) ≤ (Fintype.card V : ℝ) ^ (n + 1) := by
    exact_mod_cast spernerCliqueNumber_le R (n + 1)
  have h := Real.rpow_le_rpow (Nat.cast_nonneg _) hw (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1))
  have he : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [← he, root_pow (Nat.cast_nonneg _) (Nat.succ_ne_zero n)] at h
  simpa [he] using h

theorem capacity_bddAbove : BddAbove (Set.range fun n : ℕ =>
    ((spernerCliqueNumber R (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1)))) := by
  refine ⟨Fintype.card V, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact term_le_card R n

theorem le_capacity (n : ℕ) (hn : n ≠ 0) :
    (spernerCliqueNumber R n : ℝ) ^ ((1 : ℝ) / n) ≤ capacity R := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := le_ciSup (capacity_bddAbove R) m
  have he : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [he]; exact h

theorem capacity_le_card_internal : capacity R ≤ Fintype.card V :=
  ciSup_le fun n => term_le_card R n

theorem capacity_nonneg : 0 ≤ capacity R :=
  (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans (le_capacity R 1 one_ne_zero)

/-- A clique of the `n`-th power larger than `tⁿ` gives `t < C(R)`. -/
theorem lt_capacity_of_clique {t n : ℕ} (S : Finset (Fin n → V)) (hS : IsSpernerClique R S)
    (h : t ^ n < S.card) : (t : ℝ) < capacity R := by
  have hn : n ≠ 0 := by
    rintro rfl
    have : S.card ≤ 1 := by
      calc S.card ≤ Fintype.card (Fin 0 → V) := Finset.card_le_univ S
        _ = 1 := by simp
    simp at h; omega
  have hw : ((t ^ n : ℕ) : ℝ) < spernerCliqueNumber R n := by
    exact_mod_cast lt_of_lt_of_le h (card_le_spernerCliqueNumber R S hS)
  push_cast at hw
  have h2 := Real.rpow_lt_rpow (by positivity) hw (by positivity : (0 : ℝ) < 1 / n)
  rw [root_pow (Nat.cast_nonneg t) hn] at h2
  exact lt_of_lt_of_le h2 (le_capacity R n hn)

set_option linter.unusedSectionVars false in
/-- If every term `w(Rⁿ)^{1/n}` is at most `b`, then `C(R) ≤ b`. -/
theorem capacity_le_of_forall {b : ℝ} (hb : ∀ n : ℕ, n ≠ 0 →
    (spernerCliqueNumber R n : ℝ) ^ ((1 : ℝ) / n) ≤ b) : capacity R ≤ b := by
  refine ciSup_le fun n => ?_
  have h := hb (n + 1) (Nat.succ_ne_zero n)
  have he : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [he] at h
  exact h

theorem transitiveSizes_bddAbove :
    BddAbove {k | ∃ f : Fin k → V, Function.Injective f ∧ IsTransitiveChain R f} := by
  refine ⟨Fintype.card V, ?_⟩
  rintro k ⟨f, hinj, -⟩
  simpa using Fintype.card_le_of_injective f hinj

theorem transitiveNumber_attained :
    ∃ f : Fin (transitiveNumber R) → V, Function.Injective f ∧ IsTransitiveChain R f :=
  Nat.sSup_mem (transitiveSizes_nonempty R) (transitiveSizes_bddAbove R)

theorem le_transitiveNumber {k : ℕ} (f : Fin k → V) (hinj : Function.Injective f)
    (htr : IsTransitiveChain R f) : k ≤ transitiveNumber R :=
  le_csSup (transitiveSizes_bddAbove R) ⟨f, hinj, htr⟩

/-- `t(R) ≤ k` when there is no injective transitive chain of length `k + 1`. -/
theorem transitiveNumber_le {k : ℕ}
    (h : ¬ ∃ f : Fin (k + 1) → V, Function.Injective f ∧ IsTransitiveChain R f) :
    transitiveNumber R ≤ k := by
  by_contra hlt
  push Not at hlt
  obtain ⟨f, hinj, htr⟩ := transitiveNumber_attained R
  refine h ⟨f ∘ Fin.castLE (by omega), hinj.comp (Fin.castLE_injective _), ?_⟩
  intro i j hij
  exact htr _ _ hij

theorem exists_pow_mul_lt {ρ T : ℝ} (hρ : 0 ≤ ρ) (hT : ρ < T) (a : ℕ) :
    ∃ m : ℕ, 1 ≤ m ∧ ρ ^ m * ((a * m + 1 : ℕ) : ℝ) < T ^ m := by
  have hTpos : 0 < T := lt_of_le_of_lt hρ hT
  have hq : |ρ / T| < 1 := by
    rw [abs_of_nonneg (div_nonneg hρ hTpos.le), div_lt_one hTpos]; exact hT
  have hlim := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hq
  have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hev := ((tendsto_order.1 hlim).2 (1 / ((a : ℝ) + 1)) (by positivity)).and
    (Filter.eventually_ge_atTop 1)
  obtain ⟨m, hm, hm1⟩ := hev.exists
  refine ⟨m, hm1, ?_⟩
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hTm : 0 < T ^ m := pow_pos hTpos m
  have key : ρ ^ m = (ρ / T) ^ m * T ^ m := by rw [div_pow, div_mul_cancel₀ _ hTm.ne']
  have hD : ((a * m + 1 : ℕ) : ℝ) ≤ ((a : ℝ) + 1) * m := by push_cast; nlinarith
  have hm' : ((a : ℝ) + 1) * ((m : ℝ) ^ 1 * (ρ / T) ^ m) < 1 := by
    have := mul_lt_mul_of_pos_left hm ha1
    rwa [mul_one_div_cancel ha1.ne'] at this
  calc ρ ^ m * ((a * m + 1 : ℕ) : ℝ) ≤ ρ ^ m * (((a : ℝ) + 1) * m) :=
        mul_le_mul_of_nonneg_left hD (pow_nonneg hρ m)
    _ = T ^ m * (((a : ℝ) + 1) * ((m : ℝ) ^ 1 * (ρ / T) ^ m)) := by rw [key]; ring
    _ < T ^ m * 1 := mul_lt_mul_of_pos_left hm' hTm
    _ = T ^ m := mul_one _

/-- The statement of `Challenge.lean`. -/
theorem rpow_le_capacity_internal {k N : ℕ} (hk : k ≠ 0) (pts : Fin N → Fin k → V)
    (hinj : Function.Injective pts) (hfwd : ∀ i j : Fin N, i < j → ∃ c, R (pts i c) (pts j c)) :
    (N : ℝ) ^ ((1 : ℝ) / k) ≤ capacity R := by
  apply le_of_forall_lt
  intro r hr
  rcases lt_or_ge r 0 with hr0 | hr0
  · exact lt_of_lt_of_le hr0 (capacity_nonneg R)
  have hρ : r ^ k < N := by
    have := pow_lt_pow_left₀ hr hr0 hk
    rwa [one_div, Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) hk] at this
  obtain ⟨m, hm1, hm⟩ := exists_pow_mul_lt (pow_nonneg hr0 k) hρ (N - 1)
  obtain ⟨S, hS, hle⟩ := lift_lemma_internal R pts hinj hfwd m
  have hD : (0 : ℝ) ≤ (((N - 1) * m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hle' : (N : ℝ) ^ m ≤ (((N - 1) * m + 1 : ℕ) : ℝ) * S.card := by exact_mod_cast hle
  have hcard : (r ^ k) ^ m < S.card := by
    refine lt_of_mul_lt_mul_left ?_ hD
    rw [mul_comm]
    exact lt_of_lt_of_le hm hle'
  have hkm : k * m ≠ 0 := Nat.mul_ne_zero hk (by omega)
  have hw : r ^ (k * m) < spernerCliqueNumber R (k * m) := by
    rw [pow_mul]
    exact lt_of_lt_of_le hcard (by exact_mod_cast card_le_spernerCliqueNumber R S hS)
  have h2 := Real.rpow_lt_rpow (by positivity) hw (by positivity : (0 : ℝ) < 1 / ((k * m : ℕ) : ℝ))
  rw [root_pow hr0 hkm] at h2
  exact lt_of_lt_of_le h2 (le_capacity R (k * m) hkm)

/-- A transitive `t`-chain gives `t ≤ C(R)`. -/
theorem transitive_le_capacity {t : ℕ} (f : Fin t → V) (hinj : Function.Injective f)
    (htr : IsTransitiveChain R f) : (t : ℝ) ≤ capacity R := by
  have h := rpow_le_capacity_internal R one_ne_zero (fun i (_ : Fin 1) => f i)
    (fun i j hij => hinj (congrFun hij 0)) (fun i j hij => ⟨0, htr i j hij⟩)
  simpa using h

/-- The statement of `Challenge.lean`. -/
theorem transitiveNumber_le_capacity_internal : (transitiveNumber R : ℝ) ≤ capacity R := by
  obtain ⟨f, hinj, htr⟩ := transitiveNumber_attained R
  exact transitive_le_capacity R f hinj htr

/-- The counterexample criterion: `N > tᵏ` forward-ordered injective points of the `k`-th power
force `t < C(R)`. -/
theorem lt_capacity_of_forward {k N t : ℕ} (hk : k ≠ 0) (pts : Fin N → Fin k → V)
    (hinj : Function.Injective pts) (hfwd : ∀ i j : Fin N, i < j → ∃ c, R (pts i c) (pts j c))
    (h : t ^ k < N) : (t : ℝ) < capacity R := by
  have h1 : ((t : ℝ) ^ k) < (N : ℝ) := by exact_mod_cast h
  have h2 := Real.rpow_lt_rpow (by positivity) h1 (by positivity : (0 : ℝ) < 1 / (k : ℝ))
  rw [root_pow (Nat.cast_nonneg t) hk] at h2
  exact lt_of_lt_of_le h2 (rpow_le_capacity_internal R hk pts hinj hfwd)

end Finite

end SpernerCapacity

end
