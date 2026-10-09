module

public import SpernerCapacity.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

/-!
# The lift lemma

`N` injective points of the `k`-th Sperner power of `R`, each earlier one sending an arc to each
later one in some coordinate, give for every `m` a clique of the `k·m`-th power of size at least
`Nᵐ / ((N - 1)·m + 1)`: index the points `0, …, N - 1`, take all words of length `m` whose index sum
is the most frequent one, and concatenate the points. Two distinct words of equal index sum have a
position where the first index is larger and one where it is smaller, so the concatenations carry
arcs in both directions. (Lane: lift.)
-/

@[expose] public section

namespace SpernerCapacity

variable {V : Type*}

section Lift

variable (R : V → V → Prop) {k N : ℕ} (pts : Fin N → Fin k → V)

/-- Concatenation: the word `w` of length `m` over `Fin N` gives the point of the `k * m`-th power
whose block `j` is `pts (w j)`. -/
def liftWord (m : ℕ) (w : Fin m → Fin N) : Fin (k * m) → V :=
  fun i => pts (w (finProdFinEquiv.symm i).2) (finProdFinEquiv.symm i).1

theorem liftWord_injective (hinj : Function.Injective pts) (m : ℕ) :
    Function.Injective (liftWord pts m) := by
  intro w w' h
  funext j
  apply hinj
  funext c
  have := congrFun h (finProdFinEquiv (c, j))
  simpa [liftWord] using this

theorem clique_of_equal_sums [DecidableEq V]
    (hfwd : ∀ i j : Fin N, i < j → ∃ c, R (pts i c) (pts j c)) {m : ℕ}
    (S : Finset (Fin m → Fin N)) (s : ℕ) (hS : ∀ w ∈ S, ∑ j, (w j : ℕ) = s) :
    IsSpernerClique R (S.image (liftWord pts m)) := by
  intro u hu v hv huv
  rw [Finset.mem_image] at hu hv
  obtain ⟨w, hw, rfl⟩ := hu
  obtain ⟨w', hw', rfl⟩ := hv
  have hne : w ≠ w' := fun h => huv (by rw [h])
  have hex : ∃ j, w j < w' j := by
    by_contra hcon
    push Not at hcon
    apply hne
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin m)), (w' j : ℕ) ≤ (w j : ℕ) := fun j _ => hcon j
    have heq : ∑ j, (w' j : ℕ) = ∑ j, (w j : ℕ) := by rw [hS w hw, hS w' hw']
    have := (Finset.sum_eq_sum_iff_of_le hle).mp heq
    funext j
    exact Fin.ext (this j (Finset.mem_univ j)).symm
  obtain ⟨j, hj⟩ := hex
  obtain ⟨c, hc⟩ := hfwd (w j) (w' j) hj
  exact ⟨finProdFinEquiv (c, j), by simpa [liftWord] using hc⟩

/-- The lift lemma (the statement of `Challenge.lean`, without any decidability instance). -/
theorem lift_lemma_internal (hinj : Function.Injective pts)
    (hfwd : ∀ i j : Fin N, i < j → ∃ c, R (pts i c) (pts j c)) (m : ℕ) :
    ∃ S : Finset (Fin (k * m) → V), IsSpernerClique R S ∧
      N ^ m ≤ ((N - 1) * m + 1) * S.card := by
  classical
  let f : (Fin m → Fin N) → ℕ := fun w => ∑ j, (w j : ℕ)
  have hmaps : ((Finset.univ : Finset (Fin m → Fin N)) : Set (Fin m → Fin N)).MapsTo f
      (Finset.range ((N - 1) * m + 1)) := by
    intro w _
    simp only [Finset.coe_range, Set.mem_Iio, f]
    rw [Nat.lt_succ_iff]
    calc ∑ j, (w j : ℕ) ≤ ∑ _j : Fin m, (N - 1) :=
          Finset.sum_le_sum fun j _ => by have := (w j).isLt; omega
      _ = (N - 1) * m := by simp [mul_comm]
  obtain ⟨y, -, hmax⟩ := Finset.exists_max_image (Finset.range ((N - 1) * m + 1))
    (fun y => (Finset.univ.filter fun w => f w = y).card) ⟨0, by simp⟩
  refine ⟨(Finset.univ.filter fun w => f w = y).image (liftWord pts m),
    clique_of_equal_sums R pts hfwd _ y (fun w hw => (Finset.mem_filter.mp hw).2), ?_⟩
  rw [Finset.card_image_of_injective _ (liftWord_injective pts hinj m)]
  have h1 := Finset.card_eq_sum_card_fiberwise hmaps
  have h2 := Finset.sum_le_card_nsmul _ _ _ hmax
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h1
  rw [smul_eq_mul, Finset.card_range] at h2
  exact h1.le.trans h2

/-- The lift in ℕ: if `(tᵏ)ᵐ · ((N - 1)·m + 1) < Nᵐ`, some clique of the `k·m`-th power is larger
than `t^{k·m}`. -/
theorem lift_corollary (hinj : Function.Injective pts)
    (hfwd : ∀ i j : Fin N, i < j → ∃ c, R (pts i c) (pts j c)) (t m : ℕ)
    (h : (t ^ k) ^ m * ((N - 1) * m + 1) < N ^ m) :
    ∃ S : Finset (Fin (k * m) → V), t ^ (k * m) < S.card ∧ IsSpernerClique R S := by
  obtain ⟨S, hS, hle⟩ := lift_lemma_internal R pts hinj hfwd m
  refine ⟨S, ?_, hS⟩
  rw [pow_mul]
  have h3 : ((N - 1) * m + 1) * (t ^ k) ^ m < ((N - 1) * m + 1) * S.card := by
    rw [mul_comm]; exact lt_of_lt_of_le h hle
  exact Nat.lt_of_mul_lt_mul_left h3

end Lift

end SpernerCapacity

end
