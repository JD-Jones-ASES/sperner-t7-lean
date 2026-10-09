module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Definitions

The definitions of `Challenge.lean`, restated character for character (the imports are the same, so
that every definition elaborates to the same term in both files). `scripts/check_definitions.py`
compares the two files.
-/

@[expose] public section

namespace SpernerCapacity

/-- The Paley tournament on `ZMod 23`: `x → y` iff `y - x` is a nonzero square. -/
def paley (x y : ZMod 23) : Prop := x ≠ y ∧ IsSquare (y - x)

/-- The seven residues `0, 1, 2, 3, 9, 14, 18`. -/
def W : Fin 7 → ZMod 23 := ![0, 1, 2, 3, 9, 14, 18]

/-- `T₇`: the subtournament of the Paley tournament on 23 vertices induced on `W`. -/
def T7 (x y : Fin 7) : Prop := paley (W x) (W y)

/-- A tournament: no loops, and exactly one arc between any two distinct vertices. -/
def IsTournament {V : Type*} (R : V → V → Prop) : Prop :=
  (∀ x, ¬ R x x) ∧ ∀ x y, x ≠ y → (R x y ↔ ¬ R y x)

/-- `f` lists a transitive subtournament of `R` in order: every earlier vertex sends an arc to every
later one. -/
def IsTransitiveChain {V : Type*} (R : V → V → Prop) {k : ℕ} (f : Fin k → V) : Prop :=
  ∀ i j : Fin k, i < j → R (f i) (f j)

/-- `t(R)`: the largest number of vertices of a transitive subtournament of `R`. -/
noncomputable def transitiveNumber {V : Type*} (R : V → V → Prop) : ℕ :=
  sSup {k | ∃ f : Fin k → V, Function.Injective f ∧ IsTransitiveChain R f}

/-- `S ⊆ Vⁿ` is a clique of the `n`-th Sperner (OR) power of `R`: every ordered pair of distinct
members has a coordinate carrying an arc from the first to the second. -/
def IsSpernerClique {V : Type*} (R : V → V → Prop) {n : ℕ} (S : Finset (Fin n → V)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ∃ i, R (u i) (v i)

/-- `w(Rⁿ)`: the largest size of a clique of the `n`-th Sperner power of `R`. -/
noncomputable def spernerCliqueNumber {V : Type*} (R : V → V → Prop) (n : ℕ) : ℕ :=
  sSup {c | ∃ S : Finset (Fin n → V), S.card = c ∧ IsSpernerClique R S}

/-- The capacity `C(R) = sup_{n ≥ 1} w(Rⁿ)^{1/n}`. -/
noncomputable def capacity {V : Type*} (R : V → V → Prop) : ℝ :=
  ⨆ n : ℕ, ((spernerCliqueNumber R (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1)))

/-! Decidability of the two concrete tournaments, for the kernel computations of the development
(not part of the compared definitions). -/

instance (x y : ZMod 23) : Decidable (paley x y) :=
  inferInstanceAs (Decidable (x ≠ y ∧ ∃ r : ZMod 23, y - x = r * r))

instance (x y : Fin 7) : Decidable (T7 x y) := inferInstanceAs (Decidable (paley (W x) (W y)))

end SpernerCapacity

end
