module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The smallest tournament whose Sperner capacity exceeds its transitive number has seven vertices

For a digraph `R` on a vertex set `V`, `w(Rⁿ)` is the largest size of a set `S ⊆ Vⁿ` in which every
ordered pair of distinct members has a coordinate carrying an arc from the first to the second (a
clique of the `n`-th Sperner power), and the capacity is `C(R) = lim_n w(Rⁿ)^{1/n} = sup_n w(Rⁿ)^{1/n}`
(the limit exists and equals the supremum by supermultiplicativity; this file uses the supremum, so
nothing about limits is assumed). For a tournament `T`, `t(T)` is the number of vertices of its largest
transitive subtournament; always `t(T) ≤ C(T)`. Conjecture 1.1 of *On the capacity of digraphs*
(European Journal of Combinatorics 19 (1998) 1–5), attributed there to Körner and Simonyi, reads
`C(T) = t(T)` for every tournament; the same paper disproves it, with an explicit counterexample on 67
vertices, and asks for the smallest tournament for which the equality fails.

Let `T₇` be the subtournament of the Paley tournament on `ZMod 23` (`x → y` iff `y - x` is a nonzero
square) induced on the residues `0, 1, 2, 3, 9, 14, 18`. This file states, and `Solution.lean` proves:

* `T₇` is a tournament with `t(T₇) = 4`;
* eighteen points of `T₇ × T₇`, listed in order, form a transitive clique of the second Sperner
  power (every earlier point sends an arc to every later one in some coordinate), so by the lift lemma
  below some Sperner power of `T₇` has a clique larger than `4ⁿ`, and `√18 ≤ C(T₇)`; in particular
  `t(T₇) = 4 < C(T₇)`, so the equality fails on seven vertices;
* `C(T₇) ≤ 5`, by an explicit rank-5 factorization over `ZMod 2` of a matrix with nonzero diagonal and
  zeros on the arcs (the rank bound below);
* the general tools: the lift lemma (`N` injective points of the `k`-th power, each earlier one
  dominating each later one in some coordinate, give for every `m` a clique of the `k·m`-th power of
  size at least `Nᵐ / ((N - 1)m + 1)`), its consequence `N^{1/k} ≤ C(R)`, the bound `t(R) ≤ C(R)`,
  the rank bound `C(R) ≤ r` for any factorization `M = A·B` through `Fʳ` with `M` nonzero on the
  diagonal and zero on the arcs, and `C(R) ≤ |V|`;
* the same for the Paley tournament on 23 vertices itself: `t = 5` and `√29 ≤ C`, from a
  29-point transitive clique of its second Sperner power;

* every tournament on at most six vertices satisfies `C(T) = t(T)` (for each of the 1, 1, 1, 2, 4,
  12, 56 isomorphism classes on 0, …, 6 vertices, a representative with a rank-`t` factorization over
  `ZMod 2` and a transitive `t`-chain; the kernel checks that every labelled tournament on `n ≤ 6`
  vertices is a relabelling of a representative, by a bitset over all `2^{n(n-1)/2}` orientations);
  hence a tournament whose capacity exceeds its transitive number has at least seven vertices, and
  with `T₇` seven is exactly the least number of vertices of a counterexample.

That `T₇` is the only counterexample on seven vertices up to isomorphism, and that the square value
18 is exact, are established on paper in the accompanying note by explicit certificates with
standard-library checkers; they are not formalized here.

This Mathlib-only file intentionally contains placeholders; the corresponding Solution declarations
are proved in a separate environment.
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

/-! ### `T₇` -/

/-- `T₇` is a tournament. -/
theorem T7_isTournament : IsTournament T7 := sorry

/-- The largest transitive subtournament of `T₇` has four vertices. -/
theorem transitiveNumber_T7 : transitiveNumber T7 = 4 := sorry

/-- Eighteen points of `T₇ × T₇` form a transitive clique of the second Sperner power of `T₇`: in
the listed order every earlier point sends an arc to every later one in some coordinate. -/
theorem T7_square_witness : ∃ e : Fin 18 → Fin 2 → Fin 7, Function.Injective e ∧
    ∀ i j : Fin 18, i < j → ∃ c, T7 (e i c) (e j c) := sorry

/-- Some Sperner power of `T₇` has a clique larger than `4ⁿ = t(T₇)ⁿ`. -/
theorem T7_exists_clique_gt_four_pow :
    ∃ n : ℕ, ∃ S : Finset (Fin n → Fin 7), 4 ^ n < S.card ∧ IsSpernerClique T7 S := sorry

/-- `4 < C(T₇)`. -/
theorem four_lt_capacity_T7 : (4 : ℝ) < capacity T7 := sorry

/-- `√18 ≤ C(T₇)`. -/
theorem sqrt18_le_capacity_T7 : Real.sqrt 18 ≤ capacity T7 := sorry

/-- `C(T₇) ≤ 5`, by a rank-5 factorization over `ZMod 2`. -/
theorem capacity_T7_le_five : capacity T7 ≤ 5 := sorry

/-- The equality `C(T) = t(T)` fails for `T₇`: its capacity exceeds its transitive number. -/
theorem transitiveNumber_lt_capacity_T7 : (transitiveNumber T7 : ℝ) < capacity T7 := sorry

/-! ### General tools -/

/-- **The lift lemma.** `N` injective points of the `k`-th Sperner power of `R`, each earlier one
sending an arc to each later one in some coordinate, give for every `m` a clique of the `k·m`-th
power of size at least `Nᵐ / ((N - 1)·m + 1)` (words of length `m` over the points with a fixed
index sum, concatenated). -/
theorem lift_lemma {V : Type*} (R : V → V → Prop) {k N : ℕ} (pts : Fin N → Fin k → V)
    (hinj : Function.Injective pts) (hfwd : ∀ i j : Fin N, i < j → ∃ c, R (pts i c) (pts j c))
    (m : ℕ) : ∃ S : Finset (Fin (k * m) → V), IsSpernerClique R S ∧
      N ^ m ≤ ((N - 1) * m + 1) * S.card := sorry

/-- `N` such points of the `k`-th power give `N^{1/k} ≤ C(R)`. -/
theorem rpow_le_capacity {V : Type*} [Fintype V] (R : V → V → Prop) {k N : ℕ} (hk : k ≠ 0)
    (pts : Fin N → Fin k → V) (hinj : Function.Injective pts)
    (hfwd : ∀ i j : Fin N, i < j → ∃ c, R (pts i c) (pts j c)) :
    (N : ℝ) ^ ((1 : ℝ) / k) ≤ capacity R := sorry

/-- The transitive number is a lower bound for the capacity: `t(R) ≤ C(R)`. -/
theorem transitiveNumber_le_capacity {V : Type*} [Fintype V] (R : V → V → Prop) :
    (transitiveNumber R : ℝ) ≤ capacity R := sorry

/-- **The rank bound.** If `M = A·B` is a `V × V` matrix over a field factored through `Fʳ`, with
`M v v ≠ 0` for every vertex and `M u v = 0` whenever `u → v`, then `C(R) ≤ r` (a clique of the
`n`-th power indexes a nonsingular diagonal submatrix of the `n`-th Kronecker power of `M`, which
factors through `F^{rⁿ}`). -/
theorem capacity_le_of_factorization {V : Type*} [Fintype V] (R : V → V → Prop) {F : Type*}
    [Field F] {r : ℕ} (A : V → Fin r → F) (B : Fin r → V → F)
    (hdiag : ∀ v, ∑ i, A v i * B i v ≠ 0) (harc : ∀ u v, R u v → ∑ i, A u i * B i v = 0) :
    capacity R ≤ r := sorry

/-- `C(R) ≤ |V|`. -/
theorem capacity_le_card {V : Type*} [Fintype V] (R : V → V → Prop) :
    capacity R ≤ Fintype.card V := sorry

/-! ### The Paley tournament on 23 vertices -/

/-- The Paley tournament on `ZMod 23` is a tournament. -/
theorem paley_isTournament : IsTournament paley := sorry

/-- Its largest transitive subtournament has five vertices. -/
theorem transitiveNumber_paley : transitiveNumber paley = 5 := sorry

/-- `5 < C` for the Paley tournament on 23 vertices. -/
theorem five_lt_capacity_paley : (5 : ℝ) < capacity paley := sorry

/-- `√29 ≤ C` for the Paley tournament on 23 vertices, from a 29-point transitive clique of its
second Sperner power. -/
theorem sqrt29_le_capacity_paley : Real.sqrt 29 ≤ capacity paley := sorry

/-! ### Tournaments on at most six vertices -/

/-- Every tournament on at most six vertices has capacity equal to its transitive number. -/
theorem capacity_eq_transitiveNumber_of_card_le_six {V : Type*} [Fintype V] (R : V → V → Prop)
    (hT : IsTournament R) (hV : Fintype.card V ≤ 6) : capacity R = transitiveNumber R := sorry

/-- A tournament whose capacity exceeds its transitive number has at least seven vertices. -/
theorem seven_le_card_of_transitiveNumber_lt_capacity {V : Type*} [Fintype V] (R : V → V → Prop)
    (hT : IsTournament R) (h : (transitiveNumber R : ℝ) < capacity R) : 7 ≤ Fintype.card V := sorry

end SpernerCapacity

end
