# The proofs, with the Lean names

Throughout, `R : V → V → Prop` is a digraph. A clique of the `n`-th Sperner power is a finset
`S : Finset (Fin n → V)` in which every ordered pair of distinct members has a coordinate `i` with
`R (u i) (v i)` (`IsSpernerClique`); `w(Rⁿ) = spernerCliqueNumber R n` is the largest size of one;
`C(R) = capacity R = ⨆ n, w(R^{n+1})^{1/(n+1)}`, the supremum over `n ≥ 1`; and
`t(R) = transitiveNumber R` is the largest `k` with an injective `f : Fin k → V` such that
`R (f i) (f j)` whenever `i < j` (`IsTransitiveChain`). All definitions are in
`SpernerCapacity/Defs.lean`, identical to those of `Challenge.lean`. Each Challenge theorem is the
`_internal` theorem of the same name in the module given below, restated in `Solution.lean`.

## 1. The lift (`SpernerCapacity/Lift.lean`)

Let `pts : Fin N → Fin k → V` be injective with `hfwd`: for `i < j` some coordinate `c` has
`R (pts i c) (pts j c)`. For a word `w : Fin m → Fin N`, `liftWord pts m w : Fin (k * m) → V`
concatenates the points `pts (w j)` (block `j`, through `finProdFinEquiv`); it is injective in `w`
(`liftWord_injective`).

If `w ≠ w'` have the same index sum, then `w j ≤ w' j` for all `j` would force `w = w'`
(`Finset.sum_eq_sum_iff_of_le`), so some `j` has `w' j < w j` and, symmetrically, some `j'` has
`w j' < w' j'`. At block `j'` the forward property gives an arc from `liftWord w` to `liftWord w'`;
at block `j` an arc back. So the image of any set of words with a common index sum is a clique
(`clique_of_equal_sums`). The index sum takes `(N - 1) m + 1` values; the largest fiber
(`Finset.exists_max_image`, `Finset.card_eq_sum_card_fiberwise`, `Finset.sum_le_card_nsmul`) has at
least `Nᵐ / ((N - 1) m + 1)` words, which gives **`lift_lemma`** (`lift_lemma_internal`):
`Nᵐ ≤ ((N - 1) m + 1) · |S|`. No finiteness of `V` is needed; decidable equality is opened
classically inside the proof. In ℕ form, `(tᵏ)ᵐ ((N - 1) m + 1) < Nᵐ` gives a clique of the `k·m`-th
power with more than `t^{k·m}` points (`lift_corollary`).

## 2. Cliques and the capacity (`SpernerCapacity/Clique.lean`)

Clique sizes form a nonempty (`cliqueSizes_nonempty`, the empty set) set bounded by `|V|ⁿ`
(`cliqueSizes_bddAbove`, `spernerCliqueNumber_le`), so `w(Rⁿ)` is attained
(`spernerCliqueNumber_attained`) and bounds every clique (`card_le_spernerCliqueNumber`). The terms of
the supremum are at most `|V|` (`root_pow`: `(xⁿ)^{1/n} = x`), so the supremum is bounded
(`capacity_bddAbove`), `w(Rⁿ)^{1/n} ≤ C(R)` for `n ≥ 1` (`le_capacity`), `C(R) ≥ 0`
(`capacity_nonneg`), and **`capacity_le_card`** (`capacity_le_card_internal`): `C(R) ≤ |V|`.
Conversely, a bound on every term bounds `C(R)` (`capacity_le_of_forall`). A clique of the `n`-th
power with more than `tⁿ` points gives `t < C(R)` (`lt_capacity_of_clique`).

**`rpow_le_capacity`** (`rpow_le_capacity_internal`). Let `0 ≤ ρ < N^{1/k}`. Then `ρᵏ < N`, and since
`(ρᵏ/N)ᵐ ((N - 1) m + 1) → 0` there is `m ≥ 1` with `(ρᵏ)ᵐ ((N - 1) m + 1) < Nᵐ`
(`exists_pow_mul_lt`, from `tendsto_pow_const_mul_const_pow_of_abs_lt_one`). The lift gives a clique
of the `k·m`-th power with more than `(ρᵏ)ᵐ` points, so `ρ < w(R^{km})^{1/(km)} ≤ C(R)`. As `ρ` was
arbitrary, `N^{1/k} ≤ C(R)` (`le_of_forall_lt`). With `t < N^{1/k}` for `tᵏ < N` this gives the
counterexample criterion `lt_capacity_of_forward`.

**`transitiveNumber_le_capacity`** (`transitiveNumber_le_capacity_internal`). The transitive number
is bounded by `|V|` (`transitiveSizes_bddAbove`) and attained (`transitiveSizes_nonempty`,
`transitiveNumber_attained`); its chain, read as points of the first power, has the forward
property, so `rpow_le_capacity` at `k = 1` gives `t ≤ C` (`transitive_le_capacity`). The helpers
`le_transitiveNumber` and `transitiveNumber_le` (a longer chain restricts along `Fin.castLE`)
compute `t` from a chain and from the absence of a longer one.

## 3. The rank bound (`SpernerCapacity/Rank.lean`)

**`capacity_le_of_factorization`** (`capacity_le_of_factorization_internal`). Let
`M u v = ∑ i, A u i * B i v` over a field, with `M v v ≠ 0` and `M u v = 0` whenever `R u v`. Put
`Mₙ u v = ∏ i, M (u i) (v i)`; expanding the product of sums, `Mₙ = Aₙ * Bₙ` with
`Aₙ u j = ∏ i, A (u i) (j i)` and `Bₙ j v = ∏ i, B (j i) (v i)`, indexed by `j : Fin n → Fin r`
(`Finset.prod_univ_sum`). On a clique `S` the submatrix of `Mₙ` is diagonal with nonzero diagonal: for
`u ≠ v` some coordinate has `R (u i) (v i)`, so a factor vanishes (`Finset.prod_eq_zero`). It is the
product of an `S × rⁿ` and an `rⁿ × S` block, so `|S| ≤ rⁿ` (`card_le_pow_of_factorization`), hence
`w(Rⁿ) ≤ rⁿ` (`spernerCliqueNumber_le_pow_of_factorization`), every term of the supremum is at most
`r` (`root_pow`, `Real.rpow_le_rpow`), and `C(R) ≤ r` (`capacity_le_of_forall`). Alon's Theorem 1.2
is the case `M u v = ∏_{j ∈ N⁻(v)} (u - j)`; it is not formalized.

## 4. `T₇` (`SpernerCapacity/T7.lean`)

`T7 x y = paley (W x) (W y)` with `W = ![0, 1, 2, 3, 9, 14, 18]` on `ZMod 23`.

- **`T7_isTournament`** (`T7_isTournament_internal`): `decide` over the 49 pairs (each `IsSquare`
  test searches the 23 residues); `-1` is not a square mod 23.
- **`transitiveNumber_T7`** (`transitiveNumber_T7_internal`): the chain `0, 1, 2, 3` is transitive
  (`T7_transitive_four`); no transitive 5-chain exists (`T7_no_transitive_five`, a pruned nested
  search in which each vertex ranges over the common out-neighbours of the previous ones); then
  `le_transitiveNumber` and `transitiveNumber_le`.
- **`T7_square_witness`** (`T7_square_witness_internal`): the 18 points `T7pts`, in residues
  (0,0) (1,0) (14,1) (0,1) (0,9) (1,9) (14,2) (0,2) (9,14) (2,14) (3,0) (9,0) (9,3) (2,3) (3,9) (9,9)
  (18,2) (18,18); the forward property over the 153 pairs (`T7pts_forward`, `decide +kernel`);
  injectivity from it and irreflexivity (`T7pts_injective`).
- **`T7_exists_clique_gt_four_pow`** (`T7_exists_clique_gt_four_pow_internal`): `lift_corollary` with
  `t = 4`, `k = 2`, `N = 18`, `m = 59`, since `(4²)⁵⁹ (17 · 59 + 1) < 18⁵⁹` (`decide +kernel`): a clique of
  `T₇¹¹⁸` with more than `4¹¹⁸` points.
- **`four_lt_capacity_T7`** (`four_lt_capacity_T7_internal`): `lt_capacity_of_clique` on that clique.
- **`sqrt18_le_capacity_T7`** (`sqrt18_le_capacity_T7_internal`): `rpow_le_capacity_internal` at
  `k = 2`, `N = 18`, with `Real.sqrt_eq_rpow`.
- **`capacity_T7_le_five`** (`capacity_T7_le_five_internal`): `capacity_le_of_factorization_internal`
  over `ZMod 2` with `T7A` (rows 10000 / 01000 / 00100 / 00010 / 01110 / 00001 / 01100) and `T7B`
  (rows 1000000 / 0100001 / 0110100 / 0011001 / 0000010); the product has diagonal 1 (`T7AB_diag`)
  and vanishes on every arc (`T7AB_arc`), both by `decide`. Over ℚ the same zero pattern is carried
  by the matrix with rows `e0, e1+e18, e1+e2+e9, −e2+e3+e18, e3+e9, e14, −e2−e9+e18` (W order), whose
  rows satisfy `v18 = v1 − v2 = v3 − v9`; its reduction mod 2 is `T7A · T7B`.
- **`transitiveNumber_lt_capacity_T7`** (`transitiveNumber_lt_capacity_T7_internal`): rewrite with
  `transitiveNumber_T7` and apply `four_lt_capacity_T7`.

## 5. The Paley tournament on 23 vertices (`SpernerCapacity/T23.lean`)

- **`paley_isTournament`** (`paley_isTournament_internal`): `decide` over the 529 pairs.
- **`transitiveNumber_paley`** (`transitiveNumber_paley_internal`): `0, 1, 2, 3, 4` is transitive
  (`paley_transitive_five`); a transitive 6-chain can be translated to start at `0`
  (`paley_translate`), and the pruned nested search over common out-neighbourhoods finds none
  (`paley_no_transitive_six`).
- **`sqrt29_le_capacity_paley`** (`sqrt29_le_capacity_paley_internal`): the 29 points `paleyPts`
  have the forward property (`paleyPts_forward`, 406 pairs) and are injective (`paleyPts_injective`);
  `rpow_le_capacity_internal` at `k = 2`.
- **`five_lt_capacity_paley`** (`five_lt_capacity_paley_internal`): `lt_capacity_of_forward`, since
  `29 > 5²`.

## 6. Tournaments on at most six vertices (`SpernerCapacity/Six.lean`, `SixCover.lean`)

**`capacity_eq_transitiveNumber_of_card_le_six`** (`capacity_eq_transitiveNumber_of_card_le_six_internal`). A
tournament on `Fin n` is encoded by its bits on the pairs `a < b` (`six_code`; equal codes give equal relations on the
listed pairs, `six_code_eq`). The Mathlib-free leaf `SixCover.lean` holds, for each `n ≤ 6`, the pairs, the `n!`
permutations, and one representative per isomorphism class (1, 1, 1, 2, 4, 12, 56 of them) with a factorization over
`ZMod 2` of rank `t` (rows of `A` and columns of `B` as bitmasks) and a transitive chain of length `t`; the kernel
checks the data (`six_dataOK`: tournament, diagonal 1, zeros on the arcs, the chain transitive) and the coverage bitset
(`six_cover`: the `or` of `1 <<< code` over every representative and every permutation equals `2^{2^{n(n−1)/2}} − 1`),
both by `decide +kernel`. The reflection lemma `six_cover_spec` (from `Nat.testBit_or`, `Nat.one_shiftLeft`,
`Nat.testBit_two_pow`, `Nat.testBit_two_pow_sub_one`) turns the set bit of a given tournament's code into a
representative and a permutation `σ` with `R u v ↔ rep (σ u) (σ v)`; `six_bridge` composes the factorization with `σ`
(`A' v i = A (σ v) i`) and applies `capacity_le_of_factorization_internal` for `C(R) ≤ t`, pulls the chain back along `σ`
(surjective by `Finite.injective_iff_surjective`) and applies `le_transitiveNumber` for `t ≤ t(R)`, and closes with
`transitiveNumber_le_capacity_internal`; `six_fin` matches over `k ≤ 6`. A finite type of at most six elements is
relabelled onto `Fin (card V)` by `Fintype.equivFin`, and `capacity_equiv`, `transitiveNumber_equiv` transport the
statement (`six_spernerCliqueNumber_equiv` maps cliques through `Equiv.arrowCongr`).

**`seven_le_card_of_transitiveNumber_lt_capacity`** (`seven_le_card_of_transitiveNumber_lt_capacity_internal`): if
`card V ≤ 6` the previous theorem makes `t(R) = C(R)`, contradicting `t(R) < C(R)`.

## 7. On paper (the note, with certificates under `note/certificates/`)

- `tr(T₇²) = 18` exactly, with 84 optimal sets (three engines and a standard-library exhaustive
  checker; the count from two engines). Rank 4 is impossible over every field since `18 > 4²`; so the
  GF(2) factorization above is optimal and `√18 ≤ C(T₇) ≤ 5`. The degree bound gives only 6.
- `w(T₇²) = 7`: a clique of the second power is the graph of a partial injection, and a 7-point one
  is the graph of an anti-automorphism; `T₇` has exactly one, `(0 3)(1 18)(9 14)`, and `Aut(T₇)` is
  trivial (computed over all `7!` permutations).
- Certificate 0004 re-derives the six-vertex theorem on paper from two independent class lists (complete by
  `∑ n!/|Aut| = 2^{n(n-1)/2}`), a cross-check of the kernel route of section 6.
- On seven vertices, 455 of the 456 classes have a rank-`t` GF(2) matrix; the remaining class is
  `T₇`. So `T₇` is the unique smallest tournament with `C > t`, every proper subtournament of it has
  `C = t`, and `C(Q₇) = 3` (the GF(2) matrix `I` plus the converse adjacency matrix has rank 3).
- `75 ≤ tr(T₇³) ≤ 125`, `16 ≤ w(T₇³) ≤ 19` (the upper bound by two SAT solvers), and the least `n` with
  `w(T₇ⁿ) > 4ⁿ` lies in `[6, 76]` (76 from the largest index-sum class at `m = 38`).
- The Paley tournament on 27 elements has `t = 5` (Sanchez-Flores 1998) and the 27-point anti-diagonal
  clique of its second Sperner power; deleting `0` gives a 26-vertex example.
