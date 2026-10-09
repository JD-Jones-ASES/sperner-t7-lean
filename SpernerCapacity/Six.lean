module

public import SpernerCapacity.Rank
public import SpernerCapacity.SixCover

/-!
# Tournaments on at most six vertices

Every tournament on at most six vertices has `C(T) = t(T)`. For each of the
1, 1, 2, 4, 12, 56 isomorphism classes on 1, …, 6 vertices there is a matrix over `ZMod 2` with
nonzero diagonal, zeros on the arcs and rank `t(T)`, so `C(T) ≤ t(T)` by the rank bound, and
`t(T) ≤ C(T)` always.

The kernel route. A tournament on `Fin n` is encoded by its bits on the listed pairs `a < b`
(`six_code`). The leaf `SixCover` holds, for each `n ≤ 6`, the pairs, the `n!` permutations and one
representative per class with a factorization over `ZMod 2` (rows of `A`, columns of `B` as
bitmasks) and a transitive chain of the same length `t`; the kernel checks the data (`six_dataOK`)
and the coverage bitset (`six_cover`, the `or` of `1 <<< code` over all representatives and all
permutations, equal to `2 ^ (2 ^ m) - 1`). Here `six_cover_spec` reads off, for the code of a given
tournament `R`, a representative and a permutation `σ` with `R u v ↔ rep (σ u) (σ v)`
(`six_code_eq`); the factorization composed with `σ` gives `C(R) ≤ t` through
`capacity_le_of_factorization_internal`, the chain pulled back along `σ` gives `t ≤ t(R)`, and
`t(R) ≤ C(R)` closes the circle (`six_bridge`). Any finite type of size at most six is relabelled
onto `Fin n` by `capacity_equiv` and `transitiveNumber_equiv`.
-/

@[expose] public section

namespace SpernerCapacity

/-! ### Relabelling -/

/-- The clique number is invariant under relabelling. -/
theorem six_spernerCliqueNumber_equiv {V W : Type*} (e : V ≃ W) (R : V → V → Prop) (n : ℕ) :
    spernerCliqueNumber (fun x y : W => R (e.symm x) (e.symm y)) n = spernerCliqueNumber R n := by
  unfold spernerCliqueNumber
  congr 1
  ext c
  let E : (Fin n → W) ≃ (Fin n → V) := Equiv.arrowCongr (Equiv.refl _) e.symm
  have hE : ∀ u : Fin n → W, ∀ i, E u i = e.symm (u i) := fun _ _ => rfl
  have hE' : ∀ u : Fin n → V, ∀ i, E.symm u i = e (u i) := fun _ _ => rfl
  constructor
  · rintro ⟨S, rfl, hS⟩
    refine ⟨S.map E.toEmbedding, Finset.card_map _, ?_⟩
    intro u hu v hv huv
    rw [Finset.mem_map_equiv] at hu hv
    obtain ⟨i, hi⟩ := hS _ hu _ hv (fun h => huv (E.symm.injective h))
    refine ⟨i, ?_⟩
    simpa only [hE', Equiv.symm_apply_apply] using hi
  · rintro ⟨S, rfl, hS⟩
    refine ⟨S.map E.symm.toEmbedding, Finset.card_map _, ?_⟩
    intro u hu v hv huv
    rw [Finset.mem_map_equiv, Equiv.symm_symm] at hu hv
    obtain ⟨i, hi⟩ := hS _ hu _ hv (fun h => huv (E.injective h))
    exact ⟨i, by simpa only [hE] using hi⟩

/-- The capacity is invariant under relabelling. -/
theorem capacity_equiv {V W : Type*} [Fintype V] [Fintype W] (e : V ≃ W) (R : V → V → Prop) :
    capacity (fun x y : W => R (e.symm x) (e.symm y)) = capacity R := by
  simp only [capacity, six_spernerCliqueNumber_equiv]

/-- The transitive number is invariant under relabelling. -/
theorem transitiveNumber_equiv {V W : Type*} (e : V ≃ W) (R : V → V → Prop) :
    transitiveNumber (fun x y : W => R (e.symm x) (e.symm y)) = transitiveNumber R := by
  unfold transitiveNumber
  congr 1
  ext k
  constructor
  · rintro ⟨f, hf, hc⟩
    exact ⟨e.symm ∘ f, e.symm.injective.comp hf, fun i j hij => hc i j hij⟩
  · rintro ⟨f, hf, hc⟩
    refine ⟨e ∘ f, e.injective.comp hf, fun i j hij => ?_⟩
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hc i j hij

/-! ### The Boolean checks -/

theorem six_all_spec (k : ℕ) (p : ℕ → Bool) : six_all k p = true ↔ ∀ x < k, p x = true := by
  induction k with
  | zero => exact ⟨fun _ x hx => absurd hx (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ k ih =>
    change (six_all k p && p k) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with h | rfl
      · exact h1 x h
      · exact h2
    · intro h
      exact ⟨fun x hx => h x (by omega), h k (by omega)⟩

theorem six_listAll_spec {α : Type} (l : List α) (p : α → Bool) :
    six_listAll l p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => exact ⟨fun _ a ha => absurd ha List.not_mem_nil, fun _ => rfl⟩
  | cons a l ih =>
    change (p a && six_listAll l p) = true ↔ _
    rw [Bool.and_eq_true, ih, List.forall_mem_cons]

theorem six_listAny_spec {α : Type} (l : List α) (p : α → Bool) :
    six_listAny l p = true ↔ ∃ a ∈ l, p a = true := by
  induction l with
  | nil =>
    exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨a, ha, _⟩ => absurd ha List.not_mem_nil⟩
  | cons a l ih =>
    change (p a || six_listAny l p) = true ↔ _
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨b, hb, h⟩)
      · exact ⟨a, List.mem_cons_self, h⟩
      · exact ⟨b, List.mem_cons_of_mem _ hb, h⟩
    · rintro ⟨b, hb, h⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl h
      · exact Or.inr ⟨b, hb, h⟩

/-! ### Codes -/

theorem six_code_lt (g : ℕ → ℕ → Bool) (ps : List (ℕ × ℕ)) : six_code g ps < 2 ^ ps.length := by
  induction ps with
  | nil => exact Nat.one_pos
  | cons q ps ih =>
    change 2 * six_code g ps + (g q.1 q.2).toNat < 2 ^ (ps.length + 1)
    have hb := Bool.toNat_le (g q.1 q.2)
    rw [Nat.pow_succ]
    omega

theorem six_code_eq {g h : ℕ → ℕ → Bool} {ps : List (ℕ × ℕ)} (H : six_code g ps = six_code h ps) :
    ∀ p ∈ ps, g p.1 p.2 = h p.1 p.2 := by
  induction ps with
  | nil => intro p hp; exact absurd hp List.not_mem_nil
  | cons q ps ih =>
    have H' : 2 * six_code g ps + (g q.1 q.2).toNat = 2 * six_code h ps + (h q.1 q.2).toNat := H
    have hq : g q.1 q.2 = h q.1 q.2 ∧ six_code g ps = six_code h ps := by
      cases hg : g q.1 q.2 <;> cases hh : h q.1 q.2 <;>
        simp only [hg, hh, Bool.toNat_false, Bool.toNat_true] at H' <;>
        first | exact ⟨rfl, by omega⟩ | (exfalso; omega)
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hq.1
    · exact ih hq.2 p hp

theorem six_coverPerms_spec (code : ℕ) (ps : List (ℕ × ℕ)) (perms : List (List ℕ)) (c : ℕ)
    (h : Nat.testBit (six_coverPerms code ps perms) c = true) :
    ∃ l ∈ perms, six_relabel code l ps = c := by
  induction perms with
  | nil =>
    have h0 : six_coverPerms code ps [] = 0 := rfl
    rw [h0, Nat.zero_testBit] at h
    exact absurd h Bool.false_ne_true
  | cons l ls ih =>
    have h' : Nat.testBit ((1 <<< six_relabel code l ps) ||| six_coverPerms code ps ls) c = true :=
      h
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact ⟨l, List.mem_cons_self, of_decide_eq_true h'⟩
    · obtain ⟨l', hl', e⟩ := ih h'
      exact ⟨l', List.mem_cons_of_mem _ hl', e⟩

theorem six_cover_spec (ps : List (ℕ × ℕ)) (perms : List (List ℕ)) (reps : List SixRep) (c : ℕ)
    (h : Nat.testBit (six_cover ps perms reps) c = true) :
    ∃ r ∈ reps, ∃ l ∈ perms, six_relabel r.code l ps = c := by
  induction reps with
  | nil =>
    have h0 : six_cover ps perms [] = 0 := rfl
    rw [h0, Nat.zero_testBit] at h
    exact absurd h Bool.false_ne_true
  | cons r rs ih =>
    have h' : Nat.testBit (six_coverPerms r.code ps perms ||| six_cover ps perms rs) c = true := h
    rw [Nat.testBit_or, Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact ⟨r, List.mem_cons_self, six_coverPerms_spec _ _ _ _ h'⟩
    · obtain ⟨r', hr', hl⟩ := ih h'
      exact ⟨r', List.mem_cons_of_mem _ hr', hl⟩

/-! ### The factorization over `ZMod 2` -/

theorem six_zmod_step (d x y : Bool) :
    ((if d then (1 : ZMod 2) else 0) + (if x then 1 else 0) * (if y then 1 else 0)) =
      if xor d (x && y) then 1 else 0 := by
  cases d <;> cases x <;> cases y <;> decide

theorem six_sum_dot (t a b : ℕ) :
    (∑ i : Fin t, (if Nat.testBit a i then (1 : ZMod 2) else 0) *
        (if Nat.testBit b i then 1 else 0)) = if six_dot t a b then 1 else 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    exact six_zmod_step _ _ _

/-! ### The bridge: checked data for `n` vertices give `C = t` for every tournament on `Fin n` -/

theorem six_bridge (n : ℕ) (ps : List (ℕ × ℕ)) (perms : List (List ℕ)) (reps : List SixRep)
    (hok : six_dataOK n ps perms reps = true)
    (hcov : six_cover ps perms reps = six_full ps.length)
    (R : Fin n → Fin n → Prop) (hT : IsTournament R) : capacity R = transitiveNumber R := by
  classical
  obtain ⟨⟨hps, hperms⟩, hreps⟩ : (six_pairsOK n ps = true ∧
      six_listAll perms (six_permOK n) = true) ∧ six_listAll reps (six_repOK n) = true := by
    unfold six_dataOK at hok
    simpa only [Bool.and_eq_true] using hok
  -- the code of `R` is the code of a relabelled representative
  let g : ℕ → ℕ → Bool := fun a b =>
    if h : a < n ∧ b < n then decide (R ⟨a, h.1⟩ ⟨b, h.2⟩) else false
  have hbit : Nat.testBit (six_cover ps perms reps) (six_code g ps) = true := by
    rw [hcov, six_full, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (six_code_lt g ps)
  obtain ⟨r, hr, l, hl, hrl⟩ := six_cover_spec ps perms reps _ hbit
  have hrl' : six_code (fun a b => six_relB r.code (six_get l a) (six_get l b)) ps =
      six_code g ps := hrl
  have hcode := six_code_eq hrl'
  -- the permutation
  have hpermOK := (six_listAll_spec _ _).1 hperms l hl
  unfold six_permOK at hpermOK
  rw [six_all_spec] at hpermOK
  have hσlt : ∀ x < n, six_get l x < n := fun x hx => by
    have := hpermOK x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  have hσinj : ∀ x < n, ∀ y < n, six_get l x = six_get l y → x = y := fun x hx y hy hxy => by
    have := hpermOK x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    have := (six_all_spec _ _).1 this.2 y hy
    simpa [hxy] using this
  -- the representative
  have hrepOK := (six_listAll_spec _ _).1 hreps r hr
  unfold six_repOK at hrepOK
  simp only [Bool.and_eq_true] at hrepOK
  obtain ⟨⟨htour, hfac⟩, hchain⟩ := hrepOK
  rw [six_all_spec] at htour hfac hchain
  have hirr : ∀ x < n, six_relB r.code x x = false := fun x hx => by
    have := htour x hx
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.1
  have hanti : ∀ x < n, ∀ y < n, x ≠ y →
      (six_relB r.code x y = true ↔ ¬ six_relB r.code y x = true) := fun x hx y hy hxy => by
    have := htour x hx
    simp only [Bool.and_eq_true] at this
    have := (six_all_spec _ _).1 this.2 y hy
    simp only [Bool.or_eq_true, decide_eq_true_eq, hxy, false_or, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq] at this
    cases h1 : six_relB r.code x y <;> cases h2 : six_relB r.code y x <;> simp_all
  have hdiag : ∀ x < n, six_dot r.t (six_get r.arows x) (six_get r.bcols x) = true :=
    fun x hx => by
      have := hfac x hx
      simp only [Bool.and_eq_true] at this
      exact this.1
  have harc : ∀ x < n, ∀ y < n, six_relB r.code x y = true →
      six_dot r.t (six_get r.arows x) (six_get r.bcols y) = false := fun x hx y hy hxy => by
    have := hfac x hx
    simp only [Bool.and_eq_true] at this
    have := (six_all_spec _ _).1 this.2 y hy
    simpa [hxy] using this
  have hchainlt : ∀ i < r.t, six_get r.chain i < n := fun i hi => by
    have := hchain i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  have hchainR : ∀ i < r.t, ∀ j < r.t, i < j →
      six_relB r.code (six_get r.chain i) (six_get r.chain j) = true := fun i hi j hj hij => by
    have := hchain i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    have := (six_all_spec _ _).1 this.2 j hj
    simpa [hij] using this
  -- `R` is the relabelled representative
  have keylt : ∀ u v : Fin n, (u : ℕ) < v →
      (R u v ↔ six_relB r.code (six_get l u) (six_get l v) = true) := by
    intro u v huv
    have hp := (six_all_spec _ _).1 ((six_all_spec _ _).1 hps u u.2) v v.2
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt,
      six_listAny_spec, Bool.and_eq_true, decide_eq_true_eq] at hp
    rcases hp with hp | ⟨p, hp, hp1, hp2⟩
    · omega
    · have := hcode p hp
      rw [hp1, hp2] at this
      rw [this]
      simp [g, u.2, v.2]
  have key : ∀ u v : Fin n, u ≠ v →
      (R u v ↔ six_relB r.code (six_get l u) (six_get l v) = true) := by
    intro u v huv
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne huv) with h | h
    · exact keylt u v h
    · rw [hT.2 u v huv, keylt v u h,
        hanti _ (hσlt u u.2) _ (hσlt v v.2) (fun e => huv (Fin.ext (hσinj _ u.2 _ v.2 e)))]
  -- `C ≤ t` by the factorization
  have hle : capacity R ≤ (r.t : ℝ) := by
    refine capacity_le_of_factorization_internal R (F := ZMod 2)
      (fun (v : Fin n) (i : Fin r.t) =>
        if Nat.testBit (six_get r.arows (six_get l v)) i then 1 else 0)
      (fun (i : Fin r.t) (v : Fin n) =>
        if Nat.testBit (six_get r.bcols (six_get l v)) i then 1 else 0) ?_ ?_
    · intro v
      rw [six_sum_dot, hdiag _ (hσlt v v.2)]
      decide
    · intro u v huv
      have hne : u ≠ v := by
        rintro rfl
        exact hT.1 u huv
      rw [six_sum_dot, harc _ (hσlt u u.2) _ (hσlt v v.2) ((key u v hne).1 huv)]
      decide
  -- `t ≤ t(R)` by the chain
  let σF : Fin n → Fin n := fun x => ⟨six_get l x, hσlt x x.2⟩
  have hσFinj : Function.Injective σF := fun x y h =>
    Fin.ext (hσinj x x.2 y y.2 (congrArg Fin.val h))
  have hσFsurj : Function.Surjective σF := Finite.injective_iff_surjective.mp hσFinj
  let f : Fin r.t → Fin n := fun i =>
    Function.surjInv hσFsurj ⟨six_get r.chain i, hchainlt i i.2⟩
  have hf : ∀ i, six_get l (f i) = six_get r.chain i := fun i =>
    congrArg Fin.val (Function.surjInv_eq hσFsurj _)
  have hfR : ∀ i j : Fin r.t, i < j → R (f i) (f j) := by
    intro i j hij
    have hrel := hchainR i i.2 j j.2 hij
    have hne : f i ≠ f j := by
      intro h
      have h1 := hf i
      rw [h, hf j] at h1
      rw [h1, hirr _ (hchainlt i i.2)] at hrel
      exact Bool.false_ne_true hrel
    rw [key _ _ hne, hf, hf]
    exact hrel
  have hfinj : Function.Injective f := by
    intro i j h
    by_contra hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have := hfR i j hlt
      rw [h] at this
      exact hT.1 _ this
    · have := hfR j i hlt
      rw [h] at this
      exact hT.1 _ this
  have ht : r.t ≤ transitiveNumber R := le_transitiveNumber R f hfinj hfR
  have ht' : (r.t : ℝ) ≤ transitiveNumber R := by exact_mod_cast ht
  exact le_antisymm (hle.trans ht') (transitiveNumber_le_capacity_internal R)

/-- Every tournament on `Fin k`, `k ≤ 6`, satisfies `C = t`. -/
theorem six_fin (k : ℕ) (hk : k ≤ 6) (R : Fin k → Fin k → Prop) (hT : IsTournament R) :
    capacity R = transitiveNumber R := by
  match k, hk with
  | 0, _ => exact six_bridge 0 _ _ _ six_data0 six_cover0 R hT
  | 1, _ => exact six_bridge 1 _ _ _ six_data1 six_cover1 R hT
  | 2, _ => exact six_bridge 2 _ _ _ six_data2 six_cover2 R hT
  | 3, _ => exact six_bridge 3 _ _ _ six_data3 six_cover3 R hT
  | 4, _ => exact six_bridge 4 _ _ _ six_data4 six_cover4 R hT
  | 5, _ => exact six_bridge 5 _ _ _ six_data5 six_cover5 R hT
  | 6, _ => exact six_bridge 6 _ _ _ six_data6 six_cover6 R hT
  | k + 7, h => exact absurd h (by omega)

/-- Every tournament on `Fin 6` satisfies `C = t`. -/
theorem capacity_eq_transitiveNumber_fin6 (R : Fin 6 → Fin 6 → Prop) (hT : IsTournament R) :
    capacity R = transitiveNumber R := six_fin 6 le_rfl R hT

/-- Every tournament on at most six vertices satisfies `C = t`. -/
theorem capacity_eq_transitiveNumber_of_card_le_six_internal {V : Type*} [Fintype V] (R : V → V → Prop)
    (hT : IsTournament R) (hV : Fintype.card V ≤ 6) : capacity R = transitiveNumber R := by
  let e := Fintype.equivFin V
  have hT' : IsTournament (fun x y : Fin (Fintype.card V) => R (e.symm x) (e.symm y)) :=
    ⟨fun x => hT.1 _, fun x y hxy => hT.2 _ _ (e.symm.injective.ne hxy)⟩
  rw [← capacity_equiv e R, ← transitiveNumber_equiv e R]
  exact six_fin _ hV _ hT'

/-- A tournament whose capacity exceeds its transitive number has at least seven vertices. -/
theorem seven_le_card_of_transitiveNumber_lt_capacity_internal {V : Type*} [Fintype V]
    (R : V → V → Prop) (hT : IsTournament R) (h : (transitiveNumber R : ℝ) < capacity R) :
    7 ≤ Fintype.card V := by
  by_contra hlt
  have heq := capacity_eq_transitiveNumber_of_card_le_six_internal R hT (by omega)
  rw [heq] at h
  exact lt_irrefl _ h

end SpernerCapacity

end
