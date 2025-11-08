import Mathlib

open scoped Polynomial

/-
open ArchimedeanClass

variable {F G : Type*}
variable [Ring F] [Ring G] [LinearOrder F] [LinearOrder G] [IsOrderedRing F] [IsOrderedRing G]
variable (u : ArchimedeanClass F →o ArchimedeanClass G)

structure Partial where
  domain : Subring F
  toFun : domain →+*o G
  archimedeanMk_eq : ∀ x, mk (toFun x) = u (mk x.val)

def Partial.extend (f : F →+* G) (hf : ∀ x, ArchimedeanClass.mk (f x) = u (ArchimedeanClass.mk x))
    (p : Partial u) (x : F) (y : Subring.closure (p.domain ∪ {x})) : G := by sorry

theorem upgradeHom :
    ∃ g : F →+*o G, ∀ x, mk (g x) = u (mk x) := by sorry
-/

/-theorem lemma4_mul {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid]
    {ι : Type*} (s : Finset ι) (β : ι → G) (t : ι → ℕ)
    (ht )-/


instance {K : Type*} [Field K] : FaithfulSMul (Polynomial K) (RatFunc K) := by
  have : Polynomial.algebra K K = Algebra.id (Polynomial K) := by
    apply Algebra.algebra_ext
    simp
  rw [← this]
  exact RatFunc.faithfulSMul K K

namespace IsLocalRing.ResidueField

@[elab_as_elim, induction_eliminator]
theorem ind {R : Type*} [CommRing R] [IsLocalRing R] {motive : IsLocalRing.ResidueField R → Prop}
    (residue : ∀ (a : R), motive (IsLocalRing.residue R a)) :
    ∀ (a : IsLocalRing.ResidueField R), motive a :=
  Quotient.ind residue

end IsLocalRing.ResidueField



variable {K : Type*} [Field K]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (V : Valuation K Γ)

theorem exists_valuation_extension.{u} (L : Type u) [Field L] [Algebra K L] :
  ∃ (Γ' : Type u) (_ : LinearOrderedCommGroupWithZero Γ') (V' : Valuation L Γ'),
  Valuation.HasExtension V V' := sorry


variable {ι : Type*} [LinearOrder ι] --[IsWellOrder ι (· < ·)]

def IsPseudoConv (a : ι → K) : Prop := ∀ ⦃i j k⦄, i < j → j < k → V (a j - a k) < V (a i - a j)

theorem IsPseudoConv.sub_const {a : ι → K} (h : IsPseudoConv V a) (c : K) :
    IsPseudoConv V (fun i ↦ a i - c) := by
  unfold IsPseudoConv at ⊢ h
  intro i j k hij hjk
  convert h hij hjk using 1 <;> simp

theorem IsPseudoConv.const_sub {a : ι → K} (h : IsPseudoConv V a) (c : K) :
    IsPseudoConv V (fun i ↦ c - a i) := by
  unfold IsPseudoConv at ⊢ h
  intro i j k hij hjk
  convert h hij hjk using 1 <;> simp [Valuation.map_sub_swap]

theorem IsPseudoConv.lemma1 [NoMaxOrder ι] {a : ι → K} (h : IsPseudoConv V a) :
    (∀ i j, i < j → V (a j) < V (a i)) ∨ (∃ l, (∀ i, l ≤ i → V (a l) = V (a i)) ∧ V (a l) ≠ 0) := by
  rw [or_iff_not_imp_left]
  intro hleft
  simp_rw [not_forall, exists_prop, not_lt] at hleft
  obtain ⟨i, j, hlt, hle⟩ := hleft
  use j
  have hleft (k) (hk : j ≤ k) : V (a j) = V (a k) := by
    obtain rfl | hk := eq_or_lt_of_le hk
    · simp
    contrapose! h
    rw [← V.map_neg (a k)] at h
    obtain h1 := V.map_add_of_distinct_val h
    rw [Valuation.map_neg, ← sub_eq_add_neg] at h1 -- extract this
    have h1 : V (a j) ≤ V (a j - a k) := by  simp [h1]
    obtain h2 := V.map_sub_le hle le_rfl
    obtain h3 := h2.trans h1
    simpa [IsPseudoConv] using ⟨i, j, hlt, k, hk, h3⟩
  constructor
  · exact hleft
  by_contra! h0
  rw [h0] at hleft
  obtain ⟨k, hk⟩ := exists_gt j
  obtain ⟨l, hl⟩ := exists_gt k
  obtain hj0 := (map_eq_zero _).mp (hleft j (le_refl _)).symm
  obtain hk0 := (map_eq_zero _).mp (hleft k hk.le).symm
  obtain hl0 := (map_eq_zero _).mp (hleft l (hk.trans hl).le).symm
  specialize h hk hl
  simp [hj0, hk0, hl0] at h

theorem IsPseudoConv.lemma1_prod [NoMaxOrder ι] [Nonempty ι] {a : ι → K}
    (h : IsPseudoConv V a) (s : Multiset K) :
    (∃ i, ∀ j k, i ≤ j → j < k → V (s.map fun c ↦ a k - c).prod < V (s.map fun c ↦ a j - c).prod) ∨
    (∃ l, ∀ i, l ≤ i → V (s.map fun c ↦ a l - c).prod = V (s.map fun c ↦ a i - c).prod) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons c s ih =>
    simp_rw [Multiset.map_cons, Multiset.prod_cons, V.map_mul]
    obtain ⟨i, ih⟩ | ⟨i, ih⟩ := ih
    · obtain h | ⟨l, h, _⟩ := IsPseudoConv.lemma1 V <| IsPseudoConv.sub_const V h c
      · left
        use i
        intro j k hij hjk
        apply mul_lt_mul_of_nonneg (h j k hjk) (ih j k hij hjk) zero_le' zero_le'
      · obtain hl | hl := eq_or_lt_of_le (show 0 ≤ V (a l - c) by simp)
        · right
          use l
          intro i hi
          rw [← h i hi]
          simp [← hl]
        left
        use max i l
        intro j k hij hjk
        rw [← h j (le_of_max_le_right hij)]
        rw [← h k ((le_of_max_le_right hij).trans hjk.le)]
        apply mul_lt_mul_of_pos_left (ih j k (le_of_max_le_left hij) hjk) hl
    · obtain h | ⟨l, h, _⟩ := IsPseudoConv.lemma1 V <| IsPseudoConv.sub_const V h c
      · obtain hl | hl := eq_or_lt_of_le
          (show 0 ≤ V (Multiset.map (fun c ↦ a i - c) s).prod by simp)
        · right
          use i
          intro j hj
          rw [← ih j hj]
          simp [← hl]
        · left
          use i
          intro j k hij hjk
          rw [← ih j hij]
          rw [← ih k (hij.trans hjk.le)]
          apply mul_lt_mul_of_pos_right (h j k hjk) hl
      · right
        use max i l
        intro j hj
        congrm ?_ * ?_
        · trans V (a l - c)
          · exact (h (max i l) (by simp)).symm
          · exact h j (le_of_max_le_right hj)
        · trans V (Multiset.map (fun c ↦ a i - c) s).prod
          · exact (ih (max i l) (by simp)).symm
          · exact ih j (le_of_max_le_left hj)

theorem lemma1_prod' [Nonempty ι] {a : ι → K} (s : Multiset K)
    (hs : ∀ c ∈ s, ∃ l, (∀ i, l ≤ i → V (a l - c) = V (a i - c)) ∧ V (a l - c) ≠ 0) :
    ∃ l, (∀ i, l ≤ i → V (s.map fun c ↦ a l - c).prod = V (s.map fun c ↦ a i - c).prod)
        ∧ V (s.map fun c ↦ a l - c).prod ≠ 0 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons c s ih =>
    simp_rw [Multiset.mem_cons, forall_eq_or_imp] at hs
    obtain ⟨⟨l, hl, hl2⟩, hs⟩ := hs
    simp_rw [Multiset.map_cons, Multiset.prod_cons, V.map_mul]
    obtain ⟨i, ih, ih2⟩ := ih hs
    use max i l
    constructor
    · intro j hj
      congrm ?_ * ?_
      · trans V (a l - c)
        · exact (hl (max i l) (by simp)).symm
        · exact hl j (le_of_max_le_right hj)
      · trans V (Multiset.map (fun c ↦ a i - c) s).prod
        · exact (ih (max i l) (by simp)).symm
        · exact ih j (le_of_max_le_left hj)
    · apply mul_ne_zero
      · rw [← hl (max i l) (by simp)]
        exact hl2
      · rw [← ih (max i l) (by simp)]
        exact ih2

theorem IsPseudoConv.lemma2 {a : ι → K} (h : IsPseudoConv V a)
    {i j k : ι} (hij : i < j) (hjk : j ≤ k) :
    V (a i - a k) = V (a i - a j) := by
  obtain rfl | hjk := eq_or_lt_of_le hjk
  · simp
  rw [show a i - a k = a i - a j + (a j - a k) by simp]
  rw [V.map_add_of_distinct_val (h hij hjk).ne.symm]
  simpa using (h hij hjk).le

theorem IsPseudoConv.lemma2' {a : ι → K} (h : IsPseudoConv V a)
    {i j k : ι} (hij : i < j) (hik : i < k) :
    V (a i - a j) = V (a i - a k) := by
  obtain hjk | hjk := le_total j k
  · exact (h.lemma2 V hij hjk).symm
  · exact h.lemma2 V hik hjk

variable [NoMaxOrder ι]

/-theorem IsPseudoConv.lemma5 {a : ι → K} (h : IsPseudoConv V a) (p : Polynomial K) :
    ∃ u : ι, IsPseudoConv V fun (i : Set.Ici u) ↦ p.eval (a i) := by sorry-/

noncomputable
def γ (a : ι → K) (i : ι) : Γ := V (a i - a (exists_gt i).choose)

theorem IsPseudoConv.γ_eq {a : ι → K} (h : IsPseudoConv V a) {i j : ι} (hij : i < j) :
    γ V a i = V (a i - a j) :=
  h.lemma2' V (exists_gt i).choose_spec hij

theorem IsPseudoConv.γ_strictAnti {a : ι → K} (h : IsPseudoConv V a) : StrictAnti (γ V a) := by
  intro i j hij
  obtain ⟨k, hk⟩ := exists_gt j
  rw [h.γ_eq V (hij.trans hk), h.γ_eq V hk]
  rw [show a i - a k = a i - a j + (a j - a k) by simp]
  rw [V.map_add_of_distinct_val (h hij hk).ne.symm]
  simpa using h hij hk

theorem IsPseudoConv.γ_pos {a : ι → K} (h : IsPseudoConv V a) (i : ι) : 0 < γ V a i := by
  obtain ⟨j, hj⟩ := exists_gt i
  exact zero_le'.trans_lt (h.γ_strictAnti V hj)

def HasLimit (a : ι → K) (x : K) : Prop := ∀ i, V (x - a i) = γ V a i

def Breadth (a : ι → K) : Set K := {y | ∀ i, V y < γ V a i}

theorem IsPseudoConv.lemma3 {a : ι → K} (h : IsPseudoConv V a) {x : K} (hx : HasLimit V a x)
    {z : K} : HasLimit V a z ↔ x - z ∈ Breadth V a := by
  obtain rfl | hxz := eq_or_ne x z
  · simpa [Breadth, hx] using h.γ_pos V
  constructor
  · intro hz
    rw [Breadth, Set.mem_setOf_eq]
    intro i
    obtain ⟨j, hj⟩ := exists_gt i
    rw [show x - z = x - a j - (z - a j) by simp]
    apply Valuation.map_sub_lt
    · simpa [hx j] using h.γ_strictAnti V hj
    · simpa [hz j] using h.γ_strictAnti V hj
  · intro hz i
    rw [← hx i]
    rw [show z - a i = (x - a i) - (x - z) by simp]
    apply V.map_sub_eq_of_lt_left
    rw [hx i]
    rw [Breadth, Set.mem_setOf_eq] at hz
    exact hz i

variable {L : Type*} [Field L]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ'] (V' : Valuation L Γ')
variable [Algebra K L] [Valuation.HasExtension V V']

def resF := IsLocalRing.ResidueField V.integer
def resL := IsLocalRing.ResidueField V'.integer

noncomputable
def residueMap : IsLocalRing.ResidueField V.integer →+* IsLocalRing.ResidueField V'.integer :=
  IsLocalRing.ResidueField.map (algebraMap V.integer V'.integer)

omit [NoMaxOrder ι] in
theorem IsPseudoConv.iff {a : ι → K} :
    IsPseudoConv V a ↔ IsPseudoConv V' (algebraMap K L ∘ a) := by
  unfold IsPseudoConv
  simp [← map_sub, Valuation.HasExtension.val_map_lt_iff V V']

omit [NoMaxOrder ι] in
theorem IsPseudoConv.Ici {a : ι → K} (h : IsPseudoConv V a) (l : ι) :
    IsPseudoConv V (fun (i : Set.Ici l) ↦ a i) := by
  intro i j k hij hjk
  apply h (by simpa using hij) (by simpa using hjk)

theorem IsPseudoConv.lemma1_poly [Nonempty ι] {a : ι → K}
    (h : IsPseudoConv V a) (p : K[X]) :
    (∃ i, ∀ j k, i ≤ j → j < k → V (p.eval (a k)) < V (p.eval (a j))) ∨
    (∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) := by
  obtain rfl | hp0 := eq_or_ne p 0
  · simp
  obtain ⟨Γ', _, V', _⟩ := exists_valuation_extension V p.SplittingField
  simp_rw [← Valuation.HasExtension.val_map_lt_iff V V']
  simp_rw [← Valuation.HasExtension.val_map_eq_iff V V']
  simp_rw [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  simp_rw [Polynomial.aeval_eq_prod_aroots_sub_of_splits (Polynomial.SplittingField.splits p)]
  simp_rw [V'.map_mul]
  have h0 : (algebraMap K p.SplittingField) p.leadingCoeff ≠ 0 := by simpa using hp0
  simp only [mul_eq_mul_left_iff, map_eq_zero, h0, or_false]
  simp_rw [mul_lt_mul_iff_of_pos_left (V'.pos_iff.mpr h0)]
  apply ((IsPseudoConv.iff V V').mp h).lemma1_prod

theorem IsPseudoConv.lemma1_poly_xor [Nonempty ι] (a : ι → K) (p : K[X]) :
    ¬ ((∃ i, ∀ j k, i ≤ j → j < k → V (p.eval (a k)) < V (p.eval (a j))) ∧
    (∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))) := by
  rw [not_and]
  intro hp
  contrapose! hp
  obtain ⟨i, hi⟩ := hp
  intro l
  obtain ⟨i2, hi2⟩ := exists_gt (max i l)
  refine ⟨max i l, i2, by simp, hi2, ?_⟩
  exact (hi _ (by simp)).symm.le.trans ((hi _ (max_lt_iff.mp hi2).1.le).le)

theorem IsPseudoConv.lemma1_poly_iff [Nonempty ι] {a : ι → K}
    (ha : IsPseudoConv V a) (p : K[X]) :
    (¬ ∃ i, ∀ j k, i ≤ j → j < k → V (p.eval (a k)) < V (p.eval (a j))) ↔
    ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)) := by
  constructor
  · intro h
    obtain h' := IsPseudoConv.lemma1_poly V ha p
    exact (or_iff_right h).mp h'
  · intro h
    by_contra! h'
    exact (IsPseudoConv.lemma1_poly_xor V a p) ⟨h', h⟩

theorem IsPseudoConv.lemma1_poly_iff' [Nonempty ι] {a : ι → K}
    (ha : IsPseudoConv V a) (p : K[X]) :
    (¬ ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) ↔
    ∃ i, ∀ j k, i ≤ j → j < k → V (p.eval (a k)) < V (p.eval (a j)) :=
  not_iff_comm.mp (IsPseudoConv.lemma1_poly_iff V ha p)

theorem lemma4_two {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    {ι : Type*} [LinearOrder ι] [NoMaxOrder ι] [hι : Nonempty ι] {m n : ℕ} (h : m ≠ n)
    (c d : G) {a : ι → G} (ha : StrictAnti a) :
    (∃ l, ∀ i, l ≤ i → c * a i ^ m < d * a i ^ n) ∨
    (∃ l, ∀ i, l ≤ i → d * a i ^ n < c * a i ^ m) := by
  wlog hmn : m < n
  · exact (this h.symm d c ha (lt_of_le_of_ne (not_lt.mp hmn) h.symm)).symm
  by_cases! hl : ∃ l, d * a l ^ n < c * a l ^ m
  · obtain ⟨l, hl⟩ := hl
    refine Or.inr ⟨l, fun i hi ↦ ?_⟩
    rw [← mul_inv_lt_iff_lt_mul, mul_assoc, ← pow_sub _ hmn.le] at ⊢ hl
    refine lt_of_le_of_lt ?_ hl
    rw [mul_le_mul_iff_left]
    rw [pow_le_pow_iff_left (Nat.sub_ne_zero_of_lt hmn)]
    exact ha.le_iff_ge.mpr hi
  · refine Or.inl ⟨hι.some, fun i hi ↦ ?_⟩
    apply lt_of_le_of_ne (hl i)
    obtain ⟨j, hj⟩ := exists_gt i
    specialize hl j
    contrapose! hl
    rw [← mul_inv_lt_iff_lt_mul, mul_assoc, ← pow_sub _ hmn.le]
    rw [← eq_mul_inv_iff_mul_eq, mul_assoc, ← pow_sub _ hmn.le] at hl
    rw [hl]
    rw [mul_lt_mul_iff_left]
    apply pow_lt_pow_left' (Nat.sub_ne_zero_of_lt hmn)
    apply ha hj

theorem lemma4 {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    {ι : Type*} [LinearOrder ι] [NoMaxOrder ι] [Nonempty ι]
    {t : Finset ℕ} (ht : t.Nonempty) (c : ℕ → G) {a : ι → G} (ha : StrictAnti a) :
    ∃ m ∈ t, ∃ l, ∀ i, l ≤ i → ∀ n ∈ t \ {m}, c n * a i ^ n < c m * a i ^ m := by
  induction t using Finset.cons_induction with
  | empty => simp at ht
  | cons n s hn ih =>
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    obtain ⟨m, hm, l, hl⟩ := ih hs
    have h : m ≠ n := fun h ↦ hn (h ▸ hm)
    obtain ⟨l', hl'⟩ | ⟨l', hl'⟩ := lemma4_two h (c m) (c n) ha
    · refine ⟨n, by simp, max l l', fun i hi k hk ↦ ?_⟩
      rw [Finset.sdiff_singleton_eq_erase, Finset.erase_cons] at hk
      specialize hl' _ <| le_trans (by simp) hi
      obtain hkm | hkm := eq_or_ne k m
      · rw [hkm]
        exact hl'
      · refine lt_trans ?_ hl'
        exact hl _ (le_trans (by simp) hi) _ (by simpa using ⟨hk, hkm⟩)
    · refine ⟨m, by simp [hm], max l l', fun i hi k hk ↦ ?_⟩
      rw [Finset.sdiff_singleton_eq_erase, Finset.erase_cons_of_ne _ h.symm] at hk
      simp_rw [← Finset.sdiff_singleton_eq_erase, Finset.mem_cons] at hk
      obtain hkn | hks := hk
      · rw [hkn]
        exact hl' _ <| le_trans (by simp) hi
      · exact hl _ (le_trans (by simp) hi) _ hks

set_option maxHeartbeats 300000 in
-- huge proof
theorem IsPseudoConv.poly_eventually [hι : Nonempty ι] {a : ι → K}
    (ha : IsPseudoConv V a) {p : K[X]} (hd0 : 0 < p.natDegree) :
    ∃ l, ∀ ⦃i j k⦄, l ≤ i → i < j → j < k →
    V (p.eval (a j) - p.eval (a k)) < V (p.eval (a i) - p.eval (a j)) := by
  obtain hd1 | hd1 := eq_or_ne p.natDegree 1
  · obtain ⟨m, hm, b, rfl⟩ := Polynomial.natDegree_eq_one.mp hd1
    use hι.some
    intro i j k hli hij hjk
    suffices V (m * a j - m * a k) < V (m * a i - m * a j) by simpa
    simp_rw [← mul_sub, map_mul]
    rw [mul_lt_mul_iff_right₀ (V.pos_iff.mpr hm)]
    exact ha hij hjk
  obtain ⟨Γ', _, V', _⟩ := exists_valuation_extension V (AlgebraicClosure K)
  by_cases hlimit : ∃ (x : AlgebraicClosure K) (lb : ι),
    HasLimit V' (fun (i : Set.Ici lb) ↦ algebraMap K (AlgebraicClosure K) (a i)) x
  · obtain ⟨x, lb, hx⟩ := hlimit
    simp_rw [← Valuation.HasExtension.val_map_lt_iff V V']
    simp_rw [map_sub]
    simp_rw [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
    simp_rw [← Polynomial.eval_map_algebraMap]
    set p' := (Polynomial.map (algebraMap K (AlgebraicClosure K)) p)
    classical
    let hasse0 := (Finset.Ico 1 (p'.natDegree + 1)).filter fun n ↦ (p'.hasseDeriv n).eval x ≠ 0
    have hnonempty : hasse0.Nonempty := by
      use p'.natDegree
      suffices 1 ≤ p'.natDegree ∧ p' ≠ 0 by simpa [hasse0, Polynomial.hasseDeriv_natDegree_eq_C]
      constructor
      · suffices 1 ≤ p.natDegree by simpa [p']
        grind
      · suffices p ≠ 0 by simpa [p']
        contrapose! hd0
        simp [hd0]
    have hunit (n : ℕ) (hn : n ∈ hasse0) : IsUnit (V' ((p'.hasseDeriv n).eval x)) := by
      have : (1 ≤ n ∧ n < p'.natDegree + 1) ∧ (p'.hasseDeriv n).eval x ≠ 0 := by
        simpa [hasse0] using hn
      simpa using this.2
    choose! w hw using hunit
    have ha' : IsPseudoConv V' fun i ↦ (algebraMap K (AlgebraicClosure K)) (a i) - x := by
      apply IsPseudoConv.sub_const
      exact (IsPseudoConv.iff V V').mp ha
    have hanti : StrictAnti fun i ↦ V' (algebraMap K (AlgebraicClosure K) (a i) - x) := by
      intro i j hij
      refine (Or.resolve_right (ha'.lemma1 V') ?_) i j hij
      unfold HasLimit at hx
      by_contra!
      obtain ⟨l, hl, _⟩ := this
      obtain ⟨i, hi⟩ := exists_gt (max l lb)
      obtain hlx := hx ⟨max l lb, by simp⟩
      obtain hix := hx ⟨i, le_trans (by simp) hi.le⟩
      obtain hlx' := hl (max l lb) (by simp)
      obtain hix' := hl i (le_trans (by simp) hi.le)
      simp_rw [V'.map_sub_swap _ x] at hlx'
      simp_rw [V'.map_sub_swap _ x] at hix'
      simp only [← hlx'] at hlx
      simp only [← hix'] at hix
      refine ((IsPseudoConv.γ_strictAnti V' ?_) (by simpa using hi)).ne.symm (hlx.symm.trans hix)
      exact ((IsPseudoConv.iff V V').mp ha).Ici V' _
    have ha0 (i : ι) : (algebraMap K (AlgebraicClosure K) (a i) - x) ≠ 0 := by
      by_contra! h
      obtain ⟨j, hj⟩ := exists_gt i
      obtain hj := hanti hj
      simp [h] at hj
    have hvunit (i : ι) : IsUnit (V' (algebraMap K (AlgebraicClosure K) (a i) - x)) := by
      simpa using ha0 i
    choose ax hax using hvunit
    have hanti' : StrictAnti ax := by
      intro i j hij
      simpa [← hax] using hanti hij
    obtain ⟨m, hm, l, hl⟩ := lemma4 hnonempty w hanti'
    use l
    intro i j k hli hij hjk
    have hm' : (1 ≤ m ∧ m < p'.natDegree + 1) ∧ (p'.hasseDeriv m).eval x ≠ 0 := by
      simpa [hasse0] using hm
    have h1 (a : AlgebraicClosure K) : p'.eval a =
        ∑ n ∈ Finset.range (p'.natDegree + 1), (p'.hasseDeriv n).eval x * (a - x) ^ n := by
      nth_rw 1 [show a = a - x + x by ring]
      rw [← Polynomial.taylor_eval]
      rw [Polynomial.eval_eq_sum_range]
      rw [Polynomial.natDegree_taylor]
      simp_rw [Polynomial.taylor_coeff]
    have h2 (i : ι) (hli : l ≤ i) :
        V' (∑ n ∈ Finset.Ico 1 (p'.natDegree + 1),
          (p'.hasseDeriv n).eval x * (algebraMap K _ (a i) - x) ^ n) =
          V' ((p'.hasseDeriv m).eval x * (algebraMap K _ (a i) - x) ^ m) := by
      apply V'.map_sum_eq_of_lt (by simpa using hm'.1)
      intro n hn
      rw [Finset.mem_sdiff] at hn
      by_cases hnhasse : n ∈ hasse0
      · simp only [map_mul, hnhasse, ← hw, map_pow, ← hax, hm]
        norm_cast
        exact hl i hli n (Finset.mem_sdiff.mpr ⟨hnhasse, hn.2⟩)
      · simp_rw [hasse0, Finset.mem_filter, not_and_or] at hnhasse
        obtain h0 := hnhasse.resolve_left (by simpa using hn.1)
        rw [not_not] at h0
        suffices 0 < V' ((p'.hasseDeriv m).eval x) * V' ((algebraMap K _ (a i) - x) ^ m) by
          simpa [h0]
        refine mul_pos (V'.pos_iff.mpr hm'.2) (V'.pos_iff.mpr (pow_ne_zero _ (ha0 i)))
    have (i j : ι) (hli : l ≤ i) (hij : i < j) :
        V' (p'.eval (algebraMap K _ (a i)) - p'.eval (algebraMap K _ (a j))) =
        V' ((p'.hasseDeriv m).eval x * ((algebraMap K _ (a i)) - x) ^ m) := by
      simp_rw [h1]
      rw [Finset.sum_range_eq_add_Ico _ (by simp), Finset.sum_range_eq_add_Ico _ (by simp)]
      suffices V'
        (∑ n ∈ Finset.Ico 1 (p'.natDegree + 1),
          (p'.hasseDeriv n).eval x * (algebraMap K _ (a i) - x) ^ n -
        ∑ n ∈ Finset.Ico 1 (p'.natDegree + 1),
          (p'.hasseDeriv n).eval x * (algebraMap K _ (a j) - x) ^ n) =
        V' ((p'.hasseDeriv m).eval x * (algebraMap K _ (a i) - x) ^ m) by simpa
      rw [← h2 i hli]
      rw [V'.map_sub_swap]
      apply Valuation.map_sub_eq_of_lt_right
      rw [h2 i hli, h2 j (hli.trans hij.le)]
      simp_rw [map_mul, map_pow]
      rw [mul_lt_mul_iff_right₀ (V'.pos_iff.mpr hm'.2)]
      apply pow_lt_pow_left₀ (hanti hij) (by simp) (Nat.one_le_iff_ne_zero.mp hm'.1.1)
    rw [this i j hli hij, this j k (hli.trans (hij.le)) hjk]
    simp_rw [map_mul, map_pow]
    rw [mul_lt_mul_iff_right₀ (V'.pos_iff.mpr hm'.2)]
    apply pow_lt_pow_left₀ (hanti hij) (by simp) (Nat.one_le_iff_ne_zero.mp hm'.1.1)
  · have hconst (p : Polynomial K) :
        ∃ l : ι, (∀ i : ι, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) ∧
        (p = 0 ∨ V (p.eval (a l)) ≠ 0) := by
      obtain rfl | hp0 := eq_or_ne p 0
      · simp
      simp only [hp0, false_or]
      simp_rw [← Valuation.HasExtension.val_map_eq_iff V V']
      have hl (l : ι) : V (p.eval (a l)) ≠ 0 ↔
          V' ((algebraMap K (AlgebraicClosure K)) (Polynomial.eval (a l) p)) ≠ 0 := by simp
      simp_rw [hl]
      simp_rw [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      simp_rw [Polynomial.aeval_eq_prod_aroots_sub_of_splits (IsAlgClosed.splits_codomain p)]
      suffices ∃ l, (∀ (i : ι), l ≤ i →
        V' (Multiset.map (fun c ↦ (algebraMap K (AlgebraicClosure K)) (a l) - c)
          (p.aroots (AlgebraicClosure K))).prod =
        V' (Multiset.map (fun c ↦ (algebraMap K (AlgebraicClosure K)) (a i) - c)
          (p.aroots (AlgebraicClosure K))).prod) ∧
        V' (Multiset.map (fun c ↦ (algebraMap K (AlgebraicClosure K)) (a l) - c)
          (p.aroots (AlgebraicClosure K))).prod ≠ 0 by simpa [hp0]
      apply lemma1_prod'
      intro c hc
      refine Or.resolve_left (IsPseudoConv.lemma1 V'
        (IsPseudoConv.sub_const V' ((IsPseudoConv.iff V V').mp ha) c)) ?_
      contrapose! hlimit with hmono
      use c, hι.some
      unfold HasLimit
      intro i
      obtain ⟨j, hj⟩ := exists_gt i
      rw [IsPseudoConv.γ_eq _ (by exact (IsPseudoConv.iff V V').mp (ha.Ici V hι.some)) hj]
      rw [V'.map_sub_swap]
      rw [show V' ((algebraMap K (AlgebraicClosure K)) (a ↑i) -
          (algebraMap K (AlgebraicClosure K)) (a ↑j)) =
        V' (((algebraMap K (AlgebraicClosure K)) (a ↑i) - c) -
          ((algebraMap K (AlgebraicClosure K)) (a ↑j) - c)) by ring_nf]
      refine (Valuation.map_sub_eq_of_lt_left _ ?_).symm
      apply hmono
      simpa using hj
    have (i j : ι) : V (p.eval (a i) - p.eval (a j)) = V (∑ n ∈ Finset.Ico 1 (p.natDegree + 1),
          (p.hasseDeriv n).eval (a i) * (a j - a i) ^ n) := by
      rw [V.map_sub_swap]
      rw [show Polynomial.eval (a j) p =
        Polynomial.eval (a j - a i + a i) p by ring_nf]
      rw [← Polynomial.taylor_eval]
      rw [Polynomial.eval_eq_sum_range (a j - a i)]
      rw [Polynomial.natDegree_taylor]
      simp_rw [Polynomial.taylor_coeff]
      rw [Finset.sum_range_eq_add_Ico _ (by simp)]
      simp
    simp_rw [this]
    have hconsthasse (n : ℕ) : ∃ l : ι, (∀ i : ι, l ≤ i →
        V ((p.hasseDeriv n).eval (a l)) = V ((p.hasseDeriv n).eval (a i)))
        ∧ (p.hasseDeriv n = 0 ∨ V ((p.hasseDeriv n).eval (a l)) ≠ 0) :=
      hconst (p.hasseDeriv n)
    choose fl hfl hfl' using hconsthasse
    suffices ∃ m ∈ Finset.Ico 1 (p.natDegree + 1), ∃ l, ∀ i j, l ≤ i → i < j →
        ∀ n ∈ Finset.Ico 1 (p.natDegree + 1) \ {m},
        V ((p.hasseDeriv n).eval (a i) * (a j - a i) ^ n) <
        V ((p.hasseDeriv m).eval (a i) * (a j - a i) ^ m) by
      obtain ⟨m, hm, l, h⟩ := this
      obtain ⟨h1m, hmp⟩ : 1 ≤ m ∧ m < p.natDegree + 1 := by simpa using hm
      use max (fl m) l
      intro i j k hmli hij hjk
      obtain hli : l ≤ i := le_of_max_le_right hmli
      obtain hij' := h i j hli hij
      obtain hjk' := h j k (hli.trans hij.le) hjk
      rw [Valuation.map_sum_eq_of_lt V hm hjk']
      rw [Valuation.map_sum_eq_of_lt V hm hij']
      simp_rw [V.map_mul, V.map_pow]
      obtain hmi := le_of_max_le_left hmli
      rw [← hfl m i hmi]
      rw [← hfl m j (hmi.trans hij.le)]
      apply mul_lt_mul_of_pos_left
      · refine pow_lt_pow_left₀ ?_ (by simp) (Nat.one_le_iff_ne_zero.mp h1m)
        rw [V.map_sub_swap _ (a j), V.map_sub_swap _ (a i)]
        exact ha hij hjk
      · contrapose! hd1 with h0
        rw [le_zero_iff, map_eq_zero] at h0
        specialize hfl m
        conv at hfl => intro i h; rw [Eq.comm]
        have hfl0 : ∀ i, fl m ≤ i → (p.hasseDeriv m).eval (a i)  = 0 := by
          simpa [h0] using hfl
        specialize h (max l (fl m))
        have h : ∀ (j : ι), l < j → fl m < j → ∀ (n : ℕ), 1 ≤ n → n < p.natDegree + 1 → n = m := by
          simpa [hfl0 (max l (fl m)) (by simp)] using h
        obtain ⟨j, hj⟩ := exists_gt (max l (fl m))
        specialize h j (lt_of_le_of_lt (by simp) hj) (lt_of_le_of_lt (by simp) hj)
        have hdegree : p.natDegree = m :=
          h p.natDegree (h1m.trans (Nat.lt_add_one_iff.mp hmp)) (by simp)
        have h1 : 1 = m := h 1 (by simp) (h1m.trans_lt hmp)
        exact hdegree.trans h1.symm
    simp_rw [V.map_mul, V.map_pow]
    suffices ∃ m ∈ Finset.Ico 1 (p.natDegree + 1),
      ∃ l, ∀ i, l ≤ i → ∀ n ∈ Finset.Ico 1 (p.natDegree + 1) \ {m},
        V ((p.hasseDeriv n).eval (a (fl n))) * γ V a i ^ n <
        V ((p.hasseDeriv m).eval (a (fl m))) * γ V a i ^ m by
      obtain ⟨m, hm, l, h⟩ := this
      use m, hm, max l ((Finset.Ico 1 (p.natDegree + 1)).sup' (by simpa using hd0) fl)
      intro i j hli hij
      obtain ⟨hli, hmi⟩ := max_le_iff.mp hli
      rw [Finset.sup'_le_iff] at hmi
      rw [show V (a j - a i) = γ V a i by rw [V.map_sub_swap, ha.γ_eq V hij]]
      convert h i hli using 4 with n hn
      · exact (hfl _ _ <| hmi _ (Finset.mem_sdiff.mp hn).1).symm
      · exact (hfl _ _ <| hmi _ hm).symm
    classical
    let hasse0 := (Finset.Ico 1 (p.natDegree + 1)).filter fun n ↦ p.hasseDeriv n ≠ 0
    suffices ∃ m ∈ hasse0, ∃ l, ∀ i, l ≤ i → ∀ n ∈ hasse0 \ {m},
        V ((p.hasseDeriv n).eval (a (fl n))) * γ V a i ^ n <
        V ((p.hasseDeriv m).eval (a (fl m))) * γ V a i ^ m by
      obtain ⟨m, hm, l, h⟩ := this
      have hm : (1 ≤ m ∧ m < p.natDegree + 1) ∧ p.hasseDeriv m ≠ 0 := by
        simpa [hasse0] using hm
      refine ⟨m, by simpa using hm.1, l, ?_⟩
      intro i hli n hn
      have hn : (1 ≤ n ∧ n < p.natDegree + 1) ∧ n ≠ m := by simpa using hn
      obtain h0 | h0 := eq_or_ne (p.hasseDeriv n) 0
      · suffices 0 < V ((p.hasseDeriv m).eval (a (fl m))) * γ V a i ^ m by simpa [h0]
        apply mul_pos
        · exact lt_of_le_of_ne (by simp) ((hfl' m).resolve_left hm.2).symm
        · apply pow_pos
          apply ha.γ_pos
      apply h i hli n
      simpa [hasse0] using ⟨⟨⟨hn.1.1, hn.1.2⟩, h0⟩, hn.2⟩
    have hnonempty : hasse0.Nonempty := by
      use p.natDegree
      suffices 1 ≤ p.natDegree ∧ p ≠ 0 by simpa [hasse0, Polynomial.hasseDeriv_natDegree_eq_C]
      constructor
      · grind
      · contrapose! hd0
        simp [hd0]
    have hunit (n : ℕ) (hn : n ∈ hasse0) : IsUnit (V ((p.hasseDeriv n).eval (a (fl n)))) := by
      have hn : (1 ≤ n ∧ n < p.natDegree + 1) ∧ p.hasseDeriv n ≠ 0 := by
        simpa [hasse0] using hn
      simpa using (hfl' n).resolve_left hn.2
    have hγunit (i : ι) : IsUnit (γ V a i) := by simpa using (ha.γ_pos V i).ne.symm
    choose! w hw using hunit
    have hw' (n : ℕ) (hn : n ∈ hasse0) : w n = V ((p.hasseDeriv n).eval (a (fl n))) := by
      simp [hn, hw]
    choose g hg using hγunit
    have hganti : StrictAnti g := by
      intro u v h
      obtain h := (hg u).symm ▸ (hg v).symm ▸ γ_strictAnti V ha h
      simpa using h
    suffices ∃ m ∈ hasse0, ∃ l, ∀ i, l ≤ i → ∀ n ∈ hasse0 \ {m},
        w n * g i ^ n < w m * g i ^ m by
      obtain ⟨m, hm, l, h⟩ := this
      refine ⟨m, hm, l, ?_⟩
      intro i hli n hn
      rw [← hw' n (Finset.mem_sdiff.mp hn).1, ← hw' m hm, ← hg]
      norm_cast
      exact h i hli n hn
    apply lemma4 hnonempty w hganti


theorem IsPseudoConv.hasLimit_iff {a : ι → K} (h : IsPseudoConv V a) {x : K} :
    HasLimit V a x ↔ HasLimit V' (algebraMap K L ∘ a) (algebraMap K L x) := by
  unfold HasLimit
  suffices ∀ (i : ι),  V (x - a i) = γ V a i ↔
      V' ((algebraMap K L) x - (algebraMap K L) (a i)) =
      γ V' (algebraMap K L ∘ a) i by
    constructor
    · intro h i
      exact (this i).mp (h i)
    · intro h i
      exact (this i).mpr (h i)
  intro i
  obtain ⟨j, hj⟩ := exists_gt i
  obtain h' := (IsPseudoConv.iff V V').mp h
  rw [h.γ_eq V hj, ((IsPseudoConv.iff V V').mp h).γ_eq V' hj]
  simpa [← map_sub] using (Valuation.HasExtension.val_map_eq_iff V V' _ _).symm

def IsImmediate : Prop := Set.range V' = V' '' (⊥ : Subalgebra K L)
  ∧ Function.Surjective (IsLocalRing.ResidueField.map (algebraMap V.integer V'.integer))

theorem IsImmediate.exists_lt (h : IsImmediate V V') {z : L}
    (hz : z ∉ (⊥ : Subalgebra K L)) (g : K) :
    ∃ g' : K, V' (z - algebraMap K L g') < V' (z - algebraMap K L g) := by
  obtain ⟨hvalue, hres⟩ := h
  have h0 : V' (z - algebraMap K L g) ≠ 0 := by
    contrapose! hz
    rw [map_eq_zero, sub_eq_zero] at hz
    simp [hz]
  have : V' (z - algebraMap K L g) ∈ Set.range V' := ⟨z - algebraMap K L g, by simp⟩
  rw [hvalue] at this
  have : ∃ c, V' (algebraMap K L c) = V' (z - algebraMap K L g) := by simpa using this
  obtain ⟨c, hc⟩ := this
  have hint : (z - algebraMap K L g) / algebraMap K L c ∈ V'.integer := by
    rw [Valuation.mem_integer_iff]
    rw [Valuation.map_div, hc]
    rw [div_self h0]
  let d := IsLocalRing.residue V'.integer ⟨(z - algebraMap K L g) / algebraMap K L c, hint⟩
  obtain ⟨d', hd⟩ := hres d
  induction d' with | residue dout
  use g + c * dout
  rw [map_add, ← sub_sub]
  rw [IsLocalRing.ResidueField.map_residue] at hd
  unfold d at hd
  symm at hd
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at hd
  obtain hd := (Valuation.mem_maximalIdeal_iff _ _).mp hd
  obtain hd := (mul_lt_mul_iff_left₀ (lt_of_le_of_ne zero_le' (h0.symm))).mpr hd
  convert hd
  · rw [← hc, ← map_mul, AddSubgroupClass.coe_sub, sub_mul]
    congrm (V' (?_ - ?_))
    · suffices algebraMap K L c ≠ 0 by simp [this]
      contrapose! h0
      rw [← hc]
      simpa using h0
    · simp [mul_comm c]
  · simp

theorem IsImmediate.theorem1 (h : IsImmediate V V') {z : L} (hz : z ∉ (⊥ : Subalgebra K L)) :
    ∃ (s : Set Γ'ᵒᵈ) (_ : NoMaxOrder s) (a : s → K), IsPseudoConv V a ∧
    (∀ x : K, ¬ HasLimit V a x) ∧ (HasLimit V' (algebraMap K L ∘ a) z) := by
  let s := Set.range fun a ↦ OrderDual.toDual <| V' (z - algebraMap K L a)
  have hmax : ∀ (g : ↑s), ∃ g', g < g' := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha⟩ := Set.mem_range.mp hg
    obtain ⟨b, hb⟩ := h.exists_lt V V' hz a
    exact ⟨⟨OrderDual.toDual <| V' (z - algebraMap K L b), by simp [s]⟩, by simpa [← ha] using hb⟩
  have : NoMaxOrder ↑s := ⟨hmax⟩
  refine ⟨s, inferInstance, ?_⟩
  have hmem (i : s) : ∃ a, OrderDual.toDual (V' (z - algebraMap K L a)) = i.val := i.prop
  choose a ha using hmem
  have haanti {i j : s} (hij : i < j) :
      V' (z - algebraMap K L (a j)) < V' (z - algebraMap K L (a i)) := by
    rw [← OrderDual.toDual_lt_toDual, ha i, ha j]
    simpa using hij
  have hpconv : IsPseudoConv V a := by
    rw [IsPseudoConv.iff V V']
    intro i j k hij hjk
    simp_rw [Function.comp_apply]
    rw [show (algebraMap K L) (a j) - (algebraMap K L) (a k) =
        (z - (algebraMap K L) (a k)) + -(z - (algebraMap K L) (a j)) by simp]
    rw [show (algebraMap K L) (a i) - (algebraMap K L) (a j) =
        (z - (algebraMap K L) (a j)) + -(z - (algebraMap K L) (a i)) by simp]
    rw [V'.map_add_of_distinct_val (by
      rw [V'.map_neg]
      exact (haanti hjk).ne)]
    rw [V'.map_add_of_distinct_val (by
      rw [V'.map_neg]
      exact (haanti hij).ne)]
    rw [max_comm (V' (z - algebraMap K L (a k))), V'.map_neg, V'.map_neg, max_lt_max_right_iff]
    exact ⟨(haanti (hij.trans hjk)), haanti hij⟩
  have hzlimit : HasLimit V' (⇑(algebraMap K L) ∘ a) z := by
    unfold HasLimit
    intro k
    obtain ⟨j, hj⟩ := exists_gt k
    rw [((IsPseudoConv.iff V V').mp hpconv).γ_eq _ hj]
    simp_rw [Function.comp_apply]
    rw [show (algebraMap K L) (a k) - (algebraMap K L) (a j) =
      z - (algebraMap K L) (a j) + -(z - (algebraMap K L) (a k)) by simp]
    rw [V'.map_add_of_distinct_val (by
      rw [V'.map_neg]
      exact (haanti hj).ne)]
    rw [V'.map_neg, right_eq_sup]
    exact (haanti hj).le
  refine ⟨a, hpconv, ?_, hzlimit⟩
  obtain hexists_lt := h.exists_lt V V' hz
  contrapose! hmax with hlimit
  obtain ⟨z1, hz1⟩ := hlimit
  refine ⟨⟨OrderDual.toDual <| V' (z - algebraMap K L z1), by simp [s]⟩, fun i ↦ ?_⟩
  rw [← Subtype.coe_le_coe, ← ha i, OrderDual.toDual_le_toDual]
  rw [hpconv.hasLimit_iff V V'] at hz1
  obtain hbreadth := (((IsPseudoConv.iff V V').mp hpconv).lemma3 V' hzlimit).mp hz1
  rw [Breadth, Set.mem_setOf_eq] at hbreadth
  convert (hbreadth i).le
  exact hzlimit i


/-- Adjoin the limit of `a` to field K to form `K[lim(a)]`,
and compute the valuation of polynomials in the new field -/
noncomputable
def vPoly (a : ι → K) (p : K[X]) : Γ :=
  open Classical in
  if h : ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)) then
    V (p.eval (a h.choose))
  else
    0

omit [NoMaxOrder ι] in
theorem vPoly_eq (a : ι → K) (p : K[X]) (l : ι)
    (h : ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) :
    vPoly V a p = V (p.eval (a l)) := by
  have h' : ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)) := ⟨l, h⟩
  simp [vPoly, h', h'.choose_spec (max l h'.choose) (by simp), h (max l h'.choose) (by simp)]

theorem pigeonhole' {ι : Type*} {K : Type*}
    {a : ι → K} (s : Set ι) (hs : s.Infinite) (t : Set K) (ht : t.Finite) (h : a '' s ⊆ t) :
    ∃ k : K, (a ⁻¹' {k}).Infinite := by
  contrapose! hs
  simp_rw [Set.not_infinite] at hs ⊢
  have : s ⊆ ⋃ k ∈ t, a ⁻¹' {k} := by
    intro x hx
    have : a x ∈ a '' s := ⟨x, hx, rfl⟩
    have : a x ∈ t := h this
    simp_rw [Set.mem_iUnion]
    exact ⟨a x, this, by simp⟩
  refine Set.Finite.subset ?_ this
  exact Set.Finite.biUnion ht (fun k _ => hs k)

theorem pigeonhole {ι : Type*} [LinearOrder ι] {K : Type*}
    {a : ι → K} (s : Set ι) (hs : s.Infinite) (t : Set K) (ht : t.Finite) (h : a '' s ⊆ t) :
    ∃ i j k, i < j ∧ j < k ∧ a i = a j ∧ a j = a k := by
  obtain ⟨u, hu⟩ := pigeonhole' s hs t ht h
  obtain ⟨i, hi⟩ := hu.nonempty
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hi
  obtain ⟨j, hj⟩ := (hu.diff (Set.finite_singleton i)).nonempty
  obtain ⟨hj, hji⟩ : a j = u ∧ j ≠ i := by simpa using hj
  obtain ⟨k, hk⟩ := ((hu.diff (Set.finite_singleton i)).diff (Set.finite_singleton j)).nonempty
  obtain ⟨⟨hk, hki⟩, hkj⟩ : (a k = u ∧ k ≠ i) ∧ k ≠ j := by simpa using hk
  obtain hij | hij := lt_or_gt_of_ne hji.symm <;> obtain hjk | hjk := lt_or_gt_of_ne hkj.symm
  · use i, j, k, hij, hjk
    simp [hi, hj, hk]
  · obtain hik | hik := lt_or_gt_of_ne hki.symm
    · use i, k, j, hik, hjk
      simp [hi, hj, hk]
    · use k, i, j, hik, hij
      simp [hi, hj, hk]
  · obtain hik | hik := lt_or_gt_of_ne hki.symm
    · use j, i, k, hij, hik
      simp [hi, hj, hk]
    · use j, k, i, hjk, hik
      simp [hi, hj, hk]
  · use k, j, i, hjk, hij
    simp [hi, hj, hk]

theorem IsPseudoConv.exists_poly_ne_zero [Nonempty ι] {a : ι → K}
    (h : IsPseudoConv V a) {p : K[X]} (hp : p ≠ 0) (i : ι) :
    ∃ j, i ≤ j ∧ p.eval (a j) ≠ 0 := by
  classical
  by_contra! h0
  suffices ∃ i j k, i < j ∧ j < k ∧ a i = a j ∧ a j = a k by
    obtain ⟨i, j, k, hij, hjk, hij2, hjk2⟩ := this
    specialize h hij hjk
    simp [hij2, hjk2] at h
  have h0' : a '' Set.Ici i ⊆ (p.roots.toFinset : Set _) := by
    intro j hj
    simp_rw [Set.mem_image, Set.mem_Ici] at hj
    obtain ⟨x, hx, hxj⟩ := hj
    rw [← hxj]
    simpa [hp] using h0 x hx
  apply pigeonhole (Set.Ici i) (Set.Ici_infinite _) ((p.roots.toFinset : Set _)) (by simp) h0'

theorem vPoly_eq_zero [Nonempty ι] {a : ι → K} (ha : IsPseudoConv V a) {p : K[X]} (hp : p ≠ 0) :
    vPoly V a p = 0 ↔ ¬ ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)) := by
  constructor
  · intro h
    contrapose! hp
    obtain ⟨l, hl⟩ := hp
    rw [vPoly_eq V a p l hl] at h
    rw [h] at hl
    contrapose! hl with h0
    obtain ⟨i, hi, hi2⟩ := IsPseudoConv.exists_poly_ne_zero V ha h0 l
    use i, hi
    symm
    simpa using hi2
  · intro h
    simp [vPoly, h]

theorem vPoly_ne_zero [Nonempty ι] {a : ι → K} (ha : IsPseudoConv V a) {p : K[X]} (hp : p ≠ 0) :
    vPoly V a p ≠ 0 ↔ ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)) := by
  simpa using (vPoly_eq_zero V ha hp).not

theorem vPoly_mul_aux [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a) (p q : K[X])
    (hp : ∃ i, ∀ j k, i ≤ j → j < k → V (p.eval (a k)) < V (p.eval (a j))) :
    vPoly V a (p * q) = vPoly V a p * vPoly V a q := by
  obtain rfl | hq0 := eq_or_ne q 0
  · simp [vPoly]
  have hp' : ¬ ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)) :=
    not_and.mp (IsPseudoConv.lemma1_poly_xor V a p) hp
  suffices ¬ ∃ l, ∀ i, l ≤ i → V ((p * q).eval (a l)) = V ((p * q).eval (a i)) by
    simp only [vPoly, hp', this, reduceDIte, zero_mul]
  suffices ∃ i, ∀ (j k : ι), i ≤ j → j < k → V ((p * q).eval (a k) ) < V ((p * q).eval (a j)) from
    not_and.mp (IsPseudoConv.lemma1_poly_xor V a (p * q)) this
  obtain ⟨pi, hp⟩ := hp
  obtain ⟨qi, hq⟩ | ⟨qi, hq⟩ := IsPseudoConv.lemma1_poly V h q
  · use max pi qi
    intro j k hj hk
    simpa using mul_lt_mul_of_nonneg (hp j k (le_of_max_le_left hj) hk)
      (hq j k (le_of_max_le_right hj) hk) zero_le' zero_le'
  · use max pi qi
    intro j k hj hk
    simp_rw [Polynomial.eval_mul, map_mul]
    rw [← hq j (le_of_max_le_right hj), ← hq k ((le_of_max_le_right hj).trans hk.le)]
    apply mul_lt_mul_of_pos_right (hp j k (le_of_max_le_left hj) hk)
    apply lt_of_le_of_ne zero_le'
    contrapose! hq
    rw [← hq]
    suffices ∃ i, qi ≤ i ∧ Polynomial.eval (a i) q ≠ 0 by
      obtain ⟨i, hqi, hi⟩ := this
      refine ⟨i, hqi, ?_⟩
      symm
      simpa using hi
    apply h.exists_poly_ne_zero V hq0 qi

theorem vPoly_mul [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a) (p q : K[X]) :
    vPoly V a (p * q) = vPoly V a p * vPoly V a q := by
  obtain hp | ⟨pi, hp⟩ := IsPseudoConv.lemma1_poly V h p
  · apply vPoly_mul_aux V h p q hp
  obtain hq | ⟨qi, hq⟩ := IsPseudoConv.lemma1_poly V h q
  · rw [mul_comm p, mul_comm (vPoly V a p)]
    apply vPoly_mul_aux V h q p hq
  rw [vPoly_eq V a p (max pi qi) fun i hi ↦ by
    rw [← hp (max pi qi) (by simp)]
    rw [← hp i (le_of_max_le_left hi)]]
  rw [vPoly_eq V a q (max pi qi) fun i hi ↦ by
    rw [← hq (max pi qi) (by simp)]
    rw [← hq i (le_of_max_le_right hi)]]
  rw [vPoly_eq V a (p * q) (max pi qi) ?_]
  · simp
  intro i hi
  simp_rw [Polynomial.eval_mul, V.map_mul]
  rw [← hp (max pi qi) (by simp)]
  rw [← hp i (le_of_max_le_left hi)]
  rw [← hq (max pi qi) (by simp)]
  rw [← hq i (le_of_max_le_right hi)]

omit [NoMaxOrder ι] in
theorem vPoly_add [Nonempty ι] (a : ι → K) (p q : K[X])
    (hp : ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (hq : ∃ l, ∀ i, l ≤ i → V (q.eval (a l)) = V (q.eval (a i)))
    (hpq : ∃ l, ∀ i, l ≤ i → V ((p + q).eval (a l)) = V ((p + q).eval (a i))) :
    vPoly V a (p + q) ≤ max (vPoly V a p) (vPoly V a q) := by
  obtain ⟨pi, hp⟩ := hp
  obtain ⟨qi, hq⟩ := hq
  obtain ⟨pqi, hpq⟩ := hpq
  rw [vPoly_eq V a p (max (max pi qi) pqi) fun i hi ↦ by
    rw [← hp i (le_of_max_le_left (le_of_max_le_left hi))]
    rw [← hp (max (max pi qi) pqi) (by simp)]]
  rw [vPoly_eq V a q (max (max pi qi) pqi) fun i hi ↦ by
    rw [← hq i (le_of_max_le_right (le_of_max_le_left hi))]
    rw [← hq (max (max pi qi) pqi) (by simp)]]
  rw [vPoly_eq V a (p + q) (max (max pi qi) pqi) fun i hi ↦ by
    rw [← hpq i (le_of_max_le_right hi)]
    rw [← hpq (max (max pi qi) pqi) (by simp)]]
  simp

theorem RatFunc.mk_mul_mk {K : Type*} [CommRing K] [IsDomain K] (p q r s : Polynomial K) :
    RatFunc.mk p q * RatFunc.mk r s = RatFunc.mk (p * r) (q * s) := by
  simp_rw [RatFunc.mk_eq_div]
  simp [div_mul_div_comm]

theorem RatFunc.mk_add_mk {K : Type*} [Field K] (p q r s : Polynomial K)
    (hq : q ≠ 0) (hs : s ≠ 0) :
    RatFunc.mk p q + RatFunc.mk r s = RatFunc.mk (p * s + q * r) (q * s) := by
  simp_rw [RatFunc.mk_eq_div]
  rw [div_add_div _ _ (RatFunc.algebraMap_ne_zero hq) (RatFunc.algebraMap_ne_zero hs)]
  simp

omit [NoMaxOrder ι] in
theorem vPoly_div_zero (a : ι → K) (p : K[X]) :
    vPoly V a p / vPoly V a 0 = vPoly V a 0 / vPoly V a 1 := by
  simp [vPoly]

theorem vPoly_well [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    {p q r : K[X]} (hr : r ≠ 0) :
    vPoly V a (r * p) / vPoly V a (r * q) = vPoly V a p / vPoly V a q := by
  simp_rw [vPoly_mul V h]
  apply mul_div_mul_left
  rw [vPoly_ne_zero V h hr]
  apply htran

noncomputable
def vTransc [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) :
    Valuation (RatFunc K) Γ where
  toFun p := RatFunc.liftOn' p (fun p q ↦ vPoly V a p / vPoly V a q)
    (fun {p q r} hq hr ↦ vPoly_well V h htran hr)
  map_zero' := by
    rw [show (0 : RatFunc K) = RatFunc.mk 0 1 by simp]
    rw [RatFunc.liftOn'_mk _ _ _ (vPoly_div_zero _ _) _]
    simp [vPoly]
  map_one' := by
    rw [show (1 : RatFunc K) = RatFunc.mk 1 1 by simp]
    rw [RatFunc.liftOn'_mk _ _ _ (vPoly_div_zero _ _) _]
    simp [vPoly]
  map_mul' p q := by
    induction p using RatFunc.induction_on' with | _pq p1 p2 hp
    induction q using RatFunc.induction_on' with | _pq q1 q2 hq
    rw [RatFunc.mk_mul_mk]
    rw [RatFunc.liftOn'_mk _ _ _ (vPoly_div_zero _ _) _]
    rw [RatFunc.liftOn'_mk _ _ _ (vPoly_div_zero _ _) _]
    rw [RatFunc.liftOn'_mk _ _ _ (vPoly_div_zero _ _) _]
    simp_rw [vPoly_mul V h]
    rw [div_mul_div_comm]
  map_add_le_max' p q := by
    induction p using RatFunc.induction_on' with | _pq p1 p2 hp
    induction q using RatFunc.induction_on' with | _pq q1 q2 hq
    rw [RatFunc.mk_add_mk _ _ _ _ hp hq]
    rw [RatFunc.liftOn'_mk _ _ _ (vPoly_div_zero _ _) _]
    rw [RatFunc.liftOn'_mk _ _ _ (vPoly_div_zero _ _) _]
    rw [RatFunc.liftOn'_mk _ _ _ (vPoly_div_zero _ _) _]
    rw [vPoly_mul V h]
    have hp0 : vPoly V a p2 ≠ 0 := by
      rw [vPoly_ne_zero V h hp]
      apply htran
    have hq0 : vPoly V a q2 ≠ 0 := by
      rw [vPoly_ne_zero V h hq]
      apply htran
    rw [div_le_iff₀ (zero_lt_iff.mpr (mul_ne_zero hp0 hq0))]
    rw [← max_mul_mul_right]
    convert vPoly_add V a (p1 * q2) (p2 * q1)
      (htran _) (htran _) (htran _)
    all_goals
    rw [vPoly_mul V h]
    field_simp

theorem vTransc_mk [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (p q : K[X]) :
    vTransc V h htran (RatFunc.mk p q) = vPoly V a p / vPoly V a q := by
  rw [vTransc]
  simp only [Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  rw [RatFunc.liftOn'_mk _ _ _ (vPoly_div_zero _ _) _]

theorem RatFunc.C_eq_mk {K : Type*} [CommRing K] [IsDomain K] (a : K) :
    RatFunc.C a = RatFunc.mk (Polynomial.C a) (1 : K[X]) := rfl

theorem RatFunc.liftOn'_C {K : Type*} [CommRing K] [IsDomain K] {P : Sort*}
    (a : K) (f : K[X] → K[X] → P) (f0 : ∀ p, f p 0 = f 0 1)
    (H : ∀ {p q a} (_hq : q ≠ 0) (_ha : a ≠ 0), f (a * p) (a * q) = f p q) :
    (RatFunc.C a).liftOn' f H = f (Polynomial.C a) 1 := by
  rw [RatFunc.C_eq_mk]
  rw [RatFunc.liftOn'_mk _ _ f f0 H]

theorem vTransc_C [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (p : K) :
    vTransc V h htran (RatFunc.C p) = V p := by
  rw [vTransc]
  simp only [Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  rw [RatFunc.liftOn'_C _ _ (vPoly_div_zero _ _) _]
  simp [vPoly]

theorem vTransc_polynomial [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (p : K[X]) :
    vTransc V h htran p = vPoly V a p := by
  change (vTransc V h htran) (RatFunc.mk p 1) = vPoly V a p
  rw [vTransc_mk]
  simp [vPoly]

instance vTransc_hasExtension [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) :
    Valuation.HasExtension V (vTransc V h htran) where
  val_isEquiv_comap := by
    intro x y
    simp only [RatFunc.algebraMap_eq_C, vTransc, Valuation.comap_apply, Valuation.coe_mk,
      MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    rw [RatFunc.liftOn'_C _ _ (vPoly_div_zero _ _)
      (fun {p q r} hq hr ↦ vPoly_well V h htran hr)]
    rw [RatFunc.liftOn'_C _ _ (vPoly_div_zero _ _)
      (fun {p q r} hq hr ↦ vPoly_well V h htran hr)]
    simp [vPoly]

theorem vTransc_valueImmediate [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) :
    Set.range (vTransc V h htran) =
    (vTransc V h htran) '' (⊥ : Subalgebra K (RatFunc K)) := by
  apply Set.Subset.antisymm ?_ (by simp)
  intro v
  suffices ∀ (x : RatFunc K), vTransc V h htran x = v →
    ∃ y, vTransc V h htran (RatFunc.C y) = v by simpa
  intro x hx
  induction x using RatFunc.induction_on' with | _pq p q hp
  rw [vTransc_mk] at hx
  simp_rw [vTransc_C, ← hx]
  obtain ⟨pi, hpi⟩ := htran p
  obtain ⟨qi, hqi⟩ := htran q
  use (Polynomial.eval (a pi) p) / (Polynomial.eval (a qi) q)
  rw [vPoly_eq V a p pi hpi]
  rw [vPoly_eq V a q qi hqi]
  simp

theorem vTransc_hasLimit [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) :
    HasLimit (vTransc V h htran) (algebraMap K (RatFunc K) ∘ a) RatFunc.X := by
  unfold HasLimit
  intro i
  obtain ⟨j, hj⟩ := exists_gt i
  obtain hconv := (IsPseudoConv.iff V (vTransc V h htran)).mp h
  rw [IsPseudoConv.γ_eq _ ((IsPseudoConv.iff _ _).mp h) hj]
  rw [show (algebraMap K (RatFunc K) ∘ a) i - (algebraMap K (RatFunc K) ∘ a) j =
    (RatFunc.X - (algebraMap K (RatFunc K) ∘ a) j) -
    (RatFunc.X - (algebraMap K (RatFunc K) ∘ a) i) by ring]
  refine (Valuation.map_sub_eq_of_lt_right _ ?_).symm
  obtain hconv' := (IsPseudoConv.const_sub (vTransc V h htran) hconv RatFunc.X).lemma1
    (vTransc V h htran)
  refine (or_iff_left ?_).mp hconv' i j hj
  have hv (i : ι) : vTransc V h htran (RatFunc.X - RatFunc.C (a i)) =
      vPoly V a (Polynomial.X - Polynomial.C (a i)) := by
    suffices (RatFunc.X - RatFunc.C (a i) : RatFunc K) =
      (Polynomial.X - Polynomial.C (a i) : K[X]) by
      rw [this, vTransc_polynomial]
    change (RatFunc.X - RatFunc.C (a i) : RatFunc K) =
      algebraMap _ _ (Polynomial.X - Polynomial.C (a i) : K[X])
    simp
  rw [not_exists]
  intro i
  apply not_and_of_not_left
  suffices ∃ j, i ≤ j ∧
    (vTransc V h htran (RatFunc.X - RatFunc.C (a i)) ≠
    vTransc V h htran (RatFunc.X - RatFunc.C (a j))) by simpa
  simp_rw [hv]
  obtain ⟨j, hj⟩ := exists_gt i
  refine ⟨j, hj.le, ?_⟩
  obtain ⟨k, hk⟩ := exists_gt j
  rw [vPoly_eq V a _ j (by
    suffices ∀ l, j ≤ l → V (a j - a i) = V (a l - a i) by simpa
    intro l hl
    rw [V.map_sub_swap (a j), V.map_sub_swap (a l)]
    apply h.lemma2' V hj (hj.trans_le hl)
  )]
  rw [vPoly_eq V a _ k (by
    suffices ∀ l, k ≤ l → V (a k - a j) = V (a l - a j) by simpa
    intro l hl
    rw [V.map_sub_swap (a k), V.map_sub_swap (a l)]
    apply h.lemma2' V hk (hk.trans_le hl)
  )]
  suffices V (a j - a i) ≠ V (a k - a j) by simpa
  apply ne_of_gt
  rw [V.map_sub_swap (a k), V.map_sub_swap _ (a i)]
  apply h hj hk

theorem vTransc_exists_close [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    {p : K[X]} (hp : vTransc V h htran p = 1) :
    ∃ x : K, V x = 1 ∧ vTransc V h htran (RatFunc.C x - p) < 1 := by
  rw [vTransc_polynomial] at hp
  have hv (x : K) : vTransc V h htran (RatFunc.C x - p) =
      vPoly V a (Polynomial.C x - p) := by
    suffices (RatFunc.C x - p : RatFunc K) = (Polynomial.C x - p : Polynomial K) by
      rw [this, vTransc_polynomial]
    change RatFunc.C x - algebraMap _ _ p = algebraMap _ _ (Polynomial.C x - p)
    simp
  simp_rw [hv]
  obtain hd0 | hd0 := Nat.eq_zero_or_pos p.natDegree
  · obtain ⟨x, hx⟩ := Polynomial.natDegree_eq_zero.mp hd0
    use x
    simpa [← hx, vPoly] using hp
  obtain ⟨m, hm⟩ := htran p
  obtain ⟨i, hi⟩ := IsPseudoConv.poly_eventually V h hd0
  obtain ⟨j, hj⟩ := exists_gt i
  obtain ⟨jm, hjm⟩ := exists_gt (max j m)
  obtain ⟨k, hk⟩ := exists_gt jm
  refine ⟨p.eval (a jm), ?_, ?_⟩
  · rw [← hp]
    refine (vPoly_eq V a p jm ?_).symm
    intro n hn
    rw [← hm jm (lt_of_le_of_lt (by simp) hjm).le]
    rw [← hm n (lt_of_lt_of_le (lt_of_le_of_lt (by simp) hjm) hn).le]
  rw [vPoly_eq V a _ k (by
    intro l hl
    obtain rfl | hl := eq_or_lt_of_le hl
    · simp
    suffices V (Polynomial.eval (a jm) p - Polynomial.eval (a k) p) =
      V (Polynomial.eval (a jm) p - Polynomial.eval (a k) p +
      (Polynomial.eval (a k) p - Polynomial.eval (a l) p)) by simpa
    symm
    apply Valuation.map_add_eq_of_lt_left
    apply hi (hj.trans (max_lt_iff.mp hjm).1).le hk hl
  )]
  suffices V (Polynomial.eval (a jm) p - Polynomial.eval (a k) p) < 1 by simpa
  suffices V (Polynomial.eval (a (max j m)) p - Polynomial.eval (a jm) p) ≤ 1 by
    refine lt_of_lt_of_le ?_ this
    apply hi (le_max_of_le_left hj.le) hjm hk
  apply Valuation.map_sub_le <;> apply le_of_eq <;> rw [← hp] <;> symm <;> apply vPoly_eq
    <;> intro n hn
  · rw [← hm (max j m) (by simp)]
    rw [← hm n (max_le_iff.mp hn).2]
  · rw [← hm jm (le_trans (by simp) hjm.le)]
    rw [← hm n ((max_le_iff.mp hjm.le).2.trans hn)]

theorem vTransc_exists_close' [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    {p : K[X]} (hp : p ≠ 0):
    ∃ a : K, V a = vTransc V h htran p ∧
      vTransc V h htran (RatFunc.C a - p) < vTransc V h htran p := by
  have hp : (p : RatFunc K) ≠ 0 := by
    change (algebraMap _ _) p ≠ 0
    simpa using hp

  have hp : vTransc V h htran p ≠ 0 := (vTransc V h htran).zero_iff.ne.mpr hp
  have hmem : vTransc V h htran p ∈ Set.range (vTransc V h htran) := by simp
  rw [vTransc_valueImmediate] at hmem
  have : ∃ s, vTransc V h htran (RatFunc.C s) = vTransc V h htran p := by simpa using hmem
  obtain ⟨s, hs⟩ := this
  have : vTransc V h htran (p / Polynomial.C s : K[X]) = 1 := by
    -- why is this one hard?
    change vTransc V h htran (algebraMap K[X] (RatFunc K) (p / Polynomial.C s)) = 1
    rw [Polynomial.div_C, map_mul, Valuation.map_mul]
    simp only [RatFunc.algebraMap_C, map_inv₀, hs]
    change (vTransc V h htran) p * ((vTransc V h htran) p)⁻¹ = 1
    rw [mul_inv_cancel₀ hp]
  obtain ⟨b, hb1, hb2⟩ := vTransc_exists_close V h htran this
  refine ⟨b * s, ?_, ?_⟩
  · rw [Valuation.map_mul, ← hs, vTransc_C]
    simp [hb1]
  · rw [← div_lt_one₀ (lt_of_le_of_ne (zero_le') hp.symm)]
    rw [← hs, ← Valuation.map_div, sub_div, map_mul, mul_div_cancel_right₀ _ ?_]
    · --- ehh
      change (vTransc V h htran) (RatFunc.C b -
        algebraMap K[X] (RatFunc K) (p / Polynomial.C s)) < 1 at hb2
      rw [Polynomial.div_C, map_mul] at hb2
      rw [div_eq_mul_inv]
      simpa using hb2
    rw [← (vTransc V h htran).zero_iff.ne, hs]
    exact hp

theorem vTransc_residueImmediate [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) :
    Function.Surjective (IsLocalRing.ResidueField.map
      (algebraMap V.integer (vTransc V h htran).integer)) := by
  intro r
  induction r with | residue r
  suffices ∃ s, IsLocalRing.residue (vTransc V h htran).integer
      (algebraMap V.integer (vTransc V h htran).integer s - r) = 0 by
    obtain ⟨s, hs⟩ := this
    rw [map_sub, sub_eq_zero] at hs
    use IsLocalRing.residue V.integer s
    rw [← hs, IsLocalRing.ResidueField.map_residue]
  simp_rw [IsLocalRing.residue_eq_zero_iff]
  simp_rw [show IsLocalRing.maximalIdeal (vTransc V h htran).integer
    = IsLocalRing.maximalIdeal (vTransc V h htran).valuationSubring by rfl] -- ehh
  obtain ⟨r, hr⟩ := r
  have hr : vTransc V h htran r ≤ 1 := by simpa using hr
  suffices ∃ s,
    vTransc V h htran
      ((algebraMap V.integer (vTransc V h htran).integer) s - r) < 1 by
    obtain ⟨s, hs⟩ := this
    use s
    rw [Valuation.mem_maximalIdeal_iff]
    exact hs -- not sure why simp_rw didn't work
  suffices ∃ s ∈ V.integer, vTransc V h htran (RatFunc.C s - r) < 1 by simpa
  obtain hr | hr := lt_or_eq_of_le hr
  · exact ⟨0, by simp, by simpa using hr⟩
  induction r using RatFunc.induction_on' with | _pq p q hq
  simp_rw [vTransc_mk] at hr
  obtain rfl | hp := eq_or_ne p 0
  · exact ⟨0, by simp⟩
  obtain ⟨sp, hsp, hsp2⟩ := vTransc_exists_close' V h htran hp
  obtain ⟨sq, hsq, hsq2⟩ := vTransc_exists_close' V h htran hq
  have hspsq : V sp = V sq := by
    rw [hsp, hsq]
    simp_rw [vTransc_polynomial]
    apply eq_of_div_eq_one hr
  refine ⟨sp / sq, ?_, ?_⟩
  · rw [Valuation.mem_integer_iff, Valuation.map_div, hsp, hsq]
    simp [vTransc_polynomial, hr]
  have hq0 : (algebraMap K[X] (RatFunc K)) q ≠ 0 := by simpa using hq
  have hsq0 : RatFunc.C sq ≠ 0 := by
    rw [(vTransc V h htran).zero_iff.ne.symm, vTransc_C, hsq]
    simp only [ne_eq, map_eq_zero]
    exact hq0
  rw [map_div₀, RatFunc.mk_eq_div, div_sub_div _ _ hsq0 hq0, Valuation.map_div]
  rw [div_lt_one₀ (lt_of_le_of_ne zero_le' (by
    symm
    rw [(vTransc V h htran).zero_iff.ne]
    apply mul_ne_zero hsq0 hq0))]
  rw [show RatFunc.C sp * (algebraMap K[X] (RatFunc K)) q -
      RatFunc.C sq * (algebraMap K[X] (RatFunc K)) p =
    RatFunc.C sp * ((algebraMap K[X] (RatFunc K)) q - RatFunc.C sq) -
    RatFunc.C sq * ((algebraMap K[X] (RatFunc K)) p - RatFunc.C sp) by ring]
  change (vTransc V h htran) (RatFunc.C sp * (q - RatFunc.C sq) -
    RatFunc.C sq * (p - RatFunc.C sp)) < (vTransc V h htran) (RatFunc.C sq * q) -- ehh
  have hsq0' : 0 < V sq := by
    apply lt_of_le_of_ne zero_le'
    rw [hsq]
    symm
    rw [(vTransc V h htran).zero_iff.ne]
    exact hq0
  apply Valuation.map_sub_lt
  · simp_rw [Valuation.map_mul, vTransc_C]
    rw [hspsq]
    apply mul_lt_mul_of_pos_left
    · rw [Valuation.map_sub_swap]
      exact hsq2
    · exact hsq0'
  · simp_rw [Valuation.map_mul, vTransc_C]
    apply mul_lt_mul_of_pos_left
    · rw [Valuation.map_sub_swap, ← hsq, ← hspsq, hsp]
      exact hsp2
    · exact hsq0'

noncomputable
def vAlg [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a) (p0 : K[X]) [Fact (Irreducible p0)]
    (hp0 : ∀ p : K[X], p.degree < p0.degree →
      ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) :
    Valuation (AdjoinRoot p0) Γ where
  toFun := sorry
  map_zero' := sorry
  map_one' := sorry
  map_mul' := sorry
  map_add_le_max' := sorry
