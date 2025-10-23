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

theorem IsPseudoConv.lemma1 {a : ι → K} (h : IsPseudoConv V a) :
    (∀ i j, i < j → V (a j) < V (a i)) ∨ (∃ l, ∀ i, l ≤ i → V (a l) = V (a i)) := by
  rw [or_iff_not_imp_left]
  intro hleft
  simp_rw [not_forall, exists_prop, not_lt] at hleft
  obtain ⟨i, j, hlt, hle⟩ := hleft
  use j
  intro k hk
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

theorem IsPseudoConv.lemma1_prod [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a) (s : Multiset K) :
    (∃ i, ∀ j k, i ≤ j → j < k → V (s.map fun c ↦ a k - c).prod < V (s.map fun c ↦ a j - c).prod) ∨
    (∃ l, ∀ i, l ≤ i → V (s.map fun c ↦ a l - c).prod = V (s.map fun c ↦ (a i) - c).prod) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons c s ih =>
    simp_rw [Multiset.map_cons, Multiset.prod_cons, V.map_mul]
    obtain ⟨i, ih⟩ | ⟨i, ih⟩ := ih
    · obtain h | ⟨l, h⟩ := IsPseudoConv.lemma1 V <| IsPseudoConv.sub_const V h c
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
    · obtain h | ⟨l, h⟩ := IsPseudoConv.lemma1 V <| IsPseudoConv.sub_const V h c
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
  induction d' using IsLocalRing.ResidueField.ind with | residue dout
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

theorem vPoly_eq_zero [Nonempty ι] {a : ι → K} (ha : IsPseudoConv V a) (p : K[X]) :
    vPoly V a p = 0 ↔ p = 0 ∨ (¬ ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) := by
  constructor
  · intro h
    apply or_not_of_imp
    intro h'
    obtain ⟨l, hl⟩ := h'
    rw [vPoly_eq V a p l hl] at h
    rw [h] at hl
    contrapose! hl with h0
    obtain ⟨i, hi, hi2⟩ := IsPseudoConv.exists_poly_ne_zero V ha h0 l
    use i, hi
    symm
    simpa using hi2
  · intro h
    obtain rfl | h := h
    · simp [vPoly]
    · simp [vPoly, h]

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
theorem vPoly_add [Nonempty ι] {a : ι → K} (p q : K[X])
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

noncomputable
def vTransc {a : ι → K} (h : IsPseudoConv V a)
    (htranscendental : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) :
    Valuation K[X] Γ where
  toFun p := V (p.eval (a (htranscendental p).choose))
  map_zero' := by simp
  map_one' := by simp
  map_mul' p q := sorry
  map_add_le_max' := sorry

noncomputable
def vTranscRat {a : ι → K} (h : IsPseudoConv V a)
    (htranscendental : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) :
    Valuation (RatFunc K) Γ where
  toFun p := RatFunc.liftOn' p (fun p q ↦ (vTransc V h htranscendental p) /
    (vTransc V h htranscendental q)) (fun {p q a} hq ha ↦ by
      simp_rw [map_mul]
      rw [mul_div_mul_left _ _ ?_]
      exact V.ne_zero_iff.mpr sorry
    )
  map_zero' := sorry --by simp
  map_one' := sorry --by simp
  map_mul' p q := sorry
  map_add_le_max' := sorry
