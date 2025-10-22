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

/-theorem Valuation.map_geom_sum {x y : K} (h2 : V (x - y) < V x) (n : ℕ) :
    V (∑ i ∈ Finset.range (n + 1), x ^ i * y ^ (n - i)) = V x ^ n := by
  obtain rfl | hx := eq_or_ne x 0
  · simp at h2
  let e := y - x
  have : y = x + e := by simp [e]
  rw [V.map_sub_swap] at h2
  rw [this] at ⊢ h2
  rw [add_sub_cancel_left] at h2
  simp_rw [add_pow]
  simp_rw [Finset.mul_sum, ← mul_assoc, ← pow_add]

  have : ∑ i ∈ Finset.range (n + 1),
      ∑ j ∈ Finset.range (n - i + 1), x ^ (i + j) * e ^ (n - i - j) * ((n - i).choose j) =
      ∑ p ∈ (Finset.range (n + 1)).sigma (fun i ↦ Finset.range (n - i + 1)),
        x ^ (p.1 + p.2) * e ^ (n - p.1 - p.2) * ((n - p.1).choose p.2) :=
    (Finset.sum_sigma (Finset.range (n + 1)) (fun i ↦ Finset.range (n - i + 1))
      (fun (p : (_ : ℕ) × ℕ) ↦ x ^ (p.1 + p.2) * e ^ (n - p.1 - p.2) * ((n - p.1).choose p.2))).symm
  rw [this]

  have : ∑ p ∈ (Finset.range (n + 1)).sigma (fun i ↦ Finset.range (n - i + 1)),
        x ^ (p.1 + p.2) * e ^ (n - p.1 - p.2) * ((n - p.1).choose p.2) =
      ∑ p ∈ (Finset.range (n + 1)).sigma (fun k ↦ Finset.range (k + 1)),
        x ^ p.1 * e ^ (n - p.1) * ((n - p.2).choose (p.1 - p.2)) := by
    refine Finset.sum_nbij' (fun p ↦ ⟨p.1 + p.2, p.1⟩)
      (fun p ↦ ⟨p.2, p.1 - p.2⟩) ?_ ?_ ?_ ?_ ?_
    · simp only [Finset.mem_sigma, Finset.mem_range, and_imp]
      grind
    · simp only [Finset.mem_sigma, Finset.mem_range, and_imp]
      grind
    · simp only [Finset.mem_sigma, Finset.mem_range, and_imp]
      grind
    · simp only [Finset.mem_sigma, Finset.mem_range, and_imp]
      grind
    · grind
  rw [this, Finset.sum_sigma]
  simp only
  simp_rw [mul_assoc, ← Finset.mul_sum]

  have hv {k : ℕ} (h : k < n + 1) :
      V (x ^ k * (e ^ (n - k) * ∑ i ∈ Finset.range (k + 1), ↑((n - i).choose (k - i)))) =
      V x ^ k * V e ^ (n - k) := by
    simp_rw [V.map_mul]
    norm_cast
    --rw [V.map_nat]
    sorry

  rw [V.map_sum_eq_of_lt (show n ∈ Finset.range (n + 1) by simp) ?_ ?_]
  · rw [hv (by simp)]
    simp
  · rw [hv (by simp)]
    simp [hx]
  · intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hk
    obtain ⟨hk1, hk2⟩ := hk
    rw [hv (by simpa using hk1)]
    rw [hv (by simp)]
    rw [show V x ^ n * V e ^ (n - n) = V x ^ k * V x ^ (n - k) by
      simp [← pow_add, Nat.add_sub_cancel' (Nat.le_of_lt_add_one hk1)]]
    refine mul_lt_mul_of_pos_left ?_ (pow_pos (V.pos_iff.mpr hx) _)
    apply pow_lt_pow_left₀ h2 (by simp)
    apply Nat.sub_ne_zero_of_lt
    apply lt_of_le_of_ne (Nat.le_of_lt_add_one hk1) hk2-/


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
        apply mul_lt_mul_of_nonneg (h j k hjk) (ih j k hij hjk) (by simp) (by simp)
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
  obtain hd := (mul_lt_mul_iff_left₀ (lt_of_le_of_ne (by simp) (h0.symm))).mpr hd
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

theorem vPoly_mul [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a) (p q : K[X]) :
    vPoly V a (p * q) = vPoly V a p * vPoly V a q := by
  obtain hp | hp := IsPseudoConv.lemma1_poly V h p
  ·
    sorry
  ·
    sorry

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
