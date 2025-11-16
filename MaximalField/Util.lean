import Mathlib

open scoped Polynomial


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



@[simp]
lemma zero_le'' {G : Type*}
    [CommGroupWithZero G] [LinearOrder G] [IsOrderedMonoid G] [ZeroLEOneClass G]
    (a : G) : 0 ≤ a := by
  simpa only [mul_zero, mul_one] using mul_le_mul_left' (zero_le_one' G) a

@[simp]
lemma not_lt_zero'' {G : Type*}
    [CommGroupWithZero G] [LinearOrder G] [IsOrderedMonoid G] [ZeroLEOneClass G]
    (a : G) : ¬a < 0 := by
  simp


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



theorem lemma4₀ {G : Type*}
    [CommGroupWithZero G] [LinearOrder G] [IsOrderedMonoid G] [ZeroLEOneClass G]
    {ι : Type*} [LinearOrder ι] [NoMaxOrder ι] [Nonempty ι]
    (t : Finset ℕ) (c : ℕ → G) (htc : ∃ n ∈ t, c n ≠ 0) {a : ι → G} (ha : StrictAnti a) :
    ∃ m ∈ t, c m ≠ 0 ∧ ∃ l, ∀ i, l ≤ i → ∀ n ∈ t \ {m}, c n * a i ^ n < c m * a i ^ m  := by
  let t' := t.filter fun n ↦ c n ≠ 0
  have hunit (n : ℕ) (hn : n ∈ t') : IsUnit (c n) := by
    rw [isUnit_iff_ne_zero]
    grind
  choose! c' hc using hunit
  have ht' : t'.Nonempty := by grind
  have ha0 (i : ι) : a i ≠ 0 := by
    by_contra! h0
    obtain ⟨j, hj⟩ := exists_gt i
    obtain what := h0 ▸ (ha hj)
    simp at what
  have haunit (i : ι) : IsUnit (a i) := by simpa using ha0 i
  choose a' haeq using haunit
  have ha' : StrictAnti a' := by
    intro i j h
    simpa [← haeq] using ha h
  obtain ⟨m, hmt, l, hm⟩ := lemma4 ht' c' ha'
  have hmt' :  m ∈ t ∧ c m ≠ 0 := by simpa [t'] using hmt
  refine ⟨m, hmt'.1, hmt'.2, l, fun i hi n hn ↦ ?_⟩
  obtain h0 | h0 := eq_or_ne (c n) 0
  · rw [h0, zero_mul]
    apply lt_of_le_of_ne (by simp)
    symm
    apply mul_ne_zero hmt'.2
    suffices a i ≠ 0 by simp [this]
    exact ha0 i
  have hn : n ∈ t' := by grind
  have hn' : n ∈ t' \ {m} := by grind
  simp_rw [← hc m hmt, ← hc n hn, ← haeq]
  norm_cast
  apply hm i hi n hn'

theorem RatFunc.liftMonoidWithZeroHom_apply_mk {G₀ : Type*} {R : Type*}
    [CommGroupWithZero G₀] [CommRing R] [IsDomain R]
    (φ : Polynomial R →*₀ G₀)
    (hφ : nonZeroDivisors (Polynomial R) ≤ Submonoid.comap φ (nonZeroDivisors G₀))
    (n : Polynomial R) (d : Polynomial R) :
    liftMonoidWithZeroHom φ hφ (RatFunc.mk n d) = φ n / φ d := by
  simp

theorem RatFunc.C_eq_mk {K : Type*} [CommRing K] [IsDomain K] (a : K) :
    RatFunc.C a = RatFunc.mk (Polynomial.C a) (1 : K[X]) := rfl

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

theorem Polynomial.taylor_expand {R : Type*} [CommRing R] (r : R) (f : Polynomial R) :
    f = ∑ i ∈ Finset.range (f.natDegree + 1),
    Polynomial.C ((f.hasseDeriv i).eval r) * (Polynomial.X - Polynomial.C r) ^ i := by
  nontriviality R
  simp_rw [← Polynomial.taylor_coeff]
  simp_rw [Polynomial.taylor_apply]
  trans (f.comp (X + C r)).comp (X - C r)
  · rw [Polynomial.comp_assoc]
    simp
  rw [Polynomial.comp_eq_sum_left]
  rw [Polynomial.sum_def]
  refine Finset.sum_subset ?_ ?_
  · intro i hi
    rw [Polynomial.mem_support_iff] at hi
    obtain hi := (Polynomial.le_natDegree_of_ne_zero hi).trans Polynomial.natDegree_comp_le
    simpa [Nat.lt_add_one_iff] using hi
  · intro i hi hisupport
    rw [mem_support_iff, not_not] at hisupport
    simp [hisupport]

def AdjoinRoot.lift' {R S : Type*} [CommRing R] (p : Polynomial R)
    (f : Polynomial R → S) (h : ∀ a b, p ∣ a - b → f a = f b) (x : AdjoinRoot p) :=
  Quotient.lift f (fun a b hab ↦ by
    change (Ideal.span {p}).quotientRel a b at hab
    rw [Submodule.quotientRel_def] at hab
    rw [Ideal.mem_span_singleton] at hab
    apply h a b hab) x

@[simp]
theorem AdjoinRoot.lift'_mk {R S : Type*} [CommRing R] (p : Polynomial R)
    (f : Polynomial R → S) (h : ∀ a b, p ∣ a - b → f a = f b) (x : Polynomial R) :
    lift' p f h (mk p x) = f x := rfl

theorem Polynomial.mod_eq_of_dvd_sub {R : Type*} [Field R] {p₁ p₂ q : R[X]}
    (h : q ∣ p₁ - p₂) : p₁ % q = p₂ % q := by
  obtain rfl | hq := eq_or_ne q 0
  · simpa [sub_eq_zero] using h
  simp_rw [Polynomial.mod_def]
  refine Polynomial.modByMonic_eq_of_dvd_sub ?_ ?_
  · simp [Polynomial.Monic.def, hq]
  rw [mul_comm]
  exact (Polynomial.C_mul_dvd (by simpa using hq)).mpr h

theorem Polynomial.degree_mod_lt {R : Type*} [Field R] (p : R[X]) {q : R[X]} (hq : q ≠ 0) :
    (p % q).degree < q.degree := by
  rw [Polynomial.mod_def]
  refine (Polynomial.degree_modByMonic_lt p ?_).trans_eq (by simp)
  · simp [Polynomial.Monic.def, hq]

theorem Polynomial.add_mod {R : Type*} [Field R] (p₁ p₂ q : R[X]) :
    (p₁ + p₂) % q = p₁ % q + p₂ % q := by
  simp_rw [Polynomial.mod_def]
  rw [Polynomial.add_modByMonic]

theorem Polynomial.sub_mod {R : Type*} [Field R] (p₁ p₂ q : R[X]) :
    (p₁ - p₂) % q = p₁ % q - p₂ % q := by
  simp_rw [Polynomial.mod_def]
  rw [Polynomial.sub_modByMonic]

theorem Polynomial.mul_modByMonic {R : Type*} [Field R] (p₁ p₂ q : R[X]) :
    (p₁ * p₂) %ₘ q = ((p₁ %ₘ q) * (p₂ %ₘ q)) %ₘ q := by
  by_cases! h : ¬ q.Monic
  · simp [Polynomial.modByMonic_eq_of_not_monic, h]
  apply Polynomial.modByMonic_eq_of_dvd_sub h
  rw [show p₁ * p₂ - p₁ %ₘ q * (p₂ %ₘ q) =
    (p₁ %ₘ q) * (p₂ - p₂ %ₘ q) + p₂ * (p₁ - p₁ %ₘ q)  by ring]
  apply dvd_add
  all_goals
  · apply dvd_mul_of_dvd_right
    rw [Polynomial.modByMonic_eq_sub_mul_div _ h]
    simp

theorem Polynomial.mul_mod {R : Type*} [Field R] (p₁ p₂ q : R[X]) :
    (p₁ * p₂) % q = ((p₁ % q) * (p₂ % q)) % q := by
  simp_rw [Polynomial.mod_def]
  rw [Polynomial.mul_modByMonic]

theorem Valuation.map_sub_of_distinct_val {R : Type*} {Γ₀ : Type*}
    [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation R Γ₀) {x y : R} (h : v x ≠ v y) :
    v (x - y) = max (v x) (v y) := by
  rw [sub_eq_add_neg]
  rw [Valuation.map_add_of_distinct_val v ?_] <;> rw [Valuation.map_neg]
  exact h

/-variable {A B C ΓA ΓB ΓC : Type*} [CommRing A] [CommRing B] [Ring C]
  [LinearOrderedCommMonoidWithZero ΓA]
  [LinearOrderedCommMonoidWithZero ΓB]
  [LinearOrderedCommMonoidWithZero ΓC]
  [Algebra A B] [Algebra B C]
  (VA : Valuation A ΓA)
  (VB : Valuation A ΓB)
  (VC : Valuation A ΓC)
  [VA.HasExtension VB] [VB.HasExtension VC]-/

def Algebra.trans (A B C : Type*) [CommSemiring A] [CommSemiring B] [Semiring C]
    [Algebra A B] [Algebra B C] :
  Algebra A C := Algebra.compHom C (algebraMap A B)

instance Algebra.isScalarTower (A B C : Type*) [CommSemiring A] [CommSemiring B] [Semiring C]
    [Algebra A B] [Algebra B C] :
  let := Algebra.trans A B C
  IsScalarTower A B C := IsScalarTower.of_compHom A B C

theorem Valuation.HasExtension.trans {A B C ΓA ΓB ΓC : Type*} [CommRing A] [CommRing B] [Ring C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [LinearOrderedCommMonoidWithZero ΓA]
    [LinearOrderedCommMonoidWithZero ΓB]
    [LinearOrderedCommMonoidWithZero ΓC]
    (VA : Valuation A ΓA)
    (VB : Valuation B ΓB)
    (VC : Valuation C ΓC)
    [hAB : VA.HasExtension VB] [hBC : VB.HasExtension VC] :
    VA.HasExtension VC where
  val_isEquiv_comap := by
    rw [IsScalarTower.algebraMap_eq A B C, Valuation.comap_comp]
    apply Valuation.IsEquiv.trans hAB.val_isEquiv_comap
    apply Valuation.IsEquiv.comap
    exact hBC.val_isEquiv_comap

variable {K : Type*} [Field K]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (V : Valuation K Γ)

theorem exists_valuation_extension.{u}
  {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (V : Valuation K Γ)
  (L : Type u) [Field L] [Algebra K L] :
  ∃ (Γ' : Type u) (_ : LinearOrderedCommGroupWithZero Γ') (V' : Valuation L Γ'),
  Valuation.HasExtension V V' := sorry
