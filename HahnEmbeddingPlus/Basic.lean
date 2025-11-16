import Mathlib
import HahnEmbeddingPlus.Util

open scoped Polynomial

variable {K : Type*} [Field K]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (V : Valuation K Γ)
variable {ι : Type*} [LinearOrder ι]

def IsPseudoConv (a : ι → K) : Prop := ∀ ⦃i j k⦄, i < j → j < k → V (a j - a k) < V (a i - a j)

theorem IsPseudoConv.sub_const {a : ι → K} (h : IsPseudoConv V a) (c : K) :
    IsPseudoConv V (fun i ↦ a i - c) := by
  unfold IsPseudoConv at ⊢ h
  intro i j k hij hjk
  convert h hij hjk using 1 <;> simp

theorem IsPseudoConv.add_const {a : ι → K} (h : IsPseudoConv V a) (c : K) :
    IsPseudoConv V (fun i ↦ a i + c) := by
  unfold IsPseudoConv at ⊢ h
  intro i j k hij hjk
  convert h hij hjk using 1 <;> simp

theorem IsPseudoConv.const_sub {a : ι → K} (h : IsPseudoConv V a) (c : K) :
    IsPseudoConv V (fun i ↦ c - a i) := by
  unfold IsPseudoConv at ⊢ h
  intro i j k hij hjk
  convert h hij hjk using 1 <;> simp [Valuation.map_sub_swap]

theorem IsPseudoConv.const_mul {a : ι → K} (h : IsPseudoConv V a) {c : K} (hc : c ≠ 0) :
    IsPseudoConv V (fun i ↦ c * a i) := by
  unfold IsPseudoConv at ⊢ h
  intro i j k hij hjk
  simp_rw [← mul_sub, map_mul]
  exact mul_lt_mul_of_pos_left (h hij hjk) (V.pos_iff.mpr hc)

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

theorem lemma1_prod [Nonempty ι] {a : ι → K} (s : Multiset K)
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
    have hexist : ∃ n ∈ Finset.Ico 1 (p'.natDegree + 1),
        (fun n ↦ V' ((p'.hasseDeriv n).eval x)) n ≠ 0 := by
      use p'.natDegree
      constructor
      · suffices 1 ≤ p.natDegree by simpa [p']
        grind
      suffices p' ≠ 0 by simpa [Polynomial.hasseDeriv_natDegree_eq_C]
      suffices p ≠ 0 by simpa [p']
      contrapose! hd0
      simp [hd0]
    obtain ⟨m, hm, hm0, l, hl⟩ := lemma4₀ (Finset.Ico 1 (p'.natDegree + 1))
      (fun n ↦ V' ((p'.hasseDeriv n).eval x)) hexist hanti
    use l
    intro i j k hli hij hjk
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
      apply V'.map_sum_eq_of_lt hm
      intro n hn
      simp_rw [map_mul, map_pow]
      apply hl i hli n hn
    have hmne0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Ico.mp hm).1
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
      rw [mul_lt_mul_iff_right₀ (lt_of_le_of_ne (by simp) hm0.symm)]
      apply pow_lt_pow_left₀ (hanti hij) (by simp) hmne0
    rw [this i j hli hij, this j k (hli.trans (hij.le)) hjk]
    simp_rw [map_mul, map_pow]
    rw [mul_lt_mul_iff_right₀ (lt_of_le_of_ne (by simp) hm0.symm)]
    apply pow_lt_pow_left₀ (hanti hij) (by simp) hmne0
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
      apply lemma1_prod
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
    suffices ∃ m ∈ Finset.Ico 1 (p.natDegree + 1), V ((p.hasseDeriv m).eval (a (fl m))) ≠ 0 ∧
      ∃ l, ∀ i, l ≤ i → ∀ n ∈ Finset.Ico 1 (p.natDegree + 1) \ {m},
        V ((p.hasseDeriv n).eval (a (fl n))) * γ V a i ^ n <
        V ((p.hasseDeriv m).eval (a (fl m))) * γ V a i ^ m by
      obtain ⟨m, hm, hm0, l, h⟩ := this
      use m, hm, max l ((Finset.Ico 1 (p.natDegree + 1)).sup' (by simpa using hd0) fl)
      intro i j hli hij
      obtain ⟨hli, hmi⟩ := max_le_iff.mp hli
      rw [Finset.sup'_le_iff] at hmi
      rw [show V (a j - a i) = γ V a i by rw [V.map_sub_swap, ha.γ_eq V hij]]
      convert h i hli using 4 with n hn
      · exact (hfl _ _ <| hmi _ (Finset.mem_sdiff.mp hn).1).symm
      · exact (hfl _ _ <| hmi _ hm).symm
    refine lemma4₀ _ _ ?_ (γ_strictAnti V ha)
    use p.natDegree
    constructor
    · suffices 1 ≤ p.natDegree by simpa
      grind
    have : p.hasseDeriv p.natDegree ≠ 0 := by
      suffices p ≠ 0 by simpa [Polynomial.hasseDeriv_natDegree_eq_C]
      contrapose! hd0
      simp [hd0]
    simpa using (hfl' p.natDegree).resolve_left this

theorem IsPseudoConv.lemma1_poly [Nonempty ι] {a : ι → K}
    (h : IsPseudoConv V a) (p : K[X]) :
    (∃ i, ∀ j k, i ≤ j → j < k → V (p.eval (a k)) < V (p.eval (a j))) ∨
    (∃ l, (∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))) := by
  obtain hp | hp := Nat.eq_zero_or_pos p.natDegree
  · obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hp
    simp
  obtain ⟨l, hl⟩ := IsPseudoConv.poly_eventually V h hp
  have : IsPseudoConv V fun (i : Set.Ici l) ↦ p.eval (a i) := by
    intro i j k hij hjk
    exact hl i.prop hij hjk
  obtain h | ⟨m, h⟩ := this.lemma1
  · exact Or.inl ⟨l, fun j k hlj hjk ↦ h ⟨j, hlj⟩ ⟨k, hlj.trans hjk.le⟩ hjk⟩
  · exact Or.inr ⟨m, fun i hi ↦ (h.1 ⟨i, m.prop.trans hi⟩ hi)⟩

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

def IsMaximal.{u, v} {K : Type u} [Field K]
    {Γ : Type v} [LinearOrderedCommGroupWithZero Γ] (V : Valuation K Γ) :=
  ∀ (L : Type u) (Γ' : Type v) (_ : Field L) (_ : LinearOrderedCommGroupWithZero Γ')
  (V' : Valuation L Γ') (_ : Algebra K L) (_ : Valuation.HasExtension V V')
  (_ : IsImmediate V V'), Function.Surjective (algebraMap K L)

theorem IsImmediate.id : IsImmediate V V := by
  constructor
  · simp
  · simpa using Function.surjective_id

theorem IsImmediate.trans {A B C ΓA ΓB ΓC : Type*} [Field A] [Field B] [Field C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [LinearOrderedCommGroupWithZero ΓA]
    [LinearOrderedCommGroupWithZero ΓB]
    [LinearOrderedCommGroupWithZero ΓC]
    {VA : Valuation A ΓA}
    {VB : Valuation B ΓB}
    {VC : Valuation C ΓC}
    [hAB : VA.HasExtension VB] [hBC : VB.HasExtension VC]
    (hABimm : IsImmediate VA VB) (hBCimm : IsImmediate VB VC) :
    have := Valuation.HasExtension.trans VA VB VC
    IsImmediate VA VC := by
  obtain ⟨hABv, hABr⟩ := hABimm
  obtain ⟨hBCv, hBCr⟩ := hBCimm
  constructor
  · rw [hBCv]
    simp_rw [Algebra.coe_bot]
    rw [IsScalarTower.algebraMap_eq A B C, RingHom.coe_comp, Set.range_comp]
    rw [← Set.image_comp]
    rw [Algebra.coe_bot, Set.ext_iff] at hABv
    ext c
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Function.comp_apply]
    constructor
    · rintro ⟨b, hb⟩
      rw [← hb]
      simp_rw [Valuation.HasExtension.val_map_eq_iff VB VC]
      specialize hABv (VB b)
      simpa using hABv
    · rintro ⟨a, ha⟩
      simp [← ha, Valuation.HasExtension.val_map_eq_iff VB VC]
  · intro c
    induction c using IsLocalRing.ResidueField.ind with | residue c
    obtain ⟨b, hb⟩ := hBCr ((IsLocalRing.residue VC.integer) c)
    induction b using IsLocalRing.ResidueField.ind with | residue b
    rw [IsLocalRing.ResidueField.map_residue] at hb
    obtain ⟨a, ha⟩ := hABr ((IsLocalRing.residue VB.integer) b)
    use a
    induction a using IsLocalRing.ResidueField.ind with | residue a
    have := Valuation.HasExtension.trans VA VB VC
    have htrans : (algebraMap VA.integer VC.integer) =
        (algebraMap ↥VB.integer ↥VC.integer) ∘ (algebraMap ↥VA.integer ↥VB.integer) := by
      ext a
      simp [IsScalarTower.algebraMap_eq A B C]
    rw [IsLocalRing.ResidueField.map_residue] at ha
    rw [IsLocalRing.ResidueField.map_residue, ← hb]
    simp only [htrans, Function.comp_apply]
    simp_rw [← IsLocalRing.ResidueField.map_residue (algebraMap ↥VB.integer ↥VC.integer)]
    rw [ha]

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
    ∃ (s : Set Γ'ᵒᵈ) (_ : s.Nonempty) (_ : NoMaxOrder s) (a : s → K), IsPseudoConv V a ∧
    (∀ x : K, ¬ HasLimit V a x) ∧ (HasLimit V' (algebraMap K L ∘ a) z) := by
  let s := Set.range fun a ↦ OrderDual.toDual <| V' (z - algebraMap K L a)
  have hmax : ∀ (g : s), ∃ g', g < g' := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha⟩ := Set.mem_range.mp hg
    obtain ⟨b, hb⟩ := h.exists_lt V V' hz a
    exact ⟨⟨OrderDual.toDual <| V' (z - algebraMap K L b), by simp [s]⟩, by simpa [← ha] using hb⟩
  have : NoMaxOrder s := ⟨hmax⟩
  refine ⟨s, (by simpa [s] using Set.range_nonempty _), inferInstance, ?_⟩
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
