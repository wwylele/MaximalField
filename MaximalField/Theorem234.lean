import MaximalField.Basic


open scoped Polynomial

variable {K : Type*} [Field K]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (V : Valuation K Γ)
variable {ι : Type*} [LinearOrder ι] [NoMaxOrder ι]

variable {L : Type*} [Field L]
variable {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ'] (V' : Valuation L Γ')
variable [Algebra K L] [Valuation.HasExtension V V']

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

@[simps]
noncomputable
def vPolyMonoidWithZeroHom [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a) :
    K[X] →*₀ Γ where
  toFun := vPoly V a
  map_zero' := by simp [vPoly]
  map_one' := by simp [vPoly]
  map_mul' := vPoly_mul V h

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
  __ := RatFunc.liftMonoidWithZeroHom (vPolyMonoidWithZeroHom V h) (by
    intro p
    suffices p ≠ 0 → vPoly V a p ≠ 0 by simpa
    exact fun hp ↦ (vPoly_ne_zero V h hp).mpr (htran p)
    )
  map_add_le_max' p q := by
    induction p using RatFunc.induction_on' with | _pq p1 p2 hp
    induction q using RatFunc.induction_on' with | _pq q1 q2 hq
    rw [RatFunc.mk_add_mk _ _ _ _ hp hq]
    change ((RatFunc.liftMonoidWithZeroHom (vPolyMonoidWithZeroHom V h) _))
      (RatFunc.mk (p1 * q2 + p2 * q1) (p2 * q2)) ≤
      max (((RatFunc.liftMonoidWithZeroHom (vPolyMonoidWithZeroHom V h) _)) (RatFunc.mk p1 p2))
        (((RatFunc.liftMonoidWithZeroHom (vPolyMonoidWithZeroHom V h) _)) (RatFunc.mk q1 q2))
    rw [RatFunc.liftMonoidWithZeroHom_apply_mk]
    rw [RatFunc.liftMonoidWithZeroHom_apply_mk]
    rw [RatFunc.liftMonoidWithZeroHom_apply_mk]
    simp only [vPolyMonoidWithZeroHom_apply]
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

@[simp]
theorem vTransc_mk [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (p q : K[X]) :
    vTransc V h htran (RatFunc.mk p q) = vPoly V a p / vPoly V a q := by
  rw [vTransc]
  simp

@[simp]
theorem vTransc_C [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (p : K) :
    vTransc V h htran (RatFunc.C p) = V p := by
  rw [RatFunc.C_eq_mk]
  rw [vTransc_mk]
  simp [vPoly]

@[simp]
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
    simp

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

theorem vPoly_not_const [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (i j : ι) (hj : i < j) :
    vPoly V a (Polynomial.X - Polynomial.C (a i)) ≠
    vPoly V a (Polynomial.X - Polynomial.C (a j)) := by
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
  exact vPoly_not_const V h i j hj

theorem vPoly_exists_close [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    {p : K[X]} (hp : vPoly V a p = 1)
    (hptran : ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) :
    ∃ x, V x = 1 ∧ vPoly V a (Polynomial.C x - p) < 1 := by
  obtain hd0 | hd0 := Nat.eq_zero_or_pos p.natDegree
  · obtain ⟨x, hx⟩ := Polynomial.natDegree_eq_zero.mp hd0
    use x
    simpa [← hx, vPoly] using hp
  obtain ⟨m, hm⟩ := hptran
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
  apply vPoly_exists_close V h hp (htran p)

theorem vTransc_exists_close' [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    {p : K[X]} (hp : p ≠ 0):
    ∃ a : K, V a = vTransc V h htran p ∧
      vTransc V h htran (RatFunc.C a - p) < vTransc V h htran p := by
  have hp : (p : RatFunc K) ≠ 0 := by
    change (algebraMap _ _) p ≠ 0
    simpa using hp

  have hp : vTransc V h htran p ≠ 0 := (vTransc V h htran).zero_iff.ne.mpr hp
  have hmem : vTransc V h htran p ∈ Set.range (vTransc V h htran) := by simp [vTransc]
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
  suffices ∃ s, vTransc V h htran (algebraMap V.integer (vTransc V h htran).integer s - r) < 1 by
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

theorem vTransc_isImmediate [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) :
    IsImmediate V (vTransc V h htran) :=
  ⟨vTransc_valueImmediate V h htran, vTransc_residueImmediate V h htran⟩

theorem vPoly_equiv [Nonempty ι] {a : ι → K}
    (h : IsPseudoConv V a)
    (map : K[X] →ₐ[K] L)
    (hlimit : HasLimit V' (algebraMap K L ∘ a) (map Polynomial.X))
    (p : K[X]) (k : K) (hpk : V k = vPoly V a p)
    (htran : ∀ q : K[X], q.natDegree ≤ p.natDegree →
      ∃ l, ∀ (i : ι), l ≤ i → V (q.eval (a l)) = V (q.eval (a i))) :
    V' (map p) = V' (algebraMap _ _ k) := by
  obtain hp0 | hp0 := Nat.eq_zero_or_pos p.natDegree
  · obtain ⟨x, hx⟩ := Polynomial.natDegree_eq_zero.mp hp0
    have hpk : V k = V x := by simpa [← hx, vPoly] using hpk
    rw [← Valuation.HasExtension.val_map_eq_iff V V' _ _] at hpk
    simpa [← hx, Polynomial.C_eq_algebraMap] using hpk.symm

  have hlimit' : ∀ (i : ι), V' (map Polynomial.X - algebraMap K L (a i)) =
      γ V' (algebraMap K L ∘ a) i := by
    simpa [HasLimit, RatFunc.algebraMap_eq_C, Function.comp_apply] using hlimit

  have hsum (i : ι) : p - Polynomial.C (p.eval (a i)) = ∑ n ∈ Finset.Ico 1 (p.natDegree + 1),
      Polynomial.C ((p.hasseDeriv n).eval (a i)) * (Polynomial.X - Polynomial.C (a i)) ^ n := by
    nth_rw 1 [Polynomial.taylor_expand (a i) p]
    rw [Finset.sum_range_eq_add_Ico _ (by simp)]
    simp

  have hconst (n : ℕ) (hn : n ∈ Finset.Ico 1 (p.natDegree + 1)) :
      ∃ l, ∀ i, l ≤ i → V' (algebraMap _ _ ((p.hasseDeriv n).eval (a l))) =
      V' (algebraMap _ _ ((p.hasseDeriv n).eval (a i))) := by
    simp_rw [Valuation.HasExtension.val_map_eq_iff V V']
    exact htran _ <| (Polynomial.natDegree_hasseDeriv_le _ _).trans (by simp)
  choose! fl hfl using hconst

  have hanti : StrictAnti fun i ↦ V' (map Polynomial.X - algebraMap K L (a i)) := by
    simp_rw [hlimit']
    apply IsPseudoConv.γ_strictAnti
    exact (IsPseudoConv.iff V V').mp h

  have hexist : ∃ n ∈ Finset.Ico 1 (p.natDegree + 1),
      V' (algebraMap _ _ ((p.hasseDeriv n).eval (a (fl n)))) ≠ 0 := by
    use p.natDegree
    constructor
    · simpa using hp0
    suffices p ≠ 0 by simpa [Polynomial.hasseDeriv_natDegree_eq_C]
    contrapose! hp0
    simp [hp0]

  obtain ⟨m, hm, hm0, l, hl⟩ := lemma4₀ (Finset.Ico 1 (p.natDegree + 1))
    (fun n ↦ V' (algebraMap _ _ ((p.hasseDeriv n).eval (a (fl n))))) hexist hanti

  have hdom (i : ι) (hi : l ≤ i) (hfli : ∀ n ∈ Finset.Ico 1 (p.natDegree + 1), fl n ≤ i) :
      V' (map p - algebraMap _ _ (p.eval (a i))) =
      V' (algebraMap _ _ ((p.hasseDeriv m).eval (a (fl m)))) *
      V' (map Polynomial.X - algebraMap K L (a i)) ^ m := by
    rw [hfl m hm i (hfli m hm)]
    suffices V' (map (p - Polynomial.C (p.eval (a i)))) =
        V' (map (Polynomial.C ((p.hasseDeriv m).eval (a i)) *
        (Polynomial.X - Polynomial.C (a i)) ^ m)) by
      simpa [Polynomial.C_eq_algebraMap]
    rw [hsum, map_sum]
    apply V'.map_sum_eq_of_lt hm
    intro n hn
    obtain ⟨hn', _⟩ := Finset.mem_sdiff.mp hn
    suffices V' (algebraMap K L ((p.hasseDeriv n).eval (a i))) *
        V' (map Polynomial.X - algebraMap K L (a i)) ^ n <
        V' (algebraMap K L ((p.hasseDeriv m).eval (a i))) *
        V' (map Polynomial.X - algebraMap K L (a i)) ^ m by
      simpa [Polynomial.C_eq_algebraMap] using this
    rw [← hfl m hm i (hfli m hm)]
    rw [← hfl n hn' i (hfli n hn')]
    simpa using hl i hi n hn

  obtain ⟨pl, hpl⟩ := htran p (le_refl _)
  rw [vPoly_eq V a p pl hpl] at hpk
  rw [← Valuation.HasExtension.val_map_eq_iff V V'] at hpk
  rw [hpk]

  let i := max pl <| max l ((Finset.Ico 1 (p.natDegree + 1)).sup' (by simpa using hp0) fl)
  have hipl : pl ≤ i := by order
  have hil : l ≤ i := by order
  have hifl (n : ℕ) (hn : n ∈ Finset.Ico 1 (p.natDegree + 1)) : fl n ≤ i := by
    unfold i
    apply le_max_of_le_right
    apply le_max_of_le_right
    apply Finset.le_sup' _ hn
  obtain ⟨j, hj⟩ := exists_gt i
  obtain hdomi := hdom i hil hifl
  obtain hdomj := hdom j (hil.trans hj.le) (fun n hn ↦ (hifl n hn).trans hj.le)

  by_contra! hne
  simp_rw [← Valuation.HasExtension.val_map_eq_iff V V'] at hpl
  obtain hnei := hpl i hipl ▸ hne
  obtain hnej := hpl j (hipl.trans hj.le) ▸ hne
  rw [Valuation.map_sub_of_distinct_val _ hnei, ← hpl i hipl] at hdomi
  rw [Valuation.map_sub_of_distinct_val _ hnej, ← hpl j (hipl.trans hj.le)] at hdomj
  obtain hdomeq := hdomi.symm.trans hdomj
  rw [mul_eq_mul_left_iff] at hdomeq
  obtain hijeq := hdomeq.resolve_right hm0
  contrapose! hijeq
  apply ne_of_gt
  refine pow_lt_pow_left₀ ?_ (by simp) (Nat.one_le_iff_ne_zero.mp (Finset.mem_Ico.mp hm).1)
  simpa using hanti hj

theorem theorem2_equiv [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (htran : ∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (V' : Valuation (RatFunc K) Γ') [Valuation.HasExtension V V']
    (hlimit : HasLimit V' (algebraMap K (RatFunc K) ∘ a) RatFunc.X) :
    (vTransc V h htran).IsEquiv V' := by
  obtain ⟨himm, _⟩ := (Set.range_eq_iff _ _).mp (vTransc_valueImmediate V h htran)
  suffices ∀ (x : RatFunc K) (y : K), V y = vTransc V h htran x → V' x = V' (algebraMap _ _ y) by
    intro r s
    obtain ⟨r', hrimm⟩ : ∃ r', V r' = (vTransc V h htran) r := by simpa using himm r
    obtain ⟨s', hsimm⟩ : ∃ s', V s' = (vTransc V h htran) s := by simpa using himm s
    rw [this r r' hrimm, this s s' hsimm]
    rw [Valuation.HasExtension.val_map_le_iff V V']
    rw [hrimm, hsimm]
  suffices ∀ (x : K[X]) (y : K), V y = vPoly V a x →
      V' (algebraMap _ _ x) = V' (algebraMap _ _ y) by
    intro x y hxy
    induction x using RatFunc.induction_on' with | _pq p q hq
    obtain ⟨p', hp⟩ : ∃ p', V p' = vPoly V a p := by simpa using himm p
    obtain ⟨q', hq⟩ : ∃ q', V q' = vPoly V a q := by simpa using himm q
    rw [vTransc_mk, ← hp, ← hq, ← V.map_div] at hxy
    obtain hp2 := this p p' hp
    obtain hq2 := this q q' hq
    rw [← Valuation.HasExtension.val_map_eq_iff V V'] at hxy
    rw [hxy]
    rw [RatFunc.algebraMap_eq_C] at hp2 hq2
    simp [hp2, ← hq2]
  intro x y hxy
  exact vPoly_equiv V V' h ((Algebra.ofId K[X] (RatFunc K)).restrictScalars K)
    (by simpa using hlimit) x y hxy (fun q _ ↦ htran q)

/-def AdjoinRoot.liftMonoidWithZeroHom {R S : Type*} [CommRing R] [MonoidWithZero S]
    (p : Polynomial R) (f : Polynomial R →*₀ S) (h : ∀ a b, p ∣ a - b → f a = f b) :
    AdjoinRoot p →*₀ S where
  toFun := lift' p f h
  map_zero' := by
    rw [show (0 : AdjoinRoot p) = mk p 0 by simp]
    rw [AdjoinRoot.lift'_mk]
    simp
  map_one' := by
    rw [show (1 : AdjoinRoot p) = mk p 1 by simp]
    rw [AdjoinRoot.lift'_mk]
    simp
  map_mul' x y := by
    induction x using AdjoinRoot.induction_on with | ih x
    induction y using AdjoinRoot.induction_on with | ih y
    rw [← map_mul]
    simp_rw [AdjoinRoot.lift'_mk]
    simp

@[simp]
theorem AdjoinRoot.liftMonoidWithZeroHom_mk {R S : Type*} [CommRing R] [MonoidWithZero S]
    {p : Polynomial R} (f : Polynomial R →*₀ S) (h : ∀ a b, p ∣ a - b → f a = f b)
    (x : Polynomial R) :
    liftMonoidWithZeroHom p f h (mk p x) = f x := rfl-/

omit [NoMaxOrder ι] in
theorem vAlg_p_degree_pos [hι : Nonempty ι] (a : ι → K) (p0 : K[X])
    (h2 : ¬∃ l, ∀ i, l ≤ i → V (p0.eval (a l)) = V (p0.eval (a i))) :
    0 < p0.degree := by
  contrapose! h2 with h0
  rw [Polynomial.degree_le_zero_iff.mp h0]
  use hι.some
  simp

theorem vAlg_one_lt_degree [hι : Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (hlimit : ∀ x : K, ¬ HasLimit V a x) (p0 : K[X])
    (h2 : ¬∃ l, ∀ i, l ≤ i → V (p0.eval (a l)) = V (p0.eval (a i))) :
    1 < p0.degree := by
  by_contra! hdegree
  obtain hc1 | hc1 := eq_or_ne (p0.coeff 1) 0
  · contrapose h2
    rw [Polynomial.eq_X_add_C_of_degree_le_one hdegree]
    simp [hc1]
  rw [IsPseudoConv.lemma1_poly_iff' V h] at h2
  rw [Polynomial.eq_X_add_C_of_degree_le_one hdegree] at h2
  contrapose! hlimit
  have hpseudoconv : IsPseudoConv V (fun i ↦ p0.coeff 1 * a i + p0.coeff 0) := by
    apply IsPseudoConv.add_const
    exact IsPseudoConv.const_mul V h hc1
  have h2' : ∃ i, ∀ j k, i ≤ j → j < k →
      V (p0.coeff 1 * a k + p0.coeff 0) < V (p0.coeff 1 * a j + p0.coeff 0) := by simpa using h2
  have h2'' : ∀ i j, i < j →
      V (p0.coeff 1 * a j + p0.coeff 0) < V (p0.coeff 1 * a i + p0.coeff 0) := by
    apply (hpseudoconv.lemma1 V).resolve_right
    by_contra!
    obtain ⟨m, hm, _⟩ := this
    obtain ⟨l, hl⟩ := h2'
    obtain ⟨j, hj⟩ := exists_gt (max l m)
    obtain hmi := hm (max l m) (by simp)
    obtain hmj := hm j (le_trans (by simp) hj.le)
    specialize hl (max l m) j (by simp) hj
    simp [← hmi, ← hmj] at hl
  use -(p0.coeff 0 / p0.coeff 1)
  intro i
  rw [← neg_add', V.map_neg, add_comm]
  obtain ⟨j, hj⟩ := exists_gt i
  rw [h.γ_eq V hj]
  refine (mul_eq_mul_left_iff.mp ?_).resolve_right (show V (p0.coeff 1) ≠ 0 by simpa using hc1)
  simp_rw [← V.map_mul, mul_add, mul_sub]
  rw [mul_div_cancel₀ _ hc1]
  rw [show p0.coeff 1 * a i - p0.coeff 1 * a j =
    (p0.coeff 1 * a i + p0.coeff 0) - (p0.coeff 1 * a j + p0.coeff 0) by ring]
  rw [V.map_sub_swap]
  apply (V.map_sub_eq_of_lt_right ?_).symm
  apply h2'' _ _ hj

omit [NoMaxOrder ι] in
theorem vAlg_mod_p_degree [hι : Nonempty ι] (a : ι → K) (p0 : K[X])
    (h2 : ¬∃ l, ∀ i, l ≤ i → V (p0.eval (a l)) = V (p0.eval (a i)))
    (p : K[X]) :
    (p % p0).degree < p0.degree :=
  (Polynomial.degree_mod_lt _ (Polynomial.ne_zero_of_degree_gt (vAlg_p_degree_pos V a p0 h2)))


theorem vPoly_mul_mod [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a) (p0 : K[X])
    (h1 : ∀ p : K[X], p.degree < p0.degree → ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (h2 : ¬∃ l, ∀ i, l ≤ i → V (p0.eval (a l)) = V (p0.eval (a i)))
    {f g : K[X]} (hf : f.degree < p0.degree) (hg : g.degree < p0.degree) :
    vPoly V a (f * g % p0) = vPoly V a f * vPoly V a g := by
  rw [← vPoly_mul V h]
  have hdvd : p0 ∣ f * g - f * g % p0 := by
    rw [EuclideanDomain.mod_eq_sub_mul_div]
    simp
  obtain ⟨k, hk⟩ := hdvd
  obtain rfl | hk0 := eq_or_ne k 0
  · rw [mul_zero, sub_eq_zero] at hk
    simp [← hk]
  obtain ⟨lf, hlf⟩ := h1 f hf
  obtain ⟨lg, hlg⟩ := h1 g hg
  have hfmg : ∃ l, ∀ i, l ≤ i → V ((f * g).eval (a l)) = V ((f * g).eval (a i)) := by
    use max lf lg
    intro i hi
    simp_rw [Polynomial.eval_mul, V.map_mul]
    rw [← hlf i (by order), ← hlg i (by order)]
    rw [← hlf (max lf lg) (by order), ← hlg (max lf lg) (by order)]
  obtain ⟨lfmg, hlfmg⟩ := hfmg
  obtain ⟨lfg, hlfg⟩ := h1 (f * g % p0) (vAlg_mod_p_degree V a p0 h2 _)
  obtain ⟨lp0, hlp0⟩ := (h.lemma1_poly_iff' V p0).mp h2
  have hpk : ∃ l, ∀ i j, l ≤ i → i < j → V ((p0 * k).eval (a j)) < V ((p0 * k).eval (a i)) := by
    simp_rw [Polynomial.eval_mul, map_mul]
    obtain ⟨lk, hlk⟩ | ⟨lk, hlk⟩ := h.lemma1_poly V k <;> use max lk lp0 <;> intro i j hi hij
    · exact mul_lt_mul_of_nonneg (hlp0 i j (le_trans (by simp) hi) hij)
        (hlk i j (le_trans (by simp) hi) hij) (by simp) (by simp)
    · rw [← hlk i (le_trans (by simp) hi)]
      rw [← hlk j ((le_trans (by simp) hi).trans hij.le)]
      apply mul_lt_mul_of_pos_right (hlp0 i j (le_trans (by simp) hi) hij)
      obtain ⟨l, hlkl, hl⟩ := h.exists_poly_ne_zero V hk0 lk
      rw [hlk l hlkl, V.pos_iff]
      exact hl
  obtain ⟨lpk, hlpk⟩ := hpk
  rw [vPoly_eq V a (f * g % p0) (max lfmg (max lfg lpk)) fun i hi ↦ (by
    rw [← hlfg (max lfmg (max lfg lpk)) (by order)]
    rw [← hlfg i (by order)])]
  rw [vPoly_eq V a (f * g) (max lfmg (max lfg lpk)) fun i hi ↦ (by
    rw [← hlfmg (max lfmg (max lfg lpk)) (by order)]
    rw [← hlfmg i (by order)])]
  by_contra! hne
  have hne' : V (-(f * g % p0).eval (a (max lfmg (max lfg lpk)))) ≠
      V ((f * g).eval (a (max lfmg (max lfg lpk)))) := by
    rw [V.map_neg]
    exact hne
  obtain ⟨n, hn⟩ := exists_gt (max lfmg (max lfg lpk))
  have hne'' : V (-(f * g % p0).eval (a n)) ≠ V ((f * g).eval (a n)) := by
    convert hne' using 1
    · simp_rw [V.map_neg]
      rw [← hlfg (max lfmg (max lfg lpk)) (by order), ← hlfg n (by order)]
    · rw [← hlfmg (max lfmg (max lfg lpk)) (by order), ← hlfmg n (by order)]
  obtain h1 := V.map_add_of_distinct_val hne'
  obtain h2 := V.map_add_of_distinct_val hne''
  rw [neg_add_eq_sub, V.map_neg, ← Polynomial.eval_sub, hk] at h1 h2
  rw [← hlfg (max lfmg (max lfg lpk)) (by order), ← hlfmg (max lfmg (max lfg lpk)) (by order)] at h1
  rw [← hlfg n (by order), ← hlfmg n (by order)] at h2
  exact (hlpk (max lfmg (max lfg lpk)) n (by order) hn).ne.symm (h1.trans h2.symm)

noncomputable
def vAlg [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (p0 : K[X])
    (h1 : ∀ p : K[X], p.degree < p0.degree → ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (h2 : ¬∃ l, ∀ i, l ≤ i → V (p0.eval (a l)) = V (p0.eval (a i))) :
    Valuation (AdjoinRoot p0) Γ where
  toFun := AdjoinRoot.lift' p0 (fun p ↦ vPoly V a (p % p0))
    (fun p q h ↦ by simp [Polynomial.mod_eq_of_dvd_sub h])
  map_zero' := by
    rw [show (0 : AdjoinRoot p0) = AdjoinRoot.mk p0 0 by simp]
    rw [AdjoinRoot.lift'_mk]
    simp [vPoly]
  map_one' := by
    rw [show (1 : AdjoinRoot p0) = AdjoinRoot.mk p0 1 by simp]
    rw [AdjoinRoot.lift'_mk]
    rw [(Polynomial.mod_eq_self_iff
      (Polynomial.ne_zero_of_degree_gt (vAlg_p_degree_pos V a p0 h2))).mpr
      (by simpa using (vAlg_p_degree_pos V a p0 h2))]
    simp [vPoly]
  map_mul' p q := by
    induction p using AdjoinRoot.induction_on with | ih p
    induction q using AdjoinRoot.induction_on with | ih q
    rw [← map_mul]
    simp_rw [AdjoinRoot.lift'_mk]
    rw [Polynomial.mul_mod]
    apply vPoly_mul_mod V h p0 h1 h2 <;> exact (vAlg_mod_p_degree V a p0 h2 _)
  map_add_le_max' p q := by
    induction p using AdjoinRoot.induction_on with | ih p
    induction q using AdjoinRoot.induction_on with | ih q
    rw [← map_add]
    simp_rw [AdjoinRoot.lift'_mk]
    rw [Polynomial.add_mod]
    have hp : (p % p0).degree < p0.degree := (vAlg_mod_p_degree V a p0 h2 _)
    have hq : (q % p0).degree < p0.degree := (vAlg_mod_p_degree V a p0 h2 _)
    exact vPoly_add V a _ _ (h1 _ hp) (h1 _ hq)
      (h1 _ ((Polynomial.degree_add_le _ _).trans_lt (max_lt hp hq)))

@[simp]
theorem vAlg_polynomial [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (p0 : K[X])
    (h1 : ∀ p : K[X], p.degree < p0.degree → ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (h2 : ¬∃ l, ∀ i, l ≤ i → V (p0.eval (a l)) = V (p0.eval (a i)))
    (p : K[X]) :
    vAlg V h p0 h1 h2 (AdjoinRoot.mk p0 p) = vPoly V a (p % p0) := by
  simp [vAlg]

@[simp]
theorem vAlg_C [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (p0 : K[X])
    (h1 : ∀ p : K[X], p.degree < p0.degree → ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (h2 : ¬∃ l, ∀ i, l ≤ i → V (p0.eval (a l)) = V (p0.eval (a i)))
    (p : K) :
    vAlg V h p0 h1 h2 p = V p := by
  rw [show vAlg V h p0 h1 h2 p = vAlg V h p0 h1 h2 (AdjoinRoot.mk p0 (Polynomial.C p)) from rfl]
  rw [vAlg_polynomial]
  rw [(Polynomial.mod_eq_self_iff
      (Polynomial.ne_zero_of_degree_gt (vAlg_p_degree_pos V a p0 h2))).mpr
      (lt_of_le_of_lt (Polynomial.degree_C_le) (by simpa using (vAlg_p_degree_pos V a p0 h2)))]
  simp [vPoly]

instance vAlg_hasExtension [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (p0 : K[X])
    (h1 : ∀ p : K[X], p.degree < p0.degree → ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (h2 : ¬∃ l, ∀ i, l ≤ i → V (p0.eval (a l)) = V (p0.eval (a i))) :
    Valuation.HasExtension V (vAlg V h p0 h1 h2) where
  val_isEquiv_comap := by
    intro x y
    simp

theorem vAlg_valueImmediate [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (p0 : K[X])
    (h1 : ∀ p : K[X], p.degree < p0.degree → ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (h2 : ¬∃ l, ∀ i, l ≤ i → V (p0.eval (a l)) = V (p0.eval (a i))) :
    Set.range (vAlg V h p0 h1 h2) = (vAlg V h p0 h1 h2) '' (⊥ : Subalgebra K (AdjoinRoot p0)) := by
  apply Set.Subset.antisymm ?_ (by simp)
  intro v
  suffices ∀ p, vAlg V h p0 h1 h2 p = v → ∃ a, V a = v by simpa
  intro p
  induction p using AdjoinRoot.induction_on with | ih p
  suffices vPoly V a (p % p0) = v → ∃ a, V a = v by simpa
  intro h
  rw [← h]
  obtain ⟨l, hl⟩ := h1 (p % p0) (vAlg_mod_p_degree V a p0 h2 _)
  use (p % p0).eval (a l)
  rw [vPoly_eq V a (p % p0) l hl]

theorem vAlg_hasLimit [hι : Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (hlimit : ∀ x : K, ¬ HasLimit V a x)
    (p0 : K[X])
    (h1 : ∀ p : K[X], p.degree < p0.degree → ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (h2 : ¬∃ l, ∀ i, l ≤ i → V (p0.eval (a l)) = V (p0.eval (a i)))
    [Fact (Irreducible p0)] :
    HasLimit (vAlg V h p0 h1 h2) (algebraMap _ _ ∘ a) (AdjoinRoot.root p0) := by
  unfold HasLimit
  intro i
  obtain ⟨j, hj⟩ := exists_gt i
  rw [((IsPseudoConv.iff V (vAlg V h p0 h1 h2)).mp h).γ_eq _ hj]
  simp_rw [Function.comp_apply]
  rw [show algebraMap K (AdjoinRoot p0) (a i) - algebraMap K (AdjoinRoot p0) (a j) =
    (AdjoinRoot.root p0 - algebraMap K (AdjoinRoot p0) (a j)) -
    (AdjoinRoot.root p0 - algebraMap K (AdjoinRoot p0) (a i)) by abel]
  refine (Valuation.map_sub_eq_of_lt_right _ ?_).symm
  obtain h' := (IsPseudoConv.iff V (vAlg V h p0 h1 h2)).mp h
  refine ((h'.const_sub _ _).lemma1 (vAlg V h p0 h1 h2)).resolve_right ?_ i j hj

  by_contra!
  obtain ⟨l, hl, _⟩ := this
  have hl : ∀ (i : ι), l ≤ i →
    vAlg V h p0 h1 h2 (AdjoinRoot.mk p0 (Polynomial.X - Polynomial.C (a l))) =
    vAlg V h p0 h1 h2 (AdjoinRoot.mk p0 (Polynomial.X - Polynomial.C (a i))) := by simpa using hl
  simp_rw [vAlg_polynomial] at hl
  have h1 (c : K) : (Polynomial.X - Polynomial.C c) % p0 = Polynomial.X - Polynomial.C c := by
    refine (Polynomial.mod_eq_self_iff
      (Polynomial.ne_zero_of_degree_gt (vAlg_p_degree_pos V a p0 h2))).mpr ?_
    simpa using vAlg_one_lt_degree V h hlimit p0 h2
  simp_rw [h1] at hl
  contrapose! hl
  obtain ⟨j, hj⟩ := exists_gt l
  use j
  constructor
  · exact hj.le
  exact vPoly_not_const V h l j hj

theorem vAlg_residueImmediate [hι : Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (p0 : K[X])
    (h1 : ∀ p : K[X], p.degree < p0.degree → ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (h2 : ¬∃ l, ∀ i, l ≤ i → V (p0.eval (a l)) = V (p0.eval (a i)))
    [Fact (Irreducible p0)] :
    Function.Surjective (IsLocalRing.ResidueField.map
      (algebraMap V.integer (vAlg V h p0 h1 h2).integer)) := by
  intro r
  induction r with | residue r
  suffices ∃ s, IsLocalRing.residue (vAlg V h p0 h1 h2).integer
      (algebraMap V.integer (vAlg V h p0 h1 h2).integer s - r) = 0 by
    obtain ⟨s, hs⟩ := this
    rw [map_sub, sub_eq_zero] at hs
    use IsLocalRing.residue V.integer s
    rw [← hs, IsLocalRing.ResidueField.map_residue]
  simp_rw [IsLocalRing.residue_eq_zero_iff]
  simp_rw [show IsLocalRing.maximalIdeal (vAlg V h p0 h1 h2).integer
    = IsLocalRing.maximalIdeal (vAlg V h p0 h1 h2).valuationSubring by rfl] -- ehh
  obtain ⟨r, hr⟩ := r
  have hr : vAlg V h p0 h1 h2 r ≤ 1 := by simpa using hr
  suffices ∃ s, vAlg V h p0 h1 h2 (algebraMap V.integer (vAlg V h p0 h1 h2).integer s - r) < 1 by
    obtain ⟨s, hs⟩ := this
    use s
    rw [Valuation.mem_maximalIdeal_iff]
    exact hs -- not sure why simp_rw didn't work
  suffices ∃ s ∈ V.integer, vAlg V h p0 h1 h2 (AdjoinRoot.of p0 s - r) < 1 by simpa
  obtain hr | hr := lt_or_eq_of_le hr
  · exact ⟨0, by simp, by simpa using hr⟩
  induction r using AdjoinRoot.induction_on with | ih r
  rw [vAlg_polynomial] at hr
  obtain rfl | hp := eq_or_ne r 0
  · exact ⟨0, by simp⟩
  obtain ⟨s, hs1, hs⟩ := vPoly_exists_close V h hr (h1 _ (vAlg_mod_p_degree V a p0 h2 _))
  refine ⟨s, (V.mem_integer_iff _).mpr hs1.le, ?_⟩
  suffices vAlg V h p0 h1 h2 (AdjoinRoot.mk p0 (Polynomial.C s - r)) < 1 by simpa
  simp_rw [vAlg_polynomial, Polynomial.sub_mod]
  convert hs
  refine (Polynomial.mod_eq_self_iff
      (Polynomial.ne_zero_of_degree_gt (vAlg_p_degree_pos V a p0 h2))).mpr ?_
  exact lt_of_le_of_lt Polynomial.degree_C_le (vAlg_p_degree_pos V a p0 h2)

theorem vAlg_isImmediate [hι : Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (p0 : K[X])
    (h1 : ∀ p : K[X], p.degree < p0.degree → ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (h2 : ¬∃ l, ∀ i, l ≤ i → V (p0.eval (a l)) = V (p0.eval (a i)))
    [Fact (Irreducible p0)] :
    IsImmediate V (vAlg V h p0 h1 h2) :=
  ⟨vAlg_valueImmediate V h p0 h1 h2, vAlg_residueImmediate V h p0 h1 h2⟩

theorem theorem3_equiv [Nonempty ι] {a : ι → K} (h : IsPseudoConv V a)
    (p0 : K[X]) [Fact (Irreducible p0)]
    (h1 : ∀ p : K[X], p.degree < p0.degree → ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i)))
    (h2 : ¬∃ l, ∀ i, l ≤ i → V (p0.eval (a l)) = V (p0.eval (a i)))
    (V' : Valuation (AdjoinRoot p0) Γ') [Valuation.HasExtension V V']
    (hlimit2 : HasLimit V' (algebraMap K (AdjoinRoot p0) ∘ a) (AdjoinRoot.root p0)) :
    (vAlg V h p0 h1 h2).IsEquiv V' := by
  obtain ⟨himm, _⟩ := (Set.range_eq_iff _ _).mp (vAlg_valueImmediate V h p0 h1 h2)
  suffices ∀ (x : AdjoinRoot p0) (y : K), V y = vAlg V h p0 h1 h2 x →
      V' x = V' (algebraMap _ _ y) by
    intro r s
    obtain ⟨r', hrimm⟩ : ∃ r', V r' = (vAlg V h p0 h1 h2) r := by simpa using himm r
    obtain ⟨s', hsimm⟩ : ∃ s', V s' = (vAlg V h p0 h1 h2) s := by simpa using himm s
    rw [this r r' hrimm, this s s' hsimm]
    rw [Valuation.HasExtension.val_map_le_iff V V']
    rw [hrimm, hsimm]
  intro x y hxy
  induction x using AdjoinRoot.induction_on with | ih x
  rw [vAlg_polynomial] at hxy
  obtain h := vPoly_equiv V V' h (AdjoinRoot.mkₐ p0) (by simpa using hlimit2) _ _ hxy
    (fun q hq ↦ by
      apply h1
      apply Polynomial.degree_lt_degree
      apply hq.trans_lt
      apply Polynomial.natDegree_mod_lt
      apply Nat.ne_of_gt
      rw [Polynomial.natDegree_pos_iff_degree_pos]
      exact vAlg_p_degree_pos V a p0 h2
    )
  suffices AdjoinRoot.mkₐ p0 (x % p0) = AdjoinRoot.mkₐ p0 x by simpa [this] using h
  simp [EuclideanDomain.mod_eq_sub_mul_div]

omit [NoMaxOrder ι] in
theorem trans_or_alg [Nonempty ι] (a : ι → K) :
    (∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) ∨
    (∃ p0 : K[X], Irreducible p0 ∧
      (∀ p : K[X], p.degree < p0.degree → ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) ∧
      (¬∃ l, ∀ i, l ≤ i → V (p0.eval (a l)) = V (p0.eval (a i)))) := by

  let ps := {p : K[X] | ¬∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))}
  have hunit (p : K[X]) (hp : p ∈ ps) : ¬ IsUnit p := by
    contrapose! hp
    obtain ⟨r, _, hr⟩ := Polynomial.isUnit_iff.mp hp
    simp [← hr, ps]

  by_cases hnonempty : ps.Nonempty
  · right
    refine ⟨Polynomial.degree_lt_wf.min ps hnonempty, ?_, ?_, ?_⟩
    · obtain hpmem := Polynomial.degree_lt_wf.min_mem ps hnonempty
      have hp0 : Polynomial.degree_lt_wf.min ps hnonempty ≠ 0 := by
        contrapose! hpmem with h0
        rw [h0]
        simp [ps]
      rw [irreducible_iff]
      constructor
      · exact hunit _ hpmem
      intro u v hp
      have huvmem : u ∈ ps ∨ v ∈ ps := by
        contrapose! hpmem with huvmem
        rw [hp]
        simp_rw [ps, Set.notMem_setOf_iff, not_not] at huvmem ⊢
        obtain ⟨⟨ul, hu⟩, ⟨vl, hv⟩⟩ := huvmem
        use max ul vl
        intro i hi
        simp_rw [Polynomial.eval_mul, map_mul]
        rw [← hu (max ul vl) (by simp)]
        rw [← hv (max ul vl) (by simp)]
        congrm $(hu i (by order)) * $(hv i (by order))
      by_contra!
      simp_rw [Polynomial.isUnit_iff_degree_eq_zero] at this
      obtain ⟨hu, hv⟩ := this
      have hu' : 0 < u.degree := by
        apply lt_of_le_of_ne ?_ (Ne.symm hu)
        refine Polynomial.zero_le_degree_iff.mpr ?_
        contrapose! hp0
        simp [hp, hp0]
      have hv' : 0 < v.degree := by
        apply lt_of_le_of_ne ?_ (Ne.symm hv)
        refine Polynomial.zero_le_degree_iff.mpr ?_
        contrapose! hp0
        simp [hp, hp0]
      have hu'' : u.degree ≠ ⊥ := by
        contrapose! hu'
        simp [hu']
      have hv'' : v.degree ≠ ⊥ := by
        contrapose! hv'
        simp [hv']
      obtain hdegree := congrArg Polynomial.degree hp
      rw [Polynomial.degree_mul] at hdegree
      obtain hmem | hmem := huvmem
      <;> obtain hle := Polynomial.degree_lt_wf.not_lt_min _ hnonempty hmem
      <;> rw [hdegree, not_lt] at hle
      · conv_rhs at hle => rw [← add_zero (Polynomial.degree _)]
        rw [WithBot.add_le_add_iff_left (by assumption)] at hle
        exact (not_lt.mpr hle) hv'
      · conv_rhs at hle => rw [← zero_add (Polynomial.degree _)]
        rw [WithBot.add_le_add_iff_right (by assumption)] at hle
        exact (not_lt.mpr hle) hu'
    · intro p hp
      contrapose hp
      apply Polynomial.degree_lt_wf.not_lt_min ps hnonempty (by simpa [ps] using hp)
    · simpa [ps] using Polynomial.degree_lt_wf.min_mem ps hnonempty
  · left
    intro p
    contrapose! hnonempty with hp
    use p
    simpa [ps] using hp

omit [NoMaxOrder ι] in
theorem trans_or_alg' [Nonempty ι] (a : ι → K) :
    (∀ p : K[X], ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) ∨
    (∃ p0 : K[X], Irreducible p0 ∧ p0.Monic ∧
      (∀ p : K[X], p.degree < p0.degree → ∃ l, ∀ i, l ≤ i → V (p.eval (a l)) = V (p.eval (a i))) ∧
      (¬∃ l, ∀ i, l ≤ i → V (p0.eval (a l)) = V (p0.eval (a i)))) := by
  obtain h | ⟨p0, hirr, h1, h2⟩ := trans_or_alg V a
  · exact Or.inl h
  · have hp0 : p0 ≠ 0 := by
      contrapose! hirr with h0
      simp [h0]
    refine Or.inr ⟨p0 * Polynomial.C p0.leadingCoeff⁻¹, ?_, ?_, ?_, ?_⟩
    · exact (irreducible_mul_isUnit (by simpa using hp0)).mpr hirr
    · exact Polynomial.monic_mul_leadingCoeff_inv hp0
    · simpa using h1
    · simpa [hp0] using h2

theorem exists_isImmediate [Nonempty ι] {a : ι → K} (ha : IsPseudoConv V a)
    (hlimit : ∀ (x : K), ¬HasLimit V a x) :
    (∃ (V' : Valuation (RatFunc K) Γ) (_ : V.HasExtension V'), IsImmediate V V') ∨
    (∃ (p0 : K[X]) (_ : Fact (Irreducible p0))
      (V' : Valuation (AdjoinRoot p0) Γ) (_ : V.HasExtension V'),
      p0.Monic ∧ IsImmediate V V' ∧ ¬ Function.Surjective (algebraMap K (AdjoinRoot p0))) := by
  obtain htran | ⟨p0, hirr, hmonic, h1, h2⟩ := trans_or_alg' V a
  · exact Or.inl ⟨vTransc V ha htran, inferInstance, vTransc_isImmediate V ha htran⟩
  · have : Fact (Irreducible p0) := ⟨hirr⟩
    refine Or.inr ⟨p0, inferInstance, vAlg V ha p0 h1 h2, inferInstance,
      hmonic, vAlg_isImmediate V ha p0 h1 h2, ?_⟩
    suffices ∃ x, ∀ (c : K), AdjoinRoot.of p0 c ≠ x by simpa [Function.Surjective]
    refine ⟨AdjoinRoot.root p0, fun c ↦ ?_⟩
    rw [irreducible_iff] at hirr
    contrapose! hirr with heq
    apply_fun (Polynomial.aeval · p0) at heq
    have hc : p0.eval c = 0 := by simpa [← AdjoinRoot.algebraMap_eq] using heq
    rw [← Polynomial.IsRoot, ← Polynomial.dvd_iff_isRoot] at hc
    obtain ⟨q, hq⟩ := hc
    intro _
    refine ⟨(Polynomial.X - Polynomial.C c), q, hq, ?_, ?_⟩
    · apply Polynomial.not_isUnit_of_degree_pos
      simp
    · apply Polynomial.not_isUnit_of_degree_pos
      obtain hpdegree := vAlg_one_lt_degree V ha hlimit p0 h2
      apply_fun Polynomial.degree at hq
      have : 1 + 0 < 1 + q.degree := by simpa [hq, Polynomial.degree_mul] using hpdegree
      exact pos_of_lt_add_right this

theorem theorem4.{u, v} {K : Type u} [Field K]
    {Γ : Type v} [LinearOrderedCommGroupWithZero Γ] (V : Valuation K Γ) :
    IsMaximal V ↔
    ∀ (ι : Type v) (a : ι → K) (_ : LinearOrder ι) (_ : NoMaxOrder ι) (_ : Nonempty ι),
    IsPseudoConv V a → ∃ x : K, HasLimit V a x := by
  unfold IsMaximal
  constructor
  · contrapose!
    rintro ⟨_, a, _, _ ,_, ha, hx⟩
    obtain ⟨V', _, himm⟩ | ⟨p0, _, V', _, _, himm, hsurj⟩ := exists_isImmediate V ha hx
    · refine ⟨RatFunc K, Γ, inferInstance, inferInstance, V', inferInstance, inferInstance,
        himm, ?_⟩
      suffices ∃ x, ∀ (c : K), RatFunc.C c ≠ x by simpa [Function.Surjective]
      refine ⟨RatFunc.X, fun c ↦ ?_⟩
      by_contra! heq
      obtain h0 | h0 := eq_or_ne c 0
      · apply_fun RatFunc.eval (RingHom.id K) 1 at heq
        simp [h0] at heq
      · apply_fun RatFunc.eval (RingHom.id K) 0 at heq
        simp [h0] at heq
    · exact ⟨AdjoinRoot p0, Γ, inferInstance, inferInstance, V', inferInstance, inferInstance,
        himm, hsurj⟩
  · contrapose!
    rintro ⟨L, Γ', _, _, V', _, _, himm, hsurj⟩
    obtain ⟨z, hz⟩ : ∃ z, ∀ (x : K), algebraMap K L x ≠ z := by
      simpa [Function.Surjective] using hsurj
    have hz : z ∉ (⊥ : Subalgebra K L) := by simpa [Algebra.mem_bot] using hz
    obtain ⟨s, hs, _, a, ha, hlimit, _⟩ := himm.theorem1 V V' hz
    exact ⟨s, a, inferInstance, inferInstance, (by simpa using hs), ha, hlimit⟩
