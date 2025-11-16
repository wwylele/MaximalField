import Mathlib

def WFSet (α : Type*) [LinearOrder α] := {s : Set α // s.IsWF}

instance (α : Type*) [LinearOrder α] : LE (WFSet α) where
  le a b := a.val ⊆ b.val ∧ ∀ x y, x ∈ a.val → y ∈ b.val → y ≤ x → y ∈ a.val

theorem WFSet.le_def {α : Type*} [LinearOrder α] {a b : WFSet α} :
    a ≤ b ↔ a.val ⊆ b.val ∧ ∀ x y, x ∈ a.val → y ∈ b.val → y ≤ x → y ∈ a.val := by rfl

instance (α : Type*) [LinearOrder α] : PartialOrder (WFSet α) where
  le_refl a := by rw [WFSet.le_def]; grind
  le_trans a b c hab hbc := by
    rw [WFSet.le_def] at hab hbc ⊢
    constructor
    · exact hab.1.trans hbc.1
    intro x y hx hy hyx
    refine hab.2 x y hx ?_ hyx
    exact hbc.2 x y (Set.mem_of_subset_of_mem hab.1 hx) hy hyx
  le_antisymm a b hab hba := by
    rw [WFSet.le_def] at hab hba
    apply Subtype.ext
    apply Set.Subset.antisymm hab.1 hba.1

theorem exists_isCofinal_isWF {α : Type*} [LinearOrder α] :
    ∃ s : Set α, IsCofinal s ∧ s.IsWF := by
  suffices ∃ s : WFSet α, IsCofinal s.val by
    obtain ⟨⟨s, hs⟩, hcofinal⟩ := this
    exact ⟨s, hcofinal, hs⟩
  suffices ∃ s : WFSet α, IsMax s by
    obtain ⟨s, hmax⟩ := this
    use s
    contrapose! hmax
    have : ∃ x, ∀ y ∈ s.val, y < x := by simpa [IsCofinal] using hmax
    obtain ⟨x, hx⟩ := this
    rw [not_isMax_iff]
    refine ⟨⟨s.val ∪ {x}, by simpa using s.prop⟩, ?_⟩
    rw [lt_iff_le_and_ne, WFSet.le_def]
    constructor
    · constructor
      · simp
      · intro u v hu hv hvu
        suffices v ≠ x by simpa [this] using hv
        exact (hvu.trans_lt (hx u hu)).ne
    · apply Subtype.ext_iff.ne.mpr
      symm
      suffices x ∉ s.val by simpa
      by_contra! h
      obtain h := hx x h
      simp at h
  apply zorn_le
  intro s hs
  refine ⟨⟨⋃ a ∈ s, a.val, ?_⟩, ?_⟩
  · rw [Set.isWF_iff_no_descending_seq]
    intro f hf
    by_contra! hmem
    obtain h0 := hmem 0
    simp_rw [Set.mem_iUnion, exists_prop] at h0
    obtain ⟨a, ha, hfa⟩ := h0
    obtain hawf := a.prop
    contrapose! hawf
    rw [Set.isWF_iff_no_descending_seq]
    suffices ∃ f, StrictAnti f ∧ ∀ n : ℕ, f n ∈ a.val by simpa
    refine ⟨f, hf, ?_⟩
    intro n
    specialize hmem n
    simp_rw [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨b, hb, hfb⟩ := hmem
    obtain hab | hab := hs.total ha hb
    · exact (WFSet.le_def.mpr hab).2 (f 0) (f n) hfa hfb (hf.le_iff_ge.mpr (by simp))
    · exact Set.mem_of_subset_of_mem (WFSet.le_def.mpr hab).1 hfb
  · rw [upperBounds, Set.mem_setOf_eq]
    intro a ha
    rw [WFSet.le_def]
    constructor
    · exact le_biSup (Subtype.val) ha
    intro x y hx hy hyx
    simp_rw [Set.mem_iUnion, exists_prop] at hy
    obtain ⟨b, hb, hy⟩ := hy
    obtain hab | hab := hs.total ha hb
    · exact (WFSet.le_def.mpr hab).2 x y hx hy hyx
    · exact Set.mem_of_subset_of_mem (WFSet.le_def.mpr hab).1 hy

theorem exists_isCofinalFor_isWF {α : Type*} [LinearOrder α] (t : Set α) :
    ∃ s : Set α, s ≤ t ∧ IsCofinalFor t s ∧ s.IsWF := by
  obtain ⟨s, hcofinal, hwf⟩ := exists_isCofinal_isWF (α := t)
  refine ⟨s, by simp, ?_, ?_⟩
  · unfold IsCofinalFor
    unfold IsCofinal at hcofinal
    intro a ha
    obtain ⟨b, hb1, hb2⟩ := hcofinal ⟨a, ha⟩
    exact ⟨b, by simpa using hb1, hb2⟩
  · rw [Set.isWF_iff_no_descending_seq] at ⊢ hwf
    contrapose! hwf
    obtain ⟨f, h1, h2⟩ := hwf
    simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at h2
    refine ⟨fun n ↦ ⟨f n, (h2 n).1⟩, ?_, ?_⟩
    · intro a b h
      simpa using h1 h
    · intro n
      simpa using (h2 n).2
