import MaximalField.Theorem234

universe u v
variable {K : Type u} [Field K]
variable {Γ : Type v} [LinearOrderedCommGroupWithZero Γ] (V : Valuation K Γ)

structure ImmediateExtension where
  L : Type u
  Γ' : Type v
  [field : Field L]
  [algebra : Algebra K L]
  [group : LinearOrderedCommGroupWithZero Γ']
  V' : Valuation L Γ'
  [hasExtension : V.HasExtension V']
  isImmediate : IsImmediate V V'

namespace ImmediateExtension

instance (a : ImmediateExtension V) : Field a.L := a.field
instance (a : ImmediateExtension V) : Algebra K a.L := a.algebra
instance (a : ImmediateExtension V) : LinearOrderedCommGroupWithZero a.Γ' := a.group
instance (a : ImmediateExtension V) : V.HasExtension a.V' := a.hasExtension

instance : Inhabited (ImmediateExtension V) where
  default := {
    L := K
    Γ' := Γ
    V' := V
    isImmediate := IsImmediate.id V
  }

def le (a b : ImmediateExtension V) : Prop :=
  ∃ (_ : Algebra a.L b.L), IsScalarTower K a.L b.L ∧ Valuation.HasExtension a.V' b.V'

instance : Preorder (ImmediateExtension V) where
  le := le V
  le_refl a := ⟨Algebra.id a.L, inferInstance, inferInstance⟩
  le_trans a b c hab hbc := by
    obtain ⟨fab, _, hextab⟩ := hab
    obtain ⟨fbc, _, hextbc⟩ := hbc
    let fac := Algebra.trans a.L b.L c.L
    have sac := Algebra.isScalarTower a.L b.L c.L
    exact ⟨fac, IsScalarTower.to₁₂₄ K a.L b.L c.L, Valuation.HasExtension.trans a.V' b.V' c.V'⟩

end ImmediateExtension

-- This is likely wrong
theorem RatFunc.not_algebra {K : Type*} [Field K] (alg : Algebra (RatFunc K) K) : False := by
  have hinj : Function.Injective (algebraMap (RatFunc K) K) :=
    FaithfulSMul.algebraMap_injective (RatFunc K) K
  let := Algebra.trans (RatFunc K) K (RatFunc K)
  --have hinj : Function.Injective ( (Algebra.ofId (RatFunc K) K).restrictScalars K ) := hinj
  sorry

theorem exists_maximal : ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (Γ' : Type v)
    (_ : LinearOrderedCommGroupWithZero Γ') (V' : Valuation L Γ')
    (_ : Valuation.HasExtension V V'), IsImmediate V V' ∧ IsMaximal V' := by

  obtain ⟨m, hm⟩ := zorn_le_nonempty (α := ImmediateExtension V) sorry
  refine ⟨m.L, inferInstance, inferInstance, m.Γ', inferInstance, m.V', inferInstance,
    m.isImmediate, ?_⟩
  -- How to prove that IsMax (as-in Zorn's lemma) → IsMaximal (as in immediate extension)?

  by_contra! hmax
  obtain h := (theorem4 m.V').not.mp hmax
  have : ∃ (ι : Type v) (a : ι → m.L) (_ : LinearOrder ι),
    IsPseudoConv m.V' a ∧ Nonempty ι ∧
    ∃ (_ : NoMaxOrder ι), ∀ (x : m.L), ¬HasLimit m.V' a x := by simpa using h
  obtain ⟨_, a, _, ha, _, _, hlimit⟩ := this
  obtain ⟨V', _, himm⟩ | ⟨p0, _, V', _, _, himm, hsurj⟩ := exists_isImmediate m.V' ha hlimit
  · let n : ImmediateExtension V := {
      L := RatFunc m.L
      Γ' := m.Γ'
      V' := V'
      hasExtension := Valuation.HasExtension.trans V m.V' V'
      isImmediate := IsImmediate.trans m.isImmediate himm
    }
    have : m ≤ n := ⟨inferInstance, inferInstance, inferInstance⟩
    obtain ⟨alg : Algebra (RatFunc m.L) m.L, _⟩ := (hm this)
    exact RatFunc.not_algebra alg
  · let n : ImmediateExtension V := {
      L := AdjoinRoot p0
      Γ' := m.Γ'
      V' := V'
      hasExtension := Valuation.HasExtension.trans V m.V' V'
      isImmediate := IsImmediate.trans m.isImmediate himm
    }
    have : m ≤ n := ⟨inferInstance, inferInstance, inferInstance⟩
    obtain ⟨alg : Algebra (AdjoinRoot p0) m.L, _⟩ := (hm this)
    sorry
