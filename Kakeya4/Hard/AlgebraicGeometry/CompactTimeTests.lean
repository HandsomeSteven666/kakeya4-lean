import Kakeya4.Hard.AlgebraicGeometry.AllowedRegion

/-! Closed-interval supremum tests and the eligibility formula have the same meaning. -/

noncomputable section
open Set
open scoped Classical

namespace Kakeya4.Hard.EligibleFormula

theorem compact_interval_sSup_le_iff (a b M : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) :
    sSup (f '' Icc a b) ≤ M ↔ ∀ t ∈ Icc a b, f t ≤ M := by
  constructor
  · intro h t ht
    exact (le_csSup (isCompact_Icc.bddAbove_image hf) (mem_image_of_mem f ht)).trans h
  · intro h
    apply csSup_le ((nonempty_Icc.mpr hab).image f)
    rintro _ ⟨t,ht,rfl⟩
    exact h t ht

theorem compact_interval_le_sSup_iff (a b M : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) :
    M ≤ sSup (f '' Icc a b) ↔ ∃ t ∈ Icc a b, M ≤ f t := by
  obtain ⟨t,ht,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hf
  have he : sSup (f '' Icc a b) = f t := by
    apply le_antisymm
    · exact (compact_interval_sSup_le_iff a b (f t) hab f hf).mpr (fun _ hs => hmax hs)
    · exact le_csSup (isCompact_Icc.bddAbove_image hf) (mem_image_of_mem f ht)
  rw [he]
  exact ⟨fun h => ⟨t,ht,h⟩,fun ⟨u,hu,h⟩ => h.trans (hmax hu)⟩

theorem derivative_sup_iff_time_witness (p : Parameters) (b s : Point)
    (hI : p .lo ≤ p .hi) :
    p .invK ≤ sSup ((fun t : ℝ => |derivativeValue p b s t|) '' Icc (p .lo) (p .hi)) ↔
      ∃ t ∈ Icc (p .lo) (p .hi), p .invK ≤ |derivativeValue p b s t| := by
  apply compact_interval_le_sSup_iff
  · exact hI
  · simp_rw [derivativeValue_affine]
    fun_prop

end Kakeya4.Hard.EligibleFormula
