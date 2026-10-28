import OAI.MeasureTheory.Falconer.FlatteningExponentGrid

/-! One additive iteration budget for all interior exponent pairs bounded away from zero. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem OSS_original_energy_interior_flattening_uniform_K (kernel : SmoothKernel) {α κ : ℝ}
    (hα : 0 < α) (hκ : 0 < κ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ s t : ℝ, α ≤ s → α ≤ t → s+t < 1 →
      ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        UnitSupported μ → UnitSupported ν →
        smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-ε)) →
        smoothEnergy kernel.law t δ ν ≤ ENNReal.ofReal (δ^(-ε)) →
        ∀ k : ℕ, K ≤ k →
        smoothEnergy kernel.law (s+t) δ
          (additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k) ≤ ENNReal.ofReal (δ^(-κ)) := by
  let b : ℝ := κ/8
  have hb : 0 < b := by dsimp [b]; positivity
  have hbκ : 2*b < κ := by dsimp [b]; linarith
  let a : ℝ := min 1 b
  have ha : 0 < a := lt_min (by norm_num) hb
  have ha1 : a ≤ 1 := min_le_left _ _
  have hab : a ≤ b := min_le_right _ _
  obtain ⟨K,hK,hflat⟩ := exists_uniform_intermediate_L2_iteration_budget kernel hα hb ha
  refine ⟨K,hK,?_⟩
  intro s t hαs hαt hst
  have hs : 0 < s := hα.trans_le hαs
  have ht : 0 < t := hα.trans_le hαt
  obtain ⟨ε,r₀,hε,hr₀,hr₀1,hL2⟩ := hflat s t hαs hαt hst.le
  obtain ⟨δ₀,hδ₀,hδ₀1,henergy⟩ := exists_intermediate_L2_energy_consumer kernel
    (show 0 < s+t by positivity) hst hb hbκ ha ha1 hab hr₀
  refine ⟨ε,δ₀,hε,hδ₀,hδ₀1,?_⟩
  intro δ hδ hδsmall μ ν _ _ hμU hνU hμE hνE k hk
  let ρ := additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k
  have : IsProbabilityMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  apply henergy δ hδ hδsmall ρ
  intro R hδR hwindow hRr₀
  exact hL2 δ R hδ (hδ.trans_le hδR) hδR hwindow hRr₀ μ ν hμU hνU hμE hνE k hk

#print axioms OSS_original_energy_interior_flattening_uniform_K
end OAI.Falconer
