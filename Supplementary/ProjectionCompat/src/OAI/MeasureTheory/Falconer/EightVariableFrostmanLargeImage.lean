import OAI.MeasureTheory.Falconer.EightVariableBilinearLaw

/-! Large images of the original eight-variable pi law under open-ball
Frostman assumptions, with no artificial projection or fiber certificate. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

theorem planar_product_open_frostman (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    {s t C : ℝ} (hC : 0 ≤ C)
    (hμ : ∀ z r : ℝ, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (C*r^s))
    (hν : ∀ z r : ℝ, 0 < r → ν (ball z r) ≤ ENNReal.ofReal (C*r^t)) :
    FrostmanBallBound (planarProductLaw μ ν) (s+t) (C*C) := by
  intro z r hr
  rw [planarProductLaw,Measure.map_apply continuous_pairToPlane.measurable measurableSet_ball]
  have hsub : pairToPlane ⁻¹' ball z r ⊆ ball (z 0) r ×ˢ ball (z 1) r := by
    intro p hp
    have hn : ‖pairToPlane p-z‖ < r := by simpa only [mem_preimage,mem_ball,dist_eq_norm] using hp
    constructor
    · have hh := (PiLp.norm_apply_le (pairToPlane p-z) 0).trans_lt hn
      simpa [pairToPlane,mem_ball,Real.dist_eq,Real.norm_eq_abs] using hh
    · have hh := (PiLp.norm_apply_le (pairToPlane p-z) 1).trans_lt hn
      simpa [pairToPlane,mem_ball,Real.dist_eq,Real.norm_eq_abs] using hh
  apply (measure_mono hsub).trans
  rw [Measure.prod_prod]
  apply (mul_le_mul' (hμ _ _ hr) (hν _ _ hr)).trans_eq
  rw [← ENNReal.ofReal_mul (by positivity),Real.rpow_add hr]
  congr 1; ring

theorem uniform_eight_variable_Frostman_large_image {s t σ : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hσ : 0 ≤ σ) (hσmax : σ < min (s+t) 1) :
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
    ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ δ₀ → ∀ C : ℝ, 1 ≤ C → C ≤ δ^(-ε) →
    ∀ μ : Fin 8 → Measure ℝ, ∀ [∀ i, IsProbabilityMeasure (μ i)],
      (∀ i, UnitSupported (μ i)) →
      (∀ (i : Fin 8) (z r : ℝ), 0 < r →
        μ i (ball z r) ≤ ENNReal.ofReal (C*r^(if i.val < 2 ∨ i.val = 4 ∨ i.val = 6 then s else t))) →
      ∀ E : Set ℝ, ENNReal.ofReal (δ^ε) ≤ (Measure.pi μ).map eightBilinearValue E →
        (Nat.ceil (δ^(-σ)) : ℕ∞) ≤ externalCoveringNumber ⟨δ,hδ.le⟩ E := by
  obtain ⟨e,δ₀,he,hδ₀,hδ₀1,himage⟩ := uniform_bilinear_difference_large_image hs hs1 ht ht1 hσ hσmax
  let ε := e/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεe : ε ≤ e := by dsimp [ε]; linarith
  refine ⟨ε,δ₀,hε,hδ₀,hδ₀1,?_⟩
  intro δ hδ hδsmall C hC hCb μ _ hμ hb E hE
  have hδ1 : δ ≤ 1 := hδsmall.trans hδ₀1
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hCC1 : 1 ≤ C*C := by nlinarith
  have hCC : C*C ≤ δ^(-e) := calc
    _ ≤ δ^(-ε)*δ^(-ε) := mul_le_mul hCb hCb hC0 (by positivity)
    _ = _ := by rw [← Real.rpow_add hδ]; congr 1; dsimp [ε]; ring
  have hfront (i : Fin 4) (z r : ℝ) (hr : 0 < r) :
      μ (firstFourEightIndex i) (ball z r) ≤ ENNReal.ofReal ((C*C)*r^(if i.val < 2 then s else t)) := by
    have hne4 : i.val ≠ 4 := by omega
    have hne6 : i.val ≠ 6 := by omega
    have hh := hb (firstFourEightIndex i) z r hr
    simp only [firstFourEightIndex,hne4,hne6,or_false] at hh
    exact hh.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by nlinarith : C ≤ C*C) (by positivity)))
  have hρ : FrostmanBallBound (planarProductLaw (μ 6) (μ 7)) (s+t) (C*C) :=
    planar_product_open_frostman (μ 6) (μ 7) hC0 (by simpa using hb 6) (by simpa using hb 7)
  apply himage δ hδ hδsmall (C*C) hCC1 hCC (fun i : Fin 4 ↦ μ (firstFourEightIndex i))
    (fun i ↦ hμ (firstFourEightIndex i)) hfront (planarProductLaw (μ 4) (μ 5)) (planarProductLaw (μ 6) (μ 7))
    hρ (planarProductLaw_unitCube (μ 6) (μ 7) (hμ 6) (hμ 7)) E
  rw [← original_pi_eight_bilinear_law μ]
  exact (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hεe)).trans hE

#print axioms planar_product_open_frostman
#print axioms uniform_eight_variable_Frostman_large_image
end OAI.Falconer
