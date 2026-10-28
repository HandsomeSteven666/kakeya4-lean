import OAI.MeasureTheory.Falconer.ConvolutionLargeImageTransport

/-! Uniform original-energy large-image bounds for every additive power k ≥ 2. -/
set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

noncomputable def additiveLawPower (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | k+1 => additiveLawPower μ k ∗ μ

instance additiveLawPower_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ k, IsProbabilityMeasure (additiveLawPower μ k) := by
  intro k
  induction k with
  | zero => change IsProbabilityMeasure (Measure.dirac (0:ℝ)); infer_instance
  | succ k ih =>
    letI := ih
    change IsProbabilityMeasure (additiveLawPower μ k ∗ μ)
    infer_instance

theorem additive_law_power_two_add (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ) :
    additiveLawPower μ (k+2) = (μ ∗ μ) ∗ additiveLawPower μ k := by
  induction k with
  | zero => simp [additiveLawPower]
  | succ k ih =>
    change additiveLawPower μ (k+2) ∗ μ = (μ ∗ μ) ∗ (additiveLawPower μ k ∗ μ)
    rw [ih,Measure.conv_assoc]

theorem energy_difference_mconv_all_powers_large_image (κ : SmoothKernel) {s t σ : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hσ : 0 ≤ σ) (hσmax : σ < min (s+t) 1) :
    ∃ ε r₀ : ℝ, 0 < ε ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ r : ℝ, ∀ hr : 0 < r, r ≤ r₀ →
    ∀ μ ν : Measure ℝ, ∀ [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      UnitSupported μ → UnitSupported ν →
      smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε)) →
      smoothEnergy κ.law t r ν ≤ ENNReal.ofReal (r^(-ε)) →
      ∀ k : ℕ, 2 ≤ k → ∀ E : Set ℝ, ENNReal.ofReal (r^ε) ≤
        additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k E →
        (Nat.ceil (r^(-σ)) : ℕ∞) ≤ externalCoveringNumber ⟨r,hr.le⟩ E := by
  obtain ⟨e,r₁,he,hr₁,hr₁1,hbase⟩ :=
    energy_difference_mconv_square_large_image κ hs hs1 ht ht1 hσ hσmax
  refine ⟨e/2,min r₁ (1/2),by positivity,lt_min hr₁ (by norm_num),
    (min_le_left _ _).trans hr₁1,?_⟩
  intro r hr hrr μ ν _ _ hμU hνU hμE hνE k hk E hE
  have hr1 : r < 1 := lt_of_le_of_lt (hrr.trans (min_le_right _ _)) (by norm_num)
  have hcap : ENNReal.ofReal (r^(-(e/2))) ≤ ENNReal.ofReal (r^(-e)) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hr hr1.le (by linarith))
  have hmass : ENNReal.ofReal (r^e) < ENNReal.ofReal (r^(e/2)) := by
    exact (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hr _)).2
      (Real.rpow_lt_rpow_of_exponent_gt hr hr1 (by linarith))
  let lawP := differenceLaw μ ∗ₘ differenceLaw ν
  haveI : IsProbabilityMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  haveI : IsProbabilityMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  haveI : IsProbabilityMeasure lawP := by dsimp [lawP]; infer_instance
  have hpow : additiveLawPower lawP k = (lawP ∗ lawP) ∗ additiveLawPower lawP (k-2) := by
    convert additive_law_power_two_add lawP (k-2) using 1 <;> congr 1 <;> omega
  have hE' : ENNReal.ofReal (r^e) < ((lawP ∗ lawP) ∗ additiveLawPower lawP (k-2)) E := by
    rw [← hpow]
    exact hmass.trans_le hE
  apply convolution_large_image_of_base (lawP ∗ lawP) (additiveLawPower lawP (k-2))
    ⟨r,hr.le⟩ (ENNReal.ofReal (r^e)) (Nat.ceil (r^(-σ))) ?_ E hE'
  intro B hB
  exact hbase r hr (hrr.trans (min_le_left _ _)) μ ν hμU hνU
    (hμE.trans hcap) (hνE.trans hcap) B hB.le

#print axioms additiveLawPower_probability
#print axioms additive_law_power_two_add
#print axioms energy_difference_mconv_all_powers_large_image
end OAI.Falconer
