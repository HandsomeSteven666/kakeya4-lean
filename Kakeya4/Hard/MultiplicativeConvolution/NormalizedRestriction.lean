import Kakeya4.Hard.MultiplicativeConvolution.EnergyNonconcentration

/-! # Actual normalized large-mass restrictions and their uniform nonconcentration -/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The actual restriction normalized by its own mass. No probability fact is assumed. -/
def normalizedRestriction (μ : Measure ℝ) (A : Set ℝ) : Measure ℝ := (μ A)⁻¹ • μ.restrict A

/-- Small discarded probability mass gives a genuine lower bound for the retained mass. -/
theorem measure_half_le_of_compl_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {A : Set ℝ} (hA : MeasurableSet A) (hb : μ Aᶜ ≤ (1/2:ℝ≥0∞)) :
    (1/2:ℝ≥0∞) ≤ μ A := by
  have hsum := congrArg ENNReal.toReal (measure_add_measure_compl (μ := μ) hA)
  rw [ENNReal.toReal_add (measure_ne_top μ A) (measure_ne_top μ Aᶜ), measure_univ,
    ENNReal.toReal_one] at hsum
  have hc := ENNReal.toReal_mono (by norm_num : (1/2:ℝ≥0∞) ≠ ⊤) hb
  norm_num at hc
  have hreal : (1/2:ℝ) ≤ (μ A).toReal := by linarith
  have h := ENNReal.ofReal_le_ofReal hreal
  simpa only [ENNReal.ofReal_toReal (measure_ne_top μ A), ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using h

/-- A nonzero finite retained mass makes the actual normalization a probability law. -/
theorem isProbabilityMeasure_normalizedRestriction (μ : Measure ℝ) [IsFiniteMeasure μ]
    (A : Set ℝ) (hA0 : μ A ≠ 0) : IsProbabilityMeasure (normalizedRestriction μ A) := by
  constructor
  rw [normalizedRestriction, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hA0 (measure_ne_top μ A)

/-- Normalization of a restriction preserves unit support, including points through zero. -/
theorem normalizedRestriction_unitSupported (μ : Measure ℝ) {A : Set ℝ} (hμ : UnitSupported μ) :
    UnitSupported (normalizedRestriction μ A) :=
  Measure.ae_smul_measure (ae_restrict_of_ae hμ) _

/-- Retaining at least half the mass costs at most two in every measurable ball bound. -/
theorem normalizedRestriction_ball_le_two (μ : Measure ℝ) (A : Set ℝ)
    (hhalf : (1/2:ℝ≥0∞) ≤ μ A) (z R : ℝ) :
    normalizedRestriction μ A (closedBall z R) ≤ 2 * (μ.restrict A) (closedBall z R) := by
  have hi : (μ A)⁻¹ ≤ 2 := by
    have h := ENNReal.inv_le_inv.mpr hhalf
    norm_num at h
    exact h
  rw [normalizedRestriction, Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_left hi _

/-- The actual normalized good law is a probability with uniform scale nonconcentration. -/
theorem exists_nonconcentrated_probability_restriction (κ : SmoothKernel)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {s r ε : ℝ}
    (hs : 0 ≤ s) (hr : 0 < r) (hμ : UnitSupported μ)
    (hsmall : r^ε ≤ (1/2:ℝ))
    (he : smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε))) :
    ∃ A : Set ℝ, MeasurableSet A ∧ μ Aᶜ ≤ ENNReal.ofReal (r^ε) ∧
      IsProbabilityMeasure (normalizedRestriction μ A) ∧
      UnitSupported (normalizedRestriction μ A) ∧
      ∀ (z R : ℝ), r ≤ R →
        normalizedRestriction μ A (closedBall z R) ≤
          ENNReal.ofReal (2*(6:ℝ)^s*r^(-2*ε)*R^s) := by
  obtain ⟨A,hA,hbad,hball⟩ := exists_large_mass_nonconcentrated_restriction κ μ hs hr he
  have hhalf : (1/2:ℝ≥0∞) ≤ μ A := by
    apply measure_half_le_of_compl_le μ hA
    have h := hbad.trans (ENNReal.ofReal_le_ofReal hsmall)
    have heq : ENNReal.ofReal (1/2 : ℝ) = (1/2:ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
      norm_num
    rw [heq] at h
    exact h
  have hA0 : μ A ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞) < 1/2) hhalf)
  refine ⟨A,hA,hbad,isProbabilityMeasure_normalizedRestriction μ A hA0,
    normalizedRestriction_unitSupported μ hμ,?_⟩
  intro z R hR
  calc
    _ ≤ 2 * (μ.restrict A) (closedBall z R) := normalizedRestriction_ball_le_two μ A hhalf z R
    _ ≤ 2 * ENNReal.ofReal ((6:ℝ)^s*r^(-2*ε)*R^s) := mul_le_mul_right (hball z R hR) 2
    _ = _ := by rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]; congr 1; ring

/-- A positive exponent admits a small-scale threshold chosen before any input law. -/
theorem exists_scale_rpow_le_half {ε : ℝ} (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → r^ε ≤ (1/2:ℝ) := by
  let r₀ := min 1 ((1/2:ℝ)^(1/ε))
  refine ⟨r₀,lt_min (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _),min_le_left _ _,?_⟩
  intro r hr hrr
  have h := Real.rpow_le_rpow hr.le (hrr.trans (min_le_right _ _)) hε.le
  have heq : ((1/2:ℝ)^(1/ε))^ε = (1/2:ℝ) := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2), div_mul_cancel₀ _ hε.ne', Real.rpow_one]
  exact h.trans_eq heq

/-- Uniform high-mass probability extraction from the original energy, with no extra scale hypothesis. -/
theorem exists_uniform_nonconcentrated_probability_restriction (κ : SmoothKernel)
    {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], UnitSupported μ →
        ∀ r : ℝ, 0 < r → r ≤ r₀ →
          smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε)) →
          ∃ A : Set ℝ, MeasurableSet A ∧ μ Aᶜ ≤ ENNReal.ofReal (r^ε) ∧
            IsProbabilityMeasure (normalizedRestriction μ A) ∧
            UnitSupported (normalizedRestriction μ A) ∧
            ∀ (z R : ℝ), r ≤ R → normalizedRestriction μ A (closedBall z R) ≤
              ENNReal.ofReal (2*(6:ℝ)^s*r^(-2*ε)*R^s) := by
  obtain ⟨r₀,hr₀,hr₀1,hsmall⟩ := exists_scale_rpow_le_half hε
  refine ⟨r₀,hr₀,hr₀1,?_⟩
  intro μ _ hμ r hr hrr he
  exact exists_nonconcentrated_probability_restriction κ μ hs hr hμ (hsmall r hr hrr) he

end Kakeya4.Hard.MultiplicativeConvolution
