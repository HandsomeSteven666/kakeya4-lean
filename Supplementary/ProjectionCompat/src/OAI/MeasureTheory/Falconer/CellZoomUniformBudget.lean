import OAI.MeasureTheory.Falconer.ConditionalRadialTransport

/-! Uniform absorption of the coefficient from all small-cell similarities,
including zoom factors between1/16 and1. No dependence on the pair's position
or on its separation enters the common scale threshold. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem cell_zoom_frostman_factor_le_sixteen {a α : ℝ}
    (ha : 0 < a) (haLower : 1/16 ≤ a) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    a^(-α) ≤ 16 := by
  by_cases ha1 : a ≤ 1
  · calc
      a^(-α) ≤ a^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_ge ha ha1 (by linarith)
      _ = a⁻¹ := Real.rpow_neg_one a
      _ ≤ (1/16:ℝ)⁻¹ := inv_anti₀ (by norm_num) haLower
      _ = 16 := by norm_num
  · exact (Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge ha1) (neg_nonpos.mpr hα)).trans (by norm_num)

theorem normalized_cell_zoom_uniform_budget (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (d : ℕ) (ε κ α L C a : ℝ),
    0 ≤ α → α ≤ 1 → 0 ≤ C → 0 < L → ∀ ha : 0 < a, 1/16 ≤ a →
    C ≤ ((2:ℝ)^N)^ε → ((2:ℝ)^N)^(-κ) ≤ L →
    ∀ (μ : Measure (Space d)) [IsFiniteMeasure μ],
    ∀ (A : Set (Space d)) (hA : MeasurableSet A) (hpos : (μ.restrict A) univ ≠ 0),
    ENNReal.ofReal L ≤ μ A → ∀ center : Space d,
    FrostmanBallBound μ α C →
    FrostmanBallBound (Measure.map (radialZoom a ha.ne' center)
      (normalizedSliceLaw (μ.restrict A) hpos : Measure (Space d))) α (((2:ℝ)^N)^(ε+κ+ζ)) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hζ 16
  refine ⟨N₀,?_⟩
  intro N hN d ε κ α L C a hα hα1 hC hL ha haLower hCbudget hLbudget μ _ A hA hpos hmass center hfrost
  have hR0 : 0 < (2:ℝ)^N := by positivity
  have hInv : L⁻¹ ≤ ((2:ℝ)^N)^κ := calc
    _ ≤ (((2:ℝ)^N)^(-κ))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hR0 _) hLbudget
    _ = _ := by rw [Real.rpow_neg hR0.le,inv_inv]
  have hCL : C/L ≤ ((2:ℝ)^N)^(ε+κ) := calc
    _ = C*L⁻¹ := div_eq_mul_inv _ _
    _ ≤ ((2:ℝ)^N)^ε*((2:ℝ)^N)^κ := mul_le_mul hCbudget hInv (inv_nonneg.mpr hL.le) (Real.rpow_nonneg hR0.le _)
    _ = _ := (Real.rpow_add hR0 _ _).symm
  have hcoef : (C/L)*a^(-α) ≤ ((2:ℝ)^N)^(ε+κ+ζ) := calc
    _ ≤ ((2:ℝ)^N)^(ε+κ)*16 := mul_le_mul hCL
      (cell_zoom_frostman_factor_le_sixteen ha haLower hα hα1) (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hR0.le _)
    _ ≤ ((2:ℝ)^N)^(ε+κ)*((2:ℝ)^N)^ζ := mul_le_mul_of_nonneg_left (hN₀ N hN) (Real.rpow_nonneg hR0.le _)
    _ = _ := (Real.rpow_add hR0 _ _).symm
  intro x r hr
  exact (normalized_restriction_zoom_frostman μ A hA hpos hL hmass ha center hfrost x r hr).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hr.le _)))

#print axioms cell_zoom_frostman_factor_le_sixteen
#print axioms normalized_cell_zoom_uniform_budget
end OAI.Falconer
