






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningLayerLoss

/-! Pay the polynomial layer loss before invoking the actual large-image threshold. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set Metric
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem exists_layer_mass_threshold_coefficient {M Q e θ : ℝ}
    (hM : 0 < M) (hQ : 0 < Q) (_he : 0 < e) (hθ : θ < 2*e) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ L : ℕ,
      (2:ℝ)^L ≤ 2*max 1 (M/r) →
      Q*((L:ℝ)+1)^4*((5*r)^e)^2 ≤ r^θ := by
  obtain ⟨r₀,hr₀,hr₀1,hloss⟩ := exists_small_scale_layer_power_bound hM
    (C := Q*5^(2*e)) (by positivity) (β := 2*e-θ) (by linarith) 4
  refine ⟨r₀,hr₀,hr₀1,?_⟩
  intro r hr hrr L hheight
  have h := mul_le_mul_of_nonneg_right (hloss r hr hrr L hheight)
    (Real.rpow_nonneg hr.le (2*e))
  have hl : (Q*5^(2*e))*((L:ℝ)+1)^4*r^(2*e) =
      Q*((L:ℝ)+1)^4*((5*r)^e)^2 := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ 5*r),
      Real.mul_rpow (by norm_num : (0:ℝ)≤5) hr.le]
    rw [show e*(2:ℕ) = 2*e by ring]
    ring
  have hrpow : r^(-(2*e-θ))*r^(2*e) = r^θ := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  simpa only [hl,hrpow] using h

theorem mass_threshold_of_paid_squared_bound (A q target m : ℝ≥0∞)
    (hA0 : A ≠ 0) (hAtop : A ≠ ⊤)
    (hpaid : A*target^2 ≤ q) (hmass : q ≤ A*m^2) : target ≤ m := by
  have hsq := (ENNReal.mul_le_mul_iff_right hA0 hAtop).mp (hpaid.trans hmass)
  exact (ENNReal.pow_le_pow_left_iff (by norm_num : (2:ℕ)≠0)).mp hsq

theorem exists_original_mass_threshold_payment {M Q e θ : ℝ}
    (hM : 0 < M) (hQ : 0 < Q) (he : 0 < e) (hθ : θ < 2*e) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ L : ℕ,
      (2:ℝ)^L ≤ 2*max 1 (M/r) → ∀ m : ℝ≥0∞,
      ENNReal.ofReal (r^θ) ≤ ENNReal.ofReal Q * ((L+1:ℕ):ℝ≥0∞)^4 * m^2 →
      ENNReal.ofReal ((5*r)^e) ≤ m := by
  obtain ⟨r₀,hr₀,hr₀1,hcoeff⟩ := exists_layer_mass_threshold_coefficient hM hQ he hθ
  refine ⟨r₀,hr₀,hr₀1,?_⟩
  intro r hr hrr L hheight m hmass
  have hpaid := ENNReal.ofReal_le_ofReal (hcoeff r hr hrr L hheight)
  have hL : ENNReal.ofReal ((L:ℝ)+1) = ((L+1:ℕ):ℝ≥0∞) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num)]
    simp
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ Q*((L:ℝ)+1)^4),
    ENNReal.ofReal_mul hQ.le,ENNReal.ofReal_pow (by positivity : 0 ≤ (L:ℝ)+1),
    ENNReal.ofReal_pow (by positivity : 0 ≤ (5*r)^e),hL] at hpaid
  have hA0 : ENNReal.ofReal Q * ((L+1:ℕ):ℝ≥0∞)^4 ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hQ).ne' (pow_ne_zero _ (by norm_num))
  have hAtop : ENNReal.ofReal Q * ((L+1:ℕ):ℝ≥0∞)^4 ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by finiteness)
  exact mass_threshold_of_paid_squared_bound (ENNReal.ofReal Q * ((L+1:ℕ):ℝ≥0∞)^4)
    (ENNReal.ofReal (r^θ)) (ENNReal.ofReal ((5*r)^e)) m hA0 hAtop hpaid hmass

theorem exists_uniform_paid_original_slow_mass (kernel : SmoothKernel) {e : ℝ} (he : 0 < e) :
    ∃ M T r₀ : ℝ, 0 < M ∧ 0 < T ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ r : ℝ, 0 < r → r ≤ r₀ → ∃ L : ℕ,
      (2:ℝ)^L ≤ 2*max 1 (M/r) ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      ENNReal.ofReal (r^e)*densityL2 μ (kernelProfile kernel r) ≤
        densityL2 (μ ∗ μ) (kernelProfile kernel r) →
      densityL2 (μ ∗ μ) (kernelProfile kernel r) ≤ ENNReal.ofReal T * ((L+1:ℕ):ℝ≥0∞)^2 ∨
      ∃ j : ℕ, j < L ∧ ENNReal.ofReal ((5*r)^e) ≤ μ (cthickening (4*r)
        (flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j)) := by
  obtain ⟨M,T,Q,hM,hT,hQ,hselect⟩ := exists_uniform_original_slow_neighborhood_mass kernel
  obtain ⟨r₀,hr₀,hr₀1,hpay⟩ := exists_original_mass_threshold_payment hM hQ he (by linarith : e<2*e)
  refine ⟨M,T,r₀,hM,hT,hr₀,hr₀1,?_⟩
  intro r hr hrr
  obtain ⟨L,hL,hchoose⟩ := hselect r hr
  refine ⟨L,hL,?_⟩
  intro μ _ hslow
  rcases hchoose μ (ENNReal.ofReal (r^e)) hslow with hlo | ⟨j,hj,hmass⟩
  · exact Or.inl hlo
  · exact Or.inr ⟨j,hj,hpay r hr hrr L hL _ hmass⟩

#print axioms exists_layer_mass_threshold_coefficient
#print axioms mass_threshold_of_paid_squared_bound
#print axioms exists_original_mass_threshold_payment
#print axioms exists_uniform_paid_original_slow_mass
end OAI.Falconer
