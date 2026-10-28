import OAI.MeasureTheory.Falconer.FourierFlatteningTransfer

/-! Exact support radii for the actual difference-product powers. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution

theorem ae_additive_convolution_radius (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    {A B : ℝ} (hμ : ∀ᵐ x ∂μ, |x|≤A) (hν : ∀ᵐ y ∂ν, |y|≤B) :
    ∀ᵐ z ∂μ ∗ ν, |z|≤A+B := by
  unfold Measure.conv
  apply (ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)).2
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  exact (abs_add_le x y).trans (add_le_add hx hy)

theorem ae_multiplicative_convolution_radius (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    {A B : ℝ} (hA : 0 ≤ A) (hμ : ∀ᵐ x ∂μ, |x|≤A) (hν : ∀ᵐ y ∂ν, |y|≤B) :
    ∀ᵐ z ∂μ ∗ₘ ν, |z|≤A*B := by
  unfold Measure.mconv
  apply (ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)).2
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  simpa only [abs_mul] using mul_le_mul hx hy (abs_nonneg _) hA

theorem differenceLaw_radius_two (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : UnitSupported μ) :
    ∀ᵐ x ∂differenceLaw μ, |x|≤2 := by
  have hneg : ∀ᵐ x ∂μ.map (fun x : ℝ ↦ -x), |x|≤1 := by
    apply (ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)).2
    simpa only [UnitSupported,abs_neg] using hμ
  simpa only [differenceLaw,one_add_one_eq_two] using ae_additive_convolution_radius μ (μ.map (fun x ↦ -x)) hμ hneg

theorem difference_product_radius_four (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : UnitSupported μ) (hν : UnitSupported ν) :
    ∀ᵐ x ∂differenceLaw μ ∗ₘ differenceLaw ν, |x|≤4 := by
  have : IsFiniteMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  have : IsFiniteMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  simpa only [show (2:ℝ)*2=4 by norm_num] using ae_multiplicative_convolution_radius
    (differenceLaw μ) (differenceLaw ν) (by norm_num) (differenceLaw_radius_two μ hμ)
    (differenceLaw_radius_two ν hν)

theorem additiveLawPower_radius (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {R : ℝ}
    (hρ : ∀ᵐ x ∂ρ, |x|≤R) (k : ℕ) :
    ∀ᵐ x ∂additiveLawPower ρ k, |x|≤(k:ℝ)*R := by
  induction k with
  | zero => simp [additiveLawPower]
  | succ k ih =>
    have h := ae_additive_convolution_radius (additiveLawPower ρ k) ρ ih hρ
    change ∀ᵐ x ∂additiveLawPower ρ k ∗ ρ, |x|≤((k+1:ℕ):ℝ)*R
    simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using h

theorem normalized_difference_product_power_unitSupported (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμ : UnitSupported μ) (hν : UnitSupported ν)
    {k : ℕ} (hk : 0 < k) :
    UnitSupported ((additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k).map
      (fun x : ℝ ↦ x/(4*(k:ℝ)))) := by
  have : IsProbabilityMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  apply (ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)).2
  filter_upwards [additiveLawPower_radius _ (difference_product_radius_four μ ν hμ hν) k] with x hx
  rw [abs_div,abs_of_pos (by positivity : 0 < 4*(k:ℝ)),div_le_one (by positivity : 0 < 4*(k:ℝ))]
  nlinarith

#print axioms ae_additive_convolution_radius
#print axioms ae_multiplicative_convolution_radius
#print axioms differenceLaw_radius_two
#print axioms difference_product_radius_four
#print axioms additiveLawPower_radius
#print axioms normalized_difference_product_power_unitSupported
end OAI.Falconer
