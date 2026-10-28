import OAI.MeasureTheory.Falconer.FlatteningFinePairMass
import Kakeya4.Hard.MultiplicativeConvolution.AllScaleSmoothing

/-! A small extra exponent gap turns fine/intermediate/coarse bounds into one integrated power bound. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem three_range_mass_power_bound {δ r u β a C : ℝ} (F : ℝ≥0∞)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hr : 0 < r) (hβ : 0 < β)
    (hv : 0 ≤ u+β) (hv1 : u+β ≤ 1) (hgap : a*(u+β) ≤ 2*β) (hC : 0 ≤ C)
    (hf : F ≤ ENNReal.ofReal (2*r*δ^(u-1-β)))
    (hi : δ ≤ 4*r → 4*r ≤ δ^a → F ≤ ENNReal.ofReal (C*r*(4*r)^(u-1-β)))
    (hp : F ≤ 1) :
    F ≤ ENNReal.ofReal (max 2 (max C (4^(u+β)))*δ^(-2*β)*r^(u+β)) := by
  let B : ℝ := max 2 (max C (4^(u+β)))
  have hB2 : 2 ≤ B := le_max_left _ _
  have hBC : C ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hB4 : 4^(u+β) ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  by_cases hlo : 4*r < δ
  · have hdp : δ^(u-1-β)=δ^(-2*β)*δ^(u+β-1) := by
      rw [← Real.rpow_add hδ]; congr 1; ring
    apply hf.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = (2*δ^(-2*β))*(δ^(u+β-1)*r) := by rw [hdp]; ring
      _ ≤ (2*δ^(-2*β))*r^(u+β) := mul_le_mul_of_nonneg_left
        (fine_radius_linear_le_power hv1 hδ hr (by linarith)) (by positivity)
      _ ≤ _ := by gcongr
  by_cases hhi : 4*r ≤ δ^a
  · apply (hi (le_of_not_gt hlo) hhi).trans
    apply ENNReal.ofReal_le_ofReal
    have hsplit : (4*r)^(u-1-β)=(4*r)^(-2*β)*(4*r)^(u+β-1) := by
      rw [← Real.rpow_add (by positivity : 0 < 4*r)]; congr 1; ring
    have hpow : (4*r)^(-2*β) ≤ δ^(-2*β) :=
      Real.rpow_le_rpow_of_nonpos hδ (le_of_not_gt hlo) (by linarith)
    have hpow' : (4*r)^(u+β-1) ≤ r^(u+β-1) :=
      Real.rpow_le_rpow_of_nonpos hr (by linarith) (by linarith)
    calc
      _ = (C*r)*((4*r)^(-2*β)*(4*r)^(u+β-1)) := by rw [hsplit]
      _ ≤ (C*r)*(δ^(-2*β)*r^(u+β-1)) := mul_le_mul_of_nonneg_left
        (mul_le_mul hpow hpow' (by positivity) (by positivity)) (by positivity)
      _ = C*δ^(-2*β)*r^(u+β) := by
        rw [Real.rpow_sub hr,Real.rpow_one]
        field_simp [hr.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hBC (by positivity)) (by positivity)
  · apply hp.trans
    have hpower : δ^(2*β) ≤ 4^(u+β)*r^(u+β) := by
      calc
        _ ≤ δ^(a*(u+β)) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hgap
        _ = (δ^a)^(u+β) := Real.rpow_mul hδ.le _ _
        _ ≤ (4*r)^(u+β) := Real.rpow_le_rpow (by positivity) (le_of_not_ge hhi) hv
        _ = _ := Real.mul_rpow (by norm_num) hr.le
    have hcancel : δ^(-2*β)*δ^(2*β)=1 := by rw [← Real.rpow_add hδ]; simp
    have hpaid : (1:ℝ) ≤ B*δ^(-2*β)*r^(u+β) := by
      calc
        _ = δ^(-2*β)*δ^(2*β) := hcancel.symm
        _ ≤ δ^(-2*β)*(4^(u+β)*r^(u+β)) := mul_le_mul_of_nonneg_left hpower (by positivity)
        _ = 4^(u+β)*δ^(-2*β)*r^(u+β) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hB4 (by positivity)) (by positivity)
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hpaid

#print axioms three_range_mass_power_bound
end OAI.Falconer
