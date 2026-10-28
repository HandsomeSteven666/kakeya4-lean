import OAI.MeasureTheory.Falconer.FourierFlattenedMerge

/-! Preserve the positive exponent surplus and pay the Fourier power root. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution

theorem exists_interior_merge_exponents {s t T : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hT : 0 < T) (htotal : 1 < s+t+T) :
    ∃ u v : ℝ, 0 < u ∧ u ≤ s ∧ 0 < v ∧ v ≤ t ∧ u+v < 1 ∧ 1 < u+v+T := by
  have hbound : max 0 (1-T) < min (s+t) 1 := by
    apply lt_min
    · exact max_lt (by positivity) (by linarith)
    · exact max_lt (by norm_num) (by linarith)
  obtain ⟨w,hwlo,hwhi⟩ := exists_between hbound
  have hw : 0 < w := (le_max_left _ _).trans_lt hwlo
  have hwS : w < s+t := hwhi.trans_le (min_le_left _ _)
  have hw1 : w < 1 := hwhi.trans_le (min_le_right _ _)
  let c : ℝ := w/(s+t)
  have hc : 0 < c := div_pos hw (by positivity)
  have hc1 : c ≤ 1 := (div_le_one (by positivity : 0<s+t)).mpr hwS.le
  have hsum : c*s+c*t=w := by
    rw [← mul_add]
    exact div_mul_cancel₀ _ (by positivity : s+t≠0)
  refine ⟨c*s,c*t,mul_pos hc hs,?_,mul_pos hc ht,?_,?_,?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hs.le
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 ht.le
  · linarith
  · have hp := (le_max_right 0 (1-T)).trans_lt hwlo
    linarith

theorem fourier_power_root_after_normalization {z : ℂ} {p : ℕ} {R ξ τ : ℝ}
    (hp : 0 < p) (hR : 1 ≤ R) (hξ : 0 < |ξ|) (hτ : 0 ≤ τ)
    (hbound : ‖z‖^p ≤ |R*ξ|^(-τ)) : ‖z‖ ≤ |ξ|^(-τ/(p:ℝ)) := by
  apply le_of_pow_le_pow_left₀ hp.ne' (Real.rpow_nonneg (abs_nonneg ξ) _)
  have hpow : (|ξ|^(-τ/(p:ℝ)))^p = |ξ|^(-τ) := by
    rw [← Real.rpow_mul_natCast (abs_nonneg ξ),div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hp.ne')]
  rw [hpow]
  apply hbound.trans
  apply Real.rpow_le_rpow_of_nonpos hξ
  · rw [abs_mul,abs_of_pos (by linarith : 0<R)]
    exact le_mul_of_one_le_left (abs_nonneg _) hR
  · linarith

#print axioms exists_interior_merge_exponents
#print axioms fourier_power_root_after_normalization
end OAI.Falconer
