import Mathlib

/-! Exact-sequence logarithmic subpower closure used by the slope-volume bound.
This is a theorem about a supplied filter and supplied limit, not a replacement
for the user-owned Foundation subpower definitions or their configuration semantics. -/

noncomputable section
open Filter
open scoped Topology

namespace Kakeya4.Hard

theorem tendsto_log_const_mul_pow_div {ι : Type*} (l : Filter ι) (R K : ι → ℝ)
    (hR : Tendsto R l atTop) (hK : ∀ i, 0 < K i)
    (hlog : Tendsto (fun i => Real.log (K i) / Real.log (R i)) l (𝓝 0))
    (c : ℝ) (hc : 0 < c) (m : ℕ) :
    Tendsto (fun i => Real.log (c * K i ^ m) / Real.log (R i)) l (𝓝 0) := by
  have hconst : Tendsto (fun i => Real.log c / Real.log (R i)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hR)
  have he (i : ι) : Real.log (c*K i^m) / Real.log (R i) =
      Real.log c / Real.log (R i) + (m : ℝ)*(Real.log (K i)/Real.log (R i)) := by
    rw [Real.log_mul hc.ne' (pow_ne_zero m (hK i).ne'),Real.log_pow]
    ring
  have hm : Tendsto (fun _ : ι => (m : ℝ)) l (𝓝 (m : ℝ)) := tendsto_const_nhds
  have hh := hconst.add (hm.mul hlog)
  simpa only [← he,mul_zero,add_zero] using hh

theorem le_const_mul_pow_of_one_le (K c : ℝ) (hK : 1 ≤ K) (hc : 1 ≤ c) (m : ℕ)
    (hm : 1 ≤ m) : K ≤ c*K^m := by
  have hpow : K ≤ K^m := by
    simpa only [pow_one] using pow_le_pow_right₀ hK hm
  exact hpow.trans (le_mul_of_one_le_left (pow_nonneg (le_trans zero_le_one hK) _) hc)

end Kakeya4.Hard
