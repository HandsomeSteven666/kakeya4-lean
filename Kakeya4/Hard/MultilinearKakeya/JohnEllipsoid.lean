import Kakeya4.Hard.MultilinearKakeya.Imported.John.John
import Kakeya4.Hard.MultilinearKakeya.VisibilityBody

/-! John's ellipsoid for the actual truncated directional unit body.
The existence and contact decomposition are reused from the licensed Ullrich proof. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

def bodySeminorm {n : ℕ} (p : Seminorm ℝ (E n)) : Seminorm ℝ (E n) :=
  normSeminorm ℝ (E n) ⊔ p

theorem bodySeminorm_apply {n : ℕ} (p : Seminorm ℝ (E n)) (x : E n) :
    bodySeminorm p x = max ‖x‖ (p x) := rfl

theorem continuous_bodySeminorm {n : ℕ} (p : Seminorm ℝ (E n)) (hp : Continuous p) :
    Continuous (bodySeminorm p) := continuous_norm.max hp

theorem mem_visibilityBody_iff_bodySeminorm {n : ℕ} (p : Seminorm ℝ (E n)) (x : E n) :
    x ∈ visibilityBody p ↔ bodySeminorm p x ≤ 1 := by
  rw [mem_visibilityBody, bodySeminorm_apply, max_le_iff]

theorem norm_le_sqrt_mul_of_john_position {n : ℕ} (q : Seminorm ℝ (E n))
    (hq : Continuous q) (hq1 : ∀ u, q u ≤ ‖u‖)
    (hmax : ∀ S ∈ John.Feasible q, ‖S.det‖ ≤ 1) (z : E n) :
    ‖z‖ ≤ Real.sqrt n * q z := by
  obtain ⟨N, u, c, hcU, hc, hsum, hdec⟩ := John.john_decomposition q hq hq1 hmax
  have hcontact (i : Fin N) : ‖inner ℝ (u i) z‖ ≤ q z := by
    simpa only [norm_inner_symm] using John.norm_inner_le_of_contact (hcU i) z
  have hsq : ‖z‖^2 ≤ (n : ℝ) * (q z)^2 := by
    calc
      _ = ∑ i, c i * ‖inner ℝ (u i) z‖^2 := (John.sum_weight_inner_sq c u hdec z).symm
      _ ≤ ∑ i, c i * (q z)^2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (norm_nonneg _) (apply_nonneg q z)).mpr (hcontact i)) (hc i)
      _ = (∑ i, c i) * (q z)^2 := (Finset.sum_mul ..).symm
      _ = _ := by rw [hsum]
  apply (sq_le_sq₀ (norm_nonneg z) (mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg q z))).mp
  calc
    _ ≤ (n : ℝ) * (q z)^2 := hsq
    _ = (Real.sqrt n * q z)^2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

theorem exists_visibilityBody_johnEllipsoid_of_bound {n : ℕ} (p : Seminorm ℝ (E n))
    (hp : Continuous p) {C : ℝ} (hup : ∀ x, p x ≤ C * ‖x‖) :
    ∃ T : E n ≃L[ℝ] E n,
      T '' Metric.closedBall 0 1 ⊆ visibilityBody p ∧
      visibilityBody p ⊆ T '' Metric.closedBall 0 (Real.sqrt n) := by
  let q := bodySeminorm p
  have hqc : Continuous q := continuous_bodySeminorm p hp
  have hlo (x : E n) : (1 : ℝ) * ‖x‖ ≤ q x := by
    change (1 : ℝ) * ‖x‖ ≤ max ‖x‖ (p x)
    rw [one_mul]
    exact le_max_left _ _
  have hqup (x : E n) : q x ≤ max 1 C * ‖x‖ := by
    change max ‖x‖ (p x) ≤ max 1 C * ‖x‖
    apply max_le
    · simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) C) (norm_nonneg x)
    · exact (hup x).trans (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) C) (norm_nonneg x))
  obtain ⟨A, hA, hdet, hAmax⟩ := John.exists_maxVolume q hqc zero_lt_one hlo hqup
  let T := A.toContinuousLinearEquivOfDetNeZero hdet
  let q' : Seminorm ℝ (E n) := q.comp A.toLinearMap
  have hq'c : Continuous q' := hqc.comp A.continuous
  have hq'1 (u : E n) : q' u ≤ ‖u‖ := hA u
  have hq'max (S : E n →L[ℝ] E n) (hS : S ∈ John.Feasible q') : ‖S.det‖ ≤ 1 := by
    have hAS : A.comp S ∈ John.Feasible q := hS
    have h := hAmax (A.comp S) hAS
    have hdc : (A.comp S).det = A.det * S.det := by
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
    rw [hdc, norm_mul] at h
    exact (mul_le_iff_le_one_right (norm_pos_iff.mpr hdet)).mp h
  have hT (x : E n) : q' x = q (T x) := rfl
  refine ⟨T, ?_, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    rw [mem_visibilityBody_iff_bodySeminorm]
    exact (hA z).trans (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  · intro x hx
    refine ⟨T.symm x, ?_, T.apply_symm_apply x⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hxq : q x ≤ 1 := (mem_visibilityBody_iff_bodySeminorm p x).mp hx
    calc
      _ ≤ Real.sqrt n * q' (T.symm x) :=
        norm_le_sqrt_mul_of_john_position q' hq'c hq'1 hq'max _
      _ = Real.sqrt n * q x := by rw [hT, T.apply_symm_apply]
      _ ≤ Real.sqrt n * 1 := mul_le_mul_of_nonneg_left hxq (Real.sqrt_nonneg _)
      _ = _ := mul_one _

theorem exists_smoothVisibility_johnEllipsoid {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (ε : ℝ) {Q : Set (E n)} (hQ : IsCompact Q) :
    ∃ T : E n ≃L[ℝ] E n,
      T '' Metric.closedBall 0 1 ⊆ visibilityBody (smoothDirectionalSeminorm P ε Q hQ) ∧
      visibilityBody (smoothDirectionalSeminorm P ε Q hQ) ⊆
        T '' Metric.closedBall 0 (Real.sqrt n) :=
  exists_visibilityBody_johnEllipsoid_of_bound _ (continuous_smoothDirectionalSeminorm P ε hQ)
    (directionalEnergy_le_gradient_integral P ε hQ)

theorem volume_image_closedBall_scaled {n : ℕ} (T : E n ≃L[ℝ] E n)
    {r : ℝ} (hr : 0 ≤ r) :
    volume (T '' Metric.closedBall 0 r) =
      ENNReal.ofReal (r^n) * volume (T '' Metric.closedBall 0 1) := by
  rw [Measure.addHaar_image_continuousLinearEquiv,
    Measure.addHaar_image_continuousLinearEquiv,
    Measure.addHaar_closedBall' volume (0 : E n) hr]
  simp only [E, finrank_euclideanSpace, Fintype.card_fin]
  ac_rfl

theorem johnEllipsoid_volume_comparison {n : ℕ} (p : Seminorm ℝ (E n))
    (T : E n ≃L[ℝ] E n)
    (hinner : T '' Metric.closedBall 0 1 ⊆ visibilityBody p)
    (houter : visibilityBody p ⊆ T '' Metric.closedBall 0 (Real.sqrt n)) :
    volume (T '' Metric.closedBall 0 1) ≤ volume (visibilityBody p) ∧
      volume (visibilityBody p) ≤ ENNReal.ofReal (Real.sqrt n ^ n) *
        volume (T '' Metric.closedBall 0 1) := by
  refine ⟨measure_mono hinner, ?_⟩
  exact (measure_mono houter).trans_eq (volume_image_closedBall_scaled T (Real.sqrt_nonneg _))

end Kakeya4.Hard.MultilinearKakeya
