import Kakeya4.Hard.MultilinearKakeya.SpatialTestGeometry
import Kakeya4.Hard.MultilinearKakeya.ShapeClasses

/-! Coordinate identification of actual spatial tests with the already proved
affine bisection-energy interfaces. The reference-chart radius depends only on n. -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Kakeya4.Hard.MultilinearKakeya

def spatialReferenceChart (n : ℕ) : (Fin n → ℝ) ≃L[ℝ] E n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm

theorem spatialReferenceChart_apply (n : ℕ) (x : Fin n → ℝ) :
    spatialReferenceChart n x = WithLp.toLp 2 x := rfl

def chartOfShape {n : ℕ} (T : E n ≃L[ℝ] E n) : (Fin n → ℝ) ≃L[ℝ] E n :=
  (spatialReferenceChart n).trans T

def spatialReferenceRadius (n : ℕ) : ℝ := max 1 ‖(spatialReferenceChart n).toContinuousLinearMap‖

theorem spatialReferenceRadius_pos (n : ℕ) : 0 < spatialReferenceRadius n :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem norm_chartOfShape_le {n : ℕ} (T : E n ≃L[ℝ] E n) (hT : ‖T.toContinuousLinearMap‖ ≤ 1) :
    ‖(chartOfShape T).toContinuousLinearMap‖ ≤ spatialReferenceRadius n := by
  have he : (chartOfShape T).toContinuousLinearMap =
      T.toContinuousLinearMap.comp (spatialReferenceChart n).toContinuousLinearMap := by ext x; rfl
  rw [he]
  calc
    _ ≤ ‖T.toContinuousLinearMap‖ * ‖(spatialReferenceChart n).toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖(spatialReferenceChart n).toContinuousLinearMap‖ :=
      mul_le_mul_of_nonneg_right hT (norm_nonneg _)
    _ ≤ spatialReferenceRadius n := by simpa only [one_mul, spatialReferenceRadius] using (le_max_right 1 _)

def nativeDilation (n : ℕ) (r : ℝ) (hr : r ≠ 0) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (r • ContinuousLinearMap.id ℝ (Fin n → ℝ))
    (r⁻¹ • ContinuousLinearMap.id ℝ (Fin n → ℝ))
    (fun x => by simp [smul_smul,hr]) (fun x => by simp [smul_smul,hr])

theorem nativeDilation_apply (n : ℕ) (r : ℝ) (hr : r ≠ 0) (x : Fin n → ℝ) :
    nativeDilation n r hr x = r • x := rfl

def nativeSpatialShape {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n) (r : ℝ) (hr : r ≠ 0) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  (nativeDilation n r hr).trans (L.trans (spatialReferenceChart n).symm)

theorem nativeSpatialShape_toEuclidean {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    (r : ℝ) (hr : r ≠ 0) (x : Fin n → ℝ) :
    spatialReferenceChart n (nativeSpatialShape L r hr x) = r • L x := by
  change spatialReferenceChart n ((spatialReferenceChart n).symm (L (nativeDilation n r hr x))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, nativeDilation_apply, map_smul]

theorem spatialTestCell_eq_euclideanAffineRegion {n : ℕ}
    (L : (Fin n → ℝ) ≃L[ℝ] E n) (c : E n) {r : ℝ} (hr : 0 < r) :
    spatialTestCell L c r =
      euclideanAffineRegion (WithLp.ofLp c) (nativeSpatialShape L r hr.ne') := by
  ext x
  constructor
  · intro hx
    change ‖L.symm (x-c)‖ < r at hx
    let y := r⁻¹ • L.symm (x-c)
    have hy : y ∈ Metric.ball (0 : Fin n → ℝ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      change ‖r⁻¹ • L.symm (x-c)‖ < 1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), inv_mul_eq_div]
      exact (div_lt_iff₀ hr).mpr (by simpa only [one_mul] using hx)
    change WithLp.ofLp x ∈ (fun z => WithLp.ofLp c + nativeSpatialShape L r hr.ne' z) '' referenceDomain n
    refine ⟨y,hy,?_⟩
    apply (spatialReferenceChart n).injective
    rw [map_add, nativeSpatialShape_toEuclidean]
    change c + r • L y = x
    simp [y, map_smul, smul_smul, hr.ne']
  · rintro ⟨y,hy,he⟩
    have hy' : ‖y‖ < 1 := by simpa only [referenceDomain, Metric.mem_ball, dist_zero_right] using hy
    have he' := congrArg (spatialReferenceChart n) he
    change spatialReferenceChart n (WithLp.ofLp c + nativeSpatialShape L r hr.ne' y) = _ at he'
    rw [map_add, nativeSpatialShape_toEuclidean] at he'
    change c+r • L y = x at he'
    change ‖L.symm (x-c)‖ < r
    rw [← he', add_sub_cancel_left, map_smul, L.symm_apply_apply, norm_smul, Real.norm_of_nonneg hr.le]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hy' hr

theorem nativeSpatialShape_axis {n : ℕ} (T : E n ≃L[ℝ] E n) (r : ℝ) (hr : r ≠ 0) (j : Fin n) :
    WithLp.toLp 2 (nativeSpatialShape (chartOfShape T) r hr (Pi.single j 1)) =
      r • T (WithLp.toLp 2 (Pi.single j 1)) :=
  nativeSpatialShape_toEuclidean (chartOfShape T) r hr (Pi.single j 1)

end Kakeya4.Hard.MultilinearKakeya
