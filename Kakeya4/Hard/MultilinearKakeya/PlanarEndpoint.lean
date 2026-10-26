import Kakeya4.Hard.MultilinearKakeya.PlanarGeometry

/-! The genuine planar endpoint, for arbitrary radius and finite weighted full-line families. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Kakeya4.Hard.MultilinearKakeya

def normalMatrix (L : Fin 2 → Line 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => perpendicular (L i).direction j

theorem det_normalMatrix (L : Fin 2 → Line 2) :
    (normalMatrix L).det = Matrix.det (fun i j : Fin 2 => (L j).direction i) := by
  rw [Matrix.det_fin_two (normalMatrix L),
    Matrix.det_fin_two (fun i j : Fin 2 => (L j).direction i)]
  simp [normalMatrix, perpendicular]
  ring

theorem normalMatrix_mulVec (L : Fin 2 → Line 2) (x : Fin 2 → ℝ) (i : Fin 2) :
    (normalMatrix L).mulVec x i =
      ⟪perpendicular (L i).direction, (WithLp.toLp 2 x : E 2)⟫_ℝ := by
  simp [normalMatrix, Matrix.mulVec, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, mul_comm]

/-- Determinant-weighted intersection area, including parallel lines and infinite
unweighted intersections. No angle-separation or anchor bound is required. -/
theorem determinantWeight_mul_volume_tupleRegion_two
    (L : Fin 2 → Line 2) (r : ℝ) (hr : 0 ≤ r) :
    determinantWeight L * volume (tupleRegion L r) ≤ ENNReal.ofReal (4*r^2) := by
  let S : Set (Fin 2 → ℝ) := (WithLp.toLp 2) ⁻¹' tupleRegion L r
  let c : Fin 2 → ℝ := fun i => ⟪perpendicular (L i).direction, (L i).anchor⟫_ℝ
  have hvol : volume S = volume (tupleRegion L r) :=
    (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
      (measurableSet_tupleRegion L r).nullMeasurableSet
  have hS (x : Fin 2 → ℝ) (hx : x ∈ S) (i : Fin 2) :
      |(normalMatrix L).mulVec x i - c i| ≤ r := by
    rw [normalMatrix_mulVec]
    change |⟪perpendicular (L i).direction, (WithLp.toLp 2 x : E 2)⟫_ℝ -
      ⟪perpendicular (L i).direction, (L i).anchor⟫_ℝ| ≤ r
    rw [← inner_sub_right]
    exact tube_subset_normalStrip (L i) r (hx i)
  have h := determinant_mul_volume_le_rectangle (normalMatrix L) S c r hr hS
  rw [det_normalMatrix, hvol] at h
  exact h

/-- The planar determinant endpoint with the uniform constant C₂=4. -/
theorem endpointBound_two : EndpointBound 2 := by
  refine ⟨4, by norm_num, ?_⟩
  intro ι _ L w r hr
  have h := lintegral_kernel_le_of_tuple_bound L w r (ENNReal.ofReal (4*r^2))
    (fun a => determinantWeight_mul_volume_tupleRegion_two (fun i => L i (a i)) r hr.le)
  have hexp : endpointExponent 2 = 1 := by norm_num [endpointExponent]
  simp only [hexp, ENNReal.rpow_one]
  convert h using 1
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

end Kakeya4.Hard.MultilinearKakeya
