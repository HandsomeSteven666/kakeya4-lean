import Kakeya4.Hard.AlgebraicGeometry.SpatialRegionVolume
import Kakeya4.Hard.AlgebraicGeometry.EligibleVolume

/-! The physical inverse matrix produces the determinant factor in the allowed-region volume. -/

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace Kakeya4.Hard.EligibleFormula

def inverseSpatialMap (p : Parameters) : Plane →ₗ[ℝ] Plane :=
  Matrix.toLin' (fun i j : Fin 2 => p (.inverseMatrix i j))

def physicalCenter (p : Parameters) (t : ℝ) : Plane :=
  fun j => p (.centerBase j) + t * p (.centerVelocity j)

theorem spatialEnergyValue_base (p : Parameters) (t : ℝ) (y : Plane) :
    spatialEnergyValue p t (Fin.snoc y 0) =
      ∑ i : Fin 2, (inverseSpatialMap p (y-physicalCenter p t) i)^2 := by
  change (∑ i : Fin 2, (∑ j : Fin 2, p (.inverseMatrix i j) *
    ((Fin.snoc y 0 : Point) j.castSucc - p (.centerBase j) - t*p (.centerVelocity j)))^2) =
    ∑ i : Fin 2, (∑ j : Fin 2, p (.inverseMatrix i j) * (y-physicalCenter p t) j)^2
  simp only [Fin.snoc_castSucc,Pi.sub_apply,physicalCenter,sub_add_eq_sub_sub]

theorem volume_baseRegion_le (p : Parameters) (t : ℝ) (D : Plane ≃L[ℝ] Plane)
    (hD : inverseSpatialMap p = (D.symm : Plane →ₗ[ℝ] Plane)) (hK : 0 ≤ p .K) :
    volume (baseRegion p t) ≤ ENNReal.ofReal (4*(p .K)^2 * |(D : Plane →ₗ[ℝ] Plane).det|) := by
  have he : baseRegion p t = normalizedPlanarRegion D (physicalCenter p t) (p .K) := by
    ext y
    simp only [baseRegion,normalizedPlanarRegion,mem_ofPred_eq,spatialEnergyValue_base,hD]
    rfl
  rw [he]
  exact volume_normalizedPlanarRegion_le D (physicalCenter p t) (p .K) hK

theorem volume_allowedRegion_physical_le (p : Parameters) (t : ℝ) (D : Plane ≃L[ℝ] Plane)
    (hD : inverseSpatialMap p = (D.symm : Plane →ₗ[ℝ] Plane))
    (hK : 0 < p .K) (ha : 0 < p .thickness) (hM : 0 < p .invK) :
    volume (allowedRegion p t) ≤
      ENNReal.ofReal (512 * (p .K)^3 * p .thickness * |(D : Plane →ₗ[ℝ] Plane).det| / p .invK) := by
  calc
    volume (allowedRegion p t) ≤ ENNReal.ofReal (4*(p .K*p .thickness)/(p .invK/32)) *
        volume (baseRegion p t) := volume_allowedRegion_le_base p t (mul_pos hK ha) hM
    _ ≤ ENNReal.ofReal (4*(p .K*p .thickness)/(p .invK/32)) *
        ENNReal.ofReal (4*(p .K)^2*|(D : Plane →ₗ[ℝ] Plane).det|) := by
      gcongr
      exact volume_baseRegion_le p t D hD hK.le
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4*(p .K*p .thickness)/(p .invK/32))]
      congr 1
      field_simp
      ring

/-- The remaining spatial bound is now discharged, with the exact physical determinant. -/
theorem physical_eligible_slope_volume :
    ∃ N : ℕ, ∀ (p : Parameters) (D : Plane ≃L[ℝ] Plane),
      inverseSpatialMap p = (D.symm : Plane →ₗ[ℝ] Plane) →
      p .lo < p .hi → 0 < p .K → 0 < p .thickness → p .invK = (p .K)⁻¹ →
      volume (eligibleSlopes p) ≤ ENNReal.ofReal
        (14155776 * (N : ℝ) * (p .K)^4 * p .thickness * |(D : Plane →ₗ[ℝ] Plane).det| /
          (p .hi-p .lo)^3) := by
  obtain ⟨N,hN⟩ := eligible_slope_volume_of_region_bound
  refine ⟨N,fun p D hD hI hK ha hrec => ?_⟩
  have hM : 0 < p .invK := by rw [hrec]; exact inv_pos.mpr hK
  have hh := hN p hI hM
    (512*(p .K)^3*p .thickness*|(D : Plane →ₗ[ℝ] Plane).det|/p .invK)
    (fun t _ => volume_allowedRegion_physical_le p t D hD hK ha hM)
  convert hh using 1
  congr 1
  rw [hrec,div_inv_eq_mul]
  ring

end Kakeya4.Hard.EligibleFormula
