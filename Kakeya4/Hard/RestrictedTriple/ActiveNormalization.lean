import Kakeya4.Hard.RestrictedTriple.SelectedFrostman

set_option autoImplicit false
noncomputable section
open Set Metric

namespace Kakeya4.Hard.RestrictedTriple

def endpointCoordinateMap (a b : ℝ) (z : Plane) : Fin 3 → Plane → Plane :=
  ![(fun x ↦ a • x),(fun x ↦ z+b • x),(fun x ↦ z+b • x)]

theorem affinePlane_injective {c : ℝ} (hc : c ≠ 0) (z : Plane) :
    Function.Injective (fun x : Plane ↦ z+c • x) := by
  intro x y h
  have hh := congrArg (fun v : Plane ↦ c⁻¹ • v) (add_left_cancel h)
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hh

theorem endpointCoordinateMap_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (z : Plane) :
    ∀ j, Function.Injective (endpointCoordinateMap a b z j) := by
  intro j
  fin_cases j
  · simpa [endpointCoordinateMap] using affinePlane_injective ha (0 : Plane)
  · exact affinePlane_injective hb z
  · exact affinePlane_injective hb z

theorem activeTripleClasses_endpointNormalization (a b : ℝ) (z : Plane) (Q : Finset Triple) :
    activeTripleClasses (Q.image (endpointNormalization a b z)) =
      (fun j ↦ (activeTripleClasses Q j).image (endpointCoordinateMap a b z j)) := by
  classical
  funext j
  fin_cases j <;> simp [activeTripleClasses,threeClasses,endpointNormalization,
    endpointCoordinateMap,Finset.image_image,Function.comp_def]

theorem coordinateDensity_active_endpointNormalization {c a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (z : Plane) {Q : Finset Triple}
    (h : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap)) :
    coordinateDensity c (activeTripleClasses (Q.image (endpointNormalization a b z)))
      ((Q.image (endpointNormalization a b z)).image tripleVertexMap) := by
  classical
  have hh := coordinateDensity_map (endpointCoordinateMap a b z)
    (endpointCoordinateMap_injective ha hb z) h
  have himage : (Q.image tripleVertexMap).image (fun x i ↦ endpointCoordinateMap a b z i (x i)) =
      (Q.image (endpointNormalization a b z)).image tripleVertexMap := by
    simp only [Finset.image_image]
    congr 1
    funext t i
    fin_cases i <;> rfl
  rw [← activeTripleClasses_endpointNormalization,himage] at hh
  exact hh

theorem finiteFrostman_active_endpointNormalization {p η a b : ℝ} (hp : 0 < p) (hη : 0 ≤ η)
    (hpay : 8 ≤ p^(-η)) (ha : 1/8 ≤ a) (hb : 1/8 ≤ b) (z : Plane) (Q : Finset Triple)
    (h : ∀ j, finiteFrostman p (p^(-43*η)) (activeTripleClasses Q j)) :
    ∀ j, finiteFrostman (p/8) ((p/8)^(-44*η))
      (activeTripleClasses (Q.image (endpointNormalization a b z)) j) := by
  rw [activeTripleClasses_endpointNormalization]
  intro j
  fin_cases j
  · simpa [endpointCoordinateMap] using finiteFrostman_selected_affine_power hp hη hpay ha
      (0 : Plane) (activeTripleClasses Q 0) (h 0)
  · exact finiteFrostman_selected_affine_power hp hη hpay hb z _ (h 1)
  · exact finiteFrostman_selected_affine_power hp hη hpay hb z _ (h 2)

theorem coordinateDensity_active_endpoint_power {p η a b : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hη : 0 ≤ η) (ha : a ≠ 0) (hb : b ≠ 0)
    (z : Plane) {Q : Finset Triple}
    (h : coordinateDensity (p^(43*η)) (activeTripleClasses Q) (Q.image tripleVertexMap)) :
    coordinateDensity ((p/8)^(44*η))
      (activeTripleClasses (Q.image (endpointNormalization a b z)))
      ((Q.image (endpointNormalization a b z)).image tripleVertexMap) := by
  have hcoef : (p/8)^(44*η) ≤ p^(43*η) := by
    calc
      _ ≤ (p/8)^(43*η) := Real.rpow_le_rpow_of_exponent_ge (by positivity) (by linarith) (by linarith)
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  exact coordinateDensity_mono hcoef (coordinateDensity_active_endpointNormalization ha hb z h)

end Kakeya4.Hard.RestrictedTriple
