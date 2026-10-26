import Kakeya4.Hard.MultilinearKakeya.Basic

/-! Exact homotheties of full-line families, with unchanged unit directions and weights. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal Pointwise

namespace Kakeya4.Hard.MultilinearKakeya

def Line.dilate {n : ℕ} (L : Line n) (c : ℝ) : Line n where
  anchor := c • L.anchor
  direction := L.direction
  norm_direction := L.norm_direction

theorem Line.carrier_dilate {n : ℕ} (L : Line n) (c : ℝ) (hc : c ≠ 0) :
    (L.dilate c).carrier = c • L.carrier := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨L.anchor + (c⁻¹*t) • L.direction, ⟨c⁻¹*t,rfl⟩, ?_⟩
    simp [Line.dilate, smul_add, smul_smul, hc]
  · rintro ⟨y,⟨t,rfl⟩,rfl⟩
    refine ⟨c*t, ?_⟩
    simp [Line.dilate, smul_add, smul_smul]

theorem Line.infDist_carrier_dilate {n : ℕ} (L : Line n) (c : ℝ) (hc : 0 < c)
    (x : E n) : Metric.infDist (c • x) (L.dilate c).carrier =
      c * Metric.infDist x L.carrier := by
  rw [L.carrier_dilate c hc.ne', infDist_smul₀ hc.ne']
  simp [Real.norm_eq_abs, abs_of_pos hc]

theorem Line.mem_tube_dilate {n : ℕ} (L : Line n) (c : ℝ) (hc : 0 < c)
    (r : ℝ) (x : E n) : c • x ∈ (L.dilate c).tube (c*r) ↔ x ∈ L.tube r := by
  change Metric.infDist (c • x) (L.dilate c).carrier ≤ c*r ↔
    Metric.infDist x L.carrier ≤ r
  rw [L.infDist_carrier_dilate c hc]
  exact mul_le_mul_iff_right₀ hc

theorem mem_tupleRegion_dilate {n : ℕ} (L : Fin n → Line n) (c : ℝ) (hc : 0 < c)
    (r : ℝ) (x : E n) :
    c • x ∈ tupleRegion (fun i => (L i).dilate c) (c*r) ↔ x ∈ tupleRegion L r :=
  forall_congr' (fun i => (L i).mem_tube_dilate c hc r x)

theorem kernel_dilate {n : ℕ} {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (c : ℝ) (hc : 0 < c)
    (r : ℝ) (x : E n) :
    kernel (fun i a => (L i a).dilate c) w (c*r) (c • x) = kernel L w r x := by
  unfold kernel
  apply Finset.sum_congr rfl
  intro a _
  have hm := mem_tupleRegion_dilate (fun i => L i (a i)) c hc r x
  simp only [Set.indicator]
  by_cases hx : x ∈ tupleRegion (fun i => L i (a i)) r
  · simp only [hx, hm.mpr hx, if_pos]
    rfl
  · have hnot := mt hm.mp hx
    simp only [hx, hnot, if_false]

/-- The pushforward of Euclidean volume under inverse dilation, with the exact
dimension exponent and no omitted normalization factor. -/
theorem map_inverse_dilation_volume (n : ℕ) (c : ℝ) (hc : 0 < c) :
    Measure.map (fun x : E n => c⁻¹ • x) volume =
      ENNReal.ofReal (c^n) • volume := by
  rw [Measure.map_addHaar_smul volume (inv_ne_zero hc.ne')]
  simp [E, finrank_euclideanSpace, inv_pow, abs_of_nonneg (pow_nonneg hc.le _)]

theorem lintegral_inverse_dilation (n : ℕ) (c : ℝ) (hc : 0 < c)
    (f : E n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f (c⁻¹ • x) ∂volume) = ENNReal.ofReal (c^n) * ∫⁻ x, f x ∂volume := by
  have hg : Measurable (fun x : E n => c⁻¹ • x) := by fun_prop
  rw [← lintegral_map (g := fun x : E n => c⁻¹ • x) hf hg,
    map_inverse_dilation_volume n c hc, lintegral_smul_measure]
  rfl

/-- Radius-r geometry equals radius-one geometry of the inverse-dilated family,
and its endpoint integral acquires precisely the factor r^n. -/
theorem endpointIntegral_radius_reduction {n : ℕ} {ι : Fin n → Type*}
    [∀ i, Fintype (ι i)] (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0)
    (r : ℝ) (hr : 0 < r) :
    (∫⁻ x, (kernel L w r x)^endpointExponent n ∂volume) =
      ENNReal.ofReal (r^n) * ∫⁻ x,
        (kernel (fun i a => (L i a).dilate r⁻¹) w 1 x)^endpointExponent n ∂volume := by
  have heq (x : E n) : kernel (fun i a => (L i a).dilate r⁻¹) w 1 (r⁻¹ • x) =
      kernel L w r x := by
    simpa only [inv_mul_cancel₀ hr.ne'] using kernel_dilate L w r⁻¹ (inv_pos.mpr hr) r x
  simp_rw [← heq]
  exact lintegral_inverse_dilation n r hr _ (measurable_endpointKernel _ w 1 _)

/-- The remaining unit-radius endpoint; this is a genuine proposition, not an axiom. -/
def UnitRadiusBound (n : ℕ) : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧ ∀ (ι : Fin n → Type) [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0),
    (∫⁻ x, (kernel L w 1 x)^endpointExponent n ∂volume) ≤
      (C : ℝ≥0∞) * ∏ i, (∑ a, (w i a : ℝ≥0∞))^endpointExponent n

/-- All-radii and unit-radius statements are equivalent without changing the
uniform constant or imposing any geometric restriction on the line families. -/
theorem endpointBound_iff_unitRadiusBound (n : ℕ) :
    EndpointBound n ↔ UnitRadiusBound n := by
  constructor
  · rintro ⟨C,hC,h⟩
    refine ⟨C,hC,fun ι _ L w => ?_⟩
    simpa only [one_pow, ENNReal.ofReal_one, mul_one] using h ι L w 1 zero_lt_one
  · rintro ⟨C,hC,h⟩
    refine ⟨C,hC,fun ι _ L w r hr => ?_⟩
    rw [endpointIntegral_radius_reduction L w r hr]
    calc
      _ ≤ ENNReal.ofReal (r^n) *
          ((C : ℝ≥0∞) * ∏ i, (∑ a, (w i a : ℝ≥0∞))^endpointExponent n) :=
        mul_le_mul_right (h ι (fun i a => (L i a).dilate r⁻¹) w) _
      _ = _ := by ac_rfl

end Kakeya4.Hard.MultilinearKakeya
