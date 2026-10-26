import Kakeya4.Hard.MultilinearKakeya.LineVariation
import Kakeya4.Construction.Combinatorics.CylinderVolume

/-! Orthogonal transport of the full-line polynomial budget to actual Euclidean tubes.
The existing Construction coordinate map is used without changing its implementation. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace Kakeya4.Hard.MultilinearKakeya

abbrev TransverseSpace {n : ℕ} (v : E n) := ((ℝ ∙ v)ᗮ : Submodule ℝ (E n))

def axialMeasurableEquiv {n : ℕ} (v : E n) (hv : ‖v‖ = 1) :
    E n ≃ᵐ ℝ × TransverseSpace v :=
  let K : Submodule ℝ (E n) := ℝ ∙ v
  let φ := LinearIsometryEquiv.toSpanUnitSingleton v hv
  let e := K.orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdCongr 2 φ.symm
      (LinearIsometryEquiv.refl ℝ (Kᗮ : Submodule ℝ (E n))))
  e.toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 _).symm

theorem axialMeasurableEquiv_apply {n : ℕ} (v : E n) (hv : ‖v‖ = 1) (x : E n) :
    axialMeasurableEquiv v hv x = Construction.axialCoordinates v hv x := rfl

theorem measurePreserving_axialMeasurableEquiv {n : ℕ} (v : E n) (hv : ‖v‖ = 1) :
    MeasurePreserving (axialMeasurableEquiv v hv) :=
  Construction.measurePreserving_axialCoordinates v hv

theorem axialMeasurableEquiv_symm_apply {n : ℕ} (v : E n) (hv : ‖v‖ = 1)
    (z : ℝ × TransverseSpace v) :
    (axialMeasurableEquiv v hv).symm z = z.1 • v + (z.2 : E n) := by
  change (ℝ ∙ v : Submodule ℝ (E n)).orthogonalDecomposition.symm
    (WithLp.toLp 2 ((LinearIsometryEquiv.toSpanUnitSingleton v hv) z.1, z.2)) = _
  change (LinearIsometryEquiv.toSpanUnitSingleton v hv z.1 : E n) + (z.2 : E n) = _
  rfl

theorem transverse_norm_le_infDist {n : ℕ} (L : Line n) (x : E n) :
    ‖(axialMeasurableEquiv L.direction L.norm_direction (x-L.anchor)).2‖ ≤
      Metric.infDist x L.carrier := by
  rw [axialMeasurableEquiv_apply, Construction.axialCoordinates_snd_norm]
  apply (Metric.le_infDist L.carrier_nonempty).mpr
  rintro y ⟨t, rfl⟩
  have h := Construction.lineFootPoint_perpNorm_le_dist L.direction (0 : E n)
    (x-L.anchor) (t • L.direction) L.norm_direction ⟨t, by simp⟩
  simp only [Construction.lineFootPoint, inner_zero_left, zero_smul, sub_zero] at h
  calc
    _ ≤ dist (x-L.anchor) (t • L.direction) := h
    _ = _ := by rw [dist_eq_norm, dist_eq_norm]; congr 1; module

set_option maxHeartbeats 800000 in
theorem tube_subset_transverse_ball {n : ℕ} (L : Line n) (r : ℝ) :
    L.tube r ⊆ {x : E n | (axialMeasurableEquiv L.direction L.norm_direction (x-L.anchor)).2 ∈
      Metric.closedBall (0 : TransverseSpace L.direction) r} := by
  intro x hx
  change ‖(axialMeasurableEquiv L.direction L.norm_direction (x-L.anchor)).2 - 0‖ ≤ r
  rw [sub_zero]
  exact (transverse_norm_le_infDist L x).trans hx

def tubeParameterization {n : ℕ} (L : Line n) :
    TransverseSpace L.direction × ℝ ≃ᵐ E n :=
  (MeasurableEquiv.prodComm.trans
    (axialMeasurableEquiv L.direction L.norm_direction).symm).trans
      (MeasurableEquiv.addLeft L.anchor)

theorem tubeParameterization_apply {n : ℕ} (L : Line n)
    (z : TransverseSpace L.direction × ℝ) :
    tubeParameterization L z = L.anchor + (z.1 : E n) + z.2 • L.direction := by
  change L.anchor + (axialMeasurableEquiv L.direction L.norm_direction).symm (z.2,z.1) = _
  rw [axialMeasurableEquiv_symm_apply]
  abel

theorem measurePreserving_tubeParameterization {n : ℕ} (L : Line n) :
    MeasurePreserving (tubeParameterization L)
      ((volume : Measure (TransverseSpace L.direction)).prod (volume : Measure ℝ)) volume := by
  have he := MeasurePreserving.symm (axialMeasurableEquiv L.direction L.norm_direction)
    (measurePreserving_axialMeasurableEquiv L.direction L.norm_direction)
  change MeasurePreserving (fun z : TransverseSpace L.direction × ℝ =>
    L.anchor + (axialMeasurableEquiv L.direction L.norm_direction).symm (z.2,z.1)) _ _
  rw [← Measure.volume_eq_prod]
  exact (measurePreserving_add_left (volume : Measure (E n)) L.anchor).comp
    (he.comp Measure.measurePreserving_swap)

set_option maxHeartbeats 800000 in
theorem tubeParameterization_preimage_tube_subset {n : ℕ} (L : Line n) (r : ℝ) :
    (tubeParameterization L) ⁻¹' L.tube r ⊆
      Metric.closedBall (0 : TransverseSpace L.direction) r ×ˢ (univ : Set ℝ) := by
  intro z hz
  refine ⟨?_, mem_univ _⟩
  have h := tube_subset_transverse_ball L r hz
  change (axialMeasurableEquiv L.direction L.norm_direction
    (tubeParameterization L z - L.anchor)).2 ∈
      Metric.closedBall (0 : TransverseSpace L.direction) r at h
  have heq : tubeParameterization L z - L.anchor =
      (axialMeasurableEquiv L.direction L.norm_direction).symm (z.2,z.1) := by
    change L.anchor + _ - L.anchor = _
    abel
  rw [heq, MeasurableEquiv.apply_symm_apply] at h
  exact h

theorem lintegral_tube_le_of_line_budget {n : ℕ} (L : Line n) (r : ℝ)
    (F : E n → ℝ≥0∞) (C : ℝ≥0∞)
    (hline : ∀ a : E n, ∫⁻ t : ℝ, F (a + t • L.direction) ≤ C) :
    ∫⁻ x in L.tube r, F x ≤
      volume (Metric.closedBall (0 : TransverseSpace L.direction) r) * C := by
  rw [← (measurePreserving_tubeParameterization L).setLIntegral_comp_preimage_emb
    (tubeParameterization L).measurableEmbedding F (L.tube r)]
  apply (lintegral_mono_set (tubeParameterization_preimage_tube_subset L r)).trans
  rw [← Measure.restrict_prod_eq_prod_univ]
  apply (lintegral_prod_le _).trans
  simp_rw [tubeParameterization_apply]
  calc
    _ ≤ ∫⁻ _y : TransverseSpace L.direction in Metric.closedBall 0 r, C :=
      lintegral_mono (fun y => hline (L.anchor + (y : E n)))
    _ = _ := by simp [lintegral_const, mul_comm]

theorem lintegral_smoothPolynomial_tube_le_crossSection {n : ℕ} (L : Line n)
    (P : MvPolynomial (Fin n) ℝ) {ε : ℝ} (hε : ε ≠ 0) (r : ℝ) :
    ∫⁻ x in L.tube r, ENNReal.ofReal ‖fderiv ℝ (smoothPolynomial P ε) x L.direction‖ ≤
      volume (Metric.closedBall (0 : TransverseSpace L.direction) r) *
        ENNReal.ofReal (P.totalDegree * Real.pi) :=
  lintegral_tube_le_of_line_budget L r _ _
    (fun a => lintegral_smoothPolynomial_line_le_degree P hε a L.direction)

theorem finrank_transverseSpace {n : ℕ} (L : Line n) :
    Module.finrank ℝ (TransverseSpace L.direction) = n-1 := by
  have hne : L.direction ≠ 0 := by
    intro hz
    simpa [hz] using L.norm_direction
  have hsum := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ L.direction : Submodule ℝ (E n))
  have hspan : Module.finrank ℝ (ℝ ∙ L.direction : Submodule ℝ (E n)) = 1 :=
    finrank_span_singleton hne
  rw [hspan] at hsum
  simp only [E, finrank_euclideanSpace, Fintype.card_fin] at hsum
  change 1 + Module.finrank ℝ (TransverseSpace L.direction) = n at hsum
  omega

def transverseUnitVolume (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt Real.pi ^ (n-1) /
    Real.Gamma (((n-1 : ℕ) : ℝ)/2 + 1))

theorem transverseUnitVolume_pos (n : ℕ) : 0 < transverseUnitVolume n := by
  apply ENNReal.ofReal_pos.mpr
  exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _)
    (Real.Gamma_pos_of_pos (by positivity))

theorem transverseUnitVolume_ne_top (n : ℕ) : transverseUnitVolume n ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem volume_transverse_closedBall {n : ℕ} (hn : 2 ≤ n) (L : Line n) (r : ℝ) :
    volume (Metric.closedBall (0 : TransverseSpace L.direction) r) =
      ENNReal.ofReal r ^ (n-1) * transverseUnitVolume n := by
  let : Nontrivial (TransverseSpace L.direction) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_transverseSpace]; omega)
  rw [InnerProductSpace.volume_closedBall, finrank_transverseSpace]
  rfl

theorem lintegral_smoothPolynomial_tube_le_degree {n : ℕ} (hn : 2 ≤ n) (L : Line n)
    (P : MvPolynomial (Fin n) ℝ) {ε : ℝ} (hε : ε ≠ 0) (r : ℝ) :
    ∫⁻ x in L.tube r, ENNReal.ofReal ‖fderiv ℝ (smoothPolynomial P ε) x L.direction‖ ≤
      ENNReal.ofReal r ^ (n-1) * transverseUnitVolume n *
        ENNReal.ofReal (P.totalDegree * Real.pi) := by
  have h := lintegral_smoothPolynomial_tube_le_crossSection L P hε r
  rwa [volume_transverse_closedBall hn] at h

theorem integrableOn_smoothPolynomial_tube {n : ℕ} (hn : 2 ≤ n) (L : Line n)
    (P : MvPolynomial (Fin n) ℝ) {ε : ℝ} (hε : ε ≠ 0) (r : ℝ) :
    IntegrableOn (fun x => fderiv ℝ (smoothPolynomial P ε) x L.direction) (L.tube r) := by
  refine ⟨((continuous_fderiv_smoothPolynomial P ε).clm_apply
    continuous_const).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  apply (lintegral_smoothPolynomial_tube_le_degree hn L P hε r).trans_lt
  apply ENNReal.mul_lt_top
  · exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
      (lt_top_iff_ne_top.mpr (transverseUnitVolume_ne_top n))
  · exact ENNReal.ofReal_lt_top

theorem lintegral_smoothPolynomial_unitTube_le_degree {n : ℕ} (hn : 2 ≤ n) (L : Line n)
    (P : MvPolynomial (Fin n) ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    ∫⁻ x in L.tube 1, ENNReal.ofReal ‖fderiv ℝ (smoothPolynomial P ε) x L.direction‖ ≤
      transverseUnitVolume n * ENNReal.ofReal (P.totalDegree * Real.pi) := by
  simpa only [ENNReal.ofReal_one, one_pow, one_mul] using
    lintegral_smoothPolynomial_tube_le_degree hn L P hε 1

end Kakeya4.Hard.MultilinearKakeya
