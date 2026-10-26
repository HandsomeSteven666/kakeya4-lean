import Kakeya4.Hard.MultilinearKakeya.BisectionEnergy

/-! A common smoothing parameter for finitely many invertible affine reference
charts, followed by a dimensional Poincare lower bound for the actual polynomial.
The exact inverse determinant transports reference integrals to spatial volume;
its positive factor cancels on both sides of the Poincare inequality. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology

namespace Kakeya4.Hard.MultilinearKakeya

def nativeSmoothPolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε : ℝ)
    (x : Fin n → ℝ) : ℝ := Real.arctan (MvPolynomial.eval x P / ε)

theorem contDiff_nativeSmoothPolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (nativeSmoothPolynomial P ε) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => MvPolynomial.eval x P) :=
    (AnalyticOnNhd.eval_continuousLinearMap
    (ContinuousLinearMap.id ℝ (Fin n → ℝ)) P).contDiff
  exact (hp.div_const ε).arctan

def referenceAffineChart {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) (x : Fin n → ℝ) : Fin n → ℝ := c + T x

theorem continuous_referenceAffineChart {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : Continuous (referenceAffineChart c T) :=
  continuous_const.add T.continuous

def referenceAffineMeasure {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : Measure (Fin n → ℝ) :=
  (volume.restrict (referenceDomain n)).map (referenceAffineChart c T)

theorem referenceAffineMeasure_finite {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : IsFiniteMeasure (referenceAffineMeasure c T) := by
  let := (referenceDomain_regular n).isFiniteMeasure_restrict_volume
  unfold referenceAffineMeasure
  exact inferInstance

theorem referenceAffineMeasure_absolutelyContinuous {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : referenceAffineMeasure c T ≪ volume := by
  have hT := Measure.ContinuousLinearMap.quasiMeasurePreserving volume T.toContinuousLinearMap
    (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero
  have hc := (measurePreserving_add_left volume c).quasiMeasurePreserving.comp hT
  exact (hc.mono_left Measure.absolutelyContinuous_restrict).absolutelyContinuous

theorem referenceAffineMeasure_univ {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
    referenceAffineMeasure c T univ = volume (referenceDomain n) := by
  rw [referenceAffineMeasure, Measure.map_apply (continuous_referenceAffineChart c T).measurable
    MeasurableSet.univ]
  simp

theorem contDiff_nativeSmoothPolynomial_affine {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (ε : ℝ) (c : Fin n → ℝ) (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => nativeSmoothPolynomial P ε (referenceAffineChart c T x)) := by
  apply (contDiff_nativeSmoothPolynomial P ε).comp
  exact contDiff_const.add T.contDiff

theorem fderiv_nativeSmoothPolynomial_affine {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (ε : ℝ) (c : Fin n → ℝ) (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (x v : Fin n → ℝ) :
    fderiv ℝ (fun y => nativeSmoothPolynomial P ε (referenceAffineChart c T y)) x v =
      fderiv ℝ (nativeSmoothPolynomial P ε) (referenceAffineChart c T x) (T v) := by
  have hT : HasFDerivAt (referenceAffineChart c T) T.toContinuousLinearMap x :=
    (T.toContinuousLinearMap.hasFDerivAt).const_add c
  have hp := (contDiff_nativeSmoothPolynomial P ε).differentiable (by simp)
  exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L v)
    (((hp _).hasFDerivAt.comp x hT).fderiv)

theorem affine_bisection_energy_lower {n : ℕ} [NeZero n]
    (P : MvPolynomial (Fin n) ℝ) {ε : ℝ} (hε : 0 < ε)
    (c : Fin n → ℝ) (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hneg : referenceAffineMeasure c T {x | MvPolynomial.eval x P ≤ 0} =
      referenceAffineMeasure c T univ / 2)
    (hpos : referenceAffineMeasure c T {x | 0 ≤ MvPolynomial.eval x P} =
      referenceAffineMeasure c T univ / 2)
    (hsmall : referenceAffineMeasure c T {x | |MvPolynomial.eval x P| ≤ ε} ≤ ENNReal.ofReal δ) :
    (Real.pi/4) * ((volume (referenceDomain n)).toReal/2-δ) ≤
      referencePoincareConstant n * ∑ i, ∫ x in referenceDomain n,
        ‖fderiv ℝ (nativeSmoothPolynomial P ε) (referenceAffineChart c T x) (T (Pi.single i 1))‖ := by
  let μ := referenceAffineMeasure c T
  let := referenceAffineMeasure_finite c T
  let u := fun x => nativeSmoothPolynomial P ε (referenceAffineChart c T x)
  let m := CKN.integralAverage (referenceDomain n) u
  have hlow := smoothed_bisection_oscillation_lower μ (fun x => MvPolynomial.eval x P)
    (MvPolynomial.continuous_eval _).measurable hε hδ hneg hpos hsmall m
  rw [referenceAffineMeasure_univ] at hlow
  have hmap : (∫ x, ‖nativeSmoothPolynomial P ε x - m‖ ∂μ) =
      ∫ x in referenceDomain n, ‖u x-m‖ := by
    apply integral_map (continuous_referenceAffineChart c T).measurable.aemeasurable
      (((contDiff_nativeSmoothPolynomial P ε).continuous.sub continuous_const).norm.aestronglyMeasurable)
  change (Real.pi/4) * ((volume (referenceDomain n)).toReal/2-δ) ≤
    ∫ x, ‖nativeSmoothPolynomial P ε x-m‖ ∂μ at hlow
  rw [hmap] at hlow
  have hupper := reference_poincare_directions u
    ((contDiff_nativeSmoothPolynomial_affine P ε c T).of_le (by norm_num))
  have hfinal := hlow.trans hupper
  simpa only [u, fderiv_nativeSmoothPolynomial_affine] using hfinal

theorem exists_common_affine_bisection_energy_lower {n k : ℕ} [NeZero n]
    {ι : Type*} [Fintype ι]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (c : ι → Fin n → ℝ) (T : ι → (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    {S : Set (E k)} (hS : IsCompact S) (hzero : ∀ u ∈ S, u ≠ 0)
    (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ∀ u ∈ S,
      (referenceAffineMeasure (c i) (T i) {x | MvPolynomial.eval x (coefficientPolynomial B u) ≤ 0} =
        referenceAffineMeasure (c i) (T i) univ / 2) →
      (referenceAffineMeasure (c i) (T i) {x | 0 ≤ MvPolynomial.eval x (coefficientPolynomial B u)} =
        referenceAffineMeasure (c i) (T i) univ / 2) →
      (Real.pi/4) * ((volume (referenceDomain n)).toReal/2-δ i) ≤
        referencePoincareConstant n * ∑ j, ∫ x in referenceDomain n,
          ‖fderiv ℝ (nativeSmoothPolynomial (coefficientPolynomial B u) ε)
            (referenceAffineChart (c i) (T i) x) (T i (Pi.single j 1))‖ := by
  obtain ⟨ε, hε, hsmall⟩ := exists_common_smoothingScale_small_values B hB
    (fun i => referenceAffineMeasure (c i) (T i))
    (fun i => referenceAffineMeasure_finite (c i) (T i))
    (fun i => referenceAffineMeasure_absolutelyContinuous (c i) (T i)) hS hzero δ hδ
  refine ⟨ε, hε, fun i u hu hneg hpos => ?_⟩
  exact affine_bisection_energy_lower _ hε _ _ (hδ i).le hneg hpos (hsmall i u hu)

def referenceAffineEquiv {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  T.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.addLeft c)

def referenceAffineRegion {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  referenceAffineChart c T '' referenceDomain n

def inverseAffineJacobian {n : ℕ} (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : ℝ :=
  |(LinearMap.det T.toLinearEquiv.toLinearMap)⁻¹|

theorem inverseAffineJacobian_pos {n : ℕ}
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : 0 < inverseAffineJacobian T := by
  exact abs_pos.mpr (inv_ne_zero (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero)

theorem map_referenceAffineChart_volume {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
    volume.map (referenceAffineChart c T) = ENNReal.ofReal (inverseAffineJacobian T) • volume := by
  have hm : volume.map T = ENNReal.ofReal (inverseAffineJacobian T) • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero
  change Measure.map ((fun x => c+x) ∘ T) volume = _
  have hadd : Measurable (fun x : Fin n → ℝ => c+x) :=
    (continuous_const.add continuous_id).measurable
  rw [← Measure.map_map hadd T.continuous.measurable, hm,
    Measure.map_smul _ hadd.aemeasurable, map_add_left_eq_self]

theorem referenceAffineMeasure_eq_scaled_volume {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
    referenceAffineMeasure c T = ENNReal.ofReal (inverseAffineJacobian T) •
      volume.restrict (referenceAffineRegion c T) := by
  have h := (referenceAffineEquiv c T).restrict_map volume
    ((referenceAffineEquiv c T) '' referenceDomain n)
  rw [Set.preimage_image_eq _ (referenceAffineEquiv c T).injective] at h
  change (volume.map (referenceAffineChart c T)).restrict (referenceAffineRegion c T) =
    referenceAffineMeasure c T at h
  rw [map_referenceAffineChart_volume, Measure.restrict_smul] at h
  exact h.symm

theorem integral_referenceAffineChart {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    (∫ x in referenceDomain n, f (referenceAffineChart c T x)) =
      inverseAffineJacobian T * ∫ y in referenceAffineRegion c T, f y := by
  have h := (referenceAffineEquiv c T).measurableEmbedding.integral_map
    (μ := volume.restrict (referenceDomain n)) f
  change (∫ y, f y ∂referenceAffineMeasure c T) =
    ∫ x in referenceDomain n, f (referenceAffineChart c T x) at h
  rw [referenceAffineMeasure_eq_scaled_volume, integral_smul_measure,
    ENNReal.toReal_ofReal (inverseAffineJacobian_pos T).le, smul_eq_mul] at h
  exact h.symm

theorem referenceAffineRegion_volume_lt_top {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : volume (referenceAffineRegion c T) < ⊤ := by
  have hc := (referenceDomain_regular n).isBoundedDomain.isBounded.isCompact_closure
  exact (measure_mono (Set.image_mono subset_closure)).trans_lt
    ((hc.image (continuous_referenceAffineChart c T)).measure_lt_top)

theorem affine_poincare_directions {n : ℕ} [NeZero n] (u : (Fin n → ℝ) → ℝ)
    (hu : ContDiff ℝ 1 u) (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
    ∫ y in referenceAffineRegion c T,
        ‖u y - CKN.integralAverage (referenceDomain n) (fun x => u (referenceAffineChart c T x))‖ ≤
      referencePoincareConstant n * ∑ i, ∫ y in referenceAffineRegion c T,
        ‖fderiv ℝ u y (T (Pi.single i 1))‖ := by
  let v := fun x => u (referenceAffineChart c T x)
  have hv : ContDiff ℝ 1 v := hu.comp (contDiff_const.add T.contDiff)
  have hd (x w : Fin n → ℝ) :
      fderiv ℝ v x w = fderiv ℝ u (referenceAffineChart c T x) (T w) := by
    have hT : HasFDerivAt (referenceAffineChart c T) T.toContinuousLinearMap x :=
      (T.toContinuousLinearMap.hasFDerivAt).const_add c
    exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L w)
      ((((hu.differentiable (by norm_num)) _).hasFDerivAt.comp x hT).fderiv)
  have h := reference_poincare_directions v hv
  simp_rw [hd] at h
  change (∫ x in referenceDomain n,
    ‖u (referenceAffineChart c T x)-CKN.integralAverage (referenceDomain n) v‖) ≤ _ at h
  rw [integral_referenceAffineChart c T
    (fun y => ‖u y-CKN.integralAverage (referenceDomain n) v‖)] at h
  have haxis (i : Fin n) :=
    integral_referenceAffineChart c T (fun y => ‖fderiv ℝ u y (T (Pi.single i 1))‖)
  simp_rw [haxis] at h
  rw [← Finset.mul_sum] at h
  apply (mul_le_mul_iff_left₀ (inverseAffineJacobian_pos T)).mp
  convert h using 1 <;> ring

theorem affine_spatial_bisection_energy_lower {n : ℕ} [NeZero n]
    (P : MvPolynomial (Fin n) ℝ) {ε : ℝ} (hε : 0 < ε)
    (c : Fin n → ℝ) (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hneg : (volume.restrict (referenceAffineRegion c T)) {x | MvPolynomial.eval x P ≤ 0} =
      volume (referenceAffineRegion c T) / 2)
    (hpos : (volume.restrict (referenceAffineRegion c T)) {x | 0 ≤ MvPolynomial.eval x P} =
      volume (referenceAffineRegion c T) / 2)
    (hsmall : (volume.restrict (referenceAffineRegion c T)) {x | |MvPolynomial.eval x P| ≤ ε} ≤
      ENNReal.ofReal δ) :
    (Real.pi/4) * ((volume (referenceAffineRegion c T)).toReal/2-δ) ≤
      referencePoincareConstant n * ∑ i, ∫ y in referenceAffineRegion c T,
        ‖fderiv ℝ (nativeSmoothPolynomial P ε) y (T (Pi.single i 1))‖ := by
  let μ := volume.restrict (referenceAffineRegion c T)
  let := isFiniteMeasure_restrict.mpr (referenceAffineRegion_volume_lt_top c T).ne
  let m := CKN.integralAverage (referenceDomain n)
    (fun x => nativeSmoothPolynomial P ε (referenceAffineChart c T x))
  have hn : μ {x | MvPolynomial.eval x P ≤ 0} = μ univ / 2 := by simpa [μ] using hneg
  have hp : μ {x | 0 ≤ MvPolynomial.eval x P} = μ univ / 2 := by simpa [μ] using hpos
  have hlow := smoothed_bisection_oscillation_lower μ (fun x => MvPolynomial.eval x P)
    (MvPolynomial.continuous_eval _).measurable hε hδ hn hp hsmall m
  have hupper := affine_poincare_directions (nativeSmoothPolynomial P ε)
    ((contDiff_nativeSmoothPolynomial P ε).of_le (by norm_num)) c T
  apply le_trans _ hupper
  simpa only [μ, m, Measure.restrict_apply_univ, nativeSmoothPolynomial] using hlow

theorem referenceAffineRegion_volume_pos {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
    0 < (volume (referenceAffineRegion c T)).toReal := by
  apply ENNReal.toReal_pos _ (referenceAffineRegion_volume_lt_top c T).ne
  intro hz
  have hzero : referenceAffineMeasure c T univ = 0 := by
    rw [referenceAffineMeasure_eq_scaled_volume, Measure.smul_apply,
      Measure.restrict_apply_univ, hz, smul_eq_mul, mul_zero]
  rw [referenceAffineMeasure_univ] at hzero
  have hpos := referenceDomain_volume_pos n
  rw [hzero, ENNReal.toReal_zero] at hpos
  exact lt_irrefl 0 hpos

theorem exists_common_affine_spatial_bisection_energy_lower {n k : ℕ} [NeZero n]
    {ι : Type*} [Fintype ι]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (c : ι → Fin n → ℝ) (T : ι → (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    {S : Set (E k)} (hS : IsCompact S) (hzero : ∀ u ∈ S, u ≠ 0)
    (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ∀ u ∈ S,
      ((volume.restrict (referenceAffineRegion (c i) (T i)))
        {x | MvPolynomial.eval x (coefficientPolynomial B u) ≤ 0} =
        volume (referenceAffineRegion (c i) (T i)) / 2) →
      ((volume.restrict (referenceAffineRegion (c i) (T i)))
        {x | 0 ≤ MvPolynomial.eval x (coefficientPolynomial B u)} =
        volume (referenceAffineRegion (c i) (T i)) / 2) →
      (Real.pi/4) * ((volume (referenceAffineRegion (c i) (T i))).toReal/2-δ i) ≤
        referencePoincareConstant n * ∑ j, ∫ y in referenceAffineRegion (c i) (T i),
          ‖fderiv ℝ (nativeSmoothPolynomial (coefficientPolynomial B u) ε) y (T i (Pi.single j 1))‖ := by
  let μ := fun i => volume.restrict (referenceAffineRegion (c i) (T i))
  have hfin (i : ι) : IsFiniteMeasure (μ i) :=
    isFiniteMeasure_restrict.mpr (referenceAffineRegion_volume_lt_top (c i) (T i)).ne
  obtain ⟨ε, hε, hsmall⟩ := exists_common_smoothingScale_small_values B hB μ hfin
    (fun _ => Measure.absolutelyContinuous_restrict) hS hzero δ hδ
  refine ⟨ε, hε, fun i u hu hneg hpos => ?_⟩
  exact affine_spatial_bisection_energy_lower _ hε _ _ (hδ i).le hneg hpos (hsmall i u hu)

theorem exists_common_affine_spatial_bisection_energy_fraction {n k : ℕ} [NeZero n]
    {ι : Type*} [Fintype ι]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (c : ι → Fin n → ℝ) (T : ι → (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    {S : Set (E k)} (hS : IsCompact S) (hzero : ∀ u ∈ S, u ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ∀ u ∈ S,
      ((volume.restrict (referenceAffineRegion (c i) (T i)))
        {x | MvPolynomial.eval x (coefficientPolynomial B u) ≤ 0} =
        volume (referenceAffineRegion (c i) (T i)) / 2) →
      ((volume.restrict (referenceAffineRegion (c i) (T i)))
        {x | 0 ≤ MvPolynomial.eval x (coefficientPolynomial B u)} =
        volume (referenceAffineRegion (c i) (T i)) / 2) →
      (Real.pi/10) * (volume (referenceAffineRegion (c i) (T i))).toReal ≤
        referencePoincareConstant n * ∑ j, ∫ y in referenceAffineRegion (c i) (T i),
          ‖fderiv ℝ (nativeSmoothPolynomial (coefficientPolynomial B u) ε) y (T i (Pi.single j 1))‖ := by
  obtain ⟨ε, hε, h⟩ := exists_common_affine_spatial_bisection_energy_lower B hB c T hS hzero
    (fun i => (volume (referenceAffineRegion (c i) (T i))).toReal/10)
    (fun i => div_pos (referenceAffineRegion_volume_pos (c i) (T i)) (by norm_num))
  refine ⟨ε, hε, fun i u hu hneg hpos => ?_⟩
  convert h i u hu hneg hpos using 1; ring

end Kakeya4.Hard.MultilinearKakeya
