import Kakeya4.Hard.MultilinearKakeya.AffineBisectionEnergy

/-! Measure-preserving transport of affine bisection energy to the actual
Euclidean directional energy, and summation over disjoint spatial tests. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace Kakeya4.Hard.MultilinearKakeya

theorem measurableSet_referenceAffineRegion {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : MeasurableSet (referenceAffineRegion c T) := by
  exact (referenceAffineEquiv c T).measurableEmbedding.measurableSet_image.mpr
    (referenceDomain_regular n).measurableSet

def euclideanAffineRegion {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : Set (E n) :=
  WithLp.ofLp ⁻¹' referenceAffineRegion c T

theorem measurableSet_euclideanAffineRegion {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) : MeasurableSet (euclideanAffineRegion c T) :=
  (PiLp.volume_preserving_ofLp (Fin n)).measurable (measurableSet_referenceAffineRegion c T)

theorem volume_euclideanAffineRegion {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
    volume (euclideanAffineRegion c T) = volume (referenceAffineRegion c T) :=
  (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (measurableSet_referenceAffineRegion c T).nullMeasurableSet

theorem euclideanAffineRegion_restrict_preimage {n : ℕ} (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    (volume.restrict (euclideanAffineRegion c T)) (WithLp.ofLp ⁻¹' A) =
      (volume.restrict (referenceAffineRegion c T)) A :=
  ((PiLp.volume_preserving_ofLp (Fin n)).restrict_preimage
    (measurableSet_referenceAffineRegion c T)).measure_preimage hA.nullMeasurableSet

theorem fderiv_nativeSmoothPolynomial_eq_euclidean {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (ε : ℝ) (x v : Fin n → ℝ) :
    fderiv ℝ (nativeSmoothPolynomial P ε) x v =
      fderiv ℝ (smoothPolynomial P ε) (WithLp.toLp 2 x) (WithLp.toLp 2 v) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  have hp := (contDiff_smoothPolynomial P ε).differentiable (by simp)
  exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L v)
    (((hp (e x)).hasFDerivAt.comp x e.toContinuousLinearMap.hasFDerivAt).fderiv)

theorem native_direction_integral_eq_euclidean {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (ε : ℝ) (c : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) (v : Fin n → ℝ) :
    (∫ x in referenceAffineRegion c T, ‖fderiv ℝ (nativeSmoothPolynomial P ε) x v‖) =
      directionalEnergy P ε (euclideanAffineRegion c T) (WithLp.toLp 2 v) := by
  have hm : MeasurePreserving (fun x : E n => (WithLp.ofLp x : Fin n → ℝ)) volume volume :=
    PiLp.volume_preserving_ofLp (Fin n)
  have h := (hm.restrict_preimage
    (measurableSet_referenceAffineRegion c T)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding
      (fun x => ‖fderiv ℝ (nativeSmoothPolynomial P ε) x v‖)
  symm
  simpa only [fderiv_nativeSmoothPolynomial_eq_euclidean, WithLp.toLp_ofLp,
    directionalEnergy, euclideanAffineRegion] using h

theorem exists_common_euclidean_bisection_energy_fraction {n k : ℕ} [NeZero n]
    {ι : Type*} [Fintype ι]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (c : ι → Fin n → ℝ) (T : ι → (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    {S : Set (E k)} (hS : IsCompact S) (hzero : ∀ u ∈ S, u ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ∀ u ∈ S,
      ((volume.restrict (euclideanAffineRegion (c i) (T i)))
        {x | MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B u) ≤ 0} =
        volume (euclideanAffineRegion (c i) (T i)) / 2) →
      ((volume.restrict (euclideanAffineRegion (c i) (T i)))
        {x | 0 ≤ MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B u)} =
        volume (euclideanAffineRegion (c i) (T i)) / 2) →
      (Real.pi/10) * (volume (euclideanAffineRegion (c i) (T i))).toReal ≤
        referencePoincareConstant n * ∑ j, directionalEnergy (coefficientPolynomial B u) ε
          (euclideanAffineRegion (c i) (T i)) (WithLp.toLp 2 (T i (Pi.single j 1))) := by
  obtain ⟨ε, hε, h⟩ := exists_common_affine_spatial_bisection_energy_fraction B hB c T hS hzero
  refine ⟨ε, hε, fun i u hu hneg hpos => ?_⟩
  have hn := euclideanAffineRegion_restrict_preimage (c i) (T i)
    (A := {x | MvPolynomial.eval x (coefficientPolynomial B u) ≤ 0})
    ((isClosed_le (MvPolynomial.continuous_eval _) continuous_const).measurableSet)
  have hp := euclideanAffineRegion_restrict_preimage (c i) (T i)
    (A := {x | 0 ≤ MvPolynomial.eval x (coefficientPolynomial B u)})
    ((isClosed_le continuous_const (MvPolynomial.continuous_eval _)).measurableSet)
  change (volume.restrict (euclideanAffineRegion (c i) (T i)))
    (WithLp.ofLp ⁻¹' {x | MvPolynomial.eval x (coefficientPolynomial B u) ≤ 0}) = _ at hneg
  change (volume.restrict (euclideanAffineRegion (c i) (T i)))
    (WithLp.ofLp ⁻¹' {x | 0 ≤ MvPolynomial.eval x (coefficientPolynomial B u)}) = _ at hpos
  rw [hn, volume_euclideanAffineRegion] at hneg
  rw [hp, volume_euclideanAffineRegion] at hpos
  have he := h i u hu hneg hpos
  rw [volume_euclideanAffineRegion]
  simpa only [native_direction_integral_eq_euclidean] using he

theorem sum_directionalEnergy_disjoint_le {n : ℕ} {ι : Type*} [Fintype ι]
    (P : MvPolynomial (Fin n) ℝ) (ε : ℝ) {Q : Set (E n)} (hQ : IsCompact Q)
    (A : ι → Set (E n)) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (hsub : ∀ i, A i ⊆ Q)
    (v : E n) : ∑ i, directionalEnergy P ε (A i) v ≤ directionalEnergy P ε Q v := by
  have hi := integrableOn_smoothPolynomial_direction P ε hQ v
  simp only [directionalEnergy]
  rw [← integral_iUnion_fintype hA hd (fun i => hi.mono_set (hsub i))]
  apply setIntegral_mono_set hi (Eventually.of_forall (fun _ => norm_nonneg _))
  exact Eventually.of_forall (iUnion_subset hsub)

theorem exists_common_disjoint_bisection_energy_budget {n k : ℕ} [NeZero n]
    {ι : Type*} [Fintype ι]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (c : ι → Fin n → ℝ) (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    {S : Set (E k)} (hS : IsCompact S) (hzero : ∀ u ∈ S, u ≠ 0)
    {Q : Set (E n)} (hQ : IsCompact Q)
    (hd : Pairwise (fun i j => Disjoint (euclideanAffineRegion (c i) T) (euclideanAffineRegion (c j) T)))
    (hsub : ∀ i, euclideanAffineRegion (c i) T ⊆ Q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u ∈ S,
      (∀ i, (volume.restrict (euclideanAffineRegion (c i) T))
        {x | MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B u) ≤ 0} =
        volume (euclideanAffineRegion (c i) T) / 2) →
      (∀ i, (volume.restrict (euclideanAffineRegion (c i) T))
        {x | 0 ≤ MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B u)} =
        volume (euclideanAffineRegion (c i) T) / 2) →
      (Real.pi/10) * (∑ i, (volume (euclideanAffineRegion (c i) T)).toReal) ≤
        referencePoincareConstant n * ∑ j, directionalEnergy (coefficientPolynomial B u) ε Q
          (WithLp.toLp 2 (T (Pi.single j 1))) := by
  obtain ⟨ε, hε, h⟩ := exists_common_euclidean_bisection_energy_fraction B hB c (fun _ => T) hS hzero
  refine ⟨ε, hε, fun u hu hneg hpos => ?_⟩
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i u hu (hneg i) (hpos i))
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (referencePoincareConstant_pos n).le
  apply Finset.sum_le_sum
  intro j _
  exact sum_directionalEnergy_disjoint_le _ _ hQ _
    (fun i => measurableSet_euclideanAffineRegion (c i) T) hd hsub _

theorem volume_euclideanAffineRegion_toReal_eq {n : ℕ} (c d : Fin n → ℝ)
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
    (volume (euclideanAffineRegion c T)).toReal = (volume (euclideanAffineRegion d T)).toReal := by
  have h (a : Fin n → ℝ) : (volume (referenceDomain n)).toReal =
      inverseAffineJacobian T * (volume (euclideanAffineRegion a T)).toReal := by
    have he := congrArg (fun μ : Measure (Fin n → ℝ) => (μ univ).toReal)
      (referenceAffineMeasure_eq_scaled_volume a T)
    rw [referenceAffineMeasure_univ] at he
    simpa only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (inverseAffineJacobian_pos T).le,
      volume_euclideanAffineRegion] using he
  exact mul_left_cancel₀ (inverseAffineJacobian_pos T).ne' ((h c).symm.trans (h d))

theorem sum_directionalEnergy_finset_disjoint_le {n : ℕ} {ι : Type*}
    (P : MvPolynomial (Fin n) ℝ) (ε : ℝ) {Q : Set (E n)} (hQ : IsCompact Q)
    (A : ι → Set (E n)) (t : Finset ι) (hA : ∀ i ∈ t, MeasurableSet (A i))
    (hd : Set.Pairwise (↑t) (fun i j => Disjoint (A i) (A j)))
    (hsub : ∀ i ∈ t, A i ⊆ Q) (v : E n) :
    ∑ i ∈ t, directionalEnergy P ε (A i) v ≤ directionalEnergy P ε Q v := by
  have hi := integrableOn_smoothPolynomial_direction P ε hQ v
  simp only [directionalEnergy]
  rw [← integral_biUnion_finset t hA hd (fun i hi' => hi.mono_set (hsub i hi'))]
  apply setIntegral_mono_set hi (Eventually.of_forall (fun _ => norm_nonneg _))
  exact Eventually.of_forall (iUnion₂_subset hsub)

theorem exists_common_selected_bisection_count_budget {n k : ℕ} [NeZero n]
    {ι : Type*} [Fintype ι]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (c : ι → Fin n → ℝ) (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    {S : Set (E k)} (hS : IsCompact S) (hzero : ∀ u ∈ S, u ≠ 0)
    {Q : Set (E n)} (hQ : IsCompact Q)
    (hd : Pairwise (fun i j => Disjoint (euclideanAffineRegion (c i) T) (euclideanAffineRegion (c j) T)))
    (hsub : ∀ i, euclideanAffineRegion (c i) T ⊆ Q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u ∈ S, ∀ t : Finset ι,
      (∀ i ∈ t, (volume.restrict (euclideanAffineRegion (c i) T))
        {x | MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B u) ≤ 0} =
        volume (euclideanAffineRegion (c i) T) / 2) →
      (∀ i ∈ t, (volume.restrict (euclideanAffineRegion (c i) T))
        {x | 0 ≤ MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B u)} =
        volume (euclideanAffineRegion (c i) T) / 2) →
      (Real.pi/10) * (t.card : ℝ) * (volume (euclideanAffineRegion 0 T)).toReal ≤
        referencePoincareConstant n * ∑ j, directionalEnergy (coefficientPolynomial B u) ε Q
          (WithLp.toLp 2 (T (Pi.single j 1))) := by
  obtain ⟨ε, hε, h⟩ := exists_common_euclidean_bisection_energy_fraction B hB c (fun _ => T) hS hzero
  refine ⟨ε, hε, fun u hu t hneg hpos => ?_⟩
  have hs := Finset.sum_le_sum (fun i (hi : i ∈ t) => h i u hu (hneg i hi) (hpos i hi))
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm] at hs
  have hvol (i : ι) := volume_euclideanAffineRegion_toReal_eq (c i) 0 T
  simp_rw [hvol] at hs
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  rw [← mul_assoc] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (referencePoincareConstant_pos n).le
  apply Finset.sum_le_sum
  intro j _
  exact sum_directionalEnergy_finset_disjoint_le _ _ hQ _ t
    (fun i _ => measurableSet_euclideanAffineRegion (c i) T)
    (fun _ _ _ _ hij => hd hij) (fun i _ => hsub i) _

theorem exists_common_bisection_obstruction {n k : ℕ} [NeZero n]
    {ι : Type*} [Fintype ι]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (c : ι → Fin n → ℝ) (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    {S : Set (E k)} (hS : IsCompact S) (hzero : ∀ u ∈ S, u ≠ 0)
    {Q : Set (E n)} (hQ : IsCompact Q)
    (hd : Pairwise (fun i j => Disjoint (euclideanAffineRegion (c i) T) (euclideanAffineRegion (c j) T)))
    (hsub : ∀ i, euclideanAffineRegion (c i) T ⊆ Q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u ∈ S, ∀ M : ℝ,
      (∀ j, directionalEnergy (coefficientPolynomial B u) ε Q
        (WithLp.toLp 2 (T (Pi.single j 1))) ≤ M) →
      referencePoincareConstant n * (n : ℝ) * M <
        (Real.pi/10) * (Fintype.card ι : ℝ) * (volume (euclideanAffineRegion 0 T)).toReal →
      ∃ i, ¬ ((volume.restrict (euclideanAffineRegion (c i) T))
          {x | MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B u) ≤ 0} =
          volume (euclideanAffineRegion (c i) T) / 2 ∧
        (volume.restrict (euclideanAffineRegion (c i) T))
          {x | 0 ≤ MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B u)} =
          volume (euclideanAffineRegion (c i) T) / 2) := by
  classical
  obtain ⟨ε, hε, h⟩ := exists_common_selected_bisection_count_budget B hB c T hS hzero hQ hd hsub
  refine ⟨ε, hε, fun u hu M hM hlarge => ?_⟩
  by_contra hall
  push Not at hall
  have hb := h u hu Finset.univ (fun i _ => (hall i).1) (fun i _ => (hall i).2)
  have hsum : (∑ j, directionalEnergy (coefficientPolynomial B u) ε Q
      (WithLp.toLp 2 (T (Pi.single j 1)))) ≤ (n : ℝ) * M := by
    calc
      _ ≤ ∑ _j : Fin n, M := Finset.sum_le_sum (fun j _ => hM j)
      _ = _ := by simp
  have hupper := mul_le_mul_of_nonneg_left hsum (referencePoincareConstant_pos n).le
  simp only [Finset.card_univ] at hb
  have hfinal := hb.trans hupper
  rw [← mul_assoc] at hfinal
  exact (not_lt_of_ge hfinal) hlarge

end Kakeya4.Hard.MultilinearKakeya
