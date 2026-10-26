import Kakeya4.Hard.MultilinearKakeya.OperatorShapeNet
import Kakeya4.Hard.MultilinearKakeya.CoefficientEnergyContinuity

/-! Actual closed antipodally invariant coefficient classes associated to the
finite coloured operator net. Same-colour classes have disjoint intersections. -/

noncomputable section
open Set
open scoped Topology

namespace Kakeya4.Hard.MultilinearKakeya

def bodyShapeComparison {n : ℕ} (p : Seminorm ℝ (E n)) (T : E n ≃L[ℝ] E n) : Prop :=
  ∀ x, bodySeminorm p x ≤ 2*‖T.symm x‖ ∧
    ‖T.symm x‖ ≤ (2*Real.sqrt n)*bodySeminorm p x

def coefficientShapeClass {n k : ℕ} (B : Fin k → MvPolynomial (Fin n) ℝ)
    (ε : ℝ) (Q : Set (E n)) (T : E n ≃L[ℝ] E n) : Set (E k) :=
  {u | ∀ x, max ‖x‖ (directionalEnergy (coefficientPolynomial B u) ε Q x) ≤ 2*‖T.symm x‖ ∧
    ‖T.symm x‖ ≤ (2*Real.sqrt n)*max ‖x‖ (directionalEnergy (coefficientPolynomial B u) ε Q x)}

theorem mem_coefficientShapeClass_iff {n k : ℕ} (B : Fin k → MvPolynomial (Fin n) ℝ)
    (ε : ℝ) {Q : Set (E n)} (hQ : IsCompact Q) (T : E n ≃L[ℝ] E n) (u : E k) :
    u ∈ coefficientShapeClass B ε Q T ↔
      bodyShapeComparison (smoothDirectionalSeminorm (coefficientPolynomial B u) ε Q hQ) T := Iff.rfl

theorem isClosed_coefficientShapeClass {n k : ℕ} (B : Fin k → MvPolynomial (Fin n) ℝ)
    (ε : ℝ) {Q : Set (E n)} (hQ : IsCompact Q) (T : E n ≃L[ℝ] E n) :
    IsClosed (coefficientShapeClass B ε Q T) := by
  simp only [coefficientShapeClass, ofPred_forall, ofPred_and]
  apply isClosed_iInter
  intro x
  have hq : Continuous (fun u : E k => max ‖x‖ (directionalEnergy (coefficientPolynomial B u) ε Q x)) :=
    continuous_const.max (continuous_directionalEnergy_coefficients B ε hQ x)
  exact (isClosed_le hq continuous_const).inter
    (isClosed_le continuous_const (continuous_const.mul hq))

theorem neg_mem_coefficientShapeClass_iff {n k : ℕ} (B : Fin k → MvPolynomial (Fin n) ℝ)
    (ε : ℝ) (Q : Set (E n)) (T : E n ≃L[ℝ] E n) (u : E k) :
    -u ∈ coefficientShapeClass B ε Q T ↔ u ∈ coefficientShapeClass B ε Q T := by
  simp only [coefficientShapeClass, mem_ofPred_eq, directionalEnergy_neg_coefficients]

theorem directionalEnergy_transformed_le_of_shapeClass {n k : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) (ε : ℝ) (Q : Set (E n))
    (T : E n ≃L[ℝ] E n) {u : E k} (hu : u ∈ coefficientShapeClass B ε Q T)
    (v : E n) : directionalEnergy (coefficientPolynomial B u) ε Q (T v) ≤ 2*‖v‖ := by
  have h := (hu (T v)).1
  have he := (le_max_right ‖T v‖ (directionalEnergy (coefficientPolynomial B u) ε Q (T v))).trans h
  simpa only [T.symm_apply_apply] using he

theorem directionalEnergy_scaled_axis_le_of_shapeClass {n k : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) (ε : ℝ) (Q : Set (E n))
    (T : E n ≃L[ℝ] E n) {u : E k} (hu : u ∈ coefficientShapeClass B ε Q T)
    {η : ℝ} (hη : 0 ≤ η) (j : Fin n) :
    directionalEnergy (coefficientPolynomial B u) ε Q
      (η • T (WithLp.toLp 2 (Pi.single j 1))) ≤ 2*η := by
  rw [directionalEnergy_smul, Real.norm_of_nonneg hη]
  have hv : ‖(WithLp.toLp 2 (Pi.single j 1) : E n)‖ = 1 := by
    exact PiLp.norm_single 2 (fun _ : Fin n => ℝ) j (1 : ℝ) |>.trans (by norm_num)
  have h := directionalEnergy_transformed_le_of_shapeClass B ε Q T hu
    (WithLp.toLp 2 (Pi.single j 1))
  rw [hv, mul_one] at h
  exact (mul_le_mul_of_nonneg_left h hη).trans_eq (mul_comm _ _)

theorem bodyShapeComparison_of_near_john {n : ℕ} (p : Seminorm ℝ (E n))
    (T S : E n ≃L[ℝ] E n)
    (hinner : T '' Metric.closedBall 0 1 ⊆ visibilityBody p)
    (houter : visibilityBody p ⊆ T '' Metric.closedBall 0 (Real.sqrt n))
    (hST : ‖S.symm.toContinuousLinearMap.comp T.toContinuousLinearMap‖ ≤ 2)
    (hTS : ‖T.symm.toContinuousLinearMap.comp S.toContinuousLinearMap‖ ≤ 2) :
    bodyShapeComparison p S := by
  intro x
  have hq : bodySeminorm p x ≤ ‖T.symm x‖ := by
    simpa only [T.apply_symm_apply] using
      bodySeminorm_comp_le_norm_of_ellipsoid_subset p T hinner (T.symm x)
  have htx : ‖T.symm x‖ ≤ 2*‖S.symm x‖ := by
    have h := (T.symm.toContinuousLinearMap.comp S.toContinuousLinearMap).le_opNorm (S.symm x)
    have h' : ‖T.symm x‖ ≤ ‖T.symm.toContinuousLinearMap.comp S.toContinuousLinearMap‖ * ‖S.symm x‖ := by
      simpa using h
    exact h'.trans (mul_le_mul_of_nonneg_right hTS (norm_nonneg _))
  have hsx : ‖S.symm x‖ ≤ 2*‖T.symm x‖ := by
    have h := (S.symm.toContinuousLinearMap.comp T.toContinuousLinearMap).le_opNorm (T.symm x)
    have h' : ‖S.symm x‖ ≤ ‖S.symm.toContinuousLinearMap.comp T.toContinuousLinearMap‖ * ‖T.symm x‖ := by
      simpa using h
    exact h'.trans (mul_le_mul_of_nonneg_right hST (norm_nonneg _))
  refine ⟨hq.trans htx, ?_⟩
  calc
    _ ≤ 2*‖T.symm x‖ := hsx
    _ ≤ 2*(Real.sqrt n*bodySeminorm p x) :=
      mul_le_mul_of_nonneg_left (norm_inverse_le_radius_mul_bodySeminorm p T houter x) (by norm_num)
    _ = _ := by ring

theorem relative_norm_le_of_bodyShapeComparison {n : ℕ} (p : Seminorm ℝ (E n))
    (T S : E n ≃L[ℝ] E n) (hT : bodyShapeComparison p T) (hS : bodyShapeComparison p S) :
    ‖T.symm.toContinuousLinearMap.comp S.toContinuousLinearMap‖ ≤ 4*Real.sqrt n := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖T.symm (S x)‖ ≤ (4*Real.sqrt n)*‖x‖
  have hs : bodySeminorm p (S x) ≤ 2*‖x‖ := by simpa only [S.symm_apply_apply] using (hS (S x)).1
  calc
    _ ≤ (2*Real.sqrt n)*bodySeminorm p (S x) := (hT (S x)).2
    _ ≤ (2*Real.sqrt n)*(2*‖x‖) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

theorem inner_ellipsoid_subset_of_bodyShapeComparison {n : ℕ} (p : Seminorm ℝ (E n))
    (T : E n ≃L[ℝ] E n) (hT : bodyShapeComparison p T) :
    T '' Metric.closedBall 0 (1/2 : ℝ) ⊆ visibilityBody p := by
  rintro x ⟨z,hz,rfl⟩
  apply (mem_visibilityBody_iff_bodySeminorm p _).mpr
  have hq : bodySeminorm p (T z) ≤ 2*‖z‖ := by simpa only [T.symm_apply_apply] using (hT (T z)).1
  have hz' : ‖z‖ ≤ 1/2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  linarith

theorem visibilityBody_subset_outer_ellipsoid_of_bodyShapeComparison {n : ℕ}
    (p : Seminorm ℝ (E n)) (T : E n ≃L[ℝ] E n) (hT : bodyShapeComparison p T) :
    visibilityBody p ⊆ T '' Metric.closedBall 0 (2*Real.sqrt n) := by
  intro x hx
  have hqx := (mem_visibilityBody_iff_bodySeminorm p x).mp hx
  have hn : ‖T.symm x‖ ≤ 2*Real.sqrt n :=
    (hT x).2.trans ((mul_le_mul_of_nonneg_left hqx (by positivity)).trans_eq (mul_one _))
  exact ⟨T.symm x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hn, T.apply_symm_apply x⟩

theorem volume_bounds_of_bodyShapeComparison {n : ℕ} (p : Seminorm ℝ (E n))
    (T : E n ≃L[ℝ] E n) (hT : bodyShapeComparison p T) :
    ENNReal.ofReal ((1/2 : ℝ)^n) * MeasureTheory.volume (T '' Metric.closedBall 0 1) ≤
        MeasureTheory.volume (visibilityBody p) ∧
      MeasureTheory.volume (visibilityBody p) ≤ ENNReal.ofReal ((2*Real.sqrt n)^n) *
        MeasureTheory.volume (T '' Metric.closedBall 0 1) := by
  have hi := MeasureTheory.measure_mono (μ := MeasureTheory.volume)
    (inner_ellipsoid_subset_of_bodyShapeComparison p T hT)
  have ho := MeasureTheory.measure_mono (μ := MeasureTheory.volume)
    (visibilityBody_subset_outer_ellipsoid_of_bodyShapeComparison p T hT)
  rw [volume_image_closedBall_scaled T (by norm_num : (0 : ℝ) ≤ 1/2)] at hi
  rw [volume_image_closedBall_scaled T (by positivity : (0 : ℝ) ≤ 2*Real.sqrt n)] at ho
  exact ⟨hi,ho⟩

theorem exists_uniform_closed_shape_classes {n k d : ℕ} (hn : 2 ≤ n)
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : ∀ i, (B i).totalDegree ≤ d)
    {Q : Set (E n)} (hQ : IsCompact Q) {c : E n} {R : ℝ}
    (hQR : Q ⊆ Metric.closedBall c R) :
    ∃ s : Finset (E n ≃L[ℝ] E n), ∃ colour : s → Fin (shapeColourCount n),
      (∀ S ∈ s, ‖S.toContinuousLinearMap‖ ≤ 1) ∧
      ∀ ε : ℝ, ε ≠ 0 →
        (∀ T : s, IsClosed (coefficientShapeClass B ε Q T.val)) ∧
        (∀ T : s, ∀ u : E k, -u ∈ coefficientShapeClass B ε Q T.val ↔
          u ∈ coefficientShapeClass B ε Q T.val) ∧
        (∀ T S : s, T ≠ S → colour T = colour S →
          Disjoint (coefficientShapeClass B ε Q T.val) (coefficientShapeClass B ε Q S.val)) ∧
        (⋃ T : s, coefficientShapeClass B ε Q T.val) = univ := by
  classical
  obtain ⟨s,colour,hbounded,hcolour,hcover⟩ := exists_uniform_smoothVisibility_shape_net hn hQ hQR d
  refine ⟨s,colour,hbounded,fun ε hε => ⟨fun T => isClosed_coefficientShapeClass B ε hQ T.val,
    fun T u => neg_mem_coefficientShapeClass_iff B ε Q T.val u, ?_, ?_⟩⟩
  · intro T S hTS hcol
    apply Set.disjoint_left.mpr
    intro u huT huS
    let p := smoothDirectionalSeminorm (coefficientPolynomial B u) ε Q hQ
    have hT : bodyShapeComparison p T.val := (mem_coefficientShapeClass_iff B ε hQ T.val u).mp huT
    have hS : bodyShapeComparison p S.val := (mem_coefficientShapeClass_iff B ε hQ S.val u).mp huS
    have ht := relative_norm_le_of_bodyShapeComparison p T.val S.val hT hS
    have hs := relative_norm_le_of_bodyShapeComparison p S.val T.val hS hT
    rcases hcolour T S hTS hcol with h | h <;> linarith
  · apply eq_univ_of_forall
    intro u
    obtain ⟨T,hinner,houter,S,hS,hST,hTS⟩ := hcover (coefficientPolynomial B u) ε hε
      (totalDegree_coefficientPolynomial_le B hB u)
    apply mem_iUnion.mpr
    refine ⟨⟨S,hS⟩, ?_⟩
    apply (mem_coefficientShapeClass_iff B ε hQ S u).mpr
    exact bodyShapeComparison_of_near_john _ T S hinner houter hST hTS

end Kakeya4.Hard.MultilinearKakeya
