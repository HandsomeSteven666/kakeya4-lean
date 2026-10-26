import Kakeya4.Hard.MultilinearKakeya.RelativeOperatorGeometry
import Kakeya4.Hard.MultilinearKakeya.LocalEnergyBound

/-! Compact operator candidates and finite relative covers. The candidate bounds
can depend on a degree budget, while the local relative-neighborhood geometry does not. -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Kakeya4.Hard.MultilinearKakeya

def operatorCandidateSet (n : ℕ) (c R : ℝ) : Set (Operator n) :=
  {A | ‖A‖ ≤ R ∧ ∀ x, c * ‖x‖ ≤ ‖A x‖}

theorem isCompact_operatorCandidateSet (n : ℕ) (c R : ℝ) :
    IsCompact (operatorCandidateSet n c R) := by
  have hl : IsClosed {A : Operator n | ∀ x, c*‖x‖ ≤ ‖A x‖} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const ((continuous_id.clm_apply continuous_const).norm)
  have hb : {A : Operator n | ‖A‖ ≤ R} = Metric.closedBall 0 R := by
    ext A
    simp only [Metric.mem_closedBall, dist_zero_right, mem_ofPred_eq]
  unfold operatorCandidateSet
  rw [ofPred_and, hb]
  exact (isCompact_closedBall 0 R).inter_right hl

theorem operatorCandidate_injective {n : ℕ} {c R : ℝ} (hc : 0 < c)
    {A : Operator n} (hA : A ∈ operatorCandidateSet n c R) : Function.Injective A := by
  intro x y hxy
  have hz : A (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  have h := hA.2 (x-y)
  rw [hz, norm_zero] at h
  have hn : ‖x-y‖ ≤ 0 := (mul_le_mul_iff_left₀ hc).mp (by simpa [mul_comm] using h)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

theorem operatorCandidate_eq_equiv {n : ℕ} {c R : ℝ} (hc : 0 < c)
    {A : Operator n} (hA : A ∈ operatorCandidateSet n c R) :
    ∃ T : E n ≃L[ℝ] E n, T.toContinuousLinearMap = A := by
  let T := (LinearEquiv.ofInjectiveEndo A.toLinearMap (operatorCandidate_injective hc hA)).toContinuousLinearEquiv
  refine ⟨T, ?_⟩
  ext x
  rfl

theorem exists_finite_relativeOperator_cover (n : ℕ) {c R δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) :
    ∃ s : Finset (E n ≃L[ℝ] E n),
      (∀ T ∈ s, T.toContinuousLinearMap ∈ operatorCandidateSet n c R) ∧
      ∀ A ∈ operatorCandidateSet n c R, ∃ T ∈ s, A ∈ relativeOperatorBall T δ := by
  classical
  let K := operatorCandidateSet n c R
  choose T hT using (fun A : K => operatorCandidate_eq_equiv hc A.property)
  have hcover : K ⊆ ⋃ A : K, relativeOperatorBall (T A) δ := by
    intro A hA
    apply mem_iUnion.mpr
    refine ⟨⟨A,hA⟩, ?_⟩
    have hself := center_mem_relativeOperatorBall (T ⟨A,hA⟩) hδ
    rwa [hT ⟨A,hA⟩] at hself
  obtain ⟨t, ht⟩ := (isCompact_operatorCandidateSet n c R).elim_finite_subcover
    (fun A : K => relativeOperatorBall (T A) δ) (fun _ => isOpen_relativeOperatorBall _ _) hcover
  refine ⟨t.image T, ?_, ?_⟩
  · intro S hS
    obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hS
    rw [hT A]
    exact A.property
  · intro A hA
    obtain ⟨a, ha⟩ := mem_iUnion.mp (ht hA)
    obtain ⟨hat, hball⟩ := mem_iUnion.mp ha
    exact ⟨T a, Finset.mem_image.mpr ⟨a,hat,rfl⟩, hball⟩

theorem bodySeminorm_comp_le_norm_of_ellipsoid_subset {n : ℕ} (p : Seminorm ℝ (E n))
    (T : E n ≃L[ℝ] E n)
    (hinner : T '' Metric.closedBall 0 1 ⊆ visibilityBody p) (x : E n) :
    bodySeminorm p (T x) ≤ ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, bodySeminorm_apply]
  · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hu : ‖x‖⁻¹ • x ∈ Metric.closedBall (0 : E n) 1 := by
      simp only [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hxn.le), inv_mul_cancel₀ hxn.ne', le_refl]
    have h := (mem_visibilityBody_iff_bodySeminorm p _).mp (hinner ⟨_,hu,rfl⟩)
    rw [map_smul, map_smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.mpr hxn.le)] at h
    have hm := mul_le_mul_of_nonneg_left h hxn.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hxn.ne', one_mul, mul_one] using hm

theorem norm_johnOperator_le_one {n : ℕ} (p : Seminorm ℝ (E n))
    (T : E n ≃L[ℝ] E n) (hinner : T '' Metric.closedBall 0 1 ⊆ visibilityBody p) :
    ‖T.toContinuousLinearMap‖ ≤ 1 := by
  apply T.toContinuousLinearMap.opNorm_le_bound zero_le_one
  intro x
  change ‖T x‖ ≤ 1*‖x‖
  have h := (le_max_left ‖T x‖ (p (T x))).trans
    (bodySeminorm_comp_le_norm_of_ellipsoid_subset p T hinner x)
  simpa only [one_mul] using h

theorem norm_inverse_le_radius_mul_bodySeminorm {n : ℕ} (p : Seminorm ℝ (E n))
    (T : E n ≃L[ℝ] E n) {R : ℝ}
    (houter : visibilityBody p ⊆ T '' Metric.closedBall 0 R) (x : E n) :
    ‖T.symm x‖ ≤ R * bodySeminorm p x := by
  by_cases hx : x = 0
  · simp [hx, bodySeminorm_apply]
  · let q := bodySeminorm p
    have hq : 0 < q x := (norm_pos_iff.mpr hx).trans_le (le_max_left _ _)
    have hunit : q ((q x)⁻¹ • x) ≤ 1 := by
      rw [map_smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.mpr hq.le), inv_mul_cancel₀ hq.ne']
    have hmem := (mem_visibilityBody_iff_bodySeminorm p _).mpr hunit
    obtain ⟨z, hz, he⟩ := houter hmem
    have hn : ‖T.symm ((q x)⁻¹ • x)‖ ≤ R := by
      rw [← he, T.symm_apply_apply]
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hq.le)] at hn
    have hm := mul_le_mul_of_nonneg_left hn hq.le
    have hf : ‖T.symm x‖ ≤ q x * R := by
      simpa only [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] using hm
    exact hf.trans_eq (mul_comm _ _)

theorem johnOperator_mem_uniform_candidates {n : ℕ} (p : Seminorm ℝ (E n))
    (T : E n ≃L[ℝ] E n) {D : ℝ} (hD : 1 ≤ D)
    (hup : ∀ x, p x ≤ D*‖x‖)
    (hinner : T '' Metric.closedBall 0 1 ⊆ visibilityBody p)
    (houter : visibilityBody p ⊆ T '' Metric.closedBall 0 (Real.sqrt n)) :
    T.toContinuousLinearMap ∈ operatorCandidateSet n (((1+Real.sqrt n)*D)⁻¹) 1 := by
  let H := (1+Real.sqrt n)*D
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hH : 0 < H := mul_pos (by positivity) hDp
  have hq (x : E n) : bodySeminorm p x ≤ D*‖x‖ := by
    change max ‖x‖ (p x) ≤ D*‖x‖
    apply max_le _ (hup x)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hD (norm_nonneg x)
  have hinv (x : E n) : ‖T.symm x‖ ≤ H*‖x‖ := by
    calc
      _ ≤ Real.sqrt n * bodySeminorm p x := norm_inverse_le_radius_mul_bodySeminorm p T houter x
      _ ≤ Real.sqrt n * (D*‖x‖) := mul_le_mul_of_nonneg_left (hq x) (Real.sqrt_nonneg n)
      _ ≤ H*‖x‖ := by dsimp [H]; nlinarith [norm_nonneg x]
  refine ⟨norm_johnOperator_le_one p T hinner, fun x => ?_⟩
  change H⁻¹ * ‖x‖ ≤ ‖T x‖
  have hx : ‖x‖ ≤ H*‖T x‖ := by simpa only [T.symm_apply_apply] using hinv (T x)
  have hdiv : ‖x‖/H ≤ ‖T x‖ := (div_le_iff₀ hH).mpr (by simpa only [mul_comm] using hx)
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

theorem localDegreeBudget_monotone_degree (n : ℕ) (R : ℝ) : Monotone (localDegreeBudget n R) := by
  intro a b hab
  unfold localDegreeBudget
  gcongr

theorem exists_smoothVisibility_johnOperator_in_candidates {n : ℕ} (hn : 2 ≤ n)
    (P : MvPolynomial (Fin n) ℝ) {ε : ℝ} (hε : ε ≠ 0)
    {Q : Set (E n)} (hQ : IsCompact Q) {c : E n} {R : ℝ}
    (hQR : Q ⊆ Metric.closedBall c R) {d : ℕ} (hd : P.totalDegree ≤ d) :
    ∃ T : E n ≃L[ℝ] E n,
      T '' Metric.closedBall 0 1 ⊆ visibilityBody (smoothDirectionalSeminorm P ε Q hQ) ∧
      visibilityBody (smoothDirectionalSeminorm P ε Q hQ) ⊆ T '' Metric.closedBall 0 (Real.sqrt n) ∧
      T.toContinuousLinearMap ∈ operatorCandidateSet n
        (((1+Real.sqrt n)*max 1 (localDegreeBudget n R d).toReal)⁻¹) 1 := by
  obtain ⟨T, hinner, houter⟩ := exists_smoothVisibility_johnEllipsoid P ε hQ
  refine ⟨T,hinner,houter, ?_⟩
  apply johnOperator_mem_uniform_candidates _ T (le_max_left _ _) _ hinner houter
  intro x
  have hreal : (localDegreeBudget n R P.totalDegree).toReal ≤ (localDegreeBudget n R d).toReal :=
    ENNReal.toReal_mono (localDegreeBudget_ne_top n R d) (localDegreeBudget_monotone_degree n R hd)
  exact (directionalEnergy_le_degree_mul_norm hn P hε hQ hQR x).trans
    (mul_le_mul_of_nonneg_right (hreal.trans (le_max_right _ _)) (norm_nonneg x))

end Kakeya4.Hard.MultilinearKakeya
