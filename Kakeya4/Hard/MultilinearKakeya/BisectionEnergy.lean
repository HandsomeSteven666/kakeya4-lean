import Kakeya4.Hard.MultilinearKakeya.UniformSmoothing
import Kakeya4.Hard.MultilinearKakeya.SmoothEnergy
import Kakeya4.Hard.MultilinearKakeya.Imported.CKN.Poincare.LpOne

/-! Quantitative oscillation forced by two opposite masses, and its connection
to the proved L1 Poincare inequality on a fixed reference domain. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace Kakeya4.Hard.MultilinearKakeya

theorem opposite_masses_force_oscillation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Integrable f μ)
    {a m : ℝ} (ha : 0 ≤ a)
    (hneg : m ≤ μ.real {x | f x ≤ -a}) (hpos : m ≤ μ.real {x | a ≤ f x})
    (c : ℝ) : a * m ≤ ∫ x, ‖f x - c‖ ∂μ := by
  have hi : Integrable (fun x => ‖f x-c‖) μ := (hf.sub (integrable_const c)).norm
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun x => norm_nonneg (f x-c))) hi a
  by_cases hc : 0 ≤ c
  · have hs : {x | f x ≤ -a} ⊆ {x | a ≤ ‖f x-c‖} := by
      intro x hx
      change a ≤ ‖f x-c‖
      change f x ≤ -a at hx
      rw [Real.norm_eq_abs]
      exact (show a ≤ -(f x-c) by linarith).trans (neg_le_abs _)
    exact (mul_le_mul_of_nonneg_left (hneg.trans (measureReal_mono hs)) ha).trans hm
  · have hs : {x | a ≤ f x} ⊆ {x | a ≤ ‖f x-c‖} := by
      intro x hx
      change a ≤ ‖f x-c‖
      change a ≤ f x at hx
      rw [Real.norm_eq_abs]
      exact (show a ≤ f x-c by linarith).trans (le_abs_self _)
    exact (mul_le_mul_of_nonneg_left (hpos.trans (measureReal_mono hs)) ha).trans hm

theorem real_mass_lower_of_half_le_add_error {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {A : Set α} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : μ univ / 2 ≤ μ A + ENNReal.ofReal δ) :
    (μ univ).toReal / 2 - δ ≤ μ.real A := by
  have h' := ENNReal.toReal_mono (by finiteness : μ A + ENNReal.ofReal δ ≠ ⊤) h
  rw [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_add (by finiteness)
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hδ] at h'
  exact sub_le_iff_le_add.mpr h'

theorem smoothed_bisection_oscillation_lower {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 ≤ δ)
    (hneg : μ {x | f x ≤ 0} = μ univ / 2)
    (hpos : μ {x | 0 ≤ f x} = μ univ / 2)
    (hsmall : μ {x | |f x| ≤ ε} ≤ ENNReal.ofReal δ) (c : ℝ) :
    (Real.pi/4) * ((μ univ).toReal/2-δ) ≤
      ∫ x, ‖Real.arctan (f x/ε) - c‖ ∂μ := by
  have hi : Integrable (fun x => Real.arctan (f x/ε)) μ :=
    (integrable_const (Real.pi/2)).mono'
      ((Real.continuous_arctan.measurable.comp (hf.div_const ε)).aestronglyMeasurable)
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        exact (abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩).le))
  apply opposite_masses_force_oscillation μ hi (by positivity)
  · exact real_mass_lower_of_half_le_add_error μ hδ
      (negative_half_mass_le_smoothed_mass_add_error μ f hε δ hneg hsmall)
  · exact real_mass_lower_of_half_le_add_error μ hδ
      (positive_half_mass_le_smoothed_mass_add_error μ f hε δ hpos hsmall)

def referenceDomain (n : ℕ) : Set (Fin n → ℝ) := Metric.ball 0 1

theorem referenceDomain_regular (n : ℕ) :
    CKN.IsOpenBoundedConvexDomain (referenceDomain n) := by
  refine ⟨Metric.isOpen_ball, ⟨1, by norm_num, ?_⟩, convex_ball _ _⟩
  intro x hx i
  have hx' : ‖x‖ < 1 := by simpa [referenceDomain, Metric.mem_ball, dist_zero_right] using hx
  exact (le_trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i) hx'.le)

theorem referenceDomain_volume_pos (n : ℕ) :
    0 < (volume (referenceDomain n)).toReal := by
  exact ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume 0 (by norm_num)))
    ((referenceDomain_regular n).isBoundedDomain.volume_lt_top.ne)

def referencePoincareConstant (n : ℕ) : ℝ := max 1
  (((volume (referenceDomain n)).toReal⁻¹ *
      (((2 * Classical.choose (referenceDomain_regular n).isBoundedDomain) ^ n) / (n : ℝ))) *
    ((n : ℝ) * (volume (Metric.ball (0 : Fin n → ℝ) 1)).toReal *
      (4 * Classical.choose (referenceDomain_regular n).isBoundedDomain)))

theorem referencePoincareConstant_pos (n : ℕ) : 0 < referencePoincareConstant n :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem reference_poincare {n : ℕ} [NeZero n] (u : (Fin n → ℝ) → ℝ)
    (hu : ContDiff ℝ 1 u) :
    ∫ x in referenceDomain n, ‖u x - CKN.integralAverage (referenceDomain n) u‖ ≤
      referencePoincareConstant n * ∫ x in referenceDomain n, ‖fderiv ℝ u x‖ := by
  let := (referenceDomain_regular n).isFiniteMeasure_restrict_volume
  have hc : IsCompact (closure (referenceDomain n)) :=
    (referenceDomain_regular n).isBoundedDomain.isBounded.isCompact_closure
  have hi : IntegrableOn u (referenceDomain n) :=
    (hu.continuous.continuousOn.integrableOn_compact hc).mono_set subset_closure
  apply (CKN.integral_norm_sub_integralAverage_le_bound_of_isOpenBoundedConvexDomain
    (referenceDomain_regular n) hi hu (referenceDomain_volume_pos n)).trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (integral_nonneg (fun _ => norm_nonneg _))

theorem norm_clm_pi_le_sum {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i, ‖L (Pi.single i 1)‖ := by
  apply L.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro v
  have hv : (∑ i, v i • Pi.single i (1 : ℝ)) = v := by
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using Finset.univ_sum_single v
  calc
    ‖L v‖ = ‖∑ i, v i • L (Pi.single i 1)‖ := by
      conv_lhs => rw [← hv, map_sum]
      simp only [map_smul]
    _ ≤ ∑ i, ‖v i • L (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖v‖ * ‖L (Pi.single i 1)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm v i) (norm_nonneg _)
    _ = (∑ i, ‖L (Pi.single i 1)‖) * ‖v‖ := by rw [← Finset.mul_sum, mul_comm]

theorem reference_poincare_directions {n : ℕ} [NeZero n] (u : (Fin n → ℝ) → ℝ)
    (hu : ContDiff ℝ 1 u) :
    ∫ x in referenceDomain n, ‖u x - CKN.integralAverage (referenceDomain n) u‖ ≤
      referencePoincareConstant n * ∑ i, ∫ x in referenceDomain n,
        ‖fderiv ℝ u x (Pi.single i 1)‖ := by
  have hc : IsCompact (closure (referenceDomain n)) :=
    (referenceDomain_regular n).isBoundedDomain.isBounded.isCompact_closure
  have hd : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hi (i : Fin n) : IntegrableOn (fun x => ‖fderiv ℝ u x (Pi.single i 1)‖)
      (referenceDomain n) :=
    (((hd.clm_apply continuous_const).norm.continuousOn).integrableOn_compact hc).mono_set subset_closure
  apply (reference_poincare u hu).trans
  apply mul_le_mul_of_nonneg_left _ (referencePoincareConstant_pos n).le
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  apply integral_mono
    ((hd.norm.continuousOn.integrableOn_compact hc).mono_set subset_closure)
    (integrable_finsetSum _ (fun i _ => hi i))
  exact fun x => norm_clm_pi_le_sum _

theorem reference_opposite_masses_energy_lower {n : ℕ} [NeZero n]
    (u : (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 1 u) {a m : ℝ} (ha : 0 ≤ a)
    (hneg : m ≤ (volume.restrict (referenceDomain n)).real {x | u x ≤ -a})
    (hpos : m ≤ (volume.restrict (referenceDomain n)).real {x | a ≤ u x}) :
    a * m ≤ referencePoincareConstant n * ∑ i, ∫ x in referenceDomain n,
      ‖fderiv ℝ u x (Pi.single i 1)‖ := by
  let := (referenceDomain_regular n).isFiniteMeasure_restrict_volume
  have hc : IsCompact (closure (referenceDomain n)) :=
    (referenceDomain_regular n).isBoundedDomain.isBounded.isCompact_closure
  have hi : IntegrableOn u (referenceDomain n) :=
    (hu.continuous.continuousOn.integrableOn_compact hc).mono_set subset_closure
  exact (opposite_masses_force_oscillation _ hi ha hneg hpos _).trans
    (reference_poincare_directions u hu)

end Kakeya4.Hard.MultilinearKakeya
