import Kakeya4.Hard.MultilinearKakeya.DiscreteEndpoint
import Kakeya4.Hard.MultilinearKakeya.KernelLocalization
import Kakeya4.Hard.MultilinearKakeya.SpatialBallCover
import Kakeya4.Hard.MultilinearKakeya.Scaling

/-! The original integral endpoint from discrete polynomial factors. A fixed
dimensional ball multiplicity and volume pay for localization; closed-ball
exhaustion then retains the same constant on all of Euclidean space. -/

noncomputable section
open Set MeasureTheory Classical
open scoped Topology BigOperators ENNReal NNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem ofReal_totalWeight_product_rpow {n : ℕ} {ι : Fin n → Type*}
    [∀ i, Fintype (ι i)] (w : ∀ i, ι i → ℝ≥0) {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal ((∏ i, ∑ t, (w i t : ℝ))^p) =
      ∏ i, (∑ t, (w i t : ℝ≥0∞))^p := by
  rw [← ENNReal.ofReal_rpow_of_nonneg
    (Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun t _ => (w i t).coe_nonneg))) hp,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => Finset.sum_nonneg (fun t _ => (w i t).coe_nonneg)),
    ← ENNReal.prod_rpow_of_nonneg hp]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => (w _ t).coe_nonneg),ENNReal.ofReal_coe_nnreal]

def continuousEndpointConstant (n : ℕ) : ℝ :=
  (volume (Metric.closedBall (0 : E n) (1/2 : ℝ))).toReal *
    discreteEndpointConstant n (spatialBallOverlapBound n) 2

theorem continuousEndpointConstant_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ continuousEndpointConstant n :=
  mul_nonneg ENNReal.toReal_nonneg (discreteEndpointConstant_nonneg hn _ _)

theorem setLIntegral_endpointKernel_le_compact {n : ℕ} (hn : 2 ≤ n)
    {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0)
    {K : Set (E n)} (hK : IsCompact K) :
    (∫⁻ x in K, (kernel L w 1 x)^endpointExponent n ∂volume) ≤
      ENNReal.ofReal (continuousEndpointConstant n) *
        ∏ i, (∑ t, (w i t : ℝ≥0∞))^endpointExponent n := by
  obtain ⟨s,_,hcover,hoverlap⟩ := exists_finite_halfBall_cover_with_uniform_unit_overlap hK
  have hd := real_discrete_ballTube_endpoint hn (fun c : s => c.val)
    (card_filter_subtype_centres_le s hoverlap) 2 L w
  change (∑ c ∈ s.attach, (realKernel L w 2 c.val)^endpointExponent n) ≤ _ at hd
  rw [Finset.sum_attach s (fun c => (realKernel L w 2 c)^endpointExponent n)] at hd
  have he : 0 ≤ endpointExponent n := by
    unfold endpointExponent
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact (one_div_pos.mpr (by linarith)).le
  have hs : (∑ c ∈ s, ENNReal.ofReal ((realKernel L w 2 c)^endpointExponent n)) ≤
      ENNReal.ofReal (discreteEndpointConstant n (spatialBallOverlapBound n) 2) *
        ∏ i, (∑ t, (w i t : ℝ≥0∞))^endpointExponent n := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => Real.rpow_nonneg (realKernel_nonneg L w 2 c) _)]
    have h := ENNReal.ofReal_le_ofReal hd
    rwa [ENNReal.ofReal_mul (discreteEndpointConstant_nonneg hn _ _),
      ofReal_totalWeight_product_rpow w he] at h
  calc
    _ ≤ volume (Metric.closedBall (0 : E n) (1/2 : ℝ)) *
        ∑ c ∈ s, ENNReal.ofReal ((realKernel L w 2 c)^endpointExponent n) :=
      setLIntegral_endpointKernel_le_ball_cover hn L w hK.measurableSet s hcover
    _ ≤ volume (Metric.closedBall (0 : E n) (1/2 : ℝ)) *
        (ENNReal.ofReal (discreteEndpointConstant n (spatialBallOverlapBound n) 2) *
          ∏ i, (∑ t, (w i t : ℝ≥0∞))^endpointExponent n) := mul_le_mul' le_rfl hs
    _ = _ := by
      unfold continuousEndpointConstant
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (isCompact_closedBall (0 : E n) (1/2 : ℝ)).measure_ne_top]
      exact (mul_assoc _ _ _).symm

theorem lintegral_endpointKernel_le {n : ℕ} (hn : 2 ≤ n)
    {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) :
    (∫⁻ x, (kernel L w 1 x)^endpointExponent n ∂volume) ≤
      ENNReal.ofReal (continuousEndpointConstant n) *
        ∏ i, (∑ t, (w i t : ℝ≥0∞))^endpointExponent n := by
  have hm : Monotone (fun m : ℕ => Metric.closedBall (0 : E n) (m : ℝ)) := by
    intro i j hij
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hij)
  have hu := setLIntegral_iUnion_of_directed (μ := volume)
    (fun x => (kernel L w 1 x)^endpointExponent n) hm.directed_le
  rw [Metric.iUnion_closedBall_nat,Measure.restrict_univ] at hu
  rw [hu]
  exact iSup_le (fun m => setLIntegral_endpointKernel_le_compact hn L w (isCompact_closedBall _ _))

/-- The actual finite-family unit-radius endpoint, with no unproved factor input. -/
theorem unitRadiusBound_of_two_le {n : ℕ} (hn : 2 ≤ n) : UnitRadiusBound n := by
  let C : ℝ≥0 := ⟨max 1 (continuousEndpointConstant n),
    le_trans zero_le_one (le_max_left _ _)⟩
  refine ⟨C,?_,fun ι _ L w => ?_⟩
  · change 0 < max 1 (continuousEndpointConstant n)
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · apply (lintegral_endpointKernel_le hn L w).trans
    apply mul_le_mul' ?_ le_rfl
    rw [ENNReal.coe_nnreal_eq]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- Every positive radius has precisely the existing r^n scaling. -/
theorem endpointBound_of_two_le {n : ℕ} (hn : 2 ≤ n) : EndpointBound n :=
  (endpointBound_iff_unitRadiusBound n).mpr (unitRadiusBound_of_two_le hn)

theorem manuscriptBound : ManuscriptBound :=
  fun _ hn _ => endpointBound_of_two_le hn

end Kakeya4.Hard.MultilinearKakeya
