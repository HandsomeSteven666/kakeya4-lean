import Kakeya4.Hard.MultilinearKakeya.DiscreteLineMeasureEndpoint
import Kakeya4.Hard.MultilinearKakeya.LineMeasureLocalization
import Kakeya4.Hard.MultilinearKakeya.ContinuousEndpoint

/-! The unit-radius integral endpoint for arbitrary finite nonnegative Borel
line laws. The spatial cover and exhaustion preserve the dimensional constant. -/

noncomputable section
open Set MeasureTheory Classical
open scoped Topology BigOperators ENNReal NNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem ofReal_totalMass_product_rpow {n : ℕ}
    (μ : Fin n → Measure (LineParameter n)) [∀ i, IsFiniteMeasure (μ i)]
    {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal ((∏ i, (μ i).real univ)^p) = ∏ i, (μ i univ)^p := by
  have hμ (i : Fin n) : 0 ≤ (μ i).real univ := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_rpow_of_nonneg (Finset.prod_nonneg (fun i _ => hμ i)) hp,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => hμ i),
    ← ENNReal.prod_rpow_of_nonneg hp]
  apply Finset.prod_congr rfl
  intro i _
  change ENNReal.ofReal ((μ i univ).toReal)^p = _
  rw [ENNReal.ofReal_toReal (measure_ne_top (μ i) univ)]

def LineMeasureUnitRadiusBound (n : ℕ) : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧ ∀ (μ : Fin n → Measure (LineParameter n)) [∀ i, IsFiniteMeasure (μ i)],
    (∫⁻ x, (lineMeasureKernel μ 1 x)^endpointExponent n ∂volume) ≤
      (C : ℝ≥0∞) * ∏ i, (μ i univ)^endpointExponent n

theorem setLIntegral_lineMeasureEndpointKernel_le_compact {n : ℕ} (hn : 2 ≤ n)
    (μ : Fin n → Measure (LineParameter n)) [∀ i, IsFiniteMeasure (μ i)]
    {K : Set (E n)} (hK : IsCompact K) :
    (∫⁻ x in K, (lineMeasureKernel μ 1 x)^endpointExponent n ∂volume) ≤
      ENNReal.ofReal (continuousEndpointConstant n) *
        ∏ i, (μ i univ)^endpointExponent n := by
  obtain ⟨s,_,hcover,hoverlap⟩ := exists_finite_halfBall_cover_with_uniform_unit_overlap hK
  have hd := real_discrete_lineMeasure_endpoint hn μ (fun c : s => c.val)
    (card_filter_subtype_centres_le s hoverlap) 2
  change (∑ c ∈ s.attach, ((lineMeasureKernel μ 2 c.val).toReal)^endpointExponent n) ≤ _ at hd
  rw [Finset.sum_attach s (fun c => ((lineMeasureKernel μ 2 c).toReal)^endpointExponent n)] at hd
  have he : 0 ≤ endpointExponent n := by
    unfold endpointExponent
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact (one_div_pos.mpr (by linarith)).le
  have hs : (∑ c ∈ s, ENNReal.ofReal (((lineMeasureKernel μ 2 c).toReal)^endpointExponent n)) ≤
      ENNReal.ofReal (discreteEndpointConstant n (spatialBallOverlapBound n) 2) *
        ∏ i, (μ i univ)^endpointExponent n := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)]
    have h := ENNReal.ofReal_le_ofReal hd
    rwa [ENNReal.ofReal_mul (discreteEndpointConstant_nonneg hn _ _),
      ofReal_totalMass_product_rpow μ he] at h
  calc
    _ ≤ volume (Metric.closedBall (0 : E n) (1/2 : ℝ)) *
        ∑ c ∈ s, ENNReal.ofReal (((lineMeasureKernel μ 2 c).toReal)^endpointExponent n) :=
      setLIntegral_lineMeasureEndpointKernel_le_ball_cover hn μ hK.measurableSet s hcover
    _ ≤ volume (Metric.closedBall (0 : E n) (1/2 : ℝ)) *
        (ENNReal.ofReal (discreteEndpointConstant n (spatialBallOverlapBound n) 2) *
          ∏ i, (μ i univ)^endpointExponent n) := mul_le_mul' le_rfl hs
    _ = _ := by
      unfold continuousEndpointConstant
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (isCompact_closedBall (0 : E n) (1/2 : ℝ)).measure_ne_top]
      exact (mul_assoc _ _ _).symm

theorem lintegral_lineMeasureEndpointKernel_le {n : ℕ} (hn : 2 ≤ n)
    (μ : Fin n → Measure (LineParameter n)) [∀ i, IsFiniteMeasure (μ i)] :
    (∫⁻ x, (lineMeasureKernel μ 1 x)^endpointExponent n ∂volume) ≤
      ENNReal.ofReal (continuousEndpointConstant n) *
        ∏ i, (μ i univ)^endpointExponent n := by
  have hm : Monotone (fun m : ℕ => Metric.closedBall (0 : E n) (m : ℝ)) := by
    intro i j hij
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hij)
  have hu := setLIntegral_iUnion_of_directed (μ := volume)
    (fun x => (lineMeasureKernel μ 1 x)^endpointExponent n) hm.directed_le
  rw [Metric.iUnion_closedBall_nat,Measure.restrict_univ] at hu
  rw [hu]
  exact iSup_le (fun m => setLIntegral_lineMeasureEndpointKernel_le_compact hn μ (isCompact_closedBall _ _))

/-- The actual finite line-law unit-radius endpoint, with no unproved factor input. -/
theorem lineMeasureUnitRadiusBound_of_two_le {n : ℕ} (hn : 2 ≤ n) : LineMeasureUnitRadiusBound n := by
  let C : ℝ≥0 := ⟨max 1 (continuousEndpointConstant n),
    le_trans zero_le_one (le_max_left _ _)⟩
  refine ⟨C,?_,fun μ _ => ?_⟩
  · change 0 < max 1 (continuousEndpointConstant n)
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · apply (lintegral_lineMeasureEndpointKernel_le hn μ).trans
    apply mul_le_mul' ?_ le_rfl
    rw [ENNReal.coe_nnreal_eq]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)


end Kakeya4.Hard.MultilinearKakeya
