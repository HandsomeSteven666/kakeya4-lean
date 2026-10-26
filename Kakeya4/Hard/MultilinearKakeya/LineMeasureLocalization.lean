import Kakeya4.Hard.MultilinearKakeya.LineMeasureHolder

/-! Pointwise and finite-cover localization for the actual integral line-law
kernel. Each line law is arbitrary; moving the spatial point moves no measure. -/

noncomputable section
open Set MeasureTheory Classical
open scoped Topology BigOperators ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem lineMeasureKernel_le_at_center {n : ℕ} (μ : Fin n → Measure (LineParameter n))
    {b x : E n} {a r R : ℝ} (hx : x ∈ Metric.closedBall b a) (hR : r+a ≤ R) :
    lineMeasureKernel μ r x ≤ lineMeasureKernel μ R b := by
  apply lintegral_mono
  intro p
  change lineMeasureIntegrand n r (p,x) ≤ lineMeasureIntegrand n R (p,b)
  rw [lineMeasureIntegrand_eq_tupleRegion r p x,lineMeasureIntegrand_eq_tupleRegion R p b]
  by_cases ht : ∀ i, x ∈ (p i).toLine.tube r
  · have hb : ∀ i, b ∈ (p i).toLine.tube R := fun i =>
      le_trans (center_mem_tube_of_mem_closedBall (p i).toLine b x hx (ht i)) hR
    rw [Set.indicator_of_mem (show x ∈ tupleRegion (fun i => (p i).toLine) r from ht),
      Set.indicator_of_mem (show b ∈ tupleRegion (fun i => (p i).toLine) R from hb)]
  · rw [Set.indicator_of_notMem (show x ∉ tupleRegion (fun i => (p i).toLine) r from ht)]
    exact zero_le

theorem lineMeasureEndpointKernel_le_at_center {n : ℕ} (hn : 2 ≤ n)
    (μ : Fin n → Measure (LineParameter n)) [∀ i, IsFiniteMeasure (μ i)]
    {b x : E n} (hx : x ∈ Metric.closedBall b (1/2 : ℝ)) :
    (lineMeasureKernel μ 1 x)^endpointExponent n ≤
      ENNReal.ofReal ((lineMeasureKernel μ 2 b).toReal^endpointExponent n) := by
  have he : 0 ≤ endpointExponent n := by
    unfold endpointExponent
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact (one_div_pos.mpr (by linarith)).le
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg he,
    ENNReal.ofReal_toReal (lineMeasureKernel_ne_top hn μ 2 b)]
  exact ENNReal.rpow_le_rpow (lineMeasureKernel_le_at_center μ hx (by norm_num)) he

/-- A finite cover bounds the integral by the sum of constant ball majorants.
Overlap causes no loss because only an upper bound for the integral is used. -/
theorem setLIntegral_lineMeasureEndpointKernel_le_ball_cover {n : ℕ} (hn : 2 ≤ n)
    (μ : Fin n → Measure (LineParameter n)) [∀ i, IsFiniteMeasure (μ i)]
    {K : Set (E n)} (hK : MeasurableSet K) (s : Finset (E n))
    (hcover : K ⊆ ⋃ c ∈ s, Metric.closedBall c (1/2 : ℝ)) :
    (∫⁻ x in K, (lineMeasureKernel μ 1 x)^endpointExponent n ∂volume) ≤
      volume (Metric.closedBall (0 : E n) (1/2 : ℝ)) *
        ∑ c ∈ s, ENNReal.ofReal (((lineMeasureKernel μ 2 c).toReal)^endpointExponent n) := by
  rw [← lintegral_indicator hK]
  calc
    _ ≤ ∫⁻ x, ∑ c ∈ s, (Metric.closedBall c (1/2 : ℝ)).indicator
        (fun _ => ENNReal.ofReal (((lineMeasureKernel μ 2 c).toReal)^endpointExponent n)) x ∂volume := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx]
        obtain ⟨c,hc,hxc⟩ := mem_iUnion₂.mp (hcover hx)
        have hsingle := Finset.single_le_sum (s := s)
          (f := fun d => (Metric.closedBall d (1/2 : ℝ)).indicator
            (fun _ => ENNReal.ofReal (((lineMeasureKernel μ 2 d).toReal)^endpointExponent n)) x)
          (fun _ _ => zero_le) hc
        rw [Set.indicator_of_mem hxc] at hsingle
        exact (lineMeasureEndpointKernel_le_at_center hn μ hxc).trans hsingle
      · rw [Set.indicator_of_notMem hx]
        exact zero_le
    _ = _ := by
      rw [lintegral_finsetSum _ (fun c _ => measurable_const.indicator measurableSet_closedBall)]
      simp_rw [lintegral_indicator_const measurableSet_closedBall,
        Measure.addHaar_closedBall_center volume]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      exact mul_comm _ _

end Kakeya4.Hard.MultilinearKakeya
