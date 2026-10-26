import Kakeya4.Hard.MultilinearKakeya.RealKernel

/-! Pointwise localization of the original full-line kernel. No geometric
transversality or distinctness is used to move a point to a nearby centre. -/

noncomputable section
open Set MeasureTheory Classical
open scoped Topology BigOperators ENNReal NNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem realKernel_le_at_center {n : ℕ} {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) {b x : E n} {a r R : ℝ}
    (hx : x ∈ Metric.closedBall b a) (hR : r+a ≤ R) :
    realKernel L w r x ≤ realKernel L w R b := by
  apply Finset.sum_le_sum
  intro t _
  split_ifs with ht hb
  · exact le_rfl
  · exfalso
    apply hb
    intro i
    exact le_trans (center_mem_tube_of_mem_closedBall (L i (t i)) b x hx (ht i)) hR
  · exact realTupleCoefficient_nonneg L w t
  · exact le_rfl

theorem endpointKernel_le_at_center {n : ℕ} (hn : 2 ≤ n)
    {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) {b x : E n}
    (hx : x ∈ Metric.closedBall b (1/2 : ℝ)) :
    (kernel L w 1 x)^endpointExponent n ≤
      ENNReal.ofReal ((realKernel L w 2 b)^endpointExponent n) := by
  have he : 0 ≤ endpointExponent n := by
    unfold endpointExponent
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact (one_div_pos.mpr (by linarith)).le
  rw [← ENNReal.ofReal_rpow_of_nonneg (realKernel_nonneg L w 2 b) he]
  apply ENNReal.rpow_le_rpow _ he
  rw [← ofReal_realKernel]
  exact ENNReal.ofReal_le_ofReal (realKernel_le_at_center L w hx (by norm_num))

/-- A finite cover bounds the integral by the sum of constant ball majorants.
Overlap causes no loss because only an upper bound for the integral is used. -/
theorem setLIntegral_endpointKernel_le_ball_cover {n : ℕ} (hn : 2 ≤ n)
    {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0)
    {K : Set (E n)} (hK : MeasurableSet K) (s : Finset (E n))
    (hcover : K ⊆ ⋃ c ∈ s, Metric.closedBall c (1/2 : ℝ)) :
    (∫⁻ x in K, (kernel L w 1 x)^endpointExponent n ∂volume) ≤
      volume (Metric.closedBall (0 : E n) (1/2 : ℝ)) *
        ∑ c ∈ s, ENNReal.ofReal ((realKernel L w 2 c)^endpointExponent n) := by
  rw [← lintegral_indicator hK]
  calc
    _ ≤ ∫⁻ x, ∑ c ∈ s, (Metric.closedBall c (1/2 : ℝ)).indicator
        (fun _ => ENNReal.ofReal ((realKernel L w 2 c)^endpointExponent n)) x ∂volume := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx]
        obtain ⟨c,hc,hxc⟩ := mem_iUnion₂.mp (hcover hx)
        have hsingle := Finset.single_le_sum (s := s)
          (f := fun d => (Metric.closedBall d (1/2 : ℝ)).indicator
            (fun _ => ENNReal.ofReal ((realKernel L w 2 d)^endpointExponent n)) x)
          (fun _ _ => zero_le) hc
        rw [Set.indicator_of_mem hxc] at hsingle
        exact (endpointKernel_le_at_center hn L w hxc).trans hsingle
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
