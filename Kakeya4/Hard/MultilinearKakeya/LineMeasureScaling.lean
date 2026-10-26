import Kakeya4.Hard.MultilinearKakeya.ContinuousLineMeasureEndpoint
import Kakeya4.Hard.MultilinearKakeya.LineMeasurePushforward

/-! Exact radius scaling of arbitrary finite line laws. Scaling anchors leaves
unit directions, determinant weights and all input measure masses unchanged. -/

noncomputable section
open Set MeasureTheory Classical
open scoped Topology BigOperators ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

def LineParameter.dilate {n : ℕ} (c : ℝ) (p : LineParameter n) : LineParameter n :=
  (c • p.1,p.2)

theorem measurable_lineParameter_dilate (n : ℕ) (c : ℝ) :
    Measurable (LineParameter.dilate (n := n) c) := by
  unfold LineParameter.dilate
  fun_prop

theorem LineParameter.toLine_dilate {n : ℕ} (p : LineParameter n) (c : ℝ) :
    (p.dilate c).toLine = p.toLine.dilate c := rfl

theorem lineMeasureIntegrand_dilate {n : ℕ} (p : Fin n → LineParameter n)
    (c : ℝ) (hc : 0 < c) (r : ℝ) (x : E n) :
    lineMeasureIntegrand n (c*r) ((fun i => (p i).dilate c),c • x) =
      lineMeasureIntegrand n r (p,x) := by
  rw [lineMeasureIntegrand_eq_tupleRegion,lineMeasureIntegrand_eq_tupleRegion]
  have he := mem_tupleRegion_dilate (fun i => (p i).toLine) c hc r x
  have hmem : c • x ∈ tupleRegion (fun i => ((p i).dilate c).toLine) (c*r) ↔
      x ∈ tupleRegion (fun i => (p i).toLine) r := he
  by_cases hx : x ∈ tupleRegion (fun i => (p i).toLine) r
  · rw [Set.indicator_of_mem hx,Set.indicator_of_mem (hmem.mpr hx)]
    rfl
  · rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem (mt hmem.mp hx)]

theorem lineMeasureKernel_dilate {n : ℕ}
    (μ : Fin n → Measure (LineParameter n)) [∀ i, IsFiniteMeasure (μ i)]
    (c : ℝ) (hc : 0 < c) (r : ℝ) (x : E n) :
    lineMeasureKernel (fun i => (μ i).map (LineParameter.dilate c)) (c*r) (c • x) =
      lineMeasureKernel μ r x := by
  rw [lineMeasureKernel_map_parameters μ (fun _ => LineParameter.dilate c)
    (fun _ => measurable_lineParameter_dilate n c)]
  exact lintegral_congr (fun p => lineMeasureIntegrand_dilate p c hc r x)

theorem lineMeasureEndpointIntegral_radius_reduction {n : ℕ}
    (μ : Fin n → Measure (LineParameter n)) [∀ i, IsFiniteMeasure (μ i)]
    (r : ℝ) (hr : 0 < r) :
    (∫⁻ x, (lineMeasureKernel μ r x)^endpointExponent n ∂volume) =
      ENNReal.ofReal (r^n) * ∫⁻ x,
        (lineMeasureKernel (fun i => (μ i).map (LineParameter.dilate r⁻¹)) 1 x)^endpointExponent n ∂volume := by
  have he (x : E n) :
      lineMeasureKernel (fun i => (μ i).map (LineParameter.dilate r⁻¹)) 1 (r⁻¹ • x) =
        lineMeasureKernel μ r x := by
    simpa only [inv_mul_cancel₀ hr.ne'] using lineMeasureKernel_dilate μ r⁻¹ (inv_pos.mpr hr) r x
  simp_rw [← he]
  exact lintegral_inverse_dilation n r hr _ (measurable_lineMeasureEndpointKernel _ 1 _)

theorem lineMeasureEndpointBound_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    LineMeasureEndpointBound n := by
  obtain ⟨C,hC,h⟩ := lineMeasureUnitRadiusBound_of_two_le hn
  refine ⟨C,hC,fun μ _ r hr => ?_⟩
  rw [lineMeasureEndpointIntegral_radius_reduction μ r hr]
  have hd := h (fun i => (μ i).map (LineParameter.dilate r⁻¹))
  simp_rw [lineLaw_map_univ _ _ (measurable_lineParameter_dilate n r⁻¹)] at hd
  exact (mul_le_mul' le_rfl hd).trans_eq (by ac_rfl)

def LineMeasureManuscriptBound : Prop := ∀ n : ℕ, 2 ≤ n → n ≤ 4 → LineMeasureEndpointBound n

theorem lineMeasureManuscriptBound : LineMeasureManuscriptBound :=
  fun _ hn _ => lineMeasureEndpointBound_of_two_le hn

end Kakeya4.Hard.MultilinearKakeya
