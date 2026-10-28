import OAI.MeasureTheory.Falconer.Estimates.NonendpointOriginalMiddle
import OAI.MeasureTheory.Falconer.GeneralNonendpointMiddleRadial

/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Estimates/NonendpointOriginalMiddle.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_nonendpoint_original_middle_pruning 
    {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hqt : q < t) (ht : t-(h:ℝ) < 1) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+2)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (_w₀ : Sphere (h+2)) (c : Space (h+2)) (a : ℝ), 0 < a →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z-c‖ ≤ 1/(4*a)) →
      (∀ᵐ z ∂μ, ‖z-c‖ ≤ 1/(4*a)) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x ((1/(2:ℝ)^j)/a)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/(a*r) ≤ 1/(2:ℝ)^N →
      (a*H)*θ ≤ 1/(2:ℝ)^N →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖c-x‖ ∧ ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^N)^b) ∧
        ∀ p ∈ G', radialCollisionMass μ θ p ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(q+b/2)) := by
  obtain ⟨ε,b,hε,hb,N₀,hN₀⟩ := general_nonendpoint_middle_radial_pruning hq hqt ht
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ ν _ _ hν w₀ c a ha G hG hgeom hμ hball hcap r H θ hr hfreeze hwidth hpin
  let e := radialZoom a ha.ne' c
  have hν' : Measure.map e ν univ ≤ 1 := by
    simpa only [Measure.map_apply e.measurable MeasurableSet.univ,preimage_univ] using hν
  have hgeom' : ∀ z x, (z,x) ∈ zoomPairSet e G → z ≠ x ∧ ‖z‖ ≤ 1/4 := by
    intro z x hx
    have hh := hgeom (e.symm z) (e.symm x) hx
    refine ⟨fun he => hh.1 (congrArg e.symm he),?_⟩
    have hn := radialZoom_quarter_bound ha c (e.symm z) hh.2
    change ‖e (e.symm z)‖ ≤ 1/4 at hn
    simpa only [e.apply_symm_apply] using hn
  have hμ' : ∀ᵐ z ∂Measure.map e μ, ‖z‖ ≤ 1/4 := by
    rw [radialZoom_ae_iff μ ha]
    filter_upwards [hμ] with z hz
    exact radialZoom_quarter_bound ha c z hz
  have hball' : ∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      Measure.map e μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t) := by
    intro x j hj
    rw [radialZoom_ball_apply μ ha]
    exact hball _ j hj
  have hcap' : ∀ᵐ z ∂Measure.map e μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      Measure.map e ν {x | (z,x) ∈ zoomPairSet e G ∧
        dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q) := by
    rw [radialZoom_ae_iff μ ha]
    filter_upwards [hcap] with z hz
    intro w j hj
    rw [radialZoom_reverse_cap ν ha c z w _ G hG]
    exact hz w j hj
  have hpin' : ∀ x, (∃ z, (z,x) ∈ zoomPairSet e G) →
      a*r ≤ ‖(0:Space (h+2))-x‖ ∧ ∀ᵐ y ∂Measure.map e μ, ‖y-x‖ ≤ a*H := by
    intro x hx
    obtain ⟨z,hz⟩ := hx
    have hp := hpin (e.symm x) ⟨e.symm z,hz⟩
    have he : e (e.symm x) = x := e.apply_symm_apply x
    refine ⟨?_,?_⟩
    · have hd := radialZoom_pin_distance ha c (e.symm x) hp.1
      change a*r ≤ ‖(0:Space (h+2))-e (e.symm x)‖ at hd
      simpa only [he] using hd
    · have hb := radialZoom_pair_ae_bound μ ha c (e.symm x) hp.2
      change ∀ᵐ y ∂Measure.map e μ, ‖y-e (e.symm x)‖ ≤ a*H at hb
      simpa only [he] using hb
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := hN₀ N hN (Measure.map e μ) (Measure.map e ν) hν'
    w₀ (zoomPairSet e G) (zoomPairSet_measurable e hG) hgeom' hμ' hball' hcap'
    (a*r) (a*H) θ (mul_pos ha hr) hfreeze hwidth hpin'
  exact radial_pruning_unzoom μ ν ha c G hG G' hG' hsub θ _ _ hdel hbound


end OAI.Falconer
