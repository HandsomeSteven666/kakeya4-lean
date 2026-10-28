import OAI.MeasureTheory.Falconer.Radial.NonendpointRadialBadDirections
import OAI.MeasureTheory.Falconer.GeneralNonendpointBadDirections

/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Radial/NonendpointRadialBadDirections.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_nonendpoint_radial_bad_directions 
    {h : ℕ} {t q C : ℝ} (hq : (h:ℝ) < q) (hqt : q < t) (ht : t-(h:ℝ) < 1) (hC : 0 ≤ C) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+2)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (w₀ : Sphere (h+2)) (G : Set (Space (h+2) × Space (h+2))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ, ‖z‖ ≤ 1/4) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∃ B : Set (Sphere (h+2)), MeasurableSet B ∧
        {w : Sphere (h+2) | ∃ S : Finset (Space (h+2)),
          (S.card:ℝ) ≤ (1/(2:ℝ)^N)^(-q-b) ∧
          ENNReal.ofReal ((1/(2:ℝ)^N)^b) ≤
            μ {z | ∃ v ∈ S, ‖perpendicularPart (w:Space (h+2)) (z-v)‖ ≤ C*(1/(2:ℝ)^N)}} ⊆ B ∧
        (μ.prod ν) (radialBadWitness w₀ G B) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
  obtain ⟨ε,b,hε,hb,N₀,hN₀⟩ := general_nonendpoint_bad_direction_envelope hq hqt ht hC
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ ν _ _ hν w₀ G hG hdiag hμ hμball hdata
  obtain ⟨B,hB,hcontains,hbound⟩ := hN₀ N hN μ hμ hμball
  refine ⟨B,hB,hcontains,?_⟩
  have hsmall : ∀ᵐ z ∂μ, originalRadialSphereLaw w₀ ν G z B ≤
      ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
    filter_upwards [hdata] with z hz
    apply hbound (originalRadialSphereLaw w₀ ν G z)
      ((originalRadialSphereLaw_mass_le w₀ ν G z).trans hν)
    intro w j hj
    rw [originalRadialSphereLaw_ball w₀ ν G z (hdiag z)]
    exact hz w j hj
  simpa only [measure_univ,mul_one] using radial_bad_witness_mass w₀ μ ν G hG B hB _ hsmall


end OAI.Falconer
