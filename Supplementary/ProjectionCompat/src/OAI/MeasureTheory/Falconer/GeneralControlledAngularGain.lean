import OAI.MeasureTheory.Falconer.Angular.ControlledAngularGain
import OAI.MeasureTheory.Falconer.GeneralGaussianPlanarExclusion

/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Angular/ControlledAngularGain.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_controlled_dyadic_angular_gain
     {h : ℕ} {t q : ℝ}
    (hq : (h:ℝ) < q) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (w₀ : Sphere (h+2)) (B : Space h →ₗᵢ[ℝ] Space (h+2))
      (E : Set (Space (h+2) × Sphere (h+2)))
      (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2))
      (ρ Lt Lq K C₀ Nc Z a₀ : ℝ),
    1/(2:ℝ)^N < δ₀ → 0 ≤ ρ → 1/(2:ℝ)^N ≤ ρ →
    (∀ i, inner ℝ (w₀:Space (h+2)) (B (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0) →
    (∀ᵐ w ∂ν, dist w w₀ ≤ ρ) →
    (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2 →
    4*(h:ℝ)*(1/(2:ℝ)^N)+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 →
    (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    0 ≤ Lt → 0 ≤ Lq →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lt*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lq*(1/(2:ℝ)^j)^q)) →
    (∀ᵐ u : Sphere (h+2) × Sphere (h+2) ∂ν.prod ν,
      0 ≤ inner ℝ (u.1:Space (h+2)) (u.2:Space (h+2))) →
    0 < K → 0 < Nc → 0 < Z →
    (4*gaussianVectorBandConstant)^h*Lt*gaussianFrostmanFactor h t ≤ C₀ →
    (2*gaussianPairBandConstant)^h*Lq*gaussianFrostmanFactor h q ≤ C₀ →
    (2*gaussianPairBandConstant)^h*(|Lq*gaussianFrostmanFactor h q|+1) ≤ C₀ →
    ((N+1:ℕ):ℝ)*C₀ ≤ K → C₀ ≤ K → 4*(1+2*(2:ℝ)^h+1) ≤ K →
    (1/4)*((h+2:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N ≤ Z →
    1 ≤ a₀ → 1 ≤ 4*K^10*(2*Z)^h → 4+8*(h:ℝ) ≤ a₀ →
    (4*K^10*(2*Z)^h)*(4*a₀)^(t-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-η) →
    (4*K^10*(2*Z)^h)*(8*a₀)^(q-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-η) →
    (1/(2:ℝ)^N)^η < 1/(4*K^10*(2*Z)^h) →
    K^11*(Nc*(2*((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+
      (C*(1/(2:ℝ)^N))*((h+2:ℝ)*(2*ρ)+1)))^h) ≤ (1/(2:ℝ)^N)^(-(q-(h:ℝ))-η) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc) →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant (h+1) ρ^h)*
      (μ.prod ν) E < ENNReal.ofReal (1/K) := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := general_gaussian_planar_slice_exclusion
    (sub_pos.mpr hq) (by linarith : q-(h:ℝ) < t-(h:ℝ)) ht C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro N κ _ _ μ ν _ _ w₀ B E J a ρ Lt Lq K C₀ Nc Z a₀ hδsmall hρ hδρ
    hB hν hstable hchart hμ hμmass hνmass hLt hLq hμball hνball hpair
    hK hNc hZ hCpoint hCdir hCmass hcard hC₀ hlarge hZbox ha₀ hH haK hpcoef hqcoef hlow
    hTbound hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  let ε : ℝ := (h+2:ℝ)*(2*ρ)
  let M : ℝ := ε+1
  let R : ℝ := δ+(2*(1/4))*δ+(C*δ)*M
  let T : ℝ := K^11*(Nc*(2*R)^h)
  let rows : Fin h → Space (h+2) := fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hrows (i : Fin h) : ‖rows i‖ ≤ 1 := by
    rw [show rows i = B (EuclideanSpace.basisFun (Fin h) ℝ i) from rfl,B.norm_map]
    exact ((EuclideanSpace.basisFun (Fin h) ℝ).norm_eq_one i).le
  have hwB : ∀ᵐ (w : Sphere (h+2)) ∂ν, ∀ i, |inner ℝ (w:Space (h+2)) (rows i)| ≤ ρ := by
    filter_upwards [hν] with w hw i
    exact transverse_frame_chart_bound B (w₀:Space (h+2)) hB hw i
  by_contra hnot
  have hmean := le_of_not_gt hnot
  have hfactor : ENNReal.ofReal ((2:ℝ)^h)*μ univ ≤ ENNReal.ofReal ((2:ℝ)^h) := by
    simpa only [mul_one] using mul_le_mul' le_rfl hμmass
  have hcast : ((h+1:ℕ):ℝ)+1 = (h+2:ℝ) := by push_cast; ring
  obtain ⟨A,hA,z,_,hbig⟩ := dyadic_original_slice_selection rows hrows μ ν N
    (by norm_num : (1/4:ℝ) < 1/2) hμ hδρ hwB hLt hLq (hq.trans hqt) hq hμmass hνmass
    hμball hνball hpair hK (by positivity : 0 ≤ (2:ℝ)^h) hNc hR hCpoint hCdir hCmass
    hcard hC₀ hlarge hfactor E hE J hJ a hJN hmean
    (by rw [hcast]; exact gaussianSelectionThreshold_uniform h hK hZ hZbox)
  rw [hcast] at hA
  obtain ⟨e,_,he⟩ := gaussian_two_dimensional_slice_chart B A w₀ hε hδ.le hρ hB hA hstable hchart
  have hbound := row_kernel_projection_bound A B hA hstable
  have hsmall : 2*((h:ℝ)*δ) < 1 := by
    have hpos : 0 ≤ 4*(h:ℝ)*ε := by positivity
    change 4*(h:ℝ)*δ+ρ+4*(h:ℝ)*ε ≤ 1/4 at hchart
    nlinarith
  have hchartAE : ∀ᵐ (w : Sphere (h+2)) ∂ν, w ∈ gaussianDirectionBand A δ →
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2))))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2)))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 := by
    filter_upwards [hν] with w hw hband
    exact he w hband hw
  have hupper := hgain N (h+2) h κ A z e μ ν E J a K ((2*Z)^h) M T a₀ hδsmall
    hK (by positivity) hM (by dsimp [T]; positivity) hTbound ha₀ hH haK hpcoef hqcoef hlow
    hE hJ (gaussianRowNeighborhood_norm rows hrows hA) hbound hsmall hEb hanchors hcover hμ hchartAE
  simp only [gaussianSelectionThreshold,gaussianPruningWeight_eq] at hbig
  exact (not_lt_of_ge hupper) hbig


end OAI.Falconer
