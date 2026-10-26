import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Kakeya4.Construction.Combinatorics.BoxParameterBudget
import Kakeya4.Construction.Combinatorics.LineCap
import Kakeya4.Construction.Combinatorics.TruncatedConvexTest

/-!
# Source-box certificates to a sampled line-cap bound

This module composes the relevant-test source-box selector with the floor-log sampler and the
uniform line-carrier estimate.  The geometric source-box selector, weighted convex-clustering
certificate, probability budget, carrier geometry, and final integer payment remain explicit
caller inputs.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Kakeya4.Construction

/-- The explicit cardinality envelope for the quadratic orthogonal-box parameter net. -/
def orthogonalBoxSamplerNetCardBound (n : ℕ) (C α δ : ℝ) : ℝ :=
  4 ^ Module.finrank ℝ (BoxParameterSpace n) *
    ((√(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1)) / α) ^
      Module.finrank ℝ (BoxParameterSpace n) *
    (δ⁻¹) ^ (2 * Module.finrank ℝ (BoxParameterSpace n))

/-- Direct source-box-selector to all-lines line-cap interface.

Given a relevant-test source-box certificate, this theorem constructs the finite sampler boxes,
uses the caller's net-cardinality probability payment to invoke the weighted floor-log sampler,
and obtains one sample satisfying the line-carrier count bound on every unit line. This basic
interface takes a source-box selector explicitly; the source-input consumer at the end of the
file uses the proved truncated-set source-box producer and constructs the weighted certificate
from compact convex-body tests on actual segment tubes.

`tailExponent` is independent of the ambient dimension: choose it after the box-net
cardinality exponent. The hypothesis `hLtail` pays the resulting Chernoff exponent through
the logarithmic sampling constant `L`; setting it to `n` recovers the earlier interface.
-/
theorem WeightedConvexClusteringCertificate.exists_sample_with_uniform_lineCarrierBudget_of_relevant_source_box_selector
    {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {indices : Finset ι} {core : ι → Set (BoxAmbient n)} {weights : ι → ℝ}
    {scale tubeVolume : ℝ}
    (hdim : Module.finrank ℝ (BoxAmbient n) = 3)
    (δ R C α κ : ℝ) (B : ℝ≥0∞)
    (hB : B < ⊤) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hR : 0 ≤ R)
    (hindices : indices = Finset.univ)
    (hTubeBall : ∀ i ∈ indices,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (htube : 0 < tubeVolume)
    (hcommon : ∀ i ∈ indices,
      (volume (Metric.cthickening δ (core i))).toReal = tubeVolume)
    (hC : 0 ≤ C) (hκ : 0 < κ) (hα : 0 < α)
    (hscaleNet : α * δ ^ 2 ≤
      √(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1))
    (sourceBox : ∀ T : RelevantConvexTubeTest indices
        (fun i => Metric.cthickening δ (core i)),
      RelevantConvexTestSourceBox T.1 δ R C κ B)
    (weightedCert : WeightedConvexClusteringCertificate indices
      (fun i => Metric.cthickening δ (core i)) weights scale)
    (hscale : 0 < scale)
    (ell L : ℝ) (hell : 0 ≤ ell) (hδlog : Real.exp (-ell) = δ)
    (tailExponent : ℕ) (hLtail : ((tailExponent + 2 : ℕ) : ℝ) ≤ L)
    (S : ℝ)
    (hS : (∑ i ∈ Finset.univ,
      ((bernoulliInclusionProbabilitiesFromWeights weights scale hscale
        (fun i => ⟨weightedCert.weights_nonneg i,
          weightedCert.weight_le_scale i (by simp [hindices])⟩) i : unitInterval) : ℝ)) = S)
    (minSize : ℕ) (hmin : (minSize : ℝ) ≤ S / 2)
    (hnetBudget :
      ENNReal.ofReal (orthogonalBoxSamplerNetCardBound n C α δ) *
          ENNReal.ofReal (δ ^ (tailExponent + 2)) +
        ENNReal.ofReal (Real.exp (-S / 8)) < 1)
    (hcarrierVolume : ∀ o v : BoxAmbient n, ‖v‖ = 1 → ∀ i ∈ indices,
      volume (Metric.cthickening δ (core i)) =
        volume (Metric.cthickening δ (segment ℝ o (o + v))))
    (lineCapBound : ℕ)
    (hlineCapBudget :
      (ENNReal.ofReal (L * (1 + ell)) *
        (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) * B)) *
        ENNReal.ofReal (50 * R) ≤ (lineCapBound : ℝ≥0∞)) :
    ∃ ω, minSize ≤ (bernoulliProductSample ω).card ∧
      ∀ o v : BoxAmbient n, ‖v‖ = 1 →
        (lineCarrierCapFilter (bernoulliProductSample ω) core δ o v).card ≤ lineCapBound := by
  classical
  let tube : ι → Set (BoxAmbient n) := fun i => Metric.cthickening δ (core i)
  have hselector := exists_finite_orthogonalBox_sampler_cover_of_relevant_source_box_selector
    indices tube δ R C α κ B hB hδ hδ1
    (by simpa [tube] using hTubeBall) tubeVolume htube
    (by simpa [tube] using hcommon) hC hκ hα hscaleNet
    (by
      intro T
      exact sourceBox T)
  obtain ⟨N, hNcard, hNfinite,
      ⟨rep, hrepCode, hboxConvex, hboxTop, hboxVolume, hboxRatio, hboxCover⟩⟩ := hselector
  let β := {q : BoxParameterSpace n // q ∈ N}
  let boxes : Finset β := Finset.univ
  let box : β → Set (BoxAmbient n) := fun q =>
    orthogonalBox_enlargement (rep q) (orthogonalBoxNetEnlargementError n C α δ)
  let boxVolume : β → ℝ := fun q =>
    orthogonalBox_enlargementVolume (rep q) (orthogonalBoxNetEnlargementError n C α δ)
  have hcardEq : boxes.card = N.card := by
    simp [boxes, β]
  have hnetCardENN : (N.card : ℝ≥0∞) ≤
      ENNReal.ofReal (orthogonalBoxSamplerNetCardBound n C α δ) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by simpa [orthogonalBoxSamplerNetCardBound] using hNcard)
  have hbudget : (boxes.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ (tailExponent + 2)) +
      ENNReal.ofReal (Real.exp (-S / 8)) < 1 := by
    rw [hcardEq]
    calc
      (N.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ (tailExponent + 2)) +
          ENNReal.ofReal (Real.exp (-S / 8)) ≤
        ENNReal.ofReal (orthogonalBoxSamplerNetCardBound n C α δ) *
          ENNReal.ofReal (δ ^ (tailExponent + 2)) +
          ENNReal.ofReal (Real.exp (-S / 8)) := by
            gcongr
      _ < 1 := hnetBudget
  have hL2 : 2 ≤ L := by
    have hn : 2 ≤ tailExponent + 2 := by omega
    have hnReal : (2 : ℝ) ≤ ((tailExponent + 2 : ℕ) : ℝ) := by exact_mod_cast hn
    exact hnReal.trans hLtail
  have hLc : ((tailExponent + 2 : ℕ) : ℝ) ≤ L * 1 := by simpa using hLtail
  have hboxConvex' : ∀ q ∈ boxes, Convex ℝ (box q) := by
    intro q hq
    exact hboxConvex q
  have hboxVolume' : ∀ q ∈ boxes, (volume (box q)).toReal = boxVolume q := by
    intro q hq
    exact hboxVolume q
  have hboxTop' : ∀ q ∈ boxes, volume (box q) < ⊤ := by
    intro q hq
    exact hboxTop q
  have hcommon' : ∀ i ∈ indices, (volume (tube i)).toReal = tubeVolume := by
    simpa [tube] using hcommon
  have hratio : ∀ q ∈ boxes, (1 : ℝ) ≤ boxVolume q / tubeVolume := by
    intro q hq
    have h := hboxRatio q
    dsimp [boxVolume] at h ⊢
    exact h
  have hcover : ∀ K : Set (BoxAmbient n), Convex ℝ K →
      (∃ i ∈ indices, tube i ⊆ K) →
      ∃ q ∈ boxes,
        (∀ i ∈ indices, tube i ⊆ K → tube i ⊆ box q) ∧
          volume (box q) ≤
            (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) * B) * volume K := by
    intro K hK hRelevant
    obtain ⟨q, hcontains, hvol⟩ := hboxCover K hK (by simpa [tube] using hRelevant)
    refine ⟨q, Finset.mem_univ q, ?_, ?_⟩
    · simpa [tube, box] using hcontains
    · change volume (orthogonalBox_enlargement (rep q)
        (orthogonalBoxNetEnlargementError n C α δ)) ≤
          (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) * B) * volume K
      exact hvol
  have hδlog' : Real.exp (-ell) = δ := hδlog
  have hcarrierVolume' : ∀ o v : BoxAmbient n, ‖v‖ = 1 → ∀ i ∈ indices,
      volume (tube i) = volume (Metric.cthickening δ (segment ℝ o (o + v))) := by
    simpa [tube] using hcarrierVolume
  exact WeightedConvexClusteringCertificate.exists_sample_with_uniform_lineCarrierBudget_of_floor_logarithmic_box_cover
    hdim δ weightedCert hindices hscale htube ell L 1 hell hδlog' tailExponent hL2 (by norm_num) hLc
    boxes box boxVolume hboxConvex' hboxVolume' hboxTop' hcommon' hratio
    S hS minSize hmin hbudget
    (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) * B) hcover
    R hR hTubeBall
    hcarrierVolume' lineCapBound hlineCapBudget

/-- Direct source-geometry interface for the sampled line-cap theorem.  It replaces the
caller-provided source-box selector with the producer from `TruncatedConvexTest`: the only
geometric addition is a radius-`δ` ball contained in each indexed tube.  The weighted clustering
certificate, probability payment, common tube volume, carrier transfer, and final integer budget
remain explicit inputs; this theorem does not derive them from GWZ data.
-/
theorem WeightedConvexClusteringCertificate.exists_sample_with_uniform_lineCarrierBudget_of_truncated_source_geometry
    {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {indices : Finset ι} {core : ι → Set (BoxAmbient n)} {weights : ι → ℝ}
    {scale tubeVolume : ℝ}
    (hdim : Module.finrank ℝ (BoxAmbient n) = 3)
    (δ R α : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 ≤ R)
    (hindices : indices = Finset.univ)
    (hTubeBall : ∀ i ∈ indices,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (hTubeInnerBall : ∀ i ∈ indices, ∃ z : BoxAmbient n,
      Metric.closedBall z δ ⊆ Metric.cthickening δ (core i))
    (htube : 0 < tubeVolume)
    (hcommon : ∀ i ∈ indices,
      (volume (Metric.cthickening δ (core i))).toReal = tubeVolume)
    (hα : 0 < α)
    (hscaleNet : α * δ ^ 2 ≤
      √(Fintype.card (BoxParameterIndex n) : ℝ) *
        (((n : ℝ) * R + R) + 1))
    (weightedCert : WeightedConvexClusteringCertificate indices
      (fun i => Metric.cthickening δ (core i)) weights scale)
    (hscale : 0 < scale)
    (ell L : ℝ) (hell : 0 ≤ ell) (hδlog : Real.exp (-ell) = δ)
    (tailExponent : ℕ) (hLtail : ((tailExponent + 2 : ℕ) : ℝ) ≤ L)
    (S : ℝ)
    (hS : (∑ i ∈ Finset.univ,
      ((bernoulliInclusionProbabilitiesFromWeights weights scale hscale
        (fun i => ⟨weightedCert.weights_nonneg i,
          weightedCert.weight_le_scale i (by simp [hindices])⟩) i : unitInterval) : ℝ)) = S)
    (minSize : ℕ) (hmin : (minSize : ℝ) ≤ S / 2)
    (hnetBudget :
      ENNReal.ofReal (orthogonalBoxSamplerNetCardBound n ((n : ℝ) * R + R) α δ) *
          ENNReal.ofReal (δ ^ (tailExponent + 2)) +
        ENNReal.ofReal (Real.exp (-S / 8)) < 1)
    (hcarrierVolume : ∀ o v : BoxAmbient n, ‖v‖ = 1 → ∀ i ∈ indices,
      volume (Metric.cthickening δ (core i)) =
        volume (Metric.cthickening δ (segment ℝ o (o + v))))
    (lineCapBound : ℕ)
    (hlineCapBudget :
      (ENNReal.ofReal (L * (1 + ell)) *
        (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n
          ((n : ℝ) * R + R) α 1) *
          ENNReal.ofReal ((2 : ℝ)^n * (n.factorial : ℝ)))) *
        ENNReal.ofReal (50 * R) ≤ (lineCapBound : ℝ≥0∞)) :
    ∃ ω, minSize ≤ (bernoulliProductSample ω).card ∧
      ∀ o v : BoxAmbient n, ‖v‖ = 1 →
        (lineCarrierCapFilter (bernoulliProductSample ω) core δ o v).card ≤ lineCapBound := by
  let C : ℝ := (n : ℝ) * R + R
  let B : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ)^n * (n.factorial : ℝ))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg n) hR) hR
  have hB : B < ⊤ := by
    dsimp [B]
    exact ENNReal.ofReal_lt_top
  have hκ : (0 : ℝ) < 1 := by norm_num
  have hsourceBox : ∀ T : RelevantConvexTubeTest indices
      (fun i => Metric.cthickening δ (core i)),
      RelevantConvexTestSourceBox T.1 δ R C 1 B := by
    intro T
    simpa [C, B] using
      (RelevantConvexTubeTest.sourceBoxSelector
        (indices := indices) (tube := fun i => Metric.cthickening δ (core i))
        δ R tubeVolume hδ hR hTubeBall hTubeInnerBall htube hcommon T)
  exact WeightedConvexClusteringCertificate.exists_sample_with_uniform_lineCarrierBudget_of_relevant_source_box_selector
    hdim δ R C α 1 B hB hδ hδ1 hR hindices hTubeBall htube hcommon hC hκ hα
    (by simpa [C] using hscaleNet) hsourceBox weightedCert hscale ell L hell hδlog
    tailExponent hLtail S hS minSize hmin hnetBudget hcarrierVolume lineCapBound
    (by simpa [C, B] using hlineCapBudget)

/-- The scale-independent coefficient in the quadratic box-net cardinality envelope.
The geometric parameters `C` and `α` must be fixed before the sampling scale. -/
def orthogonalBoxSamplerNetCoefficient (n : ℕ) (C α : ℝ) : ℝ :=
  4 ^ Module.finrank ℝ (BoxParameterSpace n) *
    ((√(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1)) / α) ^
      Module.finrank ℝ (BoxParameterSpace n)

/-- With tail exponent twice the box-parameter dimension, the net-cardinality loss cancels
exactly and the total box-failure envelope is the fixed coefficient times `δ²`. -/
theorem orthogonalBoxSamplerNetCardBound_mul_tailPow
    (n : ℕ) (C α δ : ℝ) (hδ : δ ≠ 0) :
    orthogonalBoxSamplerNetCardBound n C α δ *
        δ ^ (2 * Module.finrank ℝ (BoxParameterSpace n) + 2) =
      orthogonalBoxSamplerNetCoefficient n C α * δ ^ 2 := by
  let D := Module.finrank ℝ (BoxParameterSpace n)
  let A := orthogonalBoxSamplerNetCoefficient n C α
  change (A * (δ⁻¹) ^ (2 * D)) * δ ^ (2 * D + 2) = A * δ ^ 2
  have hcancel : (δ⁻¹) ^ (2 * D) * δ ^ (2 * D) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hδ, one_pow]
  rw [pow_add]
  calc
    _ = A * (((δ⁻¹) ^ (2 * D) * δ ^ (2 * D)) * δ ^ 2) := by ring
    _ = A * δ ^ 2 := by rw [hcancel, one_mul]

/-- In the manuscript's large expected-size branch, `L ≥ 32` pays the actual Bernoulli
sample-size lower tail by less than `1/4`. The small-size branch is not asserted here. -/
theorem bernoulliSample_lowerTail_lt_quarter_of_logarithmic_size
    {ell L S : ℝ} (hell : 0 ≤ ell) (hL : 32 ≤ L) (hS : L * (1 + ell) ≤ S) :
    Real.exp (-S / 8) < 1 / 4 := by
  have hS32 : 32 ≤ S := by nlinarith
  have hfour : (4 : ℝ) < Real.exp 4 := lt_of_lt_of_le (by norm_num) (Real.add_one_le_exp 4)
  have htail : Real.exp (-4) < (1 / 4 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4) hfour
  exact (Real.exp_le_exp.mpr (by linarith : -S / 8 ≤ -4)).trans_lt htail

/-- A single positive scale threshold, fixed before `δ,ell,L,S`, pays both the quadratic
box-net union bound and the actual sample-size lower tail. Constants are uniform for fixed
`n,C,α`; if geometric parameters vary with scale a new envelope is required. -/
theorem exists_small_scale_orthogonalBoxSamplerNetBudget
    (n : ℕ) (C α : ℝ) (hC : 0 ≤ C) (hα : 0 < α) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ ell L S : ℝ, 0 < δ → δ < δ₀ → 0 ≤ ell → 32 ≤ L → L * (1 + ell) ≤ S →
        ENNReal.ofReal (orthogonalBoxSamplerNetCardBound n C α δ) *
            ENNReal.ofReal (δ ^ (2 * Module.finrank ℝ (BoxParameterSpace n) + 2)) +
          ENNReal.ofReal (Real.exp (-S / 8)) < 1 := by
  let A := orthogonalBoxSamplerNetCoefficient n C α
  have hA : 0 ≤ A := by dsimp [A, orthogonalBoxSamplerNetCoefficient]; positivity
  have hden : 0 < 4 * (A + 1) := by positivity
  refine ⟨min 1 (1 / (4 * (A + 1))),
    lt_min (by norm_num) (one_div_pos.mpr hden), min_le_left _ _, ?_⟩
  intro δ ell L S hδ hsmall hell hL hS
  have hδ1 : δ ≤ 1 := (hsmall.trans_le (min_le_left _ _)).le
  have hpay : δ * (4 * (A + 1)) < 1 :=
    (lt_div_iff₀ hden).mp (hsmall.trans_le (min_le_right _ _))
  have hnet : A * δ ^ 2 < 1 / 4 := by
    have hsquare : δ ^ 2 ≤ δ := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsquare hA
    nlinarith
  have htail := bernoulliSample_lowerTail_lt_quarter_of_logarithmic_size hell hL hS
  have hnetNonneg : 0 ≤ orthogonalBoxSamplerNetCardBound n C α δ := by
    unfold orthogonalBoxSamplerNetCardBound
    positivity
  have hpowNonneg : 0 ≤ δ ^ (2 * Module.finrank ℝ (BoxParameterSpace n) + 2) :=
    pow_nonneg hδ.le _
  rw [← ENNReal.ofReal_mul hnetNonneg,
    ← ENNReal.ofReal_add (mul_nonneg hnetNonneg hpowNonneg) (Real.exp_pos _).le]
  have hreal : orthogonalBoxSamplerNetCardBound n C α δ *
      δ ^ (2 * Module.finrank ℝ (BoxParameterSpace n) + 2) + Real.exp (-S / 8) < 1 := by
    rw [orthogonalBoxSamplerNetCardBound_mul_tailPow n C α δ hδ.ne']
    change A * δ ^ 2 + Real.exp (-S / 8) < 1
    linarith
  exact (ENNReal.ofReal_lt_one).mpr hreal

/-- Actual closed-thickened segment tubes satisfy all geometric fields of the weighted
sampling certificate. The only clustering input is the manuscript's compact convex-body
weighted inequality; convexity, finite positive tube volume and the finite-test extension are
proved here, without assuming a pre-existing certificate or distinctness of the segments. -/
theorem weightedConvexClusteringCertificate_of_segment_tubes
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {ι : Type*} [DecidableEq ι] (indices : Finset ι) (a b : ι → E)
    (δ scale : ℝ) (weights : ι → ℝ) (hδ : 0 < δ) (hscale : 0 ≤ scale)
    (hweights : ∀ i, 0 ≤ weights i)
    (hbody : ∀ K : Set E, IsCompact K → Convex ℝ K → 0 < volume K →
      (∑ i ∈ tubeIndicesContainedInSet indices
          (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) K,
        weights i * (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal) ≤
        scale * (volume K).toReal) :
    WeightedConvexClusteringCertificate indices
      (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) weights scale := by
  have hcompact (i : ι) : IsCompact (segment ℝ (a i) (b i)) := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  have htop (i : ι) : volume (Metric.cthickening δ (segment ℝ (a i) (b i))) ≠ ⊤ :=
    ((hcompact i).isBounded.cthickening.measure_lt_top).ne
  have hpos (i : ι) : 0 < (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal := by
    have hball : Metric.ball (a i) δ ⊆ Metric.cthickening δ (segment ℝ (a i) (b i)) :=
      Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_cthickening (left_mem_segment ℝ _ _) δ)
    have hvol := (Metric.measure_ball_pos (volume : Measure E) (a i) hδ).trans_le (measure_mono hball)
    exact ENNReal.toReal_pos hvol.ne' (htop i)
  exact weightedConvexClusteringCertificate_of_compact_convex_body_bound indices
    (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) weights scale hscale hweights
    (fun i => (convex_segment (a i) (b i)).cthickening δ) hpos htop hbody

/-- The three-dimensional box-parameter space has dimension fifteen, independently of scale. -/
theorem orthogonalBoxParameter_finrank_three :
    Module.finrank ℝ (BoxParameterSpace 3) = 15 := by
  simp [BoxParameterSpace, BoxParameterIndex]

/-- The actual three-dimensional source-box constant `C=4R` admits a uniform small-scale
sampling budget with tail exponent `30` and logarithmic sampling constant `32`. The expected
size inequality is the source proof's explicit large-size branch. -/
theorem exists_small_scale_orthogonalBoxSamplerNetBudget_three
    (R α : ℝ) (hR : 0 ≤ R) (hα : 0 < α) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ ell S : ℝ, 0 < δ → δ < δ₀ → 0 ≤ ell → 32 * (1 + ell) ≤ S →
        ENNReal.ofReal (orthogonalBoxSamplerNetCardBound 3 (4 * R) α δ) *
            ENNReal.ofReal (δ ^ (30 + 2)) +
          ENNReal.ofReal (Real.exp (-S / 8)) < 1 := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hbudget⟩ :=
    exists_small_scale_orthogonalBoxSamplerNetBudget 3 (4 * R) α (by positivity) hα
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ ell S hδ hsmall hell hS
  simpa [orthogonalBoxParameter_finrank_three] using
    hbudget δ ell 32 S hδ hsmall hell (le_refl 32) hS

/-- The actual weighted shade mass is bounded by the total original weight times the
measure of its actual union. Repeated indices and different shades on equal tubes are retained.
This uses only outer-measure monotonicity, so measurability is not an extra premise. -/
theorem weightedShadeMass_le_totalWeight_mul_union
    {E ι : Type*} [MeasurableSpace E] [DecidableEq ι]
    (μ : Measure E) (indices : Finset ι) (weights : ι → ℝ) (shade : ι → Set E)
    (hweights : ∀ i ∈ indices, 0 ≤ weights i) :
    (∑ i ∈ indices, ENNReal.ofReal (weights i) * μ (shade i)) ≤
      ENNReal.ofReal (∑ i ∈ indices, weights i) * μ (⋃ i ∈ indices, shade i) := by
  rw [ENNReal.ofReal_sum_of_nonneg hweights, Finset.sum_mul]
  exact Finset.sum_le_sum fun i hi => mul_le_mul' le_rfl (measure_mono
    (fun x hx => Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hx⟩⟩))

/-- The manuscript's deterministic small-expected-size branch, for the actual indexed
shadings. Here `S = ∑ weights / scale` is expanded, and the original weights and union are
unchanged. Logarithm absorption and the large-size extraction are separate obligations. -/
theorem weightedShadeMass_le_logarithmic_union_of_small_normalizedWeight
    {E ι : Type*} [MeasurableSpace E] [DecidableEq ι]
    (μ : Measure E) (indices : Finset ι) (weights : ι → ℝ) (shade : ι → Set E)
    (scale L ell : ℝ) (hscale : 0 < scale)
    (hweights : ∀ i ∈ indices, 0 ≤ weights i)
    (hsmall : (∑ i ∈ indices, weights i / scale) ≤ L * (1 + ell)) :
    (∑ i ∈ indices, ENNReal.ofReal (weights i) * μ (shade i)) ≤
      ENNReal.ofReal (scale * L * (1 + ell)) * μ (⋃ i ∈ indices, shade i) := by
  have htotal : (∑ i ∈ indices, weights i) ≤ scale * L * (1 + ell) := by
    rw [← Finset.sum_div] at hsmall
    have h := (div_le_iff₀ hscale).mp hsmall
    nlinarith
  exact (weightedShadeMass_le_totalWeight_mul_union μ indices weights shade hweights).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal htotal) le_rfl)

/-- The source numerator estimate for actual shadings in common-volume tubes. The original
indexed weights, including repetitions, are preserved, and `scale * S` is exactly their sum. -/
theorem weightedShadeMass_le_scale_normalizedWeight_mul_tubeVolume
    {E ι : Type*} [MeasurableSpace E] [DecidableEq ι]
    (μ : Measure E) (indices : Finset ι) (weights : ι → ℝ) (tube shade : ι → Set E)
    (scale tubeVolume : ℝ) (hscale : 0 < scale)
    (hweights : ∀ i ∈ indices, 0 ≤ weights i)
    (hshade : ∀ i ∈ indices, shade i ⊆ tube i)
    (hvolume : ∀ i ∈ indices, μ (tube i) = ENNReal.ofReal tubeVolume) :
    (∑ i ∈ indices, ENNReal.ofReal (weights i) * μ (shade i)) ≤
      ENNReal.ofReal (scale * (∑ i ∈ indices, weights i / scale) * tubeVolume) := by
  have hnorm : scale * (∑ i ∈ indices, weights i / scale) = ∑ i ∈ indices, weights i := by
    rw [← Finset.sum_div]
    field_simp
  rw [hnorm]
  calc
    _ ≤ ∑ i ∈ indices, ENNReal.ofReal (weights i) * ENNReal.ofReal tubeVolume := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul' le_rfl ((measure_mono (hshade i hi)).trans_eq (hvolume i hi))
    _ = _ := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg hweights,
        ← ENNReal.ofReal_mul (Finset.sum_nonneg hweights)]

/-- Any proved bound on normalized source weight gives the corresponding original shade-mass
budget. In particular, `B` may be a constant times the cardinality of a retained subfamily. -/
theorem weightedShadeMass_le_of_normalizedWeight_bound
    {E ι : Type*} [MeasurableSpace E] [DecidableEq ι]
    (μ : Measure E) (indices : Finset ι) (weights : ι → ℝ) (tube shade : ι → Set E)
    (scale tubeVolume B : ℝ) (hscale : 0 < scale) (htube : 0 ≤ tubeVolume)
    (hweights : ∀ i ∈ indices, 0 ≤ weights i)
    (hshade : ∀ i ∈ indices, shade i ⊆ tube i)
    (hvolume : ∀ i ∈ indices, μ (tube i) = ENNReal.ofReal tubeVolume)
    (hB : (∑ i ∈ indices, weights i / scale) ≤ B) :
    (∑ i ∈ indices, ENNReal.ofReal (weights i) * μ (shade i)) ≤
      ENNReal.ofReal (scale * B * tubeVolume) := by
  apply (weightedShadeMass_le_scale_normalizedWeight_mul_tubeVolume μ indices weights
    tube shade scale tubeVolume hscale hweights hshade hvolume).trans
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hscale.le) htube)

/-- Apply the actual finite conflict selector to a sample and transport the original weighted
source numerator to the retained cardinality. Pointwise fullness is inherited without loss;
sample shade mass and cardinality each pay `D+1`. The conflict-degree and sample cardinality
inputs are explicit: no geometric ED, Frostman or Katz--Tao hypothesis is inferred here. -/
theorem exists_conflictFree_sample_with_sourceShadeBudget
    {E ι : Type*} [MeasurableSpace E] [DecidableEq ι]
    (μ : Measure E) (indices sampled : Finset ι) (hsub : sampled ⊆ indices)
    (weights : ι → ℝ) (tube shade : ι → Set E)
    (scale tubeVolume K : ℝ) (τ : ℝ≥0∞)
    (hscale : 0 < scale) (htube : 0 ≤ tubeVolume) (hK : 0 ≤ K)
    (hweights : ∀ i ∈ indices, 0 ≤ weights i)
    (hshade : ∀ i ∈ indices, shade i ⊆ tube i)
    (hvolume : ∀ i ∈ indices, μ (tube i) = ENNReal.ofReal tubeVolume)
    (hfull : ∀ i ∈ indices, τ * μ (tube i) ≤ μ (shade i))
    (hsize : (∑ i ∈ indices, weights i / scale) ≤ K * (sampled.card : ℝ))
    (r : ι → ι → Prop) (hsymm : ∀ i j, r i j → r j i) (hirr : ∀ i, ¬ r i i)
    (D : ℕ) (hdeg : ∀ i ∈ sampled, {j ∈ (sampled : Set ι) | r j i}.ncard ≤ D) :
    ∃ selected ⊆ sampled,
      (selected : Set ι).Pairwise (fun i j => ¬ r i j) ∧
      sampled.card ≤ (D + 1) * selected.card ∧
      (∑ i ∈ sampled, μ (shade i) ≤ (D + 1 : ℕ) * ∑ i ∈ selected, μ (shade i)) ∧
      (∀ i ∈ selected, τ * μ (tube i) ≤ μ (shade i)) ∧
      (∑ i ∈ indices, ENNReal.ofReal (weights i) * μ (shade i)) ≤
        ENNReal.ofReal (scale * (K * (D + 1) * (selected.card : ℝ)) * tubeVolume) := by
  obtain ⟨selected, hsel, hpair, hmass, hcard⟩ :=
    exists_pairwise_conflictFree_retaining_weight_and_card sampled r hsymm hirr hdeg
      (fun i => μ (shade i))
  have hcardReal : (sampled.card : ℝ) ≤ (D + 1 : ℝ) * (selected.card : ℝ) := by
    exact_mod_cast hcard
  have hsizeSelected : (∑ i ∈ indices, weights i / scale) ≤
      K * (D + 1) * (selected.card : ℝ) := by
    calc
      _ ≤ K * (sampled.card : ℝ) := hsize
      _ ≤ K * ((D + 1 : ℝ) * (selected.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hcardReal hK
      _ = _ := by ring
  exact ⟨selected, hsel, hpair, hcard, hmass,
    (fun i hi => hfull i (hsub (hsel hi))),
    weightedShadeMass_le_of_normalizedWeight_bound μ indices weights tube shade
      scale tubeVolume _ hscale htube hweights hshade hvolume hsizeSelected⟩

/-- Construct the actual sample certificate from the relevant source-box producer and the
paid net budget. The same realization retains its cardinality lower bound; no carrier-volume
identity or integer line-cap payment is needed merely to produce this certificate. -/
theorem WeightedConvexClusteringCertificate.exists_sample_with_sampledCertificate_of_relevant_source_box_selector
    {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {indices : Finset ι} {core : ι → Set (BoxAmbient n)} {weights : ι → ℝ}
    {scale tubeVolume : ℝ}
    (δ R C α κ : ℝ) (B : ℝ≥0∞)
    (hB : B < ⊤) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hR : 0 ≤ R)
    (hindices : indices = Finset.univ)
    (hTubeBall : ∀ i ∈ indices,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (htube : 0 < tubeVolume)
    (hcommon : ∀ i ∈ indices,
      (volume (Metric.cthickening δ (core i))).toReal = tubeVolume)
    (hC : 0 ≤ C) (hκ : 0 < κ) (hα : 0 < α)
    (hscaleNet : α * δ ^ 2 ≤
      √(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1))
    (sourceBox : ∀ T : RelevantConvexTubeTest indices
        (fun i => Metric.cthickening δ (core i)),
      RelevantConvexTestSourceBox T.1 δ R C κ B)
    (weightedCert : WeightedConvexClusteringCertificate indices
      (fun i => Metric.cthickening δ (core i)) weights scale)
    (hscale : 0 < scale)
    (ell L : ℝ) (hell : 0 ≤ ell) (hδlog : Real.exp (-ell) = δ)
    (tailExponent : ℕ) (hLtail : ((tailExponent + 2 : ℕ) : ℝ) ≤ L)
    (S : ℝ)
    (hS : (∑ i ∈ Finset.univ,
      ((bernoulliInclusionProbabilitiesFromWeights weights scale hscale
        (fun i => ⟨weightedCert.weights_nonneg i,
          weightedCert.weight_le_scale i (by simp [hindices])⟩) i : unitInterval) : ℝ)) = S)
    (minSize : ℕ) (hmin : (minSize : ℝ) ≤ S / 2)
    (hnetBudget :
      ENNReal.ofReal (orthogonalBoxSamplerNetCardBound n C α δ) *
          ENNReal.ofReal (δ ^ (tailExponent + 2)) +
        ENNReal.ofReal (Real.exp (-S / 8)) < 1) :
    ∃ ω, minSize ≤ (bernoulliProductSample ω).card ∧
      SampledConvexClusteringCertificate (bernoulliProductSample ω) core δ
        (ENNReal.ofReal (L * (1 + ell)) *
          (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) * B)) := by
  classical
  let tube : ι → Set (BoxAmbient n) := fun i => Metric.cthickening δ (core i)
  have hselector := exists_finite_orthogonalBox_sampler_cover_of_relevant_source_box_selector
    indices tube δ R C α κ B hB hδ hδ1
    (by simpa [tube] using hTubeBall) tubeVolume htube
    (by simpa [tube] using hcommon) hC hκ hα hscaleNet
    (by
      intro T
      exact sourceBox T)
  obtain ⟨N, hNcard, hNfinite,
      ⟨rep, hrepCode, hboxConvex, hboxTop, hboxVolume, hboxRatio, hboxCover⟩⟩ := hselector
  let β := {q : BoxParameterSpace n // q ∈ N}
  let boxes : Finset β := Finset.univ
  let box : β → Set (BoxAmbient n) := fun q =>
    orthogonalBox_enlargement (rep q) (orthogonalBoxNetEnlargementError n C α δ)
  let boxVolume : β → ℝ := fun q =>
    orthogonalBox_enlargementVolume (rep q) (orthogonalBoxNetEnlargementError n C α δ)
  have hcardEq : boxes.card = N.card := by
    simp [boxes, β]
  have hnetCardENN : (N.card : ℝ≥0∞) ≤
      ENNReal.ofReal (orthogonalBoxSamplerNetCardBound n C α δ) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by simpa [orthogonalBoxSamplerNetCardBound] using hNcard)
  have hbudget : (boxes.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ (tailExponent + 2)) +
      ENNReal.ofReal (Real.exp (-S / 8)) < 1 := by
    rw [hcardEq]
    calc
      (N.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ (tailExponent + 2)) +
          ENNReal.ofReal (Real.exp (-S / 8)) ≤
        ENNReal.ofReal (orthogonalBoxSamplerNetCardBound n C α δ) *
          ENNReal.ofReal (δ ^ (tailExponent + 2)) +
          ENNReal.ofReal (Real.exp (-S / 8)) := by
            gcongr
      _ < 1 := hnetBudget
  have hL2 : 2 ≤ L := by
    have hn : 2 ≤ tailExponent + 2 := by omega
    have hnReal : (2 : ℝ) ≤ ((tailExponent + 2 : ℕ) : ℝ) := by exact_mod_cast hn
    exact hnReal.trans hLtail
  have hLc : ((tailExponent + 2 : ℕ) : ℝ) ≤ L * 1 := by simpa using hLtail
  have hboxConvex' : ∀ q ∈ boxes, Convex ℝ (box q) := by
    intro q hq
    exact hboxConvex q
  have hboxVolume' : ∀ q ∈ boxes, (volume (box q)).toReal = boxVolume q := by
    intro q hq
    exact hboxVolume q
  have hboxTop' : ∀ q ∈ boxes, volume (box q) < ⊤ := by
    intro q hq
    exact hboxTop q
  have hcommon' : ∀ i ∈ indices, (volume (tube i)).toReal = tubeVolume := by
    simpa [tube] using hcommon
  have hratio : ∀ q ∈ boxes, (1 : ℝ) ≤ boxVolume q / tubeVolume := by
    intro q hq
    have h := hboxRatio q
    dsimp [boxVolume] at h ⊢
    exact h
  have hcover : ∀ K : Set (BoxAmbient n), Convex ℝ K →
      (∃ i ∈ indices, tube i ⊆ K) →
      ∃ q ∈ boxes,
        (∀ i ∈ indices, tube i ⊆ K → tube i ⊆ box q) ∧
          volume (box q) ≤
            (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) * B) * volume K := by
    intro K hK hRelevant
    obtain ⟨q, hcontains, hvol⟩ := hboxCover K hK (by simpa [tube] using hRelevant)
    refine ⟨q, Finset.mem_univ q, ?_, ?_⟩
    · simpa [tube, box] using hcontains
    · change volume (orthogonalBox_enlargement (rep q)
        (orthogonalBoxNetEnlargementError n C α δ)) ≤
          (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) * B) * volume K
      exact hvol
  have hδlog' : Real.exp (-ell) = δ := hδlog
  obtain ⟨ω, hsize, _, hcert⟩ :=
    WeightedConvexClusteringCertificate.exists_sample_with_sampledConvexClusteringCertificate_of_floor_logarithmic_box_cover
      δ weightedCert hindices hscale htube ell L 1 hell hδlog' tailExponent hL2 (by norm_num) hLc
      boxes box boxVolume hboxConvex' hboxVolume' hboxTop' hcommon' hratio
      S hS minSize hmin hbudget
      (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) * B) hcover
  exact ⟨ω, hsize, hcert⟩

/-- The proved truncated convex-test geometry produces a certificate on the very sample
selected by the floor-log sampler. All source constants remain explicit. -/
theorem WeightedConvexClusteringCertificate.exists_sample_with_sampledCertificate_of_truncated_source_geometry
    {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {indices : Finset ι} {core : ι → Set (BoxAmbient n)} {weights : ι → ℝ}
    {scale tubeVolume : ℝ}
    (δ R α : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 ≤ R)
    (hindices : indices = Finset.univ)
    (hTubeBall : ∀ i ∈ indices,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (hTubeInnerBall : ∀ i ∈ indices, ∃ z : BoxAmbient n,
      Metric.closedBall z δ ⊆ Metric.cthickening δ (core i))
    (htube : 0 < tubeVolume)
    (hcommon : ∀ i ∈ indices,
      (volume (Metric.cthickening δ (core i))).toReal = tubeVolume)
    (hα : 0 < α)
    (hscaleNet : α * δ ^ 2 ≤
      √(Fintype.card (BoxParameterIndex n) : ℝ) *
        (((n : ℝ) * R + R) + 1))
    (weightedCert : WeightedConvexClusteringCertificate indices
      (fun i => Metric.cthickening δ (core i)) weights scale)
    (hscale : 0 < scale)
    (ell L : ℝ) (hell : 0 ≤ ell) (hδlog : Real.exp (-ell) = δ)
    (tailExponent : ℕ) (hLtail : ((tailExponent + 2 : ℕ) : ℝ) ≤ L)
    (S : ℝ)
    (hS : (∑ i ∈ Finset.univ,
      ((bernoulliInclusionProbabilitiesFromWeights weights scale hscale
        (fun i => ⟨weightedCert.weights_nonneg i,
          weightedCert.weight_le_scale i (by simp [hindices])⟩) i : unitInterval) : ℝ)) = S)
    (minSize : ℕ) (hmin : (minSize : ℝ) ≤ S / 2)
    (hnetBudget :
      ENNReal.ofReal (orthogonalBoxSamplerNetCardBound n ((n : ℝ) * R + R) α δ) *
          ENNReal.ofReal (δ ^ (tailExponent + 2)) +
        ENNReal.ofReal (Real.exp (-S / 8)) < 1) :
    ∃ ω, minSize ≤ (bernoulliProductSample ω).card ∧
      SampledConvexClusteringCertificate (bernoulliProductSample ω) core δ
        (ENNReal.ofReal (L * (1 + ell)) *
          (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n ((n : ℝ) * R + R) α 1) * ENNReal.ofReal ((2 : ℝ)^n * (n.factorial : ℝ)))) := by
  let C : ℝ := (n : ℝ) * R + R
  let B : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ)^n * (n.factorial : ℝ))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg n) hR) hR
  have hB : B < ⊤ := by
    dsimp [B]
    exact ENNReal.ofReal_lt_top
  have hκ : (0 : ℝ) < 1 := by norm_num
  have hsourceBox : ∀ T : RelevantConvexTubeTest indices
      (fun i => Metric.cthickening δ (core i)),
      RelevantConvexTestSourceBox T.1 δ R C 1 B := by
    intro T
    simpa [C, B] using
      (RelevantConvexTubeTest.sourceBoxSelector
        (indices := indices) (tube := fun i => Metric.cthickening δ (core i))
        δ R tubeVolume hδ hR hTubeBall hTubeInnerBall htube hcommon T)
  exact WeightedConvexClusteringCertificate.exists_sample_with_sampledCertificate_of_relevant_source_box_selector
    δ R C α 1 B hB hδ hδ1 hR hindices hTubeBall htube hcommon hC hκ hα
    (by simpa [C] using hscaleNet) hsourceBox weightedCert hscale ell L hell hδlog
    tailExponent hLtail S hS minSize hmin hnetBudget

/-- Actual segment-tube source input produces one small-scale sample with its own convex
clustering certificate, paying the uniform three-dimensional net and lower-tail budget.
The certificate can subsequently pay any justified line-neighborhood radius. -/
theorem exists_small_scale_sampledCertificate_of_segment_weighted_body_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (R α : ℝ) (hR : 0 ≤ R) (hα : 0 < α) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (δ : ℝ) (a b : ι → BoxAmbient 3) (weights : ι → ℝ) (scale tubeVolume ell : ℝ),
        0 < δ → δ < δ₀ → 0 < scale → 0 < tubeVolume → 0 ≤ ell →
        Real.exp (-ell) = δ → (∀ i, 0 ≤ weights i) →
        (∀ i ∈ Finset.univ,
          Metric.cthickening δ (segment ℝ (a i) (b i)) ⊆ Metric.closedBall 0 R) →
        (∀ i ∈ Finset.univ,
          (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal = tubeVolume) →
        α * δ ^ 2 ≤ √(Fintype.card (BoxParameterIndex 3) : ℝ) * (((3 : ℝ) * R + R) + 1) →
        (∀ K : Set (BoxAmbient 3), IsCompact K → Convex ℝ K → 0 < volume K →
          (∑ i ∈ tubeIndicesContainedInSet Finset.univ
              (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) K,
            weights i * (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal) ≤
            scale * (volume K).toReal) →
        32 * (1 + ell) ≤ (∑ i : ι, weights i / scale) →
        ∀ minSize : ℕ,
          (minSize : ℝ) ≤ (∑ i : ι, weights i / scale) / 2 →
          ∃ ω, minSize ≤ (bernoulliProductSample ω).card ∧
            SampledConvexClusteringCertificate (bernoulliProductSample ω)
              (fun i => segment ℝ (a i) (b i)) δ
              (ENNReal.ofReal (32 * (1 + ell)) *
                (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor 3
                  ((3 : ℝ) * R + R) α 1) * ENNReal.ofReal ((2 : ℝ)^3 * ((3 : ℕ).factorial : ℝ)))) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hbudget⟩ :=
    exists_small_scale_orthogonalBoxSamplerNetBudget_three R α hR hα
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ a b weights scale tubeVolume ell hδ hsmall hscale htube hell hlog
    hweights hTubeBall hcommon hscaleNet hbody hlarge minSize hmin
  let cert := weightedConvexClusteringCertificate_of_segment_tubes Finset.univ a b δ scale
    weights hδ hscale.le hweights hbody
  let S := ∑ i : ι, weights i / scale
  have hS : (∑ i ∈ Finset.univ,
      ((bernoulliInclusionProbabilitiesFromWeights weights scale hscale
        (fun i => ⟨cert.weights_nonneg i, cert.weight_le_scale i (by simp)⟩) i : unitInterval) : ℝ)) = S := by
    simp [bernoulliInclusionProbabilitiesFromWeights, S]
  have hnet := hbudget δ ell S hδ hsmall hell hlarge
  have hC : (3 : ℝ) * R + R = 4 * R := by ring
  exact cert.exists_sample_with_sampledCertificate_of_truncated_source_geometry
    δ R α hδ (hsmall.trans_le hδ₀1).le hR rfl hTubeBall
    (fun i _ => ⟨a i, Metric.closedBall_subset_cthickening (left_mem_segment ℝ _ _) δ⟩)
    htube hcommon hα hscaleNet hscale ell 32 hell hlog 30 (by norm_num) S hS
    minSize hmin (by simpa only [Nat.cast_ofNat, hC] using hnet)

/-- Actual source-input consumer in dimension three. The compact convex-body weighted
inequality produces the certificate for the segment tubes, and one scale threshold pays the
net and Bernoulli lower tails with `tailExponent=30`, `L=32`. The remaining common-volume,
carrier-volume, geometric net admissibility and integer line-cap payment are explicit inputs.
This theorem covers the source proof's large expected-size branch and does not assert the
final shading or WeightedPlanks estimate. -/
theorem exists_small_scale_sampledLineCap_of_segment_weighted_body_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (R α : ℝ) (hR : 0 ≤ R) (hα : 0 < α) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (δ : ℝ) (a b : ι → BoxAmbient 3) (weights : ι → ℝ) (scale tubeVolume ell : ℝ),
        0 < δ → δ < δ₀ → 0 < scale → 0 < tubeVolume → 0 ≤ ell →
        Real.exp (-ell) = δ → (∀ i, 0 ≤ weights i) →
        (∀ i ∈ Finset.univ,
          Metric.cthickening δ (segment ℝ (a i) (b i)) ⊆ Metric.closedBall 0 R) →
        (∀ i ∈ Finset.univ,
          (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal = tubeVolume) →
        α * δ ^ 2 ≤ √(Fintype.card (BoxParameterIndex 3) : ℝ) * (((3 : ℝ) * R + R) + 1) →
        (∀ K : Set (BoxAmbient 3), IsCompact K → Convex ℝ K → 0 < volume K →
          (∑ i ∈ tubeIndicesContainedInSet Finset.univ
              (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) K,
            weights i * (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal) ≤
            scale * (volume K).toReal) →
        32 * (1 + ell) ≤ (∑ i : ι, weights i / scale) →
        ∀ minSize lineCapBound : ℕ,
          (minSize : ℝ) ≤ (∑ i : ι, weights i / scale) / 2 →
          (∀ o v : BoxAmbient 3, ‖v‖ = 1 → ∀ i ∈ Finset.univ,
            volume (Metric.cthickening δ (segment ℝ (a i) (b i))) =
              volume (Metric.cthickening δ (segment ℝ o (o + v)))) →
          ((ENNReal.ofReal (32 * (1 + ell)) *
            (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor 3
              ((3 : ℝ) * R + R) α 1) * ENNReal.ofReal ((2 : ℝ)^3 * ((3 : ℕ).factorial : ℝ)))) *
            ENNReal.ofReal (50 * R) ≤ (lineCapBound : ℝ≥0∞)) →
          ∃ ω, minSize ≤ (bernoulliProductSample ω).card ∧
            ∀ o v : BoxAmbient 3, ‖v‖ = 1 →
              (lineCarrierCapFilter (bernoulliProductSample ω)
                (fun i => segment ℝ (a i) (b i)) δ o v).card ≤ lineCapBound := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hproducer⟩ :=
    exists_small_scale_sampledCertificate_of_segment_weighted_body_bound (ι := ι) R α hR hα
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ a b weights scale tubeVolume ell hδ hsmall hscale htube hell hlog
    hweights hTubeBall hcommon hscaleNet hbody hlarge minSize lineCapBound hmin hcarrier hcap
  obtain ⟨ω, hsize, hcert⟩ := hproducer δ a b weights scale tubeVolume ell
    hδ hsmall hscale htube hell hlog hweights hTubeBall hcommon hscaleNet hbody hlarge minSize hmin
  refine ⟨ω, hsize, ?_⟩
  exact sampledConvexClustering_uniform_lineCarrierBudget
    (by simp [BoxAmbient]) (bernoulliProductSample ω)
    (fun i => segment ℝ (a i) (b i)) δ R _ hδ.le hδ hR hcert
    (fun i _ => hTubeBall i (Finset.mem_univ i))
    (fun o v hv i _ => hcarrier o v hv i (Finset.mem_univ i)) lineCapBound hcap

/-- The actual large-size source branch admits a sample whose cardinality controls the
normalized original weight by a factor four. The natural sample-size threshold is constructed
internally as `ceil(S/4)`, and the certificate belongs to that same sample. -/
theorem exists_small_scale_sampledCertificate_card_quarter_of_segment_weighted_body_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (R α : ℝ) (hR : 0 ≤ R) (hα : 0 < α) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (δ : ℝ) (a b : ι → BoxAmbient 3) (weights : ι → ℝ) (scale tubeVolume ell : ℝ),
        0 < δ → δ < δ₀ → 0 < scale → 0 < tubeVolume → 0 ≤ ell →
        Real.exp (-ell) = δ → (∀ i, 0 ≤ weights i) →
        (∀ i ∈ Finset.univ,
          Metric.cthickening δ (segment ℝ (a i) (b i)) ⊆ Metric.closedBall 0 R) →
        (∀ i ∈ Finset.univ,
          (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal = tubeVolume) →
        α * δ ^ 2 ≤ √(Fintype.card (BoxParameterIndex 3) : ℝ) * (((3 : ℝ) * R + R) + 1) →
        (∀ K : Set (BoxAmbient 3), IsCompact K → Convex ℝ K → 0 < volume K →
          (∑ i ∈ tubeIndicesContainedInSet Finset.univ
              (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) K,
            weights i * (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal) ≤
            scale * (volume K).toReal) →
        32 * (1 + ell) ≤ (∑ i : ι, weights i / scale) →
        ∃ ω, (∑ i : ι, weights i / scale) ≤ 4 * ((bernoulliProductSample ω).card : ℝ) ∧
          SampledConvexClusteringCertificate (bernoulliProductSample ω)
            (fun i => segment ℝ (a i) (b i)) δ
            (ENNReal.ofReal (32 * (1 + ell)) *
              (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor 3
                ((3 : ℝ) * R + R) α 1) * ENNReal.ofReal ((2 : ℝ)^3 * ((3 : ℕ).factorial : ℝ)))) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hproducer⟩ :=
    exists_small_scale_sampledCertificate_of_segment_weighted_body_bound (ι := ι) R α hR hα
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ a b weights scale tubeVolume ell hδ hsmall hscale htube hell hlog
    hweights hTubeBall hcommon hscaleNet hbody hlarge
  let S := ∑ i : ι, weights i / scale
  have hS32 : 32 ≤ S := by dsimp [S]; nlinarith [hlarge]
  have hquarter : 0 ≤ S / 4 := by linarith
  have hceil := Nat.ceil_lt_add_one hquarter
  have hmin : (⌈S / 4⌉₊ : ℝ) ≤ S / 2 := by linarith
  obtain ⟨ω, hsize, hcert⟩ := hproducer δ a b weights scale tubeVolume ell
    hδ hsmall hscale htube hell hlog hweights hTubeBall hcommon hscaleNet hbody hlarge
    ⌈S / 4⌉₊ hmin
  have hsizeReal : (⌈S / 4⌉₊ : ℝ) ≤ ((bernoulliProductSample ω).card : ℝ) := by
    exact_mod_cast hsize
  have hceilLower := Nat.le_ceil (S / 4)
  refine ⟨ω, ?_, hcert⟩
  change S ≤ 4 * ((bernoulliProductSample ω).card : ℝ)
  linarith

/-- Equal-length segment neighborhoods have exactly equal volume, not just comparable
volume. A reflection transports one axis to the other, and preserves both distance and volume. -/
theorem volume_unitAxisSegment_cthickening_eq_of_norm_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (u v : E) (δ : ℝ) (huv : ‖u‖ = ‖v‖) :
    volume (Metric.cthickening δ (unitAxisSegment u)) =
      volume (Metric.cthickening δ (unitAxisSegment v)) := by
  let f : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (u - v))ᗮ.reflection
  have hf : f u = v := Submodule.reflection_sub huv
  have himage : f '' unitAxisSegment u = unitAxisSegment v := by
    simpa [unitAxisSegment, hf] using image_segment ℝ f.toLinearEquiv.toAffineMap 0 u
  have hpre : f ⁻¹' Metric.cthickening δ (unitAxisSegment v) =
      Metric.cthickening δ (unitAxisSegment u) := by
    ext x
    change Metric.infEDist (f x) (unitAxisSegment v) ≤ ENNReal.ofReal δ ↔ _
    rw [← himage, Metric.infEDist_image f.isometry]
    rfl
  rw [← hpre]
  exact f.measurePreserving.measure_preimage Metric.isClosed_cthickening.measurableSet.nullMeasurableSet

/-- Endpoint segments are exactly their centered representation; the direction is the full
endpoint difference, so a unit-length source segment has a unit centered direction. -/
theorem segment_eq_centeredUnitSegment (a b : BoxAmbient 3) :
    segment ℝ a b = centeredUnitSegment ((1 / 2 : ℝ) • (a + b)) (b - a) := by
  unfold centeredUnitSegment
  congr 1 <;> module

/-- The unit-length condition from the source tube definition supplies the formerly explicit
carrier-volume comparison against every unit line carrier. -/
theorem volume_segment_cthickening_eq_unitCarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a b o v : E) {δ : ℝ} (hδ : 0 ≤ δ) (hab : ‖b - a‖ = 1) (hv : ‖v‖ = 1) :
    volume (Metric.cthickening δ (segment ℝ a b)) =
      volume (Metric.cthickening δ (segment ℝ o (o + v))) := by
  have hseg : segment ℝ a b = segment ℝ a (a + (b - a)) := by congr 1 <;> module
  rw [hseg, volume_cthickening_segment_translate a (b - a) hδ,
    volume_cthickening_segment_translate o v hδ]
  exact volume_unitAxisSegment_cthickening_eq_of_norm_eq (b - a) v δ (hab.trans hv.symm)

/-- For actual unit-length source segments, the sampled certificate pays the `27δ` conflict
geometry and yields a carrier-essentially-distinct subfamily. Carrier-volume equality and
centered representation are proved internally. The original weighted numerator, sample shade
mass, cardinality and pointwise fullness are all attached to the same retained indices. -/
theorem exists_carrierED_sample_with_sourceShadeBudget
    {ι : Type*} [DecidableEq ι]
    (indices sampled : Finset ι) (hsub : sampled ⊆ indices)
    (a b : ι → BoxAmbient 3) (shade : ι → Set (BoxAmbient 3)) (weights : ι → ℝ)
    (δ R scale tubeVolume K : ℝ) (τ A : ℝ≥0∞) (D : ℕ)
    (hδ : 0 < δ) (hR : 0 ≤ R) (hscale : 0 < scale) (htube : 0 ≤ tubeVolume) (hK : 0 ≤ K)
    (hunit : ∀ i ∈ indices, ‖b i - a i‖ = 1)
    (hweights : ∀ i ∈ indices, 0 ≤ weights i)
    (hshade : ∀ i ∈ indices, shade i ⊆ Metric.cthickening δ (segment ℝ (a i) (b i)))
    (hvolume : ∀ i ∈ indices,
      volume (Metric.cthickening δ (segment ℝ (a i) (b i))) = ENNReal.ofReal tubeVolume)
    (hfull : ∀ i ∈ indices,
      τ * volume (Metric.cthickening δ (segment ℝ (a i) (b i))) ≤ volume (shade i))
    (hsize : (∑ i ∈ indices, weights i / scale) ≤ K * (sampled.card : ℝ))
    (cert : SampledConvexClusteringCertificate sampled (fun i => segment ℝ (a i) (b i)) δ A)
    (hball : ∀ i ∈ indices,
      Metric.cthickening δ (segment ℝ (a i) (b i)) ⊆ Metric.closedBall 0 R)
    (hbudget : A * ENNReal.ofReal (1458 * R) ≤ (D : ℝ≥0∞)) :
    ∃ selected ⊆ sampled,
      (selected : Set ι).Pairwise (fun i j => IsCarrierEssentiallyDistinct
        (Metric.cthickening δ (segment ℝ (a i) (b i)))
        (Metric.cthickening δ (segment ℝ (a j) (b j)))) ∧
      sampled.card ≤ (D + 1) * selected.card ∧
      (∑ i ∈ sampled, volume (shade i) ≤ (D + 1 : ℕ) * ∑ i ∈ selected, volume (shade i)) ∧
      (∀ i ∈ selected,
        τ * volume (Metric.cthickening δ (segment ℝ (a i) (b i))) ≤ volume (shade i)) ∧
      (∑ i ∈ indices, ENNReal.ofReal (weights i) * volume (shade i)) ≤
        ENNReal.ofReal (scale * (K * (D + 1) * (selected.card : ℝ)) * tubeVolume) := by
  classical
  let tube : ι → Set (BoxAmbient 3) := fun i => Metric.cthickening δ (segment ℝ (a i) (b i))
  let conflict : ι → ι → Prop := fun i j => i ≠ j ∧ ¬ IsCarrierEssentiallyDistinct (tube i) (tube j)
  have hsymm : ∀ i j, conflict i j → conflict j i := by
    intro i j hij
    refine ⟨hij.1.symm, ?_⟩
    intro hji
    apply hij.2
    unfold IsCarrierEssentiallyDistinct at hji ⊢
    simpa only [Set.inter_comm, max_comm] using hji
  have hirr : ∀ i, ¬ conflict i i := fun i hi => hi.1 rfl
  have hdim : Module.finrank ℝ (BoxAmbient 3) = 3 := by simp [BoxAmbient]
  have hcap := sampledConvexClustering_uniform_lineCarrierBudget_at_radius hdim sampled
    (fun i => segment ℝ (a i) (b i)) δ R 27 A hδ.le hδ hR (by norm_num) cert
    (fun i hi => hball i (hsub hi))
    (fun o v hv i hi => volume_segment_cthickening_eq_unitCarrier
      (a i) (b i) o v hδ.le (hunit i (hsub hi)) hv) D
    (by
      have hfactor : 2 * R * (27 : ℝ) ^ 2 = 1458 * R := by ring
      simpa only [hfactor] using hbudget)
  have hdegree : ∀ i ∈ sampled, {j ∈ (sampled : Set ι) | conflict j i}.ncard ≤ D := by
    intro i hi
    let m : ι → BoxAmbient 3 := fun k => (1 / 2 : ℝ) • (a k + b k)
    let d : ι → BoxAmbient 3 := fun k => b k - a k
    let cap := lineCarrierCapFilterAt sampled (fun k => segment ℝ (a k) (b k)) δ 27 (m i) (d i)
    have hconflictSub : {j ∈ (sampled : Set ι) | conflict j i} ⊆ (cap : Set ι) := by
      intro j hj
      have hnot : ¬ IsCarrierEssentiallyDistinct
          (centeredUnitCarrier δ (m i) (d i)) (centeredUnitCarrier δ (m j) (d j)) := by
        have h := (hsymm j i hj.2).2
        simpa only [tube, centeredUnitCarrier, m, d, ← segment_eq_centeredUnitSegment] using h
      have hline := centeredUnitCarrier_subset_lineCthickening_of_not_essentiallyDistinct
        hdim hδ (m i) (m j) (d i) (d j) (hunit i (hsub hi)) (hunit j (hsub hj.1)) hnot
      apply Finset.mem_filter.mpr
      refine ⟨hj.1, ?_⟩
      simpa only [centeredUnitCarrier, m, d, ← segment_eq_centeredUnitSegment] using hline
    have hcount := Set.ncard_le_ncard hconflictSub cap.finite_toSet
    rw [Set.ncard_coe_finset] at hcount
    exact hcount.trans (hcap (m i) (d i) (hunit i (hsub hi)))
  obtain ⟨selected, hsel, hpair, hcard, hmass, hfullSelected, hbudgetSelected⟩ :=
    exists_conflictFree_sample_with_sourceShadeBudget volume indices sampled hsub weights tube shade
      scale tubeVolume K τ hscale htube hK hweights hshade hvolume hfull hsize
      conflict hsymm hirr D hdegree
  refine ⟨selected, hsel, ?_, hcard, hmass, hfullSelected, hbudgetSelected⟩
  intro i hi j hj hij
  by_contra hnot
  exact hpair hi hj hij ⟨hij, hnot⟩

/-- The same sampled clustering constant controls every retained subfamily. -/
theorem SampledConvexClusteringCertificate.restrict
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {indices selected : Finset ι} {core : ι → Set E} {δ : ℝ} {A : ℝ≥0∞}
    (cert : SampledConvexClusteringCertificate indices core δ A) (hsub : selected ⊆ indices) :
    SampledConvexClusteringCertificate selected core δ A := by
  constructor
  intro K hK J hJ hcontained
  exact cert.convex_test_bound K hK J (hJ.trans hsub) hcontained

/-- Carrier-ED plus positive real volume rules out repeated actual carrier sets. Positive
real volume also excludes infinite volume, so the half-overlap test cannot be vacuous. -/
theorem carrierED_injOn_of_volume_toReal_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} (indices : Finset ι) (tube : ι → Set E)
    (hpair : (indices : Set ι).Pairwise (fun i j => IsCarrierEssentiallyDistinct (tube i) (tube j)))
    (hpos : ∀ i ∈ indices, 0 < (volume (tube i)).toReal) :
    Set.InjOn tube (indices : Set ι) := by
  intro i hi j hj heq
  by_contra hne
  have hbound := hpair hi hj hne
  unfold IsCarrierEssentiallyDistinct at hbound
  dsimp only at hbound
  rw [heq, Set.inter_self, max_self] at hbound
  have htop : volume (tube j) ≠ ⊤ := (ENNReal.toReal_pos_iff.mp (hpos j hj)).2.ne
  have hhalfTop : (1 / 2 : ℝ≥0∞) * volume (tube j) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) htop
  have hreal := ENNReal.toReal_mono hhalfTop hbound
  norm_num [ENNReal.toReal_mul] at hreal
  nlinarith [hpos j hj]

/-- The actual closed segment tube is precisely the closed-ball-union carrier used in the
licensed Numina `Tube` definition. No cylinder substitution or change of radius is involved. -/
theorem segment_cthickening_eq_sourceTubeCarrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) {δ : ℝ} (hδ : 0 ≤ δ) :
    Metric.cthickening δ (segment ℝ a b) = ⋃ z ∈ segment ℝ a b, Metric.closedBall z δ := by
  have hcompact : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  exact hcompact.cthickening_eq_biUnion_closedBall hδ

/-- Pointwise source fullness implies the actual average fullness on any retained indices. -/
theorem shade_averageFullness_of_pointwise
    {E ι : Type*} [MeasurableSpace E] (μ : Measure E) (indices : Finset ι)
    (tube shade : ι → Set E) (τ : ℝ≥0∞)
    (hfull : ∀ i ∈ indices, τ * μ (tube i) ≤ μ (shade i)) :
    τ * (∑ i ∈ indices, μ (tube i)) ≤ ∑ i ∈ indices, μ (shade i) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum hfull

/-- Actual source-weighted unit segments produce one sample and a carrier-ED retained family,
with the source numerator and every cardinality/fullness loss exposed. The only extra geometric
payment is the explicit `1458R` radius-27 budget; no prior sample certificate is assumed. -/
theorem exists_small_scale_carrierED_of_unit_segment_weighted_body_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (R α : ℝ) (hR : 0 ≤ R) (hα : 0 < α) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (δ : ℝ) (a b : ι → BoxAmbient 3) (weights : ι → ℝ) (scale tubeVolume ell : ℝ),
        0 < δ → δ < δ₀ → 0 < scale → 0 < tubeVolume → 0 ≤ ell →
        Real.exp (-ell) = δ → (∀ i, 0 ≤ weights i) →
        (∀ i ∈ Finset.univ,
          Metric.cthickening δ (segment ℝ (a i) (b i)) ⊆ Metric.closedBall 0 R) →
        (∀ i ∈ Finset.univ,
          (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal = tubeVolume) →
        α * δ ^ 2 ≤ √(Fintype.card (BoxParameterIndex 3) : ℝ) * (((3 : ℝ) * R + R) + 1) →
        (∀ K : Set (BoxAmbient 3), IsCompact K → Convex ℝ K → 0 < volume K →
          (∑ i ∈ tubeIndicesContainedInSet Finset.univ
              (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) K,
            weights i * (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal) ≤
            scale * (volume K).toReal) →
        32 * (1 + ell) ≤ (∑ i : ι, weights i / scale) →
        ∀ (shade : ι → Set (BoxAmbient 3)) (τ : ℝ≥0∞) (D : ℕ),
          (∀ i, ‖b i - a i‖ = 1) →
          (∀ i, shade i ⊆ Metric.cthickening δ (segment ℝ (a i) (b i))) →
          (∀ i, τ * volume (Metric.cthickening δ (segment ℝ (a i) (b i))) ≤ volume (shade i)) →
          ((ENNReal.ofReal (32 * (1 + ell)) *
            (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor 3
              ((3 : ℝ) * R + R) α 1) * ENNReal.ofReal ((2 : ℝ)^3 * ((3 : ℕ).factorial : ℝ)))) *
            ENNReal.ofReal (1458 * R) ≤ (D : ℝ≥0∞)) →
          ∃ ω, ∃ selected ⊆ bernoulliProductSample ω,
            SampledConvexClusteringCertificate selected (fun i => segment ℝ (a i) (b i)) δ
              (ENNReal.ofReal (32 * (1 + ell)) *
                (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor 3
                  ((3 : ℝ) * R + R) α 1) * ENNReal.ofReal ((2 : ℝ)^3 * ((3 : ℕ).factorial : ℝ)))) ∧
            Set.InjOn (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) (selected : Set ι) ∧
            (selected : Set ι).Pairwise (fun i j => IsCarrierEssentiallyDistinct
              (Metric.cthickening δ (segment ℝ (a i) (b i)))
              (Metric.cthickening δ (segment ℝ (a j) (b j)))) ∧
            ((∑ i : ι, weights i / scale) ≤ 4 * (D + 1) * (selected.card : ℝ)) ∧
            ((bernoulliProductSample ω).card ≤ (D + 1) * selected.card) ∧
            (∑ i ∈ bernoulliProductSample ω, volume (shade i) ≤
              (D + 1 : ℕ) * ∑ i ∈ selected, volume (shade i)) ∧
            (∀ i ∈ selected,
              τ * volume (Metric.cthickening δ (segment ℝ (a i) (b i))) ≤ volume (shade i)) ∧
            (τ * (∑ i ∈ selected, volume (Metric.cthickening δ (segment ℝ (a i) (b i)))) ≤
              ∑ i ∈ selected, volume (shade i)) ∧
            (∑ i : ι, ENNReal.ofReal (weights i) * volume (shade i)) ≤
              ENNReal.ofReal (scale * (4 * (D + 1) * (selected.card : ℝ)) * tubeVolume) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hproducer⟩ :=
    exists_small_scale_sampledCertificate_card_quarter_of_segment_weighted_body_bound (ι := ι) R α hR hα
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ a b weights scale tubeVolume ell hδ hsmall hscale htube hell hlog
    hweights hTubeBall hcommon hscaleNet hbody hlarge shade τ D hunit hshade hfull hbudget
  obtain ⟨ω, hsize, hcert⟩ := hproducer δ a b weights scale tubeVolume ell
    hδ hsmall hscale htube hell hlog hweights hTubeBall hcommon hscaleNet hbody hlarge
  let weightedCert := weightedConvexClusteringCertificate_of_segment_tubes Finset.univ a b δ scale
    weights hδ hscale.le hweights hbody
  have hvolume : ∀ i ∈ Finset.univ,
      volume (Metric.cthickening δ (segment ℝ (a i) (b i))) = ENNReal.ofReal tubeVolume := by
    intro i hi
    rw [← hcommon i hi, ENNReal.ofReal_toReal (weightedCert.tube_volume_ne_top i)]
  obtain ⟨selected, hsel, hpair, hcard, hmass, hfullSelected, hsource⟩ :=
    exists_carrierED_sample_with_sourceShadeBudget Finset.univ (bernoulliProductSample ω)
      (Finset.subset_univ _) a b shade weights δ R scale tubeVolume 4 τ _ D hδ hR hscale htube.le
      (by norm_num) (fun i _ => hunit i) (fun i _ => hweights i) (fun i _ => hshade i)
      hvolume (fun i _ => hfull i) (by simpa using hsize) hcert hTubeBall hbudget
  have hinj := carrierED_injOn_of_volume_toReal_pos selected
    (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) hpair
    (fun i _ => weightedCert.tube_volume_pos i)
  refine ⟨ω, selected, hsel, hcert.restrict hsel, hinj, hpair, ?_, hcard, hmass, hfullSelected,
    shade_averageFullness_of_pointwise volume selected
      (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) shade τ hfullSelected, ?_⟩
  · have hcardReal : ((bernoulliProductSample ω).card : ℝ) ≤ (D + 1 : ℝ) * (selected.card : ℝ) := by
      exact_mod_cast hcard
    nlinarith [hsize]
  · simpa using hsource

/-- Clustering certificates may be relaxed to a larger explicit constant. -/
theorem SampledConvexClusteringCertificate.mono
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {indices : Finset ι} {core : ι → Set E} {δ : ℝ} {A B : ℝ≥0∞}
    (cert : SampledConvexClusteringCertificate indices core δ A) (hAB : A ≤ B) :
    SampledConvexClusteringCertificate indices core δ B := by
  constructor
  intro K hK J hJ hcontained
  exact (cert.convex_test_bound K hK J hJ hcontained).trans (mul_le_mul' hAB le_rfl)

/-- A uniform scale threshold absorbs the actual source logarithmic coefficient. Its
constants are fixed before both the scale and the matching logarithmic coordinate. -/
theorem exists_small_scale_logarithmic_le_rpow
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ ell : ℝ, 0 < δ → δ < δ₀ → Real.exp (-ell) = δ →
        C * (1 + ell) ≤ δ ^ (-ε) := by
  let T := max 1 (4 * C / ε ^ 2)
  have hT : 1 ≤ T := le_max_left _ _
  refine ⟨Real.exp (-T), Real.exp_pos _, ?_, ?_⟩
  · exact (Real.exp_le_one_iff).mpr (by linarith)
  · intro δ ell hδ hsmall hlog
    have hellT : T < ell := by
      rw [← hlog] at hsmall
      have := Real.exp_lt_exp.mp hsmall
      linarith
    have hell : 1 ≤ ell := hT.trans hellT.le
    have hepsSq : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hcoef : 4 * C ≤ ell * ε ^ 2 :=
      (div_le_iff₀ hepsSq).mp ((le_max_right _ _).trans hellT.le)
    have hmul := mul_le_mul_of_nonneg_right hcoef (by linarith : 0 ≤ ell)
    have hexp := Real.pow_div_factorial_le_exp (ε * ell) (mul_nonneg hε.le (by linarith)) 2
    norm_num at hexp
    have hbound : C * (1 + ell) ≤ Real.exp (ε * ell) := by
      calc
        _ ≤ 2 * C * ell := by nlinarith
        _ ≤ (ε * ell) ^ 2 / 2 := by nlinarith
        _ ≤ _ := hexp
    rw [← hlog, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    convert hbound using 1 <;> congr 1 <;> ring

/-- Natural rounding pays the line-budget and its degree-plus-one loss at a common scale.
The actual integer is `ceil(B(1+ell))`; no integer-budget premise is left to the caller. -/
theorem exists_small_scale_rounded_logarithmic_budget
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ ell : ℝ, 0 < δ → δ < δ₀ → 0 ≤ ell → Real.exp (-ell) = δ →
        ∃ D : ℕ, ENNReal.ofReal (B * (1 + ell)) ≤ (D : ℝ≥0∞) ∧
          ((D + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-ε)) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hpay⟩ :=
    exists_small_scale_logarithmic_le_rpow (B + 2) ε (by linarith) hε
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ ell hδ hsmall hell hlog
  let D := ⌈B * (1 + ell)⌉₊
  have hupper := Nat.ceil_lt_add_one (by positivity : 0 ≤ B * (1 + ell))
  have hD : ((D + 1 : ℕ) : ℝ) ≤ (B + 2) * (1 + ell) := by
    dsimp [D]
    push_cast
    nlinarith
  have hlower := Nat.le_ceil (B * (1 + ell))
  refine ⟨D, ?_, ?_⟩
  · rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hlower
  · rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hD.trans (hpay δ ell hδ hsmall hlog))

/-- For the actual three-dimensional source constants, one uniform scale threshold pays
both the selected clustering constant and the rounded radius-27 conflict budget. -/
theorem exists_small_scale_sourceSample_exponentBudget
    (R α η ε : ℝ) (hR : 0 ≤ R) (hα : 0 < α) (hη : 0 < η) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ ell : ℝ, 0 < δ → δ < δ₀ → 0 ≤ ell → Real.exp (-ell) = δ →
        let A := ENNReal.ofReal (32 * (1 + ell)) *
          (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor 3 ((3 : ℝ) * R + R) α 1) *
            ENNReal.ofReal ((2 : ℝ)^3 * ((3 : ℕ).factorial : ℝ)))
        A ≤ ENNReal.ofReal (δ ^ (-η)) ∧
          ∃ D : ℕ, A * ENNReal.ofReal (1458 * R) ≤ (D : ℝ≥0∞) ∧
            ((D + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-ε)) := by
  let F := orthogonalBoxNetRelativeVolumeFactor 3 ((3 : ℝ) * R + R) α 1
  have hF : 0 ≤ F := by dsimp [F, orthogonalBoxNetRelativeVolumeFactor]; positivity
  let C := 32 * F * ((2 : ℝ)^3 * ((3 : ℕ).factorial : ℝ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let B := C * (1458 * R)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨δA, hδA, hδA1, hA⟩ := exists_small_scale_logarithmic_le_rpow C η hC hη
  obtain ⟨δD, hδD, hδD1, hD⟩ := exists_small_scale_rounded_logarithmic_budget B ε hB hε
  refine ⟨min δA δD, lt_min hδA hδD, (min_le_left _ _).trans hδA1, ?_⟩
  intro δ ell hδ hsmall hell hlog
  have hrepr : ENNReal.ofReal (32 * (1 + ell)) *
      (ENNReal.ofReal F * ENNReal.ofReal ((2 : ℝ)^3 * ((3 : ℕ).factorial : ℝ))) =
      ENNReal.ofReal (C * (1 + ell)) := by
    rw [← ENNReal.ofReal_mul hF, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 32 * (1 + ell))]
    congr 1
    dsimp [C]
    ring
  change _ ∧ ∃ D : ℕ, _ ≤ (D : ℝ≥0∞) ∧ _
  rw [hrepr]
  refine ⟨ENNReal.ofReal_le_ofReal (hA δ ell hδ (hsmall.trans_le (min_le_left _ _)) hlog), ?_⟩
  obtain ⟨D, hbudget, hloss⟩ := hD δ ell hδ (hsmall.trans_le (min_le_right _ _)) hell hlog
  refine ⟨D, ?_, hloss⟩
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C * (1 + ell))]
  convert hbudget using 1 <;> congr 1 <;> dsimp [B] <;> ring

/-- The actual weighted unit-segment source family produces its carrier-ED selection with
an automatically chosen radius-27 integer budget. Both clustering certificates and the exponent
loss bound concern the same realization and retained indices; the caller supplies no `D` or
integer-budget hypothesis. The source fullness parameter remains explicit. -/
theorem exists_small_scale_carrierED_with_exponentBudget_of_unit_segment_weighted_body_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (R α η ε : ℝ) (hR : 0 ≤ R) (hα : 0 < α)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (δ : ℝ) (a b : ι → BoxAmbient 3) (weights : ι → ℝ) (scale tubeVolume ell : ℝ),
        0 < δ → δ < δ₀ → 0 < scale → 0 < tubeVolume → 0 ≤ ell →
        Real.exp (-ell) = δ → (∀ i, 0 ≤ weights i) →
        (∀ i ∈ Finset.univ,
          Metric.cthickening δ (segment ℝ (a i) (b i)) ⊆ Metric.closedBall 0 R) →
        (∀ i ∈ Finset.univ,
          (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal = tubeVolume) →
        α * δ ^ 2 ≤ √(Fintype.card (BoxParameterIndex 3) : ℝ) * (((3 : ℝ) * R + R) + 1) →
        (∀ K : Set (BoxAmbient 3), IsCompact K → Convex ℝ K → 0 < volume K →
          (∑ i ∈ tubeIndicesContainedInSet Finset.univ
              (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) K,
            weights i * (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal) ≤
            scale * (volume K).toReal) →
        32 * (1 + ell) ≤ (∑ i : ι, weights i / scale) →
        ∀ (shade : ι → Set (BoxAmbient 3)) (τ : ℝ≥0∞),
          (∀ i, ‖b i - a i‖ = 1) →
          (∀ i, shade i ⊆ Metric.cthickening δ (segment ℝ (a i) (b i))) →
          (∀ i, τ * volume (Metric.cthickening δ (segment ℝ (a i) (b i))) ≤ volume (shade i)) →
          ∃ D : ℕ, ((D + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-ε)) ∧
          ((4 * (D + 1) : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-ε)) ∧
          ∃ ω, ∃ selected ⊆ bernoulliProductSample ω,
            SampledConvexClusteringCertificate selected (fun i => segment ℝ (a i) (b i)) δ
              (ENNReal.ofReal (32 * (1 + ell)) *
                (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor 3
                  ((3 : ℝ) * R + R) α 1) * ENNReal.ofReal ((2 : ℝ)^3 * ((3 : ℕ).factorial : ℝ)))) ∧
            SampledConvexClusteringCertificate selected (fun i => segment ℝ (a i) (b i)) δ
              (ENNReal.ofReal (δ ^ (-η))) ∧
            Set.InjOn (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) (selected : Set ι) ∧
            (selected : Set ι).Pairwise (fun i j => IsCarrierEssentiallyDistinct
              (Metric.cthickening δ (segment ℝ (a i) (b i)))
              (Metric.cthickening δ (segment ℝ (a j) (b j)))) ∧
            ((∑ i : ι, weights i / scale) ≤ 4 * (D + 1) * (selected.card : ℝ)) ∧
            ((bernoulliProductSample ω).card ≤ (D + 1) * selected.card) ∧
            (∑ i ∈ bernoulliProductSample ω, volume (shade i) ≤
              (D + 1 : ℕ) * ∑ i ∈ selected, volume (shade i)) ∧
            (∀ i ∈ selected,
              τ * volume (Metric.cthickening δ (segment ℝ (a i) (b i))) ≤ volume (shade i)) ∧
            (τ * (∑ i ∈ selected, volume (Metric.cthickening δ (segment ℝ (a i) (b i)))) ≤
              ∑ i ∈ selected, volume (shade i)) ∧
            (∑ i : ι, ENNReal.ofReal (weights i) * volume (shade i)) ≤
              ENNReal.ofReal (scale * (4 * (D + 1) * (selected.card : ℝ)) * tubeVolume) ∧
            (∑ i : ι, ENNReal.ofReal (weights i) * volume (shade i)) ≤
              ENNReal.ofReal (scale * (δ ^ (-ε) * (selected.card : ℝ)) * tubeVolume) := by
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨δP, hδP, hδP1, hproducer⟩ :=
    exists_small_scale_carrierED_of_unit_segment_weighted_body_bound (ι := ι) R α hR hα
  obtain ⟨δB, hδB, hδB1, hpay⟩ :=
    exists_small_scale_sourceSample_exponentBudget R α η (ε / 2) hR hα hη hhalf
  obtain ⟨δ4, hδ4, hδ41, hfour⟩ :=
    exists_small_scale_logarithmic_le_rpow 4 (ε / 2) (by norm_num) hhalf
  refine ⟨min δP (min δB δ4), lt_min hδP (lt_min hδB hδ4),
    (min_le_left _ _).trans hδP1, ?_⟩
  intro δ a b weights scale tubeVolume ell hδ hsmall hscale htube hell hlog
    hweights hTubeBall hcommon hscaleNet hbody hlarge shade τ hunit hshade hfull
  have hsmallP := hsmall.trans_le (min_le_left _ _)
  have hsmallB := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hsmall4 := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  obtain ⟨hA, D, hbudget, hloss⟩ := hpay δ ell hδ hsmallB hell hlog
  have hfourReal : 4 ≤ δ ^ (-(ε / 2)) :=
    (by nlinarith : (4 : ℝ) ≤ 4 * (1 + ell)).trans (hfour δ ell hδ hsmall4 hlog)
  have hfourENN : (4 : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-(ε / 2))) := by
    simpa using ENNReal.ofReal_le_ofReal hfourReal
  have hpowNonneg : 0 ≤ δ ^ (-(ε / 2)) := Real.rpow_nonneg hδ.le _
  have hpow : ENNReal.ofReal (δ ^ (-(ε / 2))) * ENNReal.ofReal (δ ^ (-(ε / 2))) =
      ENNReal.ofReal (δ ^ (-ε)) := by
    rw [← ENNReal.ofReal_mul hpowNonneg, ← Real.rpow_add hδ,
      show -(ε / 2) + -(ε / 2) = -ε by ring]
  have htotal : ((4 * (D + 1) : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-ε)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (mul_le_mul' hfourENN hloss).trans_eq hpow
  have hDloss : ((D + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-ε)) := by
    have hnat : D + 1 ≤ 4 * (D + 1) := by omega
    have hcast : ((D + 1 : ℕ) : ℝ≥0∞) ≤ ((4 * (D + 1) : ℕ) : ℝ≥0∞) := by
      exact_mod_cast hnat
    exact hcast.trans htotal
  have htotalReal : 4 * (D + 1 : ℝ) ≤ δ ^ (-ε) := by
    have hreal : ((4 * (D + 1) : ℕ) : ℝ) ≤ δ ^ (-ε) := by
      apply (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hδ.le _)).mp
      simpa only [ENNReal.ofReal_natCast] using htotal
    exact_mod_cast hreal
  obtain ⟨ω, selected, hsel, hcert, hinj, hpair, hsize, hcard, hmass,
      hpointwise, haverage, hsource⟩ :=
    hproducer δ a b weights scale tubeVolume ell hδ hsmallP
      hscale htube hell hlog hweights hTubeBall hcommon hscaleNet hbody hlarge
      shade τ D hunit hshade hfull hbudget
  have hsourcePaid : (∑ i : ι, ENNReal.ofReal (weights i) * volume (shade i)) ≤
      ENNReal.ofReal (scale * (δ ^ (-ε) * (selected.card : ℝ)) * tubeVolume) := by
    apply hsource.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right htotalReal (Nat.cast_nonneg _)) hscale.le) htube.le
  exact ⟨D, hDloss, htotal, ω, selected, hsel, hcert, hcert.mono hA, hinj, hpair,
    hsize, hcard, hmass, hpointwise, haverage, hsource, hsourcePaid⟩

/-- The actual deterministic small-size source branch with its logarithmic loss absorbed.
The scale threshold depends only on `L,ε`, before all actual finite weights and shadings. -/
theorem exists_small_scale_weightedShadeMass_of_small_normalizedWeight
    {E ι : Type*} [MeasurableSpace E] [DecidableEq ι]
    (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ ell scale : ℝ, 0 < δ → δ < δ₀ → Real.exp (-ell) = δ → 0 < scale →
        ∀ (μ : Measure E) (indices : Finset ι) (weights : ι → ℝ) (shade : ι → Set E),
          (∀ i ∈ indices, 0 ≤ weights i) →
          (∑ i ∈ indices, weights i / scale) ≤ L * (1 + ell) →
          (∑ i ∈ indices, ENNReal.ofReal (weights i) * μ (shade i)) ≤
            ENNReal.ofReal (scale * δ ^ (-ε)) * μ (⋃ i ∈ indices, shade i) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hpay⟩ := exists_small_scale_logarithmic_le_rpow L ε hL hε
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ ell scale hδ hsmall hlog hscale μ indices weights shade hweights hsize
  have hmass := weightedShadeMass_le_logarithmic_union_of_small_normalizedWeight
    μ indices weights shade scale L ell hscale hweights hsize
  apply hmass.trans
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_left (hpay δ ell hδ hsmall hlog) hscale.le
  nlinarith

/-- A single uniform threshold gives the manuscript's actual small/large source dichotomy.
The small branch already controls the weighted mass by the original union; the large branch
retains the complete proved sample/selection data. No finite-scale Kakeya union estimate is
assumed or asserted for that large branch. -/
theorem exists_small_scale_weightedSource_dichotomy_of_unit_segment_weighted_body_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (R α η ε : ℝ) (hR : 0 ≤ R) (hα : 0 < α)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (δ : ℝ) (a b : ι → BoxAmbient 3) (weights : ι → ℝ) (scale tubeVolume ell : ℝ),
        0 < δ → δ < δ₀ → 0 < scale → 0 < tubeVolume → 0 ≤ ell →
        Real.exp (-ell) = δ → (∀ i, 0 ≤ weights i) →
        (∀ i ∈ Finset.univ,
          Metric.cthickening δ (segment ℝ (a i) (b i)) ⊆ Metric.closedBall 0 R) →
        (∀ i ∈ Finset.univ,
          (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal = tubeVolume) →
        α * δ ^ 2 ≤ √(Fintype.card (BoxParameterIndex 3) : ℝ) * (((3 : ℝ) * R + R) + 1) →
        (∀ K : Set (BoxAmbient 3), IsCompact K → Convex ℝ K → 0 < volume K →
          (∑ i ∈ tubeIndicesContainedInSet Finset.univ
              (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) K,
            weights i * (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal) ≤
            scale * (volume K).toReal) →
        ∀ (shade : ι → Set (BoxAmbient 3)) (τ : ℝ≥0∞),
          (∀ i, ‖b i - a i‖ = 1) →
          (∀ i, shade i ⊆ Metric.cthickening δ (segment ℝ (a i) (b i))) →
          (∀ i, τ * volume (Metric.cthickening δ (segment ℝ (a i) (b i))) ≤ volume (shade i)) →
          ((∑ i : ι, ENNReal.ofReal (weights i) * volume (shade i)) ≤
            ENNReal.ofReal (scale * δ ^ (-ε)) * volume (⋃ i : ι, shade i)) ∨
          (∃ D : ℕ, ((D + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-ε)) ∧
          ((4 * (D + 1) : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-ε)) ∧
          ∃ ω, ∃ selected ⊆ bernoulliProductSample ω,
            SampledConvexClusteringCertificate selected (fun i => segment ℝ (a i) (b i)) δ
              (ENNReal.ofReal (32 * (1 + ell)) *
                (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor 3
                  ((3 : ℝ) * R + R) α 1) * ENNReal.ofReal ((2 : ℝ)^3 * ((3 : ℕ).factorial : ℝ)))) ∧
            SampledConvexClusteringCertificate selected (fun i => segment ℝ (a i) (b i)) δ
              (ENNReal.ofReal (δ ^ (-η))) ∧
            Set.InjOn (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) (selected : Set ι) ∧
            (selected : Set ι).Pairwise (fun i j => IsCarrierEssentiallyDistinct
              (Metric.cthickening δ (segment ℝ (a i) (b i)))
              (Metric.cthickening δ (segment ℝ (a j) (b j)))) ∧
            ((∑ i : ι, weights i / scale) ≤ 4 * (D + 1) * (selected.card : ℝ)) ∧
            ((bernoulliProductSample ω).card ≤ (D + 1) * selected.card) ∧
            (∑ i ∈ bernoulliProductSample ω, volume (shade i) ≤
              (D + 1 : ℕ) * ∑ i ∈ selected, volume (shade i)) ∧
            (∀ i ∈ selected,
              τ * volume (Metric.cthickening δ (segment ℝ (a i) (b i))) ≤ volume (shade i)) ∧
            (τ * (∑ i ∈ selected, volume (Metric.cthickening δ (segment ℝ (a i) (b i)))) ≤
              ∑ i ∈ selected, volume (shade i)) ∧
            (∑ i : ι, ENNReal.ofReal (weights i) * volume (shade i)) ≤
              ENNReal.ofReal (scale * (4 * (D + 1) * (selected.card : ℝ)) * tubeVolume) ∧
            (∑ i : ι, ENNReal.ofReal (weights i) * volume (shade i)) ≤
              ENNReal.ofReal (scale * (δ ^ (-ε) * (selected.card : ℝ)) * tubeVolume)) := by
  obtain ⟨δS, hδS, hδS1, hsmallProducer⟩ :=
    exists_small_scale_weightedShadeMass_of_small_normalizedWeight
      (E := BoxAmbient 3) (ι := ι) 32 ε (by norm_num) hε
  obtain ⟨δL, hδL, hδL1, hlargeProducer⟩ :=
    exists_small_scale_carrierED_with_exponentBudget_of_unit_segment_weighted_body_bound
      (ι := ι) R α η ε hR hα hη hε
  refine ⟨min δS δL, lt_min hδS hδL, (min_le_left _ _).trans hδS1, ?_⟩
  intro δ a b weights scale tubeVolume ell hδ hsmall hscale htube hell hlog
    hweights hTubeBall hcommon hscaleNet hbody shade τ hunit hshade hfull
  by_cases hlarge : 32 * (1 + ell) ≤ ∑ i : ι, weights i / scale
  · exact Or.inr (hlargeProducer δ a b weights scale tubeVolume ell hδ
      (hsmall.trans_le (min_le_right _ _)) hscale htube hell hlog hweights hTubeBall
      hcommon hscaleNet hbody hlarge shade τ hunit hshade hfull)
  · apply Or.inl
    have hsize : (∑ i ∈ Finset.univ, weights i / scale) ≤ 32 * (1 + ell) := by
      simpa using (not_le.mp hlarge).le
    simpa using hsmallProducer δ ell scale hδ (hsmall.trans_le (min_le_left _ _)) hlog hscale
      volume Finset.univ weights shade (fun i _ => hweights i) hsize

/-- A finite convex envelope and a uniform positive tube-volume lower bound control the
sum of the original indexed weights. This is the source's fixed-ball test, without sampling. -/
theorem WeightedConvexClusteringCertificate.totalWeight_le_of_envelope
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {indices : Finset ι} {tube : ι → Set E} {weights : ι → ℝ} {scale : ℝ}
    (cert : WeightedConvexClusteringCertificate indices tube weights scale)
    (K : Set E) (hK : Convex ℝ K) (hKtop : volume K ≠ ⊤)
    (hcontained : ∀ i ∈ indices, tube i ⊆ K)
    (vmin : ℝ) (hvmin : 0 < vmin)
    (hvol : ∀ i ∈ indices, vmin ≤ (volume (tube i)).toReal) :
    (∑ i ∈ indices, weights i) ≤ scale * (volume K).toReal / vmin := by
  have htest := cert.convex_test_bound K hK hKtop indices (Finset.Subset.refl _) hcontained
  have hsum : (∑ i ∈ indices, weights i) * vmin ≤
      ∑ i ∈ indices, weights i * (volume (tube i)).toReal := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (hvol i hi) (cert.weights_nonneg i)
  exact (le_div_iff₀ hvmin).mpr (hsum.trans htest)

/-- The source envelope test controls the actual weighted shade mass by its actual union. -/
theorem WeightedConvexClusteringCertificate.weightedShadeMass_le_of_envelope
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [DecidableEq ι]
    {indices : Finset ι} {tube : ι → Set E} {weights : ι → ℝ} {scale : ℝ}
    (cert : WeightedConvexClusteringCertificate indices tube weights scale)
    (K : Set E) (hK : Convex ℝ K) (hKtop : volume K ≠ ⊤)
    (hcontained : ∀ i ∈ indices, tube i ⊆ K)
    (vmin : ℝ) (hvmin : 0 < vmin)
    (hvol : ∀ i ∈ indices, vmin ≤ (volume (tube i)).toReal)
    (shade : ι → Set E) :
    (∑ i ∈ indices, ENNReal.ofReal (weights i) * volume (shade i)) ≤
      ENNReal.ofReal (scale * (volume K).toReal / vmin) * volume (⋃ i ∈ indices, shade i) := by
  apply (weightedShadeMass_le_totalWeight_mul_union volume indices weights shade
    (fun i _ => cert.weights_nonneg i)).trans
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal
    (cert.totalWeight_le_of_envelope K hK hKtop hcontained vmin hvmin hvol)) le_rfl

/-- The source's bounded-scale branch for actual unit segment tubes. The explicit constant
is `volume(ball R)/(πρ²)` for scales `δ ≥ ρ > 0`. No common-volume premise, shading density,
separation or finite-scale Kakeya estimate is required. -/
theorem weightedShadeMass_le_boundedScale_union_of_unit_segment_weighted_body_bound
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (a b : ι → BoxAmbient 3) (weights : ι → ℝ) (shade : ι → Set (BoxAmbient 3))
    (δ ρ R scale : ℝ) (hρ : 0 < ρ) (hρδ : ρ ≤ δ) (hscale : 0 ≤ scale)
    (hweights : ∀ i, 0 ≤ weights i) (hunit : ∀ i ∈ indices, ‖b i - a i‖ = 1)
    (hball : ∀ i ∈ indices,
      Metric.cthickening δ (segment ℝ (a i) (b i)) ⊆ Metric.closedBall 0 R)
    (hbody : ∀ K : Set (BoxAmbient 3), IsCompact K → Convex ℝ K → 0 < volume K →
      (∑ i ∈ tubeIndicesContainedInSet indices
          (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) K,
        weights i * (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal) ≤
        scale * (volume K).toReal) :
    (∑ i ∈ indices, ENNReal.ofReal (weights i) * volume (shade i)) ≤
      ENNReal.ofReal (scale * (volume (Metric.closedBall (0 : BoxAmbient 3) R)).toReal /
        (ρ ^ 2 * Real.pi)) * volume (⋃ i ∈ indices, shade i) := by
  have hδ : 0 < δ := hρ.trans_le hρδ
  let cert := weightedConvexClusteringCertificate_of_segment_tubes indices a b δ scale
    weights hδ hscale hweights hbody
  have hdim : Module.finrank ℝ (BoxAmbient 3) = 3 := by simp [BoxAmbient]
  have hvol : ∀ i ∈ indices,
      ρ ^ 2 * Real.pi ≤ (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal := by
    intro i hi
    have hv := (volume_unitAxisSegment_cthickening_bounds hdim (b i - a i)
      (hunit i hi) hδ.le).1
    have hseg : segment ℝ (a i) (b i) = segment ℝ (a i) (a i + (b i - a i)) := by
      congr 1 <;> module
    rw [← volume_cthickening_segment_translate (a i) (b i - a i) hδ.le, ← hseg] at hv
    have hreal := ENNReal.toReal_mono (cert.tube_volume_ne_top i) hv
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hδ.le,
      ENNReal.toReal_ofReal Real.pi_pos.le] at hreal
    have hsq : ρ ^ 2 ≤ δ ^ 2 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hsq Real.pi_pos.le).trans hreal
  exact cert.weightedShadeMass_le_of_envelope (Metric.closedBall 0 R) (convex_closedBall 0 R)
    (isCompact_closedBall (0 : BoxAmbient 3) R).measure_lt_top.ne hball
    (ρ ^ 2 * Real.pi) (by positivity) hvol shade

/-- Fixed source geometry admits a uniform scale threshold satisfying the actual
three-dimensional box-net admissibility inequality; it is not a caller hypothesis. -/
theorem exists_small_scale_orthogonalBoxNet_admissible_three
    (R α : ℝ) (hR : 0 ≤ R) (hα : 0 < α) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      α * δ ^ 2 ≤ √(Fintype.card (BoxParameterIndex 3) : ℝ) * (((3 : ℝ) * R + R) + 1) := by
  let H := √(Fintype.card (BoxParameterIndex 3) : ℝ) * (((3 : ℝ) * R + R) + 1)
  have hcard : Fintype.card (BoxParameterIndex 3) = 15 := by simp [BoxParameterIndex]
  have hH : 0 < H := by dsimp [H]; rw [hcard]; positivity
  have hden : 0 < α + 1 := by linarith
  refine ⟨min 1 (H / (α + 1)), lt_min (by norm_num) (div_pos hH hden), min_le_left _ _, ?_⟩
  intro δ hδ hsmall
  have hδ1 : δ ≤ 1 := (hsmall.trans_le (min_le_left _ _)).le
  have hpay : δ * (α + 1) ≤ H :=
    (le_div_iff₀ hden).mp (hsmall.trans_le (min_le_right _ _)).le
  have hsq : δ ^ 2 ≤ δ := by nlinarith
  change α * δ ^ 2 ≤ H
  nlinarith [mul_le_mul_of_nonneg_left hsq hα.le]

/-- Actual equal-length source tubes have a common positive finite real volume. No
nonempty-index assumption is imposed: an empty family has a vacuous common-volume assertion. -/
theorem exists_common_positive_volume_of_unit_segment_tubes
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} (indices : Finset ι) (a b : ι → E) (δ : ℝ) (hδ : 0 < δ)
    (hunit : ∀ i ∈ indices, ‖b i - a i‖ = 1) :
    ∃ tubeVolume : ℝ, 0 < tubeVolume ∧
      ∀ i ∈ indices, (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal = tubeVolume := by
  classical
  by_cases hne : indices.Nonempty
  · obtain ⟨j, hj⟩ := hne
    have hcompact : IsCompact (segment ℝ (a j) (b j)) := by
      rw [segment_eq_image']
      exact isCompact_Icc.image (by fun_prop)
    have htop : volume (Metric.cthickening δ (segment ℝ (a j) (b j))) ≠ ⊤ :=
      hcompact.isBounded.cthickening.measure_lt_top.ne
    have hball : Metric.ball (a j) δ ⊆ Metric.cthickening δ (segment ℝ (a j) (b j)) :=
      Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_cthickening (left_mem_segment ℝ _ _) δ)
    have hpos := (Metric.measure_ball_pos (volume : Measure E) (a j) hδ).trans_le (measure_mono hball)
    refine ⟨(volume (Metric.cthickening δ (segment ℝ (a j) (b j)))).toReal,
      ENNReal.toReal_pos hpos.ne' htop, ?_⟩
    intro i hi
    have h := volume_segment_cthickening_eq_unitCarrier (a i) (b i) (a j) (b j - a j)
      hδ.le (hunit i hi) (hunit j hj)
    have hseg : segment ℝ (a j) (a j + (b j - a j)) = segment ℝ (a j) (b j) := by
      congr 1 <;> module
    rw [hseg] at h
    exact congrArg ENNReal.toReal h
  · exact ⟨1, by norm_num, fun i hi => False.elim (hne ⟨i, hi⟩)⟩

/-- The actual unit-segment source dichotomy, with the formerly caller-supplied common
positive tube volume and net admissibility both proved internally. The threshold is fixed
before all endpoints, original weights, shadings and selected indices. -/
theorem exists_small_scale_weightedSource_dichotomy_of_actual_unit_segments
    {ι : Type*} [Fintype ι] [DecidableEq ι] (R α η ε : ℝ) (hR : 0 ≤ R) (hα : 0 < α)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (δ : ℝ) (a b : ι → BoxAmbient 3) (weights : ι → ℝ) (scale ell : ℝ),
        0 < δ → δ < δ₀ → 0 < scale → 0 ≤ ell →
        Real.exp (-ell) = δ → (∀ i, 0 ≤ weights i) →
        (∀ i ∈ Finset.univ,
          Metric.cthickening δ (segment ℝ (a i) (b i)) ⊆ Metric.closedBall 0 R) →
        (∀ K : Set (BoxAmbient 3), IsCompact K → Convex ℝ K → 0 < volume K →
          (∑ i ∈ tubeIndicesContainedInSet Finset.univ
              (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) K,
            weights i * (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal) ≤
            scale * (volume K).toReal) →
        ∀ (shade : ι → Set (BoxAmbient 3)) (τ : ℝ≥0∞),
          (∀ i, ‖b i - a i‖ = 1) →
          (∀ i, shade i ⊆ Metric.cthickening δ (segment ℝ (a i) (b i))) →
          (∀ i, τ * volume (Metric.cthickening δ (segment ℝ (a i) (b i))) ≤ volume (shade i)) →
          ∃ tubeVolume : ℝ, 0 < tubeVolume ∧
          (∀ i, (volume (Metric.cthickening δ (segment ℝ (a i) (b i)))).toReal = tubeVolume) ∧
          (((∑ i : ι, ENNReal.ofReal (weights i) * volume (shade i)) ≤
            ENNReal.ofReal (scale * δ ^ (-ε)) * volume (⋃ i : ι, shade i)) ∨
          (∃ D : ℕ, ((D + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-ε)) ∧
          ((4 * (D + 1) : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-ε)) ∧
          ∃ ω, ∃ selected ⊆ bernoulliProductSample ω,
            SampledConvexClusteringCertificate selected (fun i => segment ℝ (a i) (b i)) δ
              (ENNReal.ofReal (32 * (1 + ell)) *
                (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor 3
                  ((3 : ℝ) * R + R) α 1) * ENNReal.ofReal ((2 : ℝ)^3 * ((3 : ℕ).factorial : ℝ)))) ∧
            SampledConvexClusteringCertificate selected (fun i => segment ℝ (a i) (b i)) δ
              (ENNReal.ofReal (δ ^ (-η))) ∧
            Set.InjOn (fun i => Metric.cthickening δ (segment ℝ (a i) (b i))) (selected : Set ι) ∧
            (selected : Set ι).Pairwise (fun i j => IsCarrierEssentiallyDistinct
              (Metric.cthickening δ (segment ℝ (a i) (b i)))
              (Metric.cthickening δ (segment ℝ (a j) (b j)))) ∧
            ((∑ i : ι, weights i / scale) ≤ 4 * (D + 1) * (selected.card : ℝ)) ∧
            ((bernoulliProductSample ω).card ≤ (D + 1) * selected.card) ∧
            (∑ i ∈ bernoulliProductSample ω, volume (shade i) ≤
              (D + 1 : ℕ) * ∑ i ∈ selected, volume (shade i)) ∧
            (∀ i ∈ selected,
              τ * volume (Metric.cthickening δ (segment ℝ (a i) (b i))) ≤ volume (shade i)) ∧
            (τ * (∑ i ∈ selected, volume (Metric.cthickening δ (segment ℝ (a i) (b i)))) ≤
              ∑ i ∈ selected, volume (shade i)) ∧
            (∑ i : ι, ENNReal.ofReal (weights i) * volume (shade i)) ≤
              ENNReal.ofReal (scale * (4 * (D + 1) * (selected.card : ℝ)) * tubeVolume) ∧
            (∑ i : ι, ENNReal.ofReal (weights i) * volume (shade i)) ≤
              ENNReal.ofReal (scale * (δ ^ (-ε) * (selected.card : ℝ)) * tubeVolume))) := by
  obtain ⟨δP, hδP, hδP1, hproducer⟩ :=
    exists_small_scale_weightedSource_dichotomy_of_unit_segment_weighted_body_bound
      (ι := ι) R α η ε hR hα hη hε
  obtain ⟨δN, hδN, hδN1, hnet⟩ := exists_small_scale_orthogonalBoxNet_admissible_three R α hR hα
  refine ⟨min δP δN, lt_min hδP hδN, (min_le_left _ _).trans hδP1, ?_⟩
  intro δ a b weights scale ell hδ hsmall hscale hell hlog
    hweights hTubeBall hbody shade τ hunit hshade hfull
  obtain ⟨tubeVolume, htube, hcommon⟩ :=
    exists_common_positive_volume_of_unit_segment_tubes Finset.univ a b δ hδ (fun i _ => hunit i)
  refine ⟨tubeVolume, htube, (fun i => hcommon i (Finset.mem_univ i)), ?_⟩
  exact hproducer δ a b weights scale tubeVolume ell hδ (hsmall.trans_le (min_le_left _ _))
    hscale htube hell hlog hweights hTubeBall hcommon
    (hnet δ hδ (hsmall.trans_le (min_le_right _ _))) hbody shade τ hunit hshade hfull

end Kakeya4.Construction
