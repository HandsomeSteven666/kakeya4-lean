import Kakeya4.Hard.MultiplicativeConvolution.JointExtractedTransport
import Kakeya4.Hard.MultiplicativeConvolution.ExactFrostmanExtraction
import Mathlib.Data.Finset.Lattice.Fold

/-! # Uniform joint extraction and transport directly from all original energy caps -/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal BigOperators

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Original energy caps simultaneously produce all actual Frostman laws and the joint outer-mass transport. -/
theorem exists_joint_Frostman_extraction {ι : Type*} [Fintype ι] [Nonempty ι]
    (κ : SmoothKernel) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ ε r₀ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)],
        (∀ i, UnitSupported (μ i)) → ∀ r : ℝ, 0 < r → r ≤ r₀ →
          (∀ i, smoothEnergy κ.law (s i) r (μ i) ≤ ENNReal.ofReal (r^(-ε))) →
          ∃ A : ι → Set ℝ, (∀ i, MeasurableSet (A i)) ∧
            (∀ i, μ i (A i) ≠ 0) ∧ (∀ i, μ i (A i)ᶜ ≤ ENNReal.ofReal (r^ε)) ∧
            (∀ i, IsProbabilityMeasure (unitRescaledSmoothLaw κ r (normalizedRestriction (μ i) (A i)))) ∧
            (∀ i, UnitSupported (unitRescaledSmoothLaw κ r (normalizedRestriction (μ i) (A i)))) ∧
            (∀ (i : ι) (z R : ℝ), 0 < R →
              unitRescaledSmoothLaw κ r (normalizedRestriction (μ i) (A i)) (closedBall z R) ≤
                ENNReal.ofReal (r^(-η)*R^(s i))) ∧
            ∀ E : Set (ι → ℝ), Measure.pi μ E ≤
              Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (normalizedRestriction (μ i) (A i)))
                (cthickening (r/2) ((fun x i ↦ x i/2) '' E)) +
                  (Fintype.card ι : ℝ≥0∞)*ENNReal.ofReal (r^ε) := by
  classical
  choose e d he he1 hd hd1 hextract using
    (fun i ↦ exists_exact_Frostman_probability_extraction κ (hs i).1 (hs i).2 hη hη1)
  let ε := Finset.univ.inf' Finset.univ_nonempty e
  let δ := Finset.univ.inf' Finset.univ_nonempty d
  have hε : 0 < ε := (Finset.lt_inf'_iff _).mpr (fun i _ ↦ he i)
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).mpr (fun i _ ↦ hd i)
  have hεle (i : ι) : ε ≤ e i := Finset.inf'_le _ (Finset.mem_univ i)
  have hδle (i : ι) : δ ≤ d i := Finset.inf'_le _ (Finset.mem_univ i)
  let j : ι := Classical.arbitrary ι
  have hε1 : ε ≤ 1 := (hεle j).trans (he1 j)
  have hδ1 : δ ≤ 1 := (hδle j).trans (hd1 j)
  obtain ⟨rhalf,hrhalf,hrhalf1,hsmall⟩ := exists_scale_rpow_le_half hε
  refine ⟨ε,min δ rhalf,hε,hε1,lt_min hδ hrhalf,(min_le_left _ _).trans hδ1,?_⟩
  intro μ _ hμ r hr hrr hcap
  have hrδ : r ≤ δ := hrr.trans (min_le_left _ _)
  have hr1 : r ≤ 1 := hrδ.trans hδ1
  have hh : r^ε ≤ (1/2:ℝ) := hsmall r hr (hrr.trans (min_le_right _ _))
  have hi := fun i ↦ hextract i (μ i) (hμ i) r hr (hrδ.trans (hδle i))
    ((hcap i).trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith [hεle i]))))
  choose A hA hloss hprob hsupp hball using hi
  have hloss' (i : ι) : μ i (A i)ᶜ ≤ ENNReal.ofReal (r^ε) :=
    (hloss i).trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hr hr1 (hεle i)))
  have hA0 (i : ι) : μ i (A i) ≠ 0 := by
    have hc : μ i (A i)ᶜ ≤ (1/2:ℝ≥0∞) := by
      have h := (hloss' i).trans (ENNReal.ofReal_le_ofReal hh)
      have heq : ENNReal.ofReal (1/2:ℝ) = (1/2:ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
        norm_num
      simpa only [heq] using h
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞) < 1/2)
      (measure_half_le_of_compl_le (μ i) (hA i) hc))
  refine ⟨A,hA,hA0,hloss',hprob,hsupp,hball,?_⟩
  intro E
  exact original_pi_mass_le_smoothed_add_card_loss κ μ A hA hA0 hr.le hloss' E

end Kakeya4.Hard.MultiplicativeConvolution
