import Kakeya4.Hard.MultiplicativeConvolution.CoarseCapEnergy
import Kakeya4.Hard.MultiplicativeConvolution.GeneratedFlatness

/-! The analytic finite-scale flat-generated-coefficients theorem from the
manuscript's original interval cap. The fixed smoothing kernel is constructed
internally, and no energy, Fourier or flattening certificate is an input.
The original ratio law, common dilation and allowed-expression support remain
the responsibility of the actual geometric construction. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- All integers and losses precede the original law and scale. A small power
loss in its coarse interval cap produces an actual flat independent sum of products. -/
theorem exists_generated_flatness_of_coarseCap {S e : ℝ} (hS : 0 < S)
    (he : 0 < e) (he1 : e < 1) :
    ∃ (n k : ℕ) (h₀ q D : ℝ), 2 ≤ n ∧ 0 < k ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 0 < q ∧ 0 < D ∧
      ∀ (μ : Measure ℝ), IsProbabilityMeasure μ → UnitSupported μ →
        ∀ (h K : ℝ), 0 < h → h ≤ h₀ → 0 ≤ K → K ≤ h^(-q) →
          (∀ z R : ℝ, h ≤ R → R ≤ 1 → μ (closedBall z R) ≤ ENNReal.ofReal (K*R^S)) →
          ∀ x : ℝ, (generatedProductSumLaw (fun _ : Fin n ↦ μ) k).real
            (Icc (x-h) (x+h)) ≤ D*h^(1-e) := by
  let s : ℝ := min S 1 / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hsv : s < min S 1 := by dsimp [s]; linarith [lt_min hS zero_lt_one]
  have hsS : s < S := hsv.trans_le (min_le_left S 1)
  have hs1 : s < 1 := hsv.trans_le (min_le_right S 1)
  let n : ℕ := ⌈2/s⌉₊ + 2
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hns : 1 < (n:ℝ)*s := by
    have hc := Nat.le_ceil (2/s)
    have hn' : 2/s ≤ (n:ℝ) := by dsimp [n]; push_cast; linarith only [hc]
    have hm := (div_le_iff₀ hs).mp hn'
    nlinarith only [hm]
  have hsum : 1 < ∑ _j : Fin n, s := by simpa using hns
  obtain ⟨k, h₁, ε, D, hk, hh₁, hh₁1, hε, hε1, hD, hflat⟩ :=
    generatedProductSumLaw_flatness_of_uniformEnergy fixedKernel n hn (fun _ ↦ s)
      (fun _ ↦ ⟨hs, hs1.le⟩) hsum he he1
  obtain ⟨h₂, hh₂, hh₂1, henergy⟩ :=
    exists_smoothEnergy_window_cap_of_coarseCap fixedKernel hs hsS hs1 hε he
  refine ⟨n, k, min h₁ h₂, e*ε/2, D, hn, hk, lt_min hh₁ hh₂,
    (min_le_left _ _).trans hh₁1, by positivity, hD, ?_⟩
  intro μ hμ hsupp h K hh hhh hK hKq hcap x
  apply hflat (fun _ : Fin n ↦ μ) (fun _ ↦ hμ) (fun _ ↦ hsupp) h hh
    (hhh.trans (min_le_left _ _))
  · intro r hrlo hrhi _j
    exact henergy μ hμ h K hh (hhh.trans (min_le_right _ _)) hK hKq hcap r hrlo hrhi

#print axioms exists_generated_flatness_of_coarseCap
end Kakeya4.Hard.MultiplicativeConvolution
