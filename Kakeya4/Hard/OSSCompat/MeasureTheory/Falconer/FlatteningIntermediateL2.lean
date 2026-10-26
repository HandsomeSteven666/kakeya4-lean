






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningLocalPower
import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningPowerDoubling

/-! Unconditional intermediate-scale L2 flattening for all sufficiently high powers. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem OSS_original_energy_intermediate_L2_flattening (kernel : SmoothKernel) {s t β a : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s+t ≤ 1) (hβ : 0 < β) (ha : 0 < a) :
    ∃ ε r₀ : ℝ, ∃ K : ℕ, 0 < ε ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ 2 ≤ K ∧
    ∀ δ r : ℝ, 0 < δ → 0 < r → δ ≤ r → r ≤ δ^a → r ≤ r₀ →
    ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      UnitSupported μ → UnitSupported ν →
      smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-ε)) →
      smoothEnergy kernel.law t δ ν ≤ ENNReal.ofReal (δ^(-ε)) →
      ∀ k : ℕ, K ≤ k →
      densityL2 (additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k)
        (kernelProfile kernel r) ≤ ENNReal.ofReal (r^(s+t-1-β)) := by
  obtain ⟨ε,e,r₁,hε,he,_,hr₁,hr₁1,hlocal⟩ :=
    OSS_original_energy_slow_local_power_bound kernel hs ht hst hβ ha
  obtain ⟨N,r₂,hN,hr₂,hr₂1,hselect⟩ := exists_uniform_flattening_slow_step_from_two kernel he
  let K : ℕ := 2^(N+1)
  have hK : 2 ≤ K := by
    simpa [K] using Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) (by omega : 1≤N+1)
  refine ⟨ε,min r₁ r₂,K,hε,lt_min hr₁ hr₂,(min_le_left _ _).trans hr₁1,hK,?_⟩
  intro δ r hδ hr hδr hwindow hrr μ ν _ _ hμU hνU hμE hνE k hk
  let lawP := differenceLaw μ ∗ₘ differenceLaw ν
  have : IsProbabilityMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure lawP := by dsimp [lawP]; infer_instance
  have hterminal : densityL2 (additiveLawPower lawP K) (kernelProfile kernel r) ≤
      ENNReal.ofReal (r^(s+t-1-β)) := by
    rcases hselect lawP r hr (hrr.trans (min_le_right _ _)) with hlo | ⟨j,hj,hj2,_,hslow⟩
    · apply hlo.trans
      have hr1 : r ≤ 1 := (hrr.trans (min_le_left _ _)).trans hr₁1
      have hp : (1:ℝ) ≤ r^(s+t-1-β) := by
        simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hr hr1
          (by linarith : s+t-1-β≤0)
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
    · have hb := hlocal δ r hδ hr hδr hwindow (hrr.trans (min_le_left _ _))
        μ ν hμU hνU hμE hνE (2^(j+1)) hj2 hslow
      have hdown : densityL2 (additiveLawPower lawP K) (kernelProfile kernel r) ≤
          densityL2 (additiveLawPower lawP (2^(j+1)) ∗ additiveLawPower lawP (2^(j+1)))
            (kernelProfile kernel r) := by
        rw [← flatteningL2Seq_succ_eq_double kernel lawP r (j+1)]
        exact flatteningL2Seq_antitone kernel lawP r (by omega : j+1+1≤N+1)
      exact hdown.trans hb
  exact (densityL2_additiveLawPower_antitone lawP _ (measurable_kernelProfile kernel r) hk).trans hterminal

#print axioms OSS_original_energy_intermediate_L2_flattening
end OAI.Falconer

