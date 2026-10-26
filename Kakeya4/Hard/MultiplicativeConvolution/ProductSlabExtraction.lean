import Kakeya4.Hard.MultiplicativeConvolution.ProductSlabBound
import Kakeya4.Hard.MultiplicativeConvolution.JointFrostmanExtraction

/-! # The initial all-direction slab bound produced from the original energy caps -/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Original energy caps produce an actual product probability with the initial min(s,t) slab exponent. -/
theorem exists_planar_initial_slab_extraction (κ : SmoothKernel) {s t η : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ ε r₀ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        UnitSupported μ → UnitSupported ν → ∀ r : ℝ, 0 < r → r ≤ r₀ →
          smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε)) →
          smoothEnergy κ.law t r ν ≤ ENNReal.ofReal (r^(-ε)) →
          ∃ A B : Set ℝ, MeasurableSet A ∧ MeasurableSet B ∧ μ A ≠ 0 ∧ ν B ≠ 0 ∧
            μ Aᶜ ≤ ENNReal.ofReal (r^ε) ∧ ν Bᶜ ≤ ENNReal.ofReal (r^ε) ∧
            let ρ := planarProductLaw
              (unitRescaledSmoothLaw κ r (normalizedRestriction μ A))
              (unitRescaledSmoothLaw κ r (normalizedRestriction ν B))
            IsProbabilityMeasure ρ ∧ (∀ᵐ z ∂ρ, ∀ i : Fin 2, |z i| ≤ 1) ∧
              ∀ (a b c R : ℝ), a^2+b^2 = 1 → 0 < R →
                ρ (planarSlab a b c R) ≤ ENNReal.ofReal (2*r^(-η)*R^(min s t)) := by
  let q : Fin 2 → ℝ := ![s,t]
  have hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1 := by
    intro i
    fin_cases i
    · exact ⟨hs,hs1⟩
    · exact ⟨ht,ht1⟩
  obtain ⟨ε,r₀,hε,hε1,hr₀,hr₀1,hextract⟩ := exists_joint_Frostman_extraction κ q hq hη hη1
  refine ⟨ε,r₀,hε,hε1,hr₀,hr₀1,?_⟩
  intro μ ν _ _ hμ hν r hr hrr heμ heν
  let m : Fin 2 → Measure ℝ := ![μ,ν]
  letI (i : Fin 2) : IsProbabilityMeasure (m i) := by
    fin_cases i <;> dsimp [m] <;> infer_instance
  have hm : ∀ i, UnitSupported (m i) := by intro i; fin_cases i; exact hμ; exact hν
  have hcap : ∀ i, smoothEnergy κ.law (q i) r (m i) ≤ ENNReal.ofReal (r^(-ε)) := by
    intro i
    fin_cases i
    · exact heμ
    · exact heν
  obtain ⟨A,hA,hA0,hloss,hprob,hsupp,hball,_⟩ := hextract m hm r hr hrr hcap
  letI : IsProbabilityMeasure (unitRescaledSmoothLaw κ r (normalizedRestriction μ (A 0))) := by
    simpa only [m, Matrix.cons_val_zero] using hprob 0
  letI : IsProbabilityMeasure (unitRescaledSmoothLaw κ r (normalizedRestriction ν (A 1))) := by
    simpa only [m, Matrix.cons_val_one, Matrix.cons_val_zero] using hprob 1
  refine ⟨A 0,A 1,hA 0,hA 1,hA0 0,hA0 1,hloss 0,hloss 1,inferInstance,
    planarProductLaw_unitCube _ _ (hsupp 0) (hsupp 1),?_⟩
  intro a b c R hnormal hR
  have hr1 : r ≤ 1 := hrr.trans hr₀1
  have hC : 1 ≤ r^(-η) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
  have h := planarProductLaw_unit_normal_slab_bound _ _ hC hs hs1 ht ht1
    (hball 0) (hball 1) a b c hnormal hR
  simpa only [m, q, Matrix.cons_val_zero, Matrix.cons_val_one] using h

end Kakeya4.Hard.MultiplicativeConvolution
