import Kakeya4.Hard.MultiplicativeConvolution.PlanarSetTransport
import Kakeya4.Hard.MultiplicativeConvolution.JointFrostmanExtraction

/-! # The same energy extraction supplies Euclidean Frostman bounds and all test-set transports -/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Constants precede both original laws; one actual planar probability works for every test set. -/
theorem exists_planar_Frostman_extraction_with_transport (κ : SmoothKernel) {s t η : ℝ}
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
              (∀ (z : EuclideanSpace ℝ (Fin 2)) (R : ℝ), 0 < R →
                ρ (closedBall z R) ≤ ENNReal.ofReal (r^(-η)*R^(s+t))) ∧
              ∀ E : Set (EuclideanSpace ℝ (Fin 2)), planarProductLaw μ ν E ≤
                ρ (cthickening r ((fun z ↦ (1/2 : ℝ) • z) '' E)) +
                  2*ENNReal.ofReal (r^ε) := by
  let a : Fin 2 → ℝ := ![s,t]
  have ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1 := by
    intro i
    fin_cases i
    · exact ⟨hs,hs1⟩
    · exact ⟨ht,ht1⟩
  obtain ⟨ε,r₀,hε,hε1,hr₀,hr₀1,hextract⟩ :=
    exists_joint_Frostman_extraction κ a ha (by positivity : 0 < η/2) (by linarith : η/2 ≤ 1)
  refine ⟨ε,r₀,hε,hε1,hr₀,hr₀1,?_⟩
  intro μ ν _ _ hμ hν r hr hrr heμ heν
  let m : Fin 2 → Measure ℝ := ![μ,ν]
  letI (i : Fin 2) : IsProbabilityMeasure (m i) := by
    fin_cases i <;> dsimp [m] <;> infer_instance
  have hm : ∀ i, UnitSupported (m i) := by intro i; fin_cases i; exact hμ; exact hν
  have hcap : ∀ i, smoothEnergy κ.law (a i) r (m i) ≤ ENNReal.ofReal (r^(-ε)) := by
    intro i
    fin_cases i
    · exact heμ
    · exact heν
  obtain ⟨A,hA,hA0,hloss,hprob,hsupp,hball,_⟩ := hextract m hm r hr hrr hcap
  letI (i : Fin 2) : IsProbabilityMeasure
      (unitRescaledSmoothLaw κ r (normalizedRestriction (m i) (A i))) := hprob i
  letI : IsProbabilityMeasure (unitRescaledSmoothLaw κ r (normalizedRestriction μ (A 0))) := by
    simpa only [m, Matrix.cons_val_zero] using hprob 0
  letI : IsProbabilityMeasure (unitRescaledSmoothLaw κ r (normalizedRestriction ν (A 1))) := by
    simpa only [m, Matrix.cons_val_one, Matrix.cons_val_zero] using hprob 1
  refine ⟨A 0,A 1,hA 0,hA 1,hA0 0,hA0 1,hloss 0,hloss 1,inferInstance,
    planarProductLaw_unitCube _ _ (hsupp 0) (hsupp 1),?_,?_⟩
  · intro z R hR
    have h := planarProductLaw_ball_le _ _ (by positivity : 0 ≤ r^(-(η/2)))
      (by positivity : 0 ≤ r^(-(η/2))) (hball 0) (hball 1) z hR
    have hc : r^(-(η/2))*r^(-(η/2)) = r^(-η) := by
      rw [← Real.rpow_add hr]
      congr 1
      ring
    simpa only [hc, m, a, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  · intro E
    have h := original_planar_mass_le_smoothed_add_loss κ μ ν (A 0) (A 1)
      (hA 0) (hA 1) (hA0 0) (hA0 1) hr.le E
    have h' := h.trans (add_le_add (add_le_add le_rfl (hloss 0)) (hloss 1))
    simpa only [two_mul, add_assoc] using h'

end Kakeya4.Hard.MultiplicativeConvolution
