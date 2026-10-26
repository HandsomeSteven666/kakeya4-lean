import Kakeya4.Hard.MultiplicativeConvolution.PlanarProductLaw

/-!
# The actual two-dimensional Frostman input extracted from two original energy caps

The two losses and thresholds are unified before all input laws. The planar law
uses the Euclidean norm and the actual extracted one-dimensional laws.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Two original energy caps give the actual Euclidean product-law projection input. -/
theorem exists_planar_Frostman_extraction (κ : SmoothKernel) {s t η : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ ε r₀ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        UnitSupported μ → UnitSupported ν → ∀ r : ℝ, 0 < r → r ≤ r₀ →
          smoothEnergy κ.law s r μ ≤ ENNReal.ofReal (r^(-ε)) →
          smoothEnergy κ.law t r ν ≤ ENNReal.ofReal (r^(-ε)) →
          ∃ A B : Set ℝ, MeasurableSet A ∧ MeasurableSet B ∧
            μ Aᶜ ≤ ENNReal.ofReal (r^ε) ∧ ν Bᶜ ≤ ENNReal.ofReal (r^ε) ∧
            let ρ := planarProductLaw
              (unitRescaledSmoothLaw κ r (normalizedRestriction μ A))
              (unitRescaledSmoothLaw κ r (normalizedRestriction ν B))
            IsProbabilityMeasure ρ ∧ (∀ᵐ z ∂ρ, ∀ i : Fin 2, |z i| ≤ 1) ∧
              ∀ (z : EuclideanSpace ℝ (Fin 2)) (R : ℝ), 0 < R →
                ρ (closedBall z R) ≤ ENNReal.ofReal (r^(-η)*R^(s+t)) := by
  have hhalf : 0 < η/2 := by positivity
  have hhalf1 : η/2 ≤ 1 := by linarith
  obtain ⟨εs,rs,hεs,hεs1,hrs,hrs1,hsExtract⟩ := exists_exact_Frostman_probability_extraction κ hs hs1 hhalf hhalf1
  obtain ⟨εt,rt,hεt,hεt1,hrt,hrt1,htExtract⟩ := exists_exact_Frostman_probability_extraction κ ht ht1 hhalf hhalf1
  let ε := min εs εt
  have hε : 0 < ε := lt_min hεs hεt
  refine ⟨ε,min rs rt,hε,(min_le_left _ _).trans hεs1,lt_min hrs hrt,(min_le_left _ _).trans hrs1,?_⟩
  intro μ ν _ _ hμ hν r hr hrr heμ heν
  have hr1 : r ≤ 1 := (hrr.trans (min_le_left _ _)).trans hrs1
  have hcap (e : ℝ) (he : ε ≤ e) : r^(-ε) ≤ r^(-e) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have hbad (e : ℝ) (he : ε ≤ e) : r^e ≤ r^ε := Real.rpow_le_rpow_of_exponent_ge hr hr1 he
  obtain ⟨A,hA,hbadA,hprobA,hsuppA,hballA⟩ := hsExtract μ hμ r hr (hrr.trans (min_le_left _ _))
    (heμ.trans (ENNReal.ofReal_le_ofReal (hcap εs (min_le_left _ _))))
  obtain ⟨B,hB,hbadB,hprobB,hsuppB,hballB⟩ := htExtract ν hν r hr (hrr.trans (min_le_right _ _))
    (heν.trans (ENNReal.ofReal_le_ofReal (hcap εt (min_le_right _ _))))
  letI : IsProbabilityMeasure (unitRescaledSmoothLaw κ r (normalizedRestriction μ A)) := hprobA
  letI : IsProbabilityMeasure (unitRescaledSmoothLaw κ r (normalizedRestriction ν B)) := hprobB
  refine ⟨A,B,hA,hB,hbadA.trans (ENNReal.ofReal_le_ofReal (hbad εs (min_le_left _ _))),
    hbadB.trans (ENNReal.ofReal_le_ofReal (hbad εt (min_le_right _ _))),inferInstance,
    planarProductLaw_unitCube _ _ hsuppA hsuppB,?_⟩
  intro z R hR
  have h := planarProductLaw_ball_le _ _ (by positivity : 0 ≤ r^(-(η/2)))
    (by positivity : 0 ≤ r^(-(η/2))) hballA hballB z hR
  have hc : r^(-(η/2))*r^(-(η/2)) = r^(-η) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  simpa only [hc] using h

end Kakeya4.Hard.MultiplicativeConvolution
