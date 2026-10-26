






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.ProductParameterBootstrap
import Kakeya4.Hard.MultiplicativeConvolution.JointFrostmanExtraction

/-! Original smooth-energy input, actual jointly extracted laws, and the
parameter-product bootstrap. The joint transport statement retains arbitrary
sets and outer measure; no additional planar Frostman certificate is input. -/

set_option autoImplicit false
namespace OAI.Falconer.Regularization
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem energy_parameter_product_bootstrap
    (κ : SmoothKernel) {s t σ : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hσ : 0 < σ) (hσmax : σ < min (s+t) 1) (η : ℝ) (hη : 0 < η) :
    ∃ ε τ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < τ ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ μ : Fin 4 → Measure ℝ,
      ∀ [∀ i, IsProbabilityMeasure (μ i)], (∀ i, UnitSupported (μ i)) →
      (∀ i, smoothEnergy κ.law (if i.val < 2 then s else t)
        (1/((2:ℝ)^N)) (μ i) ≤ ENNReal.ofReal ((1/((2:ℝ)^N))^(-ε))) →
      ∃ (A : Fin 4 → Set ℝ) (ν : Fin 4 → ProbabilityMeasure ℝ),
        (∀ i, MeasurableSet (A i)) ∧ (∀ i, μ i (A i) ≠ 0) ∧
        (∀ i, μ i (A i)ᶜ ≤ ENNReal.ofReal ((1/((2:ℝ)^N))^ε)) ∧
        (∀ i, (ν i : Measure ℝ) = unitRescaledSmoothLaw κ (1/((2:ℝ)^N))
          (normalizedRestriction (μ i) (A i))) ∧
        (∀ i, UnitSupported (ν i : Measure ℝ)) ∧
        (∀ E : Set (Fin 4 → ℝ), Measure.pi μ E ≤
          Measure.pi (fun i ↦ (ν i : Measure ℝ))
            (cthickening ((1/((2:ℝ)^N))/2) ((fun x i ↦ x i/2) '' E)) +
              4*ENNReal.ofReal ((1/((2:ℝ)^N))^ε)) ∧
        ∃ H : Set (Space 2 × Space 2), MeasurableSet H ∧
          H ⊆ wideParameterRoot.carrier ×ˢ wideParameterRoot.carrier ∧
          ((parameterProductProbability (ν 0) (ν 2) : Measure (Space 2)).prod
            (parameterProductProbability (ν 1) (ν 3))) Hᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-τ)) ∧
          RadialCapBound (parameterProductProbability (ν 0) (ν 2))
            (parameterProductProbability (ν 1) (ν 3)) H N η σ := by
  classical
  obtain ⟨e0,τ,he0,hτ,Nb,hboot⟩ := uniform_parameter_product_bootstrap hs hs1 ht ht1 hσ hσmax η hη
  let ζ := min e0 1
  have hζ : 0 < ζ := lt_min he0 zero_lt_one
  have hζ1 : ζ ≤ 1 := min_le_right _ _
  have hζe : ζ ≤ e0 := min_le_left _ _
  let d : Fin 4 → ℝ := fun i ↦ if i.val < 2 then s else t
  have hd (i : Fin 4) : 0 ≤ d i ∧ d i ≤ 1 := by
    dsimp [d]; split_ifs
    · exact ⟨hs.le,hs1⟩
    · exact ⟨ht.le,ht1⟩
  obtain ⟨ε,r₀,hε,hε1,hr₀,hr₀1,hextract⟩ := exists_joint_Frostman_extraction κ d hd hζ hζ1
  obtain ⟨Nc,hNc⟩ := fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) (1/r₀)
  refine ⟨ε,τ,hε,hε1,hτ,max Nb Nc,?_⟩
  intro N hN μ _ hμ henergy
  let r := 1/((2:ℝ)^N)
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hR0 : 0 < (2:ℝ)^N := by positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hrr : r ≤ r₀ := by
    have hh := hNc N ((le_max_right _ _).trans hN)
    rw [Real.rpow_one] at hh
    exact (div_le_iff₀ hR0).mpr (by simpa only [mul_comm] using (div_le_iff₀ hr₀).mp hh)
  obtain ⟨A,hA,hA0,hloss,hprob,hsupp,hball,htransport⟩ := hextract μ hμ r hr hrr henergy
  let ν : Fin 4 → ProbabilityMeasure ℝ := fun i ↦
    ⟨unitRescaledSmoothLaw κ r (normalizedRestriction (μ i) (A i)),hprob i⟩
  have hν (i : Fin 4) : UnitSupported (ν i : Measure ℝ) := hsupp i
  have hpow : r^(-ζ) = ((2:ℝ)^N)^ζ := by
    dsimp [r]
    rw [one_div,Real.inv_rpow hR0.le,← Real.rpow_neg hR0.le]
    congr 1; ring
  have hball' (i : Fin 4) (z R : ℝ) (hRp : 0 < R) :
      (ν i : Measure ℝ) (closedBall z R) ≤ ENNReal.ofReal (((2:ℝ)^N)^ζ*R^(d i)) := by
    simpa only [ν,ProbabilityMeasure.coe_mk,hpow] using hball i z R hRp
  have hcap := hboot N ((le_max_left _ _).trans hN) (((2:ℝ)^N)^ζ)
    (Real.one_le_rpow hR hζ.le) (Real.rpow_le_rpow_of_exponent_le hR hζe)
    (ν 0) (ν 1) (ν 2) (ν 3) (hν 0) (hν 1) (hν 2) (hν 3)
    (by simpa [d] using hball' 0)
    (by simpa [d] using hball' 1)
    (by simpa [d] using hball' 2)
    (by simpa [d] using hball' 3)
  refine ⟨A,ν,hA,hA0,hloss,fun _ ↦ rfl,hν,?_,hcap⟩
  intro E
  simpa only [ν,ProbabilityMeasure.coe_mk,r,Fintype.card_fin,Nat.cast_ofNat] using htransport E

#print axioms energy_parameter_product_bootstrap
end OAI.Falconer.Regularization
