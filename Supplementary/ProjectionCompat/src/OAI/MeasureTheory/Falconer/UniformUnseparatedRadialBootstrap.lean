import OAI.MeasureTheory.Falconer.UniformGridBootstrap
import OAI.MeasureTheory.Falconer.DyadicSeparationScaleCosts

/-! Actual law-uniform finite-scale radial bootstrap without a geometric
separation hypothesis. Fine-grid pruning, conditional fixed-root bootstraps,
original-mass recombination and every scale cost are consumed here. -/

set_option autoImplicit false
namespace OAI.Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal

theorem uniform_unseparated_radial_bootstrap
    {a b α t : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbt : b < t)
    (ht : t < 1) (htα : t < α) (hα1 : α ≤ 1) (η : ℝ) (hη : 0 < η) :
    ∃ ε τ : ℝ, 0 < ε ∧ 0 < τ ∧ ∃ N₀ : ℕ,
    ∀ p ∈ Icc a b, ∀ N ≥ N₀, ∀ C : ℝ, 0 ≤ C → C ≤ ((2:ℝ)^N)^ε →
    ∀ μ ν : ProbabilityMeasure (Space 2),
      FrostmanBallBound (μ : Measure (Space 2)) α C →
      FrostmanBallBound (ν : Measure (Space 2)) α C →
    ∀ Q : DyadicCube 2, Q.side = 1 →
      (μ : Measure (Space 2)) Q.carrierᶜ = 0 → (ν : Measure (Space 2)) Q.carrierᶜ = 0 →
    ∀ G : Set (Space 2 × Space 2), MeasurableSet G → RadialCapBound μ ν G N ε p →
    ∃ H : Set (Space 2 × Space 2), MeasurableSet H ∧ H ⊆ G ∧
      ((μ : Measure (Space 2)).prod ν) (G \ H) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-τ)) ∧
      RadialCapBound μ ν H N η b := by
  obtain ⟨ε₀,κ,c,hε₀,hκ,hc,Ng,hNg⟩ := uniform_grid_bootstrap_raw_cost ha hab hbt ht htα hα1 η hη
  have hα : 0 < α := ha.trans (hab.trans_lt (hbt.trans htα))
  let θ := κ/4
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hκθ : 2*θ < κ := by dsimp [θ]; linarith
  let ε := min ε₀ (θ*α/2)
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεθ : ε < θ*α := (min_le_right _ _).trans_lt (by nlinarith [mul_pos hθ hα])
  obtain ⟨τ,hτ,Nc,hNc⟩ := dyadic_grid_bootstrap_error_absorbed hθ hκθ hα.le hεθ hc
  refine ⟨ε,τ,hε,hτ,max Ng Nc,?_⟩
  intro p hp N hN C hC hCbudget μ ν hfμ hfν Q hQ hμroot hνroot G hG hcap
  have hC₀ : C ≤ ((2:ℝ)^N)^ε₀ := hCbudget.trans
    (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (min_le_left _ _))
  obtain ⟨H,hH,hHG,hdel,hcaps⟩ := hNg p hp N ((le_max_left _ _).trans hN)
    ⌊θ*(N:ℝ)⌋₊ C hC hC₀ μ ν hfμ hfν Q hQ hμroot hνroot G hG
      (hcap.enlarge_loss (min_le_left _ _))
  exact ⟨H,hH,hHG,hdel.trans (hNc N ((le_max_right _ _).trans hN) C hC hCbudget),hcaps⟩

#print axioms uniform_unseparated_radial_bootstrap
end OAI.Falconer.Regularization
