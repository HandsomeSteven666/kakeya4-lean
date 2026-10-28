import OAI.MeasureTheory.Falconer.FiniteUniformRadialBootstrap

/-! Concrete finite bootstrap to the requested exponent and absorption of its
entire finite mass-loss factor. Constants remain before all original laws.
Underlying licensed proofs: Apache-2.0, OpenAI pin in COPYING/PROVENANCE.
Fixed positive geometric separation is retained. -/

set_option autoImplicit false
namespace OAI.Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem uniform_radial_bootstrap_endpoint
    {a b α t D s : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbt : b < t) (ht : t < 1) (htα : t < α)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ m : ℕ, 0 < m ∧ ∀ η : ℝ, 0 < η →
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ p ∈ Icc a b, ∀ N ≥ N₀,
      ∀ C : ℝ, 0 ≤ C → C ≤ ((2:ℝ)^N)^ε →
      ∀ μ ν : ProbabilityMeasure (Space 2),
        (μ : Measure (Space 2)) Q.carrierᶜ = 0 →
        (ν : Measure (Space 2)) Q.carrierᶜ = 0 →
        (∀ y : Space 2, ∀ r > 0,
          (μ : Measure (Space 2)) (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
        (∀ y : Space 2, ∀ r > 0,
          (ν : Measure (Space 2)) (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space 2), MeasurableSet A → MeasurableSet P →
        (μ : Measure (Space 2)) Aᶜ = 0 → (ν : Measure (Space 2)) Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ A ∪ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space 2 × Space 2), MeasurableSet G →
        RadialCapBound μ ν G N ε p →
      ∃ G' : Set (Space 2 × Space 2), MeasurableSet G' ∧ G' ⊆ G ∧
        ((μ : Measure (Space 2)).prod ν) (G \ G') ≤
          ENNReal.ofReal ((2*(m:ℝ))*((2:ℝ)^N)^(-c)) ∧
        RadialCapBound μ ν G' N η b := by
  obtain ⟨gain,hgain,hiter⟩ := uniform_radial_finite_iteration ha hab hbt ht htα Q hQ hD hDdim hs
  obtain ⟨m,hm⟩ := exists_nat_gt (max 0 ((b-a)/gain))
  have hmpos : 0 < m := by
    have hpos : (0:ℝ) < m := (le_max_left _ _).trans_lt hm
    exact_mod_cast hpos
  have hreach : b ≤ a+(m:ℝ)*gain := by
    have hh := (div_lt_iff₀ hgain).mp ((le_max_right _ _).trans_lt hm)
    linarith
  refine ⟨m,hmpos,?_⟩
  intro η hη
  obtain ⟨ε,c,hε,hc,N₀,hN₀⟩ := hiter m η hη
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro p hp N hN C hC hCbudget μ ν hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap
  obtain ⟨H,hH,hsub,hdel,hcaps⟩ := hN₀ p hp N hN C hC hCbudget μ ν
    hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap
  have hreach' : b ≤ p+(m:ℝ)*gain := by linarith [hp.1]
  exact ⟨H,hH,hsub,hdel,by simpa only [min_eq_right hreach'] using hcaps⟩

theorem uniform_radial_bootstrap_power_cost
    {a b α t D s : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbt : b < t) (ht : t < 1) (htα : t < α)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (2:ℕ) ≤ D) (hs : 0 < s) :
    ∀ η : ℝ, 0 < η →
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ p ∈ Icc a b, ∀ N ≥ N₀,
      ∀ C : ℝ, 0 ≤ C → C ≤ ((2:ℝ)^N)^ε →
      ∀ μ ν : ProbabilityMeasure (Space 2),
        (μ : Measure (Space 2)) Q.carrierᶜ = 0 →
        (ν : Measure (Space 2)) Q.carrierᶜ = 0 →
        (∀ y : Space 2, ∀ r > 0,
          (μ : Measure (Space 2)) (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
        (∀ y : Space 2, ∀ r > 0,
          (ν : Measure (Space 2)) (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space 2), MeasurableSet A → MeasurableSet P →
        (μ : Measure (Space 2)) Aᶜ = 0 → (ν : Measure (Space 2)) Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ A ∪ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space 2 × Space 2), MeasurableSet G →
        RadialCapBound μ ν G N ε p →
      ∃ G' : Set (Space 2 × Space 2), MeasurableSet G' ∧ G' ⊆ G ∧
        ((μ : Measure (Space 2)).prod ν) (G \ G') ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        RadialCapBound μ ν G' N η b := by
  obtain ⟨m,hm,hend⟩ := uniform_radial_bootstrap_endpoint ha hab hbt ht htα Q hQ hD hDdim hs
  intro η hη
  obtain ⟨ε,c,hε,hc,N₀,hN₀⟩ := hend η hη
  have hc' : 0 < c/2 := by positivity
  obtain ⟨Nb,hNb⟩ := fixed_constant_absorbed hc' (2*(m:ℝ))
  refine ⟨ε,c/2,hε,hc',max N₀ Nb,?_⟩
  intro p hp N hN C hC hCbudget μ ν hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap
  obtain ⟨H,hH,hsub,hdel,hcaps⟩ := hN₀ p hp N ((le_max_left _ _).trans hN) C hC hCbudget μ ν
    hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap
  refine ⟨H,hH,hsub,hdel.trans (ENNReal.ofReal_le_ofReal ?_),hcaps⟩
  calc
    (2*(m:ℝ))*((2:ℝ)^N)^(-c) ≤ ((2:ℝ)^N)^(c/2)*((2:ℝ)^N)^(-c) :=
      mul_le_mul_of_nonneg_right (hNb N ((le_max_right _ _).trans hN)) (by positivity)
    _ = ((2:ℝ)^N)^(-(c/2)) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      ring

#print axioms uniform_radial_bootstrap_endpoint
#print axioms uniform_radial_bootstrap_power_cost
end OAI.Falconer.Regularization
