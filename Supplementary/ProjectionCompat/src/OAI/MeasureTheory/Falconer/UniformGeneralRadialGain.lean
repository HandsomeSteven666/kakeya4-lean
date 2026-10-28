import OAI.MeasureTheory.Falconer.UniformGeneralScaleWindow

/-! General-exponent finite-scale radial improvement for the actual pair law.
It consumes the proved uniform window, not an external gain certificate.
OpenAI math Apache-2.0 support and adapted proofs are pinned at
1581d4cbdd69a0faf34b2089614fe2a814316a6a; see COPYING/WINDOW_PROVENANCE.
The common gain is chosen before the requested output loss and all exponents,
coefficients and measures. Fixed geometric separation remains a hypothesis. -/

set_option autoImplicit false
namespace OAI.Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem uniform_general_radial_gain
    {a b α t D s : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbt : b < t) (ht : t < 1) (htα : t < α)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ gain : ℝ, 0 < gain ∧ ∀ η : ℝ, 0 < η →
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
        (∀ᵐ z ∂(μ : Measure (Space 2)), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space 2, ‖u‖ = 1 →
            (ν : Measure (Space 2)) {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^p)) →
        (∀ᵐ x ∂(ν : Measure (Space 2)), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space 2, ‖u‖ = 1 →
            (μ : Measure (Space 2)) {z | (z,x) ∈ G ∧ dist (normalize (z-x)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^p)) →
      ∃ G' : Set (Space 2 × Space 2), MeasurableSet G' ∧ G' ⊆ G ∧
        ((μ : Measure (Space 2)).prod ν) (G \ G') ≤
          2*ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        RadialCapBound μ ν G' N η (p+gain) := by
  obtain ⟨ε₀,gain,hε₀,hgain,hwindow⟩ :=
    uniform_general_scale_window_gain ha hab hbt ht htα Q hQ hD hDdim hs
  refine ⟨gain,hgain,?_⟩
  intro η hη
  have hb : 0 ≤ b := (ha.trans_le hab).le
  obtain ⟨K,hK,hcoarse⟩ := exists_radial_window_denominator hη (by positivity : 0 ≤ b+gain)
  obtain ⟨c,hc,Nw,hNw⟩ := hwindow K hK
  obtain ⟨Nb,hNb⟩ := fixed_constant_absorbed hη ((2:ℝ)^(b+gain))
  have hε : 0 < ε₀/(2*(K:ℝ)) := by positivity
  refine ⟨ε₀/(2*(K:ℝ)),c,hε,hc,max Nw Nb,?_⟩
  intro p hp N hN C hC hCbudget μ ν hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap hcap'
  obtain ⟨H,hH,hsub,hdel,hbounds⟩ := hNw p hp N (le_trans (le_max_left _ _) hN)
    C hC hCbudget μ ν hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap hcap'
  refine ⟨H,hH,hsub,hdel,?_⟩
  have hp0 : 0 ≤ p := (ha.trans_le hp.1).le
  have hcoarse' : ((N/K:ℕ):ℝ)*(p+gain) ≤ (N:ℝ)*η := calc
    _ ≤ ((N/K:ℕ):ℝ)*(b+gain) := mul_le_mul_of_nonneg_left
      (by linarith [hp.2]) (Nat.cast_nonneg _)
    _ ≤ _ := hcoarse N
  have hconstant' : (2:ℝ)^(p+gain) ≤ ((2:ℝ)^N)^η := calc
    _ ≤ (2:ℝ)^(b+gain) := Real.rpow_le_rpow_of_exponent_le
      (by norm_num) (by linarith [hp.2])
    _ ≤ _ := hNb N (le_trans (le_max_right _ _) hN)
  exact radialCapBound_of_window μ ν H (Nat.div_le_self N K)
    (by positivity : 0 ≤ p+gain) le_rfl hcoarse' hconstant' hbounds

#print axioms uniform_general_radial_gain
end OAI.Falconer.Regularization
