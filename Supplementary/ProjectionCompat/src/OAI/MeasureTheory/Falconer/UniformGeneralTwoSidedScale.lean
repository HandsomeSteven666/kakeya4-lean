import OAI.MeasureTheory.Falconer.UniformGeneralOneScale
import OAI.MeasureTheory.Falconer.BundledWindowSupport

/-! Adapted from OpenAI math, Apache-2.0, exact commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: Estimates/NonendpointTwoSidedScale.lean. Preserve actual intersection/window proof; constants
now precede the entire exponent interval and scale-dependent C. See COPYING
and WINDOW_PROVENANCE.json. Fixed separation remains explicit. -/

namespace OAI.Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators

theorem uniform_general_two_sided_one_scale
    {a b α t D s : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbt : b < t)
    (ht : t < 1) (htα : t < α)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ p ∈ Icc a b, ∀ N ≥ N₀,
      ∀ C : ℝ, 0 ≤ C → C ≤ ((2:ℝ)^N)^(ε) →
      ∀ (μ ν : Measure (Space 2)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        μ Q.carrierᶜ = 0 → ν Q.carrierᶜ = 0 →
        (∀ y : Space 2, ∀ r > 0, μ (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
        (∀ y : Space 2, ∀ r > 0, ν (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space 2), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ A ∪ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space 2 × Space 2), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space 2, ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^p)) →
        (∀ᵐ x ∂ν, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space 2, ‖u‖ = 1 →
            μ {z | (z,x) ∈ G ∧ dist (normalize (z-x)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^p)) →
      ∃ G' : Set (Space 2 × Space 2), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        (∀ x u : Space 2, μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-p-c))) ∧
        (∀ z u : Space 2, ν {x | (z,x) ∈ G' ∧ ‖normalize (x-z)-u‖ ≤ 1/(2:ℝ)^N} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-p-c))) := by
  obtain ⟨ε,c,hε,hc,N₀,hscale⟩ := uniform_general_one_scale_gain ha hab hbt ht htα
    Q hQ hD hDdim hs
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro p hp N hN C hC hCscale μ ν _ _ hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap hcap'
  obtain ⟨H,hH,hHG,hHcost,hHcap⟩ := hscale p hp N hN C hC hCscale μ ν hμroot hμfrost A P hA hP hμA hνP
    hsep (fun y hy x hx => hpin y hy x (Or.inr hx)) G hG hcap
  obtain ⟨K,hK,hKG,hKcost,hKcap⟩ := hscale p hp N hN C hC hCscale ν μ hνroot hνfrost P A hP hA hνP hμA
    (fun x hx z hz => by simpa only [norm_sub_rev] using hsep z hz x hx)
    (fun y hy x hx => hpin y hy x (Or.inl hx)) (Prod.swap ⁻¹' G) (hG.preimage measurable_swap)
    (by simpa only [mem_preimage,Prod.swap_prod_mk] using hcap')
  obtain ⟨G',hG',hsub,hdel,hcaps⟩ := intersect_radial_orientations μ ν G H K hG hH hK hHG hKG
    hHcost hKcost hHcap hKcap
  refine ⟨G',hG',hsub,?_,hcaps⟩
  simpa only [two_mul] using hdel


#print axioms uniform_general_two_sided_one_scale
end OAI.Falconer.Regularization
