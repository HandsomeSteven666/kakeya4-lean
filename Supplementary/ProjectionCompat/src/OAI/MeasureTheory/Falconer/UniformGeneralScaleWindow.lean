import OAI.MeasureTheory.Falconer.UniformGeneralTwoSidedScale
import OAI.MeasureTheory.Falconer.BundledWindowSupport

/-! Adapted from OpenAI math, Apache-2.0, exact commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: Recursion/NonendpointScaleWindow.lean. Preserve actual intersection/window proof; constants
now precede the entire exponent interval and scale-dependent C. See COPYING
and WINDOW_PROVENANCE.json. Fixed separation remains explicit. -/

namespace OAI.Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators

theorem uniform_general_scale_window_gain
    {a b α t D s : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbt : b < t)
    (ht : t < 1) (htα : t < α)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε gain : ℝ, 0 < ε ∧ 0 < gain ∧ ∀ K : ℕ, 0 < K →
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ p ∈ Icc a b, ∀ N ≥ N₀,
      ∀ C : ℝ, 0 ≤ C → C ≤ ((2:ℝ)^N)^(ε/(2*(K:ℝ))) →
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
              ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^p)) →
        (∀ᵐ x ∂ν, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space 2, ‖u‖ = 1 →
            μ {z | (z,x) ∈ G ∧ dist (normalize (z-x)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^p)) →
      ∃ G' : Set (Space 2 × Space 2), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ j : ℕ, N/K ≤ j → j ≤ N →
          (∀ x u : Space 2, μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^j)^(p+gain))) ∧
          (∀ z u : Space 2, ν {x | (z,x) ∈ G' ∧ ‖normalize (x-z)-u‖ ≤ 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^j)^(p+gain))) := by
  obtain ⟨ε,gain,hε,hgain,Ns,hscale⟩ := uniform_general_two_sided_one_scale ha hab hbt
    ht htα Q hQ hD hDdim hs
  refine ⟨ε,gain,hε,hgain,?_⟩
  intro K hK
  obtain ⟨c,hc,Nc,hcost⟩ := radial_scale_window_cost K hK hgain
  refine ⟨c,hc,max (K*Ns) (max (2*K) Nc),?_⟩
  intro p hp N hN C hC hCscale μ ν _ _ hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap hcap'
  simp only [max_le_iff] at hN
  obtain ⟨hNs,hNK,hNc⟩ := hN
  have hstart : Ns ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by simpa only [Nat.mul_comm] using hNs)
  have hcapSwap : ∀ᵐ z ∂ν, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space 2, ‖u‖ = 1 →
        μ {x | (z,x) ∈ Prod.swap ⁻¹' G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(ε/(2*(K:ℝ)))*r^p) := by
    simpa only [mem_preimage,Prod.swap_prod_mk] using hcap'
  obtain ⟨H,hH,hsub,hdel,hbounds⟩ := finite_radial_refinement μ ν G hG (Finset.Icc (N/K) N)
    (fun j => 2*ENNReal.ofReal (((2:ℝ)^j)^(-gain)))
    (fun j => ENNReal.ofReal ((1/(2:ℝ)^j)^(p+gain))) (fun j => 1/(2:ℝ)^j) (by
      intro j hj
      obtain ⟨hjlo,hjhi⟩ := Finset.mem_Icc.mp hj
      have hloss := radial_scale_window_loss hK hNK hjlo hε.le
      have hc₁ := reverse_caps_all_radii μ μ ν Measure.AbsolutelyContinuous.rfl
        (Subset.rfl (s := G)) hjhi hloss hcap
      have hc₂ := reverse_caps_all_radii ν ν μ Measure.AbsolutelyContinuous.rfl
        (Subset.rfl (s := Prod.swap ⁻¹' G)) hjhi hloss hcapSwap
      obtain ⟨H,hH,hsub,hdel,hbounds⟩ := hscale p hp j (hstart.trans hjlo) C hC (hCscale.trans hloss) μ ν
        hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hc₁
        (by simpa only [mem_preimage,Prod.swap_prod_mk] using hc₂)
      refine ⟨H,hH,hsub,hdel,?_⟩
      have he : ((2:ℝ)^j)^(-p-gain) = (1/(2:ℝ)^j)^(p+gain) := by
        rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity)]
        congr 1
        ring
      simpa only [he] using hbounds)
  refine ⟨H,hH,hsub,?_,fun j hjlo hjhi => hbounds j (Finset.mem_Icc.mpr ⟨hjlo,hjhi⟩)⟩
  apply hdel.trans
  rw [← Finset.mul_sum]
  exact mul_le_mul' le_rfl (hcost N hNc)


#print axioms uniform_general_scale_window_gain
end OAI.Falconer.Regularization
