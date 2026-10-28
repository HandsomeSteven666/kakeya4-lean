import OAI.MeasureTheory.Falconer.UniformGeneralRadialGain

/-! Finite iteration of the actual proved uniform radial gain. All budgets
are selected before the original laws. No abstract bootstrap input is assumed.
Licensed upstream results are pinned in COPYING/PROVENANCE/WINDOW_PROVENANCE.
Fixed positive geometric separation remains explicit. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem RadialCapBound.enlarge_loss {d N : ℕ} {μ ν : ProbabilityMeasure (Space d)}
    {G : Set (Space d × Space d)} {e E p : ℝ}
    (h : RadialCapBound μ ν G N e p) (hle : e ≤ E) :
    RadialCapBound μ ν G N E p := by
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  constructor
  · intro x hx u hu r hr hr1
    exact (h.1 x hx u hu r hr hr1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hR hle)
        (Real.rpow_nonneg (by have := inv_pos.mpr (lt_of_lt_of_le zero_lt_one hR); linarith) _)))
  · intro x hx u hu r hr hr1
    exact (h.2 x hx u hu r hr hr1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hR hle)
        (Real.rpow_nonneg (by have := inv_pos.mpr (lt_of_lt_of_le zero_lt_one hR); linarith) _)))

theorem RadialCapBound.lower_exponent {d N : ℕ} {μ ν : ProbabilityMeasure (Space d)}
    {G : Set (Space d × Space d)} {e p q : ℝ}
    (h : RadialCapBound μ ν G N e p) (hle : q ≤ p) :
    RadialCapBound μ ν G N e q := by
  simpa only [add_zero] using h.change_exponent (le_refl (0:ℝ)) (sub_nonpos.mpr hle)

namespace Regularization

theorem uniform_radial_finite_iteration
    {a b α t D s : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbt : b < t) (ht : t < 1) (htα : t < α)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ gain : ℝ, 0 < gain ∧ ∀ m : ℕ, ∀ η : ℝ, 0 < η →
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
        RadialCapBound μ ν G' N η (min (p+(m:ℝ)*gain) b) := by
  obtain ⟨gain,hgain,hstep⟩ := uniform_general_radial_gain ha hab hbt ht htα Q hQ hD hDdim hs
  refine ⟨gain,hgain,?_⟩
  intro m
  induction m with
  | zero =>
    intro η hη
    refine ⟨η,1,hη,by norm_num,0,?_⟩
    intro p hp N hN C hC hCbudget μ ν hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap
    refine ⟨G,hG,Subset.rfl,by simp,?_⟩
    simpa only [Nat.cast_zero,zero_mul,add_zero,min_eq_left hp.2] using hcap
  | succ m ih =>
    intro η hη
    obtain ⟨εs,cs,hεs,hcs,Ns,hNs⟩ := hstep η hη
    obtain ⟨εi,ci,hεi,hci,Ni,hNi⟩ := ih εs hεs
    let ε := min εi εs
    let c := min ci cs
    refine ⟨ε,c,lt_min hεi hεs,lt_min hci hcs,max Ni Ns,?_⟩
    intro p hp N hN C hC hCbudget μ ν hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG hcap
    have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
    have hCi : C ≤ ((2:ℝ)^N)^εi := hCbudget.trans
      (Real.rpow_le_rpow_of_exponent_le hR (min_le_left _ _))
    have hCs : C ≤ ((2:ℝ)^N)^εs := hCbudget.trans
      (Real.rpow_le_rpow_of_exponent_le hR (min_le_right _ _))
    obtain ⟨H,hH,hHG,hHdel,hHcap⟩ := hNi p hp N ((le_max_left _ _).trans hN)
      C hC hCi μ ν hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin G hG
      (hcap.enlarge_loss (min_le_left _ _))
    let q := min (p+(m:ℝ)*gain) b
    have hq : q ∈ Icc a b := ⟨le_min
      (hp.1.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hgain.le))) hab,
      min_le_right _ _⟩
    have hcap₁ : ∀ᵐ z ∂(μ : Measure (Space 2)), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ∀ u : Space 2, ‖u‖ = 1 →
          (ν : Measure (Space 2)) {x | (z,x) ∈ H ∧ dist (normalize (x-z)) u < r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^εs*r^q) := by
      filter_upwards [Measure.support_mem_ae (μ := (μ : Measure (Space 2)))] with z hz
      intro r hr hr1 u hu
      exact hHcap.1 z hz u hu r (by simpa only [one_div] using hr) hr1
    have hcap₂ : ∀ᵐ x ∂(ν : Measure (Space 2)), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ∀ u : Space 2, ‖u‖ = 1 →
          (μ : Measure (Space 2)) {z | (z,x) ∈ H ∧ dist (normalize (z-x)) u < r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^εs*r^q) := by
      filter_upwards [Measure.support_mem_ae (μ := (ν : Measure (Space 2)))] with x hx
      intro r hr hr1 u hu
      exact hHcap.2 x hx u hu r (by simpa only [one_div] using hr) hr1
    obtain ⟨K,hK,hKH,hKdel,hKcap⟩ := hNs q hq N ((le_max_right _ _).trans hN)
      C hC hCs μ ν hμroot hνroot hμfrost hνfrost A P hA hP hμA hνP hsep hpin H hH hcap₁ hcap₂
    refine ⟨K,hK,hKH.trans hHG,?_,?_⟩
    · have htotal := relative_pruning_cost_trans ((μ : Measure (Space 2)).prod ν) G H K hHdel hKdel
      have hi : ((2:ℝ)^N)^(-ci) ≤ ((2:ℝ)^N)^(-c) :=
        Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg (min_le_left _ _))
      have hs' : ((2:ℝ)^N)^(-cs) ≤ ((2:ℝ)^N)^(-c) :=
        Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg (min_le_right _ _))
      apply htotal.trans
      calc
        _ ≤ ENNReal.ofReal ((2*(m:ℝ))*((2:ℝ)^N)^(-c)) +
            2*ENNReal.ofReal (((2:ℝ)^N)^(-c)) := add_le_add
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hi (by positivity)))
          (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hs'))
        _ = _ := by
          rw [show 2*ENNReal.ofReal (((2:ℝ)^N)^(-c)) =
            ENNReal.ofReal (2*((2:ℝ)^N)^(-c)) by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num]
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          push_cast
          ring
    · apply hKcap.lower_exponent
      by_cases hpb : p+(m:ℝ)*gain ≤ b
      · dsimp [q]
        rw [min_eq_left hpb]
        apply (min_le_left _ _).trans_eq
        push_cast
        ring
      · dsimp [q]
        rw [min_eq_right (le_of_not_ge hpb)]
        exact (min_le_right _ _).trans (le_add_of_nonneg_right hgain.le)

#print axioms OAI.Falconer.RadialCapBound.enlarge_loss
#print axioms OAI.Falconer.RadialCapBound.lower_exponent
#print axioms uniform_radial_finite_iteration
end Regularization
end OAI.Falconer
