






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.BundledAngularExtension
import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.CompactGainUniformization

/-! Uniformization of the actual general one-scale gain, using its proved
local constants rather than an additional projection certificate. The imported
OpenAI proof chain is Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a;
COPYING and PROVENANCE/EXTENSION_PROVENANCE record the original source bodies.
Fixed separation and the finest-scale output are intentionally explicit. -/

namespace OAI.Falconer.Regularization
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators

theorem cap_budget_transfer_nearby {R r p q E e : ℝ}
    (hR : 1 ≤ R) (hr : R⁻¹ ≤ r) (hr1 : r ≤ 1)
    (he : 0 < e) (hE : E ≤ e/4) (hpq : |p-q| < e/4) :
    R^E*r^p ≤ R^e*r^q := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hr0 : 0 < r := (inv_pos.mpr hR0).trans_le hr
  have htransfer : r^p ≤ R^(e/2)*r^q := by
    by_cases h : p ≤ q
    · apply cap_exponent_loss_transfer hR hr h
      have := (abs_lt.mp hpq).1
      linarith
    · have hpow : r^p ≤ r^q := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (le_of_not_ge h)
      exact hpow.trans (le_mul_of_one_le_left (Real.rpow_nonneg hr0.le _)
        (Real.one_le_rpow hR (by linarith)))
  calc
    R^E*r^p ≤ R^E*(R^(e/2)*r^q) :=
      mul_le_mul_of_nonneg_left htransfer (Real.rpow_nonneg hR0.le _)
    _ = R^(E+e/2)*r^q := by rw [← mul_assoc,← Real.rpow_add hR0]
    _ ≤ R^e*r^q := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) (Real.rpow_nonneg hr0.le _)

theorem uniform_general_one_scale_gain
    {a b α t D s : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbt : b < t) (ht : t < 1) (htα : t < α)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ p ∈ Icc a b, ∀ N ≥ N₀,
      ∀ C : ℝ, 0 ≤ C → C ≤ ((2:ℝ)^N)^ε →
      ∀ (μ ν : Measure (Space 2)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        μ Q.carrierᶜ = 0 →
        (∀ y : Space 2, ∀ r > 0, μ (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space 2), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space 2 × Space 2), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space 2, ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^p)) →
      ∃ G' : Set (Space 2 × Space 2), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ x u : Space 2, μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-p-c)) := by
  classical
  have hlocal (q : Icc a b) := general_scale_nonendpoint_one_scale_gain
    (h := 0) (α := α) (t := t) (q := (q:ℝ))
    (by simpa using ha.trans_le q.2.1) (q.2.2.trans_lt hbt)
    (by simpa using ht) htα Q hQ hD hDdim hs
  choose e c he hc depth hstep using hlocal
  let loss : ℝ → ℝ := fun q => if hq : q ∈ Icc a b then e ⟨q,hq⟩ else 1
  let gain : ℝ → ℝ := fun q => if hq : q ∈ Icc a b then c ⟨q,hq⟩ else 1
  let cutoff : ℝ → ℕ := fun q => if hq : q ∈ Icc a b then depth ⟨q,hq⟩ else 0
  obtain ⟨E,J,hE,hJ,N₀,hcover⟩ :=
    Kakeya4.Hard.MultiplicativeConvolution.exists_uniform_gain_cover hab loss gain cutoff
      (by intro q hq; simpa only [loss,dite_eq_left hq] using he ⟨q,hq⟩)
      (by intro q hq; simpa only [gain,dite_eq_left hq] using hc ⟨q,hq⟩)
  refine ⟨E,J,hE,hJ,N₀,?_⟩
  intro p hp N hN C hC hCscale μ ν _ _ hroot hfrost A P hA hP hAfull hPfull hsep hpin G hG hcap
  obtain ⟨q,hq,hpq,hpq',hEq,hJq,hdepth⟩ := hcover p hp
  simp only [loss,gain,cutoff,dite_eq_left hq] at hpq hpq' hEq hJq hdepth
  let q' : Icc a b := ⟨q,hq⟩
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hCbudget : C ≤ ((2:ℝ)^N)^(e q') := hCscale.trans
    (Real.rpow_le_rpow_of_exponent_le hR (by have := he q'; dsimp [q']; linarith))
  have hcap' : ∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space 2, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(e q')*r^q) := by
    filter_upwards [hcap] with z hz
    intro r hr hr1 u hu
    exact (hz r hr hr1 u hu).trans (ENNReal.ofReal_le_ofReal
      (cap_budget_transfer_nearby hR (by simpa only [one_div] using hr)
        hr1 (he q') hEq hpq))
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := hstep q' N (hdepth.trans hN)
    C hC hCbudget μ ν hroot hfrost A P hA hP hAfull hPfull hsep hpin G hG hcap'
  refine ⟨G',hG',hsub,?_,?_⟩
  · apply hdel.trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_exponent_le hR
    have := hc q'
    dsimp [q'] at *
    linarith
  · intro x u
    apply (hbound x u).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_exponent_le hR
    have hclose := (abs_lt.mp hpq').2
    dsimp [q'] at *
    linarith

#print axioms cap_budget_transfer_nearby
#print axioms uniform_general_one_scale_gain
end OAI.Falconer.Regularization
