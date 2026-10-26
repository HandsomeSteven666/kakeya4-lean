import Kakeya4.Hard.MultiplicativeConvolution.GeneratedCapFlatness

/-! Exact common-R normalization for the actual ratio law, retaining its mass,
interval cap and independent sum/product law. This does not construct the
geometric restricted ratio law or assert membership in its allowed-expression set. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

def normalizedRatioLaw (R : ℝ) (ν : Measure ℝ) : Measure ℝ := ν.map (fun t ↦ t/R)

instance normalizedRatioLaw_isProbabilityMeasure (R : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (normalizedRatioLaw R ν) := by
  unfold normalizedRatioLaw
  exact MeasureTheory.Measure.isProbabilityMeasure_map_iff (by fun_prop) |>.mpr inferInstance

theorem normalizedRatioLaw_unitSupported (ν : Measure ℝ) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ᵐ t ∂ν, |t| ≤ R) : UnitSupported (normalizedRatioLaw R ν) := by
  apply (ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)).2
  filter_upwards [hsupp] with t ht
  rw [abs_div, abs_of_pos hR]
  exact (div_le_one hR).mpr ht

theorem normalizedRatioLaw_closedBall (ν : Measure ℝ) {R : ℝ} (hR : 0 < R) (z u : ℝ) :
    normalizedRatioLaw R ν (closedBall z u) = ν (closedBall (R*z) (R*u)) := by
  rw [normalizedRatioLaw, Measure.map_apply (by fun_prop) measurableSet_closedBall]
  congr 1
  ext t
  simp only [mem_preimage, mem_closedBall, Real.dist_eq]
  have hdiv : t/R-z = (t-R*z)/R := by field_simp
  rw [hdiv, abs_div, abs_of_pos hR, div_le_iff₀ hR]
  rw [mul_comm u R]

theorem normalizedRatioLaw_coarseCap (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {R h K S : ℝ} (hR : 1 ≤ R) (hh : 0 < h) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (hcap : ∀ z u : ℝ, h ≤ u → u ≤ 1 → ν (closedBall z u) ≤ ENNReal.ofReal (K*u^S)) :
    ∀ z u : ℝ, h ≤ u → normalizedRatioLaw R ν (closedBall z u) ≤
      ENNReal.ofReal (((K+1)*R^S)*u^S) := by
  intro z u hhu
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  rw [normalizedRatioLaw_closedBall ν hRpos]
  have hhuR : h ≤ R*u := hhu.trans (by
    simpa using mul_le_mul_of_nonneg_right hR (hh.trans_le hhu).le)
  apply (probability_coarse_cap_all_radii ν hS hh hK hcap (R*z) (R*u) hhuR).trans_eq
  rw [Real.mul_rpow hRpos.le (hh.trans_le hhu).le]
  congr 1
  ring

/-- Every normalized product uses the same factor R^(-n), independent of the sample. -/
theorem productLaw_normalizedRatioLaw (ν : Measure ℝ) [IsFiniteMeasure ν] (R : ℝ) (n : ℕ) :
    productLaw (fun _ : Fin n ↦ normalizedRatioLaw R ν) =
      (productLaw (fun _ : Fin n ↦ ν)).map (fun t ↦ t/R^n) := by
  unfold normalizedRatioLaw
  rw [productLaw_map_parameters (fun _ : Fin n ↦ ν) (fun _ t ↦ t/R) (fun _ ↦ by fun_prop)]
  rw [productLaw, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext t
  simp [Finset.prod_div_distrib]

/-- The identical common R^(-n) survives every independent outer sum. -/
theorem generatedProductSumLaw_normalizedRatioLaw (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (R : ℝ) (n k : ℕ) :
    generatedProductSumLaw (fun _ : Fin n ↦ normalizedRatioLaw R ν) k =
      (generatedProductSumLaw (fun _ : Fin n ↦ ν) k).map (fun t ↦ t/R^n) := by
  simp only [generatedProductSumLaw, productLaw_normalizedRatioLaw]
  rw [← Measure.pi_map_pi (fun _ : Fin k ↦
    (show Measurable (fun t : ℝ ↦ t/R^n) from by fun_prop).aemeasurable)]
  rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext t
  simp [Finset.sum_div]

/-- The source law itself, with the common R^(-n) dilation, has the desired
interval bound under its explicit original cap and effective subpower budget. -/
theorem exists_ratioLaw_generated_flatness {S e : ℝ} (hS : 0 < S) (he : 0 < e) (he1 : e < 1) :
    ∃ (n k : ℕ) (h₀ q D : ℝ), 2 ≤ n ∧ 0 < k ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 0 < q ∧ 0 < D ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν → ∀ R : ℝ, 1 ≤ R →
        (∀ᵐ t ∂ν, |t| ≤ R) → ∀ (h K : ℝ), 0 < h → h ≤ h₀ → 0 ≤ K →
          (K+1)*R^S ≤ h^(-q) →
          (∀ z u : ℝ, h ≤ u → u ≤ 1 → ν (closedBall z u) ≤ ENNReal.ofReal (K*u^S)) →
          ∀ x : ℝ, ((generatedProductSumLaw (fun _ : Fin n ↦ ν) k).map (fun t ↦ t/R^n)).real
            (Icc (x-h) (x+h)) ≤ D*h^(1-e) := by
  obtain ⟨n, k, h₀, q, D, hn, hk, hh₀, hh₀1, hq, hD, hflat⟩ :=
    exists_generated_flatness_of_coarseCap hS he he1
  refine ⟨n, k, h₀, q, D, hn, hk, hh₀, hh₀1, hq, hD, ?_⟩
  intro ν hν R hR hsupp h K hh hhh hK hbudget hcap x
  let : IsProbabilityMeasure ν := hν
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  rw [← generatedProductSumLaw_normalizedRatioLaw ν R n k]
  apply hflat (normalizedRatioLaw R ν) inferInstance
    (normalizedRatioLaw_unitSupported ν hRpos hsupp) h ((K+1)*R^S) hh hhh
    (by positivity) hbudget
  · intro z u hhu _hu1
    exact normalizedRatioLaw_coarseCap ν hR hh hK hS.le hcap z u hhu

#print axioms normalizedRatioLaw
#print axioms normalizedRatioLaw_isProbabilityMeasure
#print axioms normalizedRatioLaw_unitSupported
#print axioms normalizedRatioLaw_closedBall
#print axioms normalizedRatioLaw_coarseCap
#print axioms productLaw_normalizedRatioLaw
#print axioms generatedProductSumLaw_normalizedRatioLaw
#print axioms exists_ratioLaw_generated_flatness

/-- Separate small-power budgets on the original cap coefficient and common R
pay the effective normalized loss. Thus the actual subpower inputs can be
instantiated without supplying an aggregate energy/Fourier certificate. -/
theorem exists_ratioLaw_generated_flatness_of_smallPowerCaps {S e : ℝ}
    (hS : 0 < S) (he : 0 < e) (he1 : e < 1) :
    ∃ (n k : ℕ) (h₀ q D : ℝ), 2 ≤ n ∧ 0 < k ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 0 < q ∧ 0 < D ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν → ∀ R : ℝ, 1 ≤ R →
        (∀ᵐ t ∂ν, |t| ≤ R) → ∀ (h K : ℝ), 0 < h → h ≤ h₀ → 0 ≤ K →
          K ≤ h^(-q) → R ≤ h^(-q) →
          (∀ z u : ℝ, h ≤ u → u ≤ 1 → ν (closedBall z u) ≤ ENNReal.ofReal (K*u^S)) →
          ∀ x : ℝ, ((generatedProductSumLaw (fun _ : Fin n ↦ ν) k).map (fun t ↦ t/R^n)).real
            (Icc (x-h) (x+h)) ≤ D*h^(1-e) := by
  obtain ⟨n, k, h₁, Q, D, hn, hk, hh₁, hh₁1, hQ, hD, hflat⟩ :=
    exists_ratioLaw_generated_flatness hS he he1
  let q : ℝ := Q/(2*(S+1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hqeq : q*(S+1) = Q/2 := by
    have hd : 2*(S+1) ≠ 0 := by positivity
    have hh := div_mul_cancel₀ Q hd
    dsimp [q]
    nlinarith only [hh]
  obtain ⟨h₂, hh₂, hh₂1, hsmall⟩ :=
    exists_small_scale_power_bound (C := 2) (a := Q/2) (τ := 0) (by norm_num) (by positivity)
  refine ⟨n, k, min h₁ h₂, q, D, hn, hk, lt_min hh₁ hh₂,
    (min_le_left _ _).trans hh₁1, hq, hD, ?_⟩
  intro ν hν R hR hsupp h K hh hhh hK hKq hRq hcap x
  have hh1 : h ≤ 1 := hhh.trans ((min_le_left _ _).trans hh₁1)
  have hone : 1 ≤ h^(-q) := by
    have hp := Real.rpow_le_rpow_of_exponent_ge hh hh1 (show -q ≤ 0 by linarith)
    simpa using hp
  have hKone : K+1 ≤ 2*h^(-q) := by linarith only [hKq, hone]
  have hRb : R^S ≤ h^(-q*S) := by
    apply (Real.rpow_le_rpow (by linarith : 0 ≤ R) hRq hS.le).trans_eq
    rw [← Real.rpow_mul hh.le]
  have hmul : h^(Q/2)*h^(-(Q/2)) = 1 := by rw [← Real.rpow_add hh]; simp
  have hpay : 2 ≤ h^(-(Q/2)) := by
    have hp : 2*h^(Q/2) ≤ 1 := by simpa using hsmall h hh (hhh.trans (min_le_right _ _))
    calc
      2 = (2*h^(Q/2))*h^(-(Q/2)) := by rw [mul_assoc, hmul, mul_one]
      _ ≤ 1*h^(-(Q/2)) := mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := one_mul _
  have hbudget : (K+1)*R^S ≤ h^(-Q) := by
    calc
      _ ≤ (2*h^(-q))*h^(-q*S) := mul_le_mul hKone hRb (by positivity) (by positivity)
      _ = 2*h^(-(Q/2)) := by
        rw [mul_assoc, ← Real.rpow_add hh]
        congr 1
        rw [show -q + -q*S = -(q*(S+1)) by ring, hqeq]
      _ ≤ h^(-(Q/2))*h^(-(Q/2)) := mul_le_mul_of_nonneg_right hpay (by positivity)
      _ = _ := by rw [← Real.rpow_add hh]; congr 1; ring
  exact hflat ν hν R hR hsupp h K hh (hhh.trans (min_le_left _ _)) hK hbudget hcap x

#print axioms exists_ratioLaw_generated_flatness_of_smallPowerCaps

/-- Full manuscript loss range e>0, with the same original-law hypotheses and
quantifier order. The internal analytic loss is always strictly below one. -/
theorem exists_ratioLaw_generated_flatness_for_all_losses {S e : ℝ}
    (hS : 0 < S) (he : 0 < e) :
    ∃ (n k : ℕ) (h₀ q D : ℝ), 2 ≤ n ∧ 0 < k ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 0 < q ∧ 0 < D ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν → ∀ R : ℝ, 1 ≤ R →
        (∀ᵐ t ∂ν, |t| ≤ R) → ∀ (h K : ℝ), 0 < h → h ≤ h₀ → 0 ≤ K →
          K ≤ h^(-q) → R ≤ h^(-q) →
          (∀ z u : ℝ, h ≤ u → u ≤ 1 → ν (closedBall z u) ≤ ENNReal.ofReal (K*u^S)) →
          ∀ x : ℝ, ((generatedProductSumLaw (fun _ : Fin n ↦ ν) k).map (fun t ↦ t/R^n)).real
            (Icc (x-h) (x+h)) ≤ D*h^(1-e) := by
  let a : ℝ := min (e/2) (1/2)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hae : a ≤ e := (min_le_left _ _).trans (by linarith)
  obtain ⟨n, k, h₀, q, D, hn, hk, hh₀, hh₀1, hq, hD, hflat⟩ :=
    exists_ratioLaw_generated_flatness_of_smallPowerCaps hS ha ha1
  refine ⟨n, k, h₀, q, D, hn, hk, hh₀, hh₀1, hq, hD, ?_⟩
  intro ν hν R hR hsupp h K hh hhh hK hKq hRq hcap x
  apply (hflat ν hν R hR hsupp h K hh hhh hK hKq hRq hcap x).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hh (hhh.trans hh₀1) (by linarith only [hae])) hD.le

#print axioms exists_ratioLaw_generated_flatness_for_all_losses
end Kakeya4.Hard.MultiplicativeConvolution
