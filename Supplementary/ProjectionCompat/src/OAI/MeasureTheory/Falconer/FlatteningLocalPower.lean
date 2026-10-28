import OAI.MeasureTheory.Falconer.FlatteningLocalL2Bound

/-! Pay every local layer loss before the actual finite doubling argument. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem layer_quotient_rpow {r : ℝ} (hr : 0 < r) (P d η : ℝ) (L : ℕ) :
    P*((L:ℝ)+1)^4/((5*r)^(-d+η)*r) =
      (P*5^(d-η))*((L:ℝ)+1)^4*r^(d-1-η) := by
  have hpow : (5*r)^(-d+η)*r = 5^(-d+η)*r^(-d+η+1) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤5) hr.le,
      Real.rpow_add hr (-d+η) 1,Real.rpow_one]
    ring
  rw [hpow,div_eq_mul_inv,mul_inv_rev,← Real.rpow_neg hr.le,
    ← Real.rpow_neg (by norm_num : (0:ℝ)≤5)]
  rw [show -(-d+η+1) = d-1-η by ring,show -(-d+η) = d-η by ring]
  ring

theorem exists_paid_local_layer_bound {M T P d β : ℝ}
    (hM : 0 < M) (hT : 0 < T) (hP : 0 < P) (hd : d ≤ 1) (hβ : 0 < β) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ L : ℕ, (2:ℝ)^L ≤ 2*max 1 (M/r) →
      max (T*((L:ℝ)+1)^2) (P*((L:ℝ)+1)^4/((5*r)^(-d+β/2)*r)) ≤
        r^(d-1-β) := by
  obtain ⟨r₁,hr₁,hr₁1,hlow⟩ := exists_small_scale_layer_power_bound hM hT.le
    (β := β/2) (by positivity) 2
  obtain ⟨r₂,hr₂,hr₂1,hhigh⟩ := exists_small_scale_layer_power_bound hM
    (C := P*5^(d-β/2)) (by positivity) (β := β/2) (by positivity) 4
  refine ⟨min r₁ r₂,lt_min hr₁ hr₂,(min_le_left _ _).trans hr₁1,?_⟩
  intro r hr hrr L hL
  have hr1 : r ≤ 1 := (hrr.trans (min_le_left _ _)).trans hr₁1
  apply max_le
  · exact (hlow r hr (hrr.trans (min_le_left _ _)) L hL).trans
      (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith : d-1-β ≤ -(β/2)))
  · rw [layer_quotient_rpow hr]
    calc
      _ ≤ r^(-(β/2))*r^(d-1-β/2) := mul_le_mul_of_nonneg_right
        (hhigh r hr (hrr.trans (min_le_right _ _)) L hL) (Real.rpow_nonneg hr.le _)
      _ = _ := by rw [← Real.rpow_add hr]; congr 1; ring

theorem OSS_original_energy_slow_local_power_bound (kernel : SmoothKernel) {s t β a : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s+t ≤ 1) (hβ : 0 < β) (ha : 0 < a) :
    ∃ ε e r₀ : ℝ, 0 < ε ∧ 0 < e ∧ e ≤ β/2 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ δ r : ℝ, 0 < δ → 0 < r → δ ≤ r → r ≤ δ^a → r ≤ r₀ →
    ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      UnitSupported μ → UnitSupported ν →
      smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-ε)) →
      smoothEnergy kernel.law t δ ν ≤ ENNReal.ofReal (δ^(-ε)) →
      ∀ k : ℕ, 2 ≤ k →
      let ρ := additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k
      ENNReal.ofReal (r^e)*densityL2 ρ (kernelProfile kernel r) ≤
        densityL2 (ρ ∗ ρ) (kernelProfile kernel r) →
      densityL2 (ρ ∗ ρ) (kernelProfile kernel r) ≤ ENNReal.ofReal (r^(s+t-1-β)) := by
  obtain ⟨ε,e,M,T,P,r₁,hε,he,hM,hT,hP,hr₁,hr₁1,hlocal⟩ :=
    OSS_original_energy_slow_local_L2_bound kernel hs ht hst (by positivity : 0<β/2) ha
  obtain ⟨r₂,hr₂,hr₂1,hpay⟩ := exists_paid_local_layer_bound hM hT hP hst hβ
  refine ⟨ε,min e (β/2),min r₁ r₂,hε,lt_min he (by positivity),min_le_right _ _,
    lt_min hr₁ hr₂,(min_le_left _ _).trans hr₁1,?_⟩
  intro δ r hδ hr hδr hwindow hrr μ ν _ _ hμU hνU hμE hνE k hk ρ hslow
  obtain ⟨L,hL,hbound⟩ := hlocal r hr (hrr.trans (min_le_left _ _))
  have hq : ENNReal.ofReal (r^e) ≤ ENNReal.ofReal (r^(min e (β/2))) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hr
      ((hrr.trans (min_le_left _ _)).trans hr₁1) (min_le_left _ _))
  exact (hbound δ hδ hδr hwindow μ ν hμU hνU hμE hνE k hk
    ((mul_le_mul_left hq _).trans hslow)).trans
      (ENNReal.ofReal_le_ofReal (by
        simpa only [neg_add_rev,sub_eq_add_neg,add_assoc,add_left_comm,add_comm] using
          hpay r hr (hrr.trans (min_le_right _ _)) L hL))

#print axioms layer_quotient_rpow
#print axioms exists_paid_local_layer_bound
#print axioms OSS_original_energy_slow_local_power_bound
end OAI.Falconer
