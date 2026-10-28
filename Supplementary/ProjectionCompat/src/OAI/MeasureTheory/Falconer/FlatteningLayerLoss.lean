import OAI.MeasureTheory.Falconer.FlatteningOriginalEnergyLayer

/-! Explicit polynomial layer-count losses are absorbed by any positive scale power. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open Kakeya4.Hard.MultiplicativeConvolution

theorem exists_layer_polynomial_exp_bound (m : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ P : ℝ, 0 < P ∧ ∀ L : ℕ, ((L:ℝ)+1)^m ≤ P*((2:ℝ)^L)^η := by
  let b : ℝ := η*Real.log 2
  have hb : 0 < b := mul_pos hη (Real.log_pos (by norm_num))
  let P : ℝ := (m.factorial : ℝ)/b^m * (2:ℝ)^η
  refine ⟨P,by dsimp [P]; positivity,?_⟩
  intro L
  have hex : Real.exp (b*((L:ℝ)+1)) = (2:ℝ)^η * ((2:ℝ)^L)^η := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
      Real.rpow_def_of_pos (by positivity : (0:ℝ)<2^L),← Real.exp_add,Real.log_pow]
    congr 1
    dsimp [b]
    ring
  have h := Real.pow_div_factorial_le_exp (b*((L:ℝ)+1)) (by positivity : 0 ≤ b*((L:ℝ)+1)) m
  have hfact : 0 < (m.factorial : ℝ) := by positivity
  have hpow : b^m * ((L:ℝ)+1)^m ≤ Real.exp (b*((L:ℝ)+1)) * (m.factorial : ℝ) := by
    simpa only [mul_pow] using (div_le_iff₀ hfact).mp h
  calc
    _ = (b^m * ((L:ℝ)+1)^m)/b^m := by field_simp
    _ ≤ (Real.exp (b*((L:ℝ)+1)) * (m.factorial : ℝ))/b^m :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ = _ := by rw [hex]; dsimp [P]; ring

theorem exists_small_scale_layer_power_bound {M C β : ℝ} (_hM : 0 < M)
    (hC : 0 ≤ C) (hβ : 0 < β) (m : ℕ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ L : ℕ,
      (2:ℝ)^L ≤ 2*max 1 (M/r) → C*((L:ℝ)+1)^m ≤ r^(-β) := by
  let η : ℝ := β/2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨P,hP,hpoly⟩ := exists_layer_polynomial_exp_bound m hη
  let K : ℝ := 2*max 1 M
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨r₀,hr₀,hr₀1,hsmall⟩ := exists_small_scale_power_bound
    (C := C*P*K^η) (a := β/2) (τ := 0) (by positivity) (by positivity)
  refine ⟨r₀,hr₀,hr₀1,?_⟩
  intro r hr hrr L hheight
  have hr1 : r ≤ 1 := hrr.trans hr₀1
  have hmax : max 1 (M/r) ≤ max 1 M / r := by
    apply max_le
    · exact (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hr1.trans (le_max_left 1 M))
    · exact div_le_div_of_nonneg_right (le_max_right 1 M) hr.le
  have hheight' : (2:ℝ)^L ≤ K/r := hheight.trans (by
    dsimp [K]
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hmax (by norm_num : (0:ℝ)≤2))
  have hp : ((L:ℝ)+1)^m ≤ P*K^η*r^(-η) := by
    calc
      _ ≤ P*((2:ℝ)^L)^η := hpoly L
      _ ≤ P*(K/r)^η := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hheight' hη.le) hP.le
      _ = _ := by rw [Real.div_rpow hK.le hr.le,Real.rpow_neg hr.le]; ring
  have hs : (C*P*K^η)*r^(β/2) ≤ 1 := by
    simpa only [neg_zero,Real.rpow_zero,mul_one] using hsmall r hr hrr
  have hs' := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hr.le (-β))
  have heq : (C*P*K^η)*r^(β/2)*r^(-β) = C*(P*K^η*r^(-η)) := by
    calc
      _ = (C*P*K^η)*(r^(β/2)*r^(-β)) := by ring
      _ = (C*P*K^η)*r^(-η) := by
        rw [← Real.rpow_add hr]
        congr 2
        dsimp [η]
        ring
      _ = _ := by ring
  have hcoef : C*(P*K^η*r^(-η)) ≤ r^(-β) := by
    simpa only [heq,one_mul] using hs'
  exact (mul_le_mul_of_nonneg_left hp hC).trans hcoef

#print axioms exists_layer_polynomial_exp_bound
#print axioms exists_small_scale_layer_power_bound
end OAI.Falconer
