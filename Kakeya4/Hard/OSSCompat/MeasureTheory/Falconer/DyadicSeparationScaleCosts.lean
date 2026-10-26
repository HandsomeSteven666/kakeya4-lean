






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FineDyadicPruning

/-! Exact floor-depth/cardinality conversion and uniform absorption of the
actual three-term grid/bootstrap deletion cost. No law-dependent threshold
is hidden in a fixed-grid or normalization constant. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set MeasureTheory
open scoped ENNReal

theorem dyadic_scaled_depth_card_bound (N : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    ((cubePaths 2 ⌊θ*(N:ℝ)⌋₊).card : ℝ) ≤ ((2:ℝ)^N)^(2*θ) := by
  let J := ⌊θ*(N:ℝ)⌋₊
  have hf : (J:ℝ) ≤ θ*(N:ℝ) := Nat.floor_le (mul_nonneg hθ (Nat.cast_nonneg _))
  rw [card_cubePaths]
  push_cast
  rw [← Real.rpow_natCast (2:ℝ) (2*⌊θ*(N:ℝ)⌋₊),
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  dsimp [J] at hf
  nlinarith

theorem dyadic_scaled_depth_inverse_bound (N : ℕ) (θ : ℝ) :
    1/(2:ℝ)^⌊θ*(N:ℝ)⌋₊ ≤ 2*((2:ℝ)^N)^(-θ) := by
  have hf := Nat.lt_floor_add_one (θ*(N:ℝ))
  calc
    _ = (2:ℝ)^(-((⌊θ*(N:ℝ)⌋₊:ℕ):ℝ)) := by
      rw [Real.rpow_neg (by norm_num),Real.rpow_natCast,one_div]
    _ ≤ (2:ℝ)^(1-(N:ℝ)*θ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = (2:ℝ)^(1+(N:ℝ)*(-θ)) := by congr 1; ring
    _ = (2:ℝ)^1*(2:ℝ)^((N:ℝ)*(-θ)) := Real.rpow_add (by norm_num) _ _
    _ = _ := by rw [Real.rpow_one,Real.rpow_natCast_mul (by norm_num)]

theorem dyadic_small_cell_scale_cost (N : ℕ) {θ κ : ℝ} (hθ : 0 ≤ θ) :
    2*((cubePaths 2 ⌊θ*(N:ℝ)⌋₊).card : ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^N)^(-κ)) ≤
      ENNReal.ofReal (2*((2:ℝ)^N)^(-(κ-2*θ))) := by
  let M := (cubePaths 2 ⌊θ*(N:ℝ)⌋₊).card
  have hm : (M:ℝ) ≤ ((2:ℝ)^N)^(2*θ) := dyadic_scaled_depth_card_bound N θ hθ
  calc
    _ = ENNReal.ofReal (2*(M:ℝ)*((2:ℝ)^N)^(-κ)) := by
      rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by norm_num)]
      simp only [ENNReal.ofReal_ofNat,ENNReal.ofReal_natCast]
      rfl
    _ ≤ ENNReal.ofReal (2*((2:ℝ)^N)^(2*θ)*((2:ℝ)^N)^(-κ)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm (by norm_num)) (by positivity))
    _ = _ := by
      rw [mul_assoc,← Real.rpow_add (by positivity)]
      congr 2
      ring

theorem dyadic_near_pair_scale_cost (N : ℕ) {θ α ε C : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ C) (hCbudget : C ≤ ((2:ℝ)^N)^ε) :
    ENNReal.ofReal (C*(20/(2:ℝ)^⌊θ*(N:ℝ)⌋₊)^α) ≤
      ENNReal.ofReal ((40:ℝ)^α*((2:ℝ)^N)^(-(θ*α-ε))) := by
  have hrad : 20/(2:ℝ)^⌊θ*(N:ℝ)⌋₊ ≤ 40*((2:ℝ)^N)^(-θ) := by
    have hh := mul_le_mul_of_nonneg_left (dyadic_scaled_depth_inverse_bound N θ) (by norm_num : (0:ℝ) ≤ 20)
    convert hh using 1 <;> ring
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ((2:ℝ)^N)^ε*(40*((2:ℝ)^N)^(-θ))^α := mul_le_mul hCbudget
      (Real.rpow_le_rpow (by positivity) hrad hα) (by positivity) (by positivity)
    _ = (40:ℝ)^α*((2:ℝ)^N)^ε*((2:ℝ)^N)^((-θ)*α) := by
      rw [Real.mul_rpow (by norm_num) (by positivity),← Real.rpow_mul (by positivity)]
      ring
    _ = _ := by
      rw [mul_assoc,← Real.rpow_add (by positivity)]
      congr 2
      ring

theorem dyadic_grid_bootstrap_error_absorbed {θ κ α ε c : ℝ}
    (hθ : 0 < θ) (hκ : 2*θ < κ) (hα : 0 ≤ α) (hε : ε < θ*α) (hc : 0 < c) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ C : ℝ, 0 ≤ C → C ≤ ((2:ℝ)^N)^ε →
      2*((cubePaths 2 ⌊θ*(N:ℝ)⌋₊).card : ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^N)^(-κ))+
        ENNReal.ofReal (C*(20/(2:ℝ)^⌊θ*(N:ℝ)⌋₊)^α)+ENNReal.ofReal (((2:ℝ)^N)^(-c)) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-τ)) := by
  let d := min (κ-2*θ) (min (θ*α-ε) c)
  have hd : 0 < d := lt_min (by linarith) (lt_min (by linarith) hc)
  have hτ : 0 < d/2 := by positivity
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hτ (3+(40:ℝ)^α)
  refine ⟨d/2,hτ,N₀,?_⟩
  intro N hN C hC hCbudget
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have h₁ : ((2:ℝ)^N)^(-(κ-2*θ)) ≤ ((2:ℝ)^N)^(-d) :=
    Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg (min_le_left _ _))
  have h₂ : ((2:ℝ)^N)^(-(θ*α-ε)) ≤ ((2:ℝ)^N)^(-d) :=
    Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg ((min_le_right _ _).trans (min_le_left _ _)))
  have h₃ : ((2:ℝ)^N)^(-c) ≤ ((2:ℝ)^N)^(-d) :=
    Real.rpow_le_rpow_of_exponent_le hR (neg_le_neg ((min_le_right _ _).trans (min_le_right _ _)))
  calc
    _ ≤ ENNReal.ofReal (2*((2:ℝ)^N)^(-(κ-2*θ)))+
        ENNReal.ofReal ((40:ℝ)^α*((2:ℝ)^N)^(-(θ*α-ε)))+
        ENNReal.ofReal (((2:ℝ)^N)^(-c)) := add_le_add
      (add_le_add (dyadic_small_cell_scale_cost N hθ.le) (dyadic_near_pair_scale_cost N hα hC hCbudget)) le_rfl
    _ ≤ ENNReal.ofReal (2*((2:ℝ)^N)^(-d))+
        ENNReal.ofReal ((40:ℝ)^α*((2:ℝ)^N)^(-d))+
        ENNReal.ofReal (((2:ℝ)^N)^(-d)) := add_le_add
      (add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h₁ (by norm_num)))
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h₂ (by positivity)))) (ENNReal.ofReal_le_ofReal h₃)
    _ = ENNReal.ofReal ((3+(40:ℝ)^α)*((2:ℝ)^N)^(-d)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (((2:ℝ)^N)^(d/2)*((2:ℝ)^N)^(-d)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity))
    _ = _ := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      ring

#print axioms dyadic_scaled_depth_card_bound
#print axioms dyadic_scaled_depth_inverse_bound
#print axioms dyadic_small_cell_scale_cost
#print axioms dyadic_near_pair_scale_cost
#print axioms dyadic_grid_bootstrap_error_absorbed
end OAI.Falconer
