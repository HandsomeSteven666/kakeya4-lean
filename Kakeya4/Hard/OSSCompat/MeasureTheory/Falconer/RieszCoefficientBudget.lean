






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.KaufmanRobustOuterConsumer

/-! Quantitative law-independent control of the actual Riesz bound in C. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal NNReal BigOperators

theorem riesz_small_ball_linear_in_coefficient {S p C : ℝ} (hC : 1 ≤ C) :
    rieszSmallBallBound S C p ≤ ENNReal.ofReal C*rieszSmallBallBound S 1 p := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have he : ENNReal.ofReal ((1/2:ℝ)^(-p)*C*2^S) =
      ENNReal.ofReal C*ENNReal.ofReal ((1/2:ℝ)^(-p)*2^S) := by
    rw [← ENNReal.ofReal_mul hC0]
    congr 1
    ring
  rw [rieszSmallBallBound,he,rieszSmallBallBound,mul_add,mul_one]
  simp only [mul_one]
  exact add_le_add (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hC)
    (le_of_eq (by ring))

theorem exists_uniform_riesz_linear_constant {S p : ℝ} (hpS : p < S) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ C : ℝ, 1 ≤ C → rieszSmallBallBound S C p ≤ ENNReal.ofReal (A*C) := by
  let B := rieszSmallBallBound S 1 p
  have hB : B ≠ ∞ := (rieszSmallBallBound_lt_top hpS).ne
  let A := B.toReal+1
  have hA : 1 ≤ A := by dsimp [A]; linarith [show 0 ≤ B.toReal from ENNReal.toReal_nonneg]
  have hBA : B ≤ ENNReal.ofReal A := by
    rw [← ENNReal.ofReal_toReal hB]
    exact ENNReal.ofReal_le_ofReal (by dsimp [A]; linarith)
  refine ⟨A,hA,?_⟩
  intro C hC
  calc
    _ ≤ ENNReal.ofReal C*B := riesz_small_ball_linear_in_coefficient hC
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal A := mul_le_mul' le_rfl hBA
    _ = _ := by rw [← ENNReal.ofReal_mul (zero_le_one.trans hC),mul_comm]

theorem uniform_riesz_dyadic_coefficient_budget {S p : ℝ} (hpS : p < S)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ e C : ℝ, 1 ≤ C → C ≤ ((2:ℝ)^N)^e →
      rieszSmallBallBound S C p ≤ ENNReal.ofReal (((2:ℝ)^N)^(e+ζ)) := by
  obtain ⟨A,hA,hbound⟩ := exists_uniform_riesz_linear_constant hpS
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hζ A
  refine ⟨N₀,?_⟩
  intro N hN e C hC hCb
  apply (hbound C hC).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ((2:ℝ)^N)^ζ*((2:ℝ)^N)^e :=
      mul_le_mul (hN₀ N hN) hCb (zero_le_one.trans hC) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

#print axioms riesz_small_ball_linear_in_coefficient
#print axioms exists_uniform_riesz_linear_constant
#print axioms uniform_riesz_dyadic_coefficient_budget
end OAI.Falconer
