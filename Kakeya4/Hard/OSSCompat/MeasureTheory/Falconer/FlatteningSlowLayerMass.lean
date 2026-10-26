






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningLayerSelection

/-! Energy cancellation and the actual large-layer mass forced by slow descent. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem slow_layer_mass_cancellation (E E₂ a V I q K B D : ℝ≥0∞)
    (hE0 : E ≠ 0) (hEtop : E ≠ ⊤) (hE₂0 : E₂ ≠ 0) (hE₂top : E₂ ≠ ⊤)
    (hslow : q*E ≤ E₂) (hselect : E₂ ≤ K*a^2*I)
    (hindicator : I^2 ≤ D*V^3*E₂) (hlayer : a^2*V ≤ B*E) :
    q ≤ K^2*D*B*(a*V)^2 := by
  have hcancel : E₂ * E₂ ≤ E₂ * (K^2*D*a^4*V^3) := by
    calc
      _ = E₂^2 := (pow_two E₂).symm
      _ ≤ (K*a^2*I)^2 := pow_le_pow_left' hselect 2
      _ = K^2*a^4*I^2 := by ring
      _ ≤ K^2*a^4*(D*V^3*E₂) := mul_le_mul_right hindicator _
      _ = _ := by ring
  have hE₂ : E₂ ≤ K^2*D*a^4*V^3 :=
    (ENNReal.mul_le_mul_iff_right hE₂0 hE₂top).mp hcancel
  have hfinal : E*q ≤ E*(K^2*D*B*(a*V)^2) := by
    calc
      _ = q*E := mul_comm _ _
      _ ≤ E₂ := hslow
      _ ≤ K^2*D*a^4*V^3 := hE₂
      _ = (K^2*D*(a*V)^2)*(a^2*V) := by ring
      _ ≤ (K^2*D*(a*V)^2)*(B*E) := mul_le_mul_right hlayer _
      _ = _ := by ring
  exact (ENNReal.mul_le_mul_iff_right hE0 hEtop).mp hfinal

theorem exists_uniform_actual_slow_layer_mass (kernel : SmoothKernel) :
    ∃ M T Q : ℝ, 0 < M ∧ 0 < T ∧ 0 < Q ∧ ∀ r : ℝ, 0 < r → ∃ L : ℕ,
      (2 : ℝ)^L ≤ 2*max 1 (M/r) ∧
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], ∀ q : ℝ≥0∞,
      q*densityL2 μ (kernelProfile kernel r) ≤ densityL2 (μ ∗ μ) (kernelProfile kernel r) →
      densityL2 (μ ∗ μ) (kernelProfile kernel r) ≤ ENNReal.ofReal T * ((L+1 : ℕ) : ℝ≥0∞)^2 ∨
      ∃ j : ℕ, j < L ∧ q ≤ ENNReal.ofReal Q * ((L+1 : ℕ) : ℝ≥0∞)^4 *
        ((2 : ℝ≥0∞)^j * volume
          (flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j))^2 := by
  obtain ⟨M,T,hM,hT,hsel⟩ := exists_uniform_actual_double_layer_selection kernel
  obtain ⟨B,hB,hlevel⟩ := exists_actual_cell_layer_sq_mass_bound kernel
  obtain ⟨D,hD,hindicator⟩ := exists_indicator_actual_convolution_L2_bound kernel
  let Q : ℝ := (4*T)^2*D*B
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  refine ⟨M,T,Q,hM,hT,hQpos,?_⟩
  intro r hr
  obtain ⟨L,hL,hselect⟩ := hsel r hr
  refine ⟨L,hL,?_⟩
  intro μ _ q hslow
  by_cases hlo : densityL2 (μ ∗ μ) (kernelProfile kernel r) ≤
      ENNReal.ofReal T * ((L+1 : ℕ) : ℝ≥0∞)^2
  · exact Or.inl hlo
  right
  obtain ⟨j,hj,hjselect⟩ := (hselect μ).resolve_left hlo
  let A := flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j
  let a : ℝ≥0∞ := 2^j
  let I : ℝ≥0∞ := ∫⁻ x, ((A.indicator (fun _ ↦ (1 : ℝ≥0∞))) ⋆ₗ
    (additiveDensity μ (kernelProfile kernel (4*r)))) x ^ 2
  have hE₂0 : densityL2 (μ ∗ μ) (kernelProfile kernel r) ≠ 0 := by
    intro hz
    apply hlo
    rw [hz]
    exact zero_le
  have hE0 : densityL2 μ (kernelProfile kernel r) ≠ 0 := by
    intro hz
    have hdown := densityL2_conv_probability_le μ μ _ (measurable_kernelProfile kernel r)
    rw [hz] at hdown
    exact hE₂0 (le_antisymm hdown zero_le)
  obtain ⟨H,_,hH⟩ := kernel.exists_height
  have hEtop : densityL2 μ (kernelProfile kernel r) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (densityL2_kernelProfile_le_height_probability kernel hH μ hr)
  have hE₂top : densityL2 (μ ∗ μ) (kernelProfile kernel r) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (densityL2_kernelProfile_le_height_probability kernel hH (μ ∗ μ) hr)
  have h4 : ENNReal.ofReal (4*T) = (4 : ℝ≥0∞)*ENNReal.ofReal T := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hs : densityL2 (μ ∗ μ) (kernelProfile kernel r) ≤
      (ENNReal.ofReal (4*T) * ((L+1 : ℕ) : ℝ≥0∞)^2) * a^2 * I := by
    convert hjselect using 1
    dsimp [a,I,A]
    rw [h4,show (2 : ℝ≥0∞)^(j+1) = 2*2^j from pow_succ' _ _]
    ring
  have hc := slow_layer_mass_cancellation _ _ a (volume A) I q
    (ENNReal.ofReal (4*T) * ((L+1 : ℕ) : ℝ≥0∞)^2) (ENNReal.ofReal B) (ENNReal.ofReal D)
    hE0 hEtop hE₂0 hE₂top hslow hs
    (hindicator μ r hr A (measurableSet_flatteningCellDyadicLevel _ r j))
    (hlevel μ r hr j)
  refine ⟨j,hj,hc.trans_eq ?_⟩
  have hQ : ENNReal.ofReal Q = ENNReal.ofReal (4*T)^2 * ENNReal.ofReal D * ENNReal.ofReal B := by
    dsimp [Q]
    rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hD.le),
      ENNReal.ofReal_mul (sq_nonneg _),ENNReal.ofReal_pow (by positivity : 0 ≤ 4*T)]
  rw [hQ]
  dsimp [a,A]
  ring

#print axioms slow_layer_mass_cancellation
#print axioms exists_uniform_actual_slow_layer_mass
end OAI.Falconer
