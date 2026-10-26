






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningPaidLayerConsumer

/-! Preserve the same selected layer for mass and energy-volume estimates. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal BigOperators

theorem selected_layer_energy_volume_bound (E a V I K D C : ℝ≥0∞)
    (hE0 : E ≠ 0) (hEtop : E ≠ ⊤) (hselect : E ≤ K*a^2*I)
    (hindicator : I^2 ≤ D*V^3*E) (hmass : a*V ≤ C) :
    E*V ≤ K^2*D*C^4 := by
  have hcancel : E*E ≤ E*(K^2*D*a^4*V^3) := by
    calc
      _ = E^2 := (pow_two E).symm
      _ ≤ (K*a^2*I)^2 := pow_le_pow_left' hselect 2
      _ = K^2*a^4*I^2 := by ring
      _ ≤ K^2*a^4*(D*V^3*E) := mul_le_mul_right hindicator _
      _ = _ := by ring
  have hE := (ENNReal.mul_le_mul_iff_right hE0 hEtop).mp hcancel
  calc
    E*V ≤ (K^2*D*a^4*V^3)*V := mul_le_mul_left hE V
    _ = K^2*D*(a*V)^4 := by ring
    _ ≤ K^2*D*C^4 := mul_le_mul_right (pow_le_pow_left' hmass 4) _

theorem exists_actual_cell_layer_mass_bound (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      ∀ r : ℝ, 0 < r → ∀ j : ℕ,
      (2:ℝ≥0∞)^j * volume
        (flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j) ≤
        ENNReal.ofReal C := by
  obtain ⟨C,hC,hbound⟩ := exists_actual_cellEnvelope_mass_bound kernel
  refine ⟨C,hC,?_⟩
  intro μ _ r hr j
  exact (Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_range.mpr (Nat.lt_succ_self j))).trans
    (hbound μ r hr (j+1))

theorem exists_uniform_slow_layer_joint_bounds (kernel : SmoothKernel) :
    ∃ M T Q P : ℝ, 0 < M ∧ 0 < T ∧ 0 < Q ∧ 0 < P ∧
    ∀ r : ℝ, 0 < r → ∃ L : ℕ,
      (2:ℝ)^L ≤ 2*max 1 (M/r) ∧
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], ∀ q : ℝ≥0∞,
      q*densityL2 μ (kernelProfile kernel r) ≤ densityL2 (μ ∗ μ) (kernelProfile kernel r) →
      densityL2 (μ ∗ μ) (kernelProfile kernel r) ≤ ENNReal.ofReal T * ((L+1:ℕ):ℝ≥0∞)^2 ∨
      ∃ j : ℕ, j < L ∧
        let V := volume (flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j)
        q ≤ ENNReal.ofReal Q * ((L+1:ℕ):ℝ≥0∞)^4 * ((2:ℝ≥0∞)^j*V)^2 ∧
        densityL2 (μ ∗ μ) (kernelProfile kernel r)*V ≤
          ENNReal.ofReal P * ((L+1:ℕ):ℝ≥0∞)^4 := by
  obtain ⟨M,T,hM,hT,hsel⟩ := exists_uniform_actual_double_layer_selection kernel
  obtain ⟨B,hB,hlevel⟩ := exists_actual_cell_layer_sq_mass_bound kernel
  obtain ⟨D,hD,hindicator⟩ := exists_indicator_actual_convolution_L2_bound kernel
  obtain ⟨C,hC,hmass⟩ := exists_actual_cell_layer_mass_bound kernel
  let Q : ℝ := (4*T)^2*D*B
  let P : ℝ := (4*T)^2*D*C^4
  refine ⟨M,T,Q,P,hM,hT,by dsimp [Q]; positivity,by dsimp [P]; positivity,?_⟩
  intro r hr
  obtain ⟨L,hL,hselect⟩ := hsel r hr
  refine ⟨L,hL,?_⟩
  intro μ _ q hslow
  by_cases hlo : densityL2 (μ ∗ μ) (kernelProfile kernel r) ≤
      ENNReal.ofReal T * ((L+1:ℕ):ℝ≥0∞)^2
  · exact Or.inl hlo
  right
  obtain ⟨j,hj,hjselect⟩ := (hselect μ).resolve_left hlo
  let A := flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j
  let a : ℝ≥0∞ := 2^j
  let I : ℝ≥0∞ := ∫⁻ x, ((A.indicator (fun _ ↦ (1:ℝ≥0∞))) ⋆ₗ
    (additiveDensity μ (kernelProfile kernel (4*r)))) x ^ 2
  have hE₂0 : densityL2 (μ ∗ μ) (kernelProfile kernel r) ≠ 0 := by
    intro hz
    exact hlo (hz.le.trans bot_le)
  have hE0 : densityL2 μ (kernelProfile kernel r) ≠ 0 := by
    intro hz
    have hdown := densityL2_conv_probability_le μ μ _ (measurable_kernelProfile kernel r)
    rw [hz] at hdown
    exact hE₂0 (le_antisymm hdown bot_le)
  obtain ⟨H,_,hH⟩ := kernel.exists_height
  have hEtop : densityL2 μ (kernelProfile kernel r) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (densityL2_kernelProfile_le_height_probability kernel hH μ hr)
  have hE₂top : densityL2 (μ ∗ μ) (kernelProfile kernel r) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (densityL2_kernelProfile_le_height_probability kernel hH (μ ∗ μ) hr)
  have h4 : ENNReal.ofReal (4*T) = (4:ℝ≥0∞)*ENNReal.ofReal T := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4)]
    norm_num
  have hs : densityL2 (μ ∗ μ) (kernelProfile kernel r) ≤
      (ENNReal.ofReal (4*T) * ((L+1:ℕ):ℝ≥0∞)^2) * a^2 * I := by
    convert hjselect using 1
    dsimp [a,I,A]
    rw [h4,show (2:ℝ≥0∞)^(j+1) = 2*2^j from pow_succ' _ _]
    ring
  have hi := hindicator μ r hr A (measurableSet_flatteningCellDyadicLevel _ r j)
  have hc := slow_layer_mass_cancellation _ _ a (volume A) I q
    (ENNReal.ofReal (4*T)*((L+1:ℕ):ℝ≥0∞)^2) (ENNReal.ofReal B) (ENNReal.ofReal D)
    hE0 hEtop hE₂0 hE₂top hslow hs hi (hlevel μ r hr j)
  have hp := selected_layer_energy_volume_bound _ a (volume A) I
    (ENNReal.ofReal (4*T)*((L+1:ℕ):ℝ≥0∞)^2) (ENNReal.ofReal D) (ENNReal.ofReal C)
    hE₂0 hE₂top hs hi (hmass μ r hr j)
  have hQ : ENNReal.ofReal Q = ENNReal.ofReal (4*T)^2*ENNReal.ofReal D*ENNReal.ofReal B := by
    dsimp [Q]
    rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hD.le),
      ENNReal.ofReal_mul (sq_nonneg _),ENNReal.ofReal_pow (by positivity : 0≤4*T)]
  have hP : ENNReal.ofReal P = ENNReal.ofReal (4*T)^2*ENNReal.ofReal D*(ENNReal.ofReal C)^4 := by
    dsimp [P]
    rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hD.le),
      ENNReal.ofReal_mul (sq_nonneg _),ENNReal.ofReal_pow (by positivity : 0≤4*T),
      ENNReal.ofReal_pow hC.le]
  refine ⟨j,hj,?_,?_⟩
  · exact hc.trans_eq (by rw [hQ]; dsimp [a,A]; ring)
  · exact hp.trans_eq (by rw [hP]; ring)

#print axioms selected_layer_energy_volume_bound
#print axioms exists_actual_cell_layer_mass_bound
#print axioms exists_uniform_slow_layer_joint_bounds
end OAI.Falconer
