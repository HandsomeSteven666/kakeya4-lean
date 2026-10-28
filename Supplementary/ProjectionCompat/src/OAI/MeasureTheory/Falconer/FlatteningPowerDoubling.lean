import OAI.MeasureTheory.Falconer.FlatteningFiniteSelection

/-! Exact additive powers and a finite search which starts at the second power. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem additiveLawPower_add (μ : Measure ℝ) [IsProbabilityMeasure μ] (m n : ℕ) :
    additiveLawPower μ (m+n) = additiveLawPower μ m ∗ additiveLawPower μ n := by
  induction n with
  | zero => simp [additiveLawPower]
  | succ n ih =>
    change additiveLawPower μ (m+n) ∗ μ =
      additiveLawPower μ m ∗ (additiveLawPower μ n ∗ μ)
    rw [ih,Measure.conv_assoc]

theorem additiveLawPower_double (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ) :
    additiveLawPower μ (2*k) = additiveLawPower μ k ∗ additiveLawPower μ k := by
  rw [show 2*k=k+k by omega,additiveLawPower_add]

theorem additiveLawPower_power (μ : Measure ℝ) [IsProbabilityMeasure μ] (k n : ℕ) :
    additiveLawPower (additiveLawPower μ k) n = additiveLawPower μ (k*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change additiveLawPower (additiveLawPower μ k) n ∗ additiveLawPower μ k =
      additiveLawPower μ (k*(n+1))
    rw [ih,Nat.mul_succ,additiveLawPower_add]

theorem additiveLawPower_two (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    additiveLawPower μ 2 = μ ∗ μ := by simp [additiveLawPower]

theorem flatteningL2Seq_square_eq_shift (kernel : SmoothKernel) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (r : ℝ) (k : ℕ) :
    flatteningL2Seq kernel (μ ∗ μ) r k = flatteningL2Seq kernel μ r (k+1) := by
  unfold flatteningL2Seq
  rw [← additiveLawPower_two μ,additiveLawPower_power,pow_succ']

theorem flatteningL2Seq_succ_eq_double (kernel : SmoothKernel) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (r : ℝ) (k : ℕ) :
    flatteningL2Seq kernel μ r (k+1) = densityL2
      (additiveLawPower μ (2^k) ∗ additiveLawPower μ (2^k)) (kernelProfile kernel r) := by
  unfold flatteningL2Seq
  rw [pow_succ',additiveLawPower_double]

theorem exists_uniform_flattening_slow_step_from_two (kernel : SmoothKernel)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ r₀ : ℝ, 0 < N ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], ∀ r : ℝ,
      0 < r → r ≤ r₀ →
      flatteningL2Seq kernel μ r (N+1) ≤ 1 ∨
      ∃ k : ℕ, k < N ∧ 2 ≤ (2:ℕ)^(k+1) ∧
        1 < flatteningL2Seq kernel μ r (k+1) ∧
        ENNReal.ofReal (r^ε) * flatteningL2Seq kernel μ r (k+1) ≤
          densityL2 (additiveLawPower μ (2^(k+1)) ∗ additiveLawPower μ (2^(k+1)))
            (kernelProfile kernel r) := by
  obtain ⟨N,r₀,hN,hr₀,hr₀1,hselect⟩ := exists_uniform_flattening_slow_step kernel hε
  refine ⟨N,r₀,hN,hr₀,hr₀1,?_⟩
  intro μ _ r hr hrr
  rcases hselect (μ ∗ μ) r hr hrr with hlo | ⟨k,hk,hbig,hslow⟩
  · exact Or.inl (by simpa only [flatteningL2Seq_square_eq_shift] using hlo)
  · refine Or.inr ⟨k,hk,?_,?_,?_⟩
    · simpa using Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) (by omega : 1≤k+1)
    · simpa only [flatteningL2Seq_square_eq_shift] using hbig
    · simpa only [flatteningL2Seq_square_eq_shift,
        flatteningL2Seq_succ_eq_double kernel μ r (k+1)] using hslow

#print axioms additiveLawPower_add
#print axioms additiveLawPower_double
#print axioms additiveLawPower_power
#print axioms additiveLawPower_two
#print axioms flatteningL2Seq_square_eq_shift
#print axioms flatteningL2Seq_succ_eq_double
#print axioms exists_uniform_flattening_slow_step_from_two
end OAI.Falconer
