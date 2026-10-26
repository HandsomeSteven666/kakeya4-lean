






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningDensityL2
import Kakeya4.Hard.MultiplicativeConvolution.SmoothEnergyL2
import Kakeya4.Hard.MultiplicativeConvolution.SmallScalePowers

/-! Finite selection for the actual squared L2 sequence in OSS Lemma 3.1. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem densityL2_kernelProfile_le_height_probability (kernel : SmoothKernel)
    {M : ℝ} (hM : ∀ z, kernel.density z ≤ M)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    densityL2 μ (kernelProfile kernel r) ≤ ENNReal.ofReal (M/r) := by
  have hmass : pairMass (2*r) μ ≤ 1 := by
    calc
      _ ≤ ∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂μ := lintegral_mono (fun _ ↦ prob_le_one)
      _ = 1 := by simp
  have h := (densityL2_kernelProfile_le_pairMass kernel hM μ hr).trans
    (mul_le_mul_right hmass (ENNReal.ofReal |r⁻¹| * ENNReal.ofReal M))
  rw [mul_one, abs_of_pos (inv_pos.mpr hr),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem exists_uniform_flatteningL2Seq_height (kernel : SmoothKernel) :
    ∃ M : ℝ, 0 < M ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      ∀ r : ℝ, 0 < r → ∀ k : ℕ,
      flatteningL2Seq kernel μ r k ≤ ENNReal.ofReal (M/r) := by
  obtain ⟨M,hM0,hM⟩ := kernel.exists_height
  exact ⟨M,hM0,fun μ _ r hr k ↦
    densityL2_kernelProfile_le_height_probability kernel hM (additiveLawPower μ (2^k)) hr⟩

theorem finite_geometric_descent_or_slow_step (a : ℕ → ℝ≥0∞) (q T : ℝ≥0∞)
    (N : ℕ) (ha : Antitone a) (hbound : q^N * a 0 ≤ T) :
    a N ≤ T ∨ ∃ k : ℕ, k < N ∧ T < a k ∧ q * a k ≤ a (k+1) := by
  classical
  by_cases h : a N ≤ T
  · exact Or.inl h
  · right
    by_contra hnone
    have hstep : ∀ k < N, a (k+1) ≤ q * a k := by
      intro k hk
      have hkT : T < a k := (lt_of_not_ge h).trans_le (ha hk.le)
      exact le_of_lt (lt_of_not_ge (fun hslow ↦ hnone ⟨k,hk,hkT,hslow⟩))
    have hind : ∀ n, n ≤ N → a n ≤ q^n * a 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        intro hn
        calc
          _ ≤ q * a n := hstep n (by omega)
          _ ≤ q * (q^n * a 0) := mul_le_mul_right (ih (by omega)) q
          _ = _ := by rw [pow_succ']; ac_rfl
    exact h ((hind N le_rfl).trans hbound)

/-- The finite search budget is chosen before the law and the scale. -/
theorem exists_uniform_flattening_slow_step (kernel : SmoothKernel)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ r₀ : ℝ, 0 < N ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], ∀ r : ℝ,
      0 < r → r ≤ r₀ →
      flatteningL2Seq kernel μ r N ≤ 1 ∨
      ∃ k : ℕ, k < N ∧ 1 < flatteningL2Seq kernel μ r k ∧
        ENNReal.ofReal (r^ε) * flatteningL2Seq kernel μ r k ≤
          flatteningL2Seq kernel μ r (k+1) := by
  obtain ⟨M,hM0,hM⟩ := exists_uniform_flatteningL2Seq_height kernel
  let N : ℕ := Nat.ceil (2/ε)
  have hNbound : (2:ℝ) ≤ ε * (N:ℝ) := by
    have h := Nat.le_ceil (2/ε)
    exact (div_le_iff₀ hε).mp h |>.trans_eq (mul_comm _ _)
  have hNpos : 0 < N := by
    by_contra hn
    have hz : N = 0 := by omega
    norm_num [hz] at hNbound
  obtain ⟨r₀,hr₀,hr₀1,hsmall⟩ :=
    exists_small_scale_power_bound (C := M) (a := ε*(N:ℝ)-1) (τ := 0) hM0.le (by linarith)
  refine ⟨N,r₀,hNpos,hr₀,hr₀1,?_⟩
  intro μ _ r hr hrr
  apply finite_geometric_descent_or_slow_step _ _ 1 N (flatteningL2Seq_antitone kernel μ r)
  calc
    _ ≤ ENNReal.ofReal (r^ε)^N * ENNReal.ofReal (M/r) :=
      mul_le_mul_right (hM μ r hr 0) _
    _ = ENNReal.ofReal (M*r^(ε*(N:ℝ)-1)) := by
      rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hr.le _) ,
        ← ENNReal.ofReal_mul (pow_nonneg (Real.rpow_nonneg hr.le _) _)]
      congr 1
      rw [← Real.rpow_mul_natCast hr.le, Real.rpow_sub hr, Real.rpow_one]
      ring
    _ ≤ 1 := by
      have h := hsmall r hr hrr
      simp only [neg_zero, Real.rpow_zero, mul_one] at h
      exact (ENNReal.ofReal_le_ofReal h).trans_eq (by simp)

#print axioms densityL2_kernelProfile_le_height_probability
#print axioms exists_uniform_flatteningL2Seq_height
#print axioms finite_geometric_descent_or_slow_step
#print axioms exists_uniform_flattening_slow_step
end OAI.Falconer
