import OAI.MeasureTheory.Falconer.FlatteningFiniteSelection

/-! Measurable dyadic density layers, with a genuine finite height cutoff. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

def densityLowLevel (f : ℝ → ℝ≥0∞) : Set ℝ := {x | f x ≤ 1}

def densityDyadicLevel (f : ℝ → ℝ≥0∞) (j : ℕ) : Set ℝ :=
  {x | (2 : ℝ≥0∞)^j < f x ∧ f x ≤ (2 : ℝ≥0∞)^(j+1)}

theorem measurableSet_densityLowLevel (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    MeasurableSet (densityLowLevel f) := measurableSet_le hf measurable_const

theorem measurableSet_densityDyadicLevel (f : ℝ → ℝ≥0∞) (hf : Measurable f) (j : ℕ) :
    MeasurableSet (densityDyadicLevel f j) :=
  (measurableSet_lt measurable_const hf).inter (measurableSet_le hf measurable_const)

theorem exists_dyadic_level_of_le_pow {v : ℝ≥0∞} (L : ℕ)
    (hv : 1 < v) (hL : v ≤ (2 : ℝ≥0∞)^L) :
    ∃ j : ℕ, j < L ∧ (2 : ℝ≥0∞)^j < v ∧ v ≤ (2 : ℝ≥0∞)^(j+1) := by
  induction L with
  | zero => simp only [pow_zero] at hL; exact (not_lt_of_ge hL hv).elim
  | succ L ih =>
    by_cases h : v ≤ (2 : ℝ≥0∞)^L
    · obtain ⟨j,hj,hjv,hvj⟩ := ih h
      exact ⟨j,by omega,hjv,hvj⟩
    · exact ⟨L,by omega,lt_of_not_ge h,hL⟩

theorem density_levels_cover_of_height (f : ℝ → ℝ≥0∞) (L : ℕ)
    (hheight : ∀ x, f x ≤ (2 : ℝ≥0∞)^L) :
    densityLowLevel f ∪ (⋃ j ∈ Finset.range L, densityDyadicLevel f j) = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : f x ≤ 1
  · exact Or.inl hx
  · obtain ⟨j,hj,hjlo,hjhi⟩ := exists_dyadic_level_of_le_pow L (lt_of_not_ge hx) (hheight x)
    exact Or.inr (mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨Finset.mem_range.mpr hj,⟨hjlo,hjhi⟩⟩⟩)

theorem densityDyadicLevel_disjoint (f : ℝ → ℝ≥0∞) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (densityDyadicLevel f i) (densityDyadicLevel f j) := by
  suffices h : ∀ a b : ℕ, a < b → Disjoint (densityDyadicLevel f a) (densityDyadicLevel f b) by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact h i j hlt
    · exact (h j i hgt).symm
  intro a b hab
  apply disjoint_left.mpr
  intro x hx hy
  have hp : (2 : ℝ≥0∞)^(a+1) ≤ (2 : ℝ≥0∞)^b :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  exact (not_lt_of_ge (hx.2.trans hp) hy.1)

theorem additiveDensity_kernelProfile_le_height (kernel : SmoothKernel)
    {M : ℝ} (hM : ∀ z, kernel.density z ≤ M) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) (z : ℝ) :
    additiveDensity μ (kernelProfile kernel r) z ≤ ENNReal.ofReal (M/r) := by
  have hp (x : ℝ) : kernelProfile kernel r (z-x) ≤ ENNReal.ofReal (M/r) := by
    have h := kernelProfile_le kernel hM r (z-x)
    rw [abs_of_pos (inv_pos.mpr hr), ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)] at h
    simpa only [div_eq_mul_inv,mul_comm] using h
  exact (lintegral_mono hp).trans_eq (by simp)

theorem exists_uniform_finite_density_levels (kernel : SmoothKernel) :
    ∃ M : ℝ, 0 < M ∧ ∀ r : ℝ, 0 < r → ∃ L : ℕ,
      (2 : ℝ)^L ≤ 2 * max 1 (M/r) ∧
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], ∀ z : ℝ,
      additiveDensity μ (kernelProfile kernel r) z ≤ (2 : ℝ≥0∞)^L := by
  obtain ⟨M,hM0,hM⟩ := kernel.exists_height
  refine ⟨M,hM0,?_⟩
  intro r hr
  obtain ⟨n,hnlo,hnhi⟩ := exists_nat_pow_near (le_max_left 1 (M/r))
    (by norm_num : (1 : ℝ) < 2)
  let L : ℕ := n+1
  refine ⟨L,?_,?_⟩
  · dsimp [L]
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_left hnlo (by norm_num)
  intro μ _ z
  have hreal : M/r ≤ (2 : ℝ)^L := (le_max_right 1 (M/r)).trans hnhi.le
  have hpow : ENNReal.ofReal ((2 : ℝ)^L) = (2 : ℝ≥0∞)^L := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num
  exact (additiveDensity_kernelProfile_le_height kernel hM μ hr z).trans
    ((ENNReal.ofReal_le_ofReal hreal).trans_eq hpow)

#print axioms densityLowLevel
#print axioms densityDyadicLevel
#print axioms measurableSet_densityLowLevel
#print axioms measurableSet_densityDyadicLevel
#print axioms exists_dyadic_level_of_le_pow
#print axioms density_levels_cover_of_height
#print axioms densityDyadicLevel_disjoint
#print axioms additiveDensity_kernelProfile_le_height
#print axioms exists_uniform_finite_density_levels
end OAI.Falconer
