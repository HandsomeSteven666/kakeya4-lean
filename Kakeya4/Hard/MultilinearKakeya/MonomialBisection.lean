import Kakeya4.Hard.MultilinearKakeya.PolynomialBisection

/-! An explicit tensor box of independent monomials supplies the polynomial
bisection space, with cardinality (d+1)^n and total degree at most n*d. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

def exponentBoxEmbedding (n d : ℕ) : (Fin n → Fin (d+1)) ↪ (Fin n →₀ ℕ) where
  toFun v := Finsupp.equivFunOnFinite.symm (fun i => (v i).val)
  inj' := by
    intro v w h
    funext i
    apply Fin.ext
    exact congrArg (fun s : Fin n →₀ ℕ => s i) h

theorem totalDegree_box_monomial_le (n d : ℕ) (v : Fin n → Fin (d+1)) :
    (MvPolynomial.monomial (exponentBoxEmbedding n d v) (1 : ℝ)).totalDegree ≤ n*d := by
  rw [MvPolynomial.totalDegree_monomial _ one_ne_zero,
    Finsupp.sum_fintype _ _ (fun _ => rfl)]
  change (∑ i : Fin n, (v i).val) ≤ n*d
  calc
    _ ≤ ∑ _i : Fin n, d := Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (v i).isLt)
    _ = _ := by simp

theorem exists_polynomial_bisection_of_card_le {n m d : ℕ}
    (hcard : m+1 ≤ (d+1)^n)
    (μ : Fin m → Measure (Fin n → ℝ)) (hfin : ∀ i, IsFiniteMeasure (μ i))
    (hac : ∀ i, μ i ≪ volume) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ P.totalDegree ≤ n*d ∧ ∀ i,
      μ i {x | MvPolynomial.eval x P ≤ 0} = μ i univ / 2 ∧
      μ i {x | 0 ≤ MvPolynomial.eval x P} = μ i univ / 2 := by
  have hle : Fintype.card (Fin (m+1)) ≤ Fintype.card (Fin n → Fin (d+1)) := by
    simpa using hcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
  let f : Fin (m+1) ↪ (Fin n →₀ ℕ) := e.trans (exponentBoxEmbedding n d)
  let B : Fin (m+1) → MvPolynomial (Fin n) ℝ := fun i => MvPolynomial.basisMonomials _ _ (f i)
  have hB : LinearIndependent ℝ B :=
    (MvPolynomial.basisMonomials (Fin n) ℝ).linearIndependent.comp f f.injective
  have hD (i : Fin (m+1)) : (B i).totalDegree ≤ n*d :=
    totalDegree_box_monomial_le n d (e i)
  exact exists_polynomial_bisection_degree_le B hB hD μ hfin hac

/-- Any m absolutely continuous finite measures admit a nonzero simultaneous
bisector of degree at most n times the integer n-th root of m. -/
theorem exists_polynomial_bisection_nthRoot {n m : ℕ} (hn : 0 < n)
    (μ : Fin m → Measure (Fin n → ℝ)) (hfin : ∀ i, IsFiniteMeasure (μ i))
    (hac : ∀ i, μ i ≪ volume) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ P.totalDegree ≤ n * Nat.nthRoot n m ∧ ∀ i,
      μ i {x | MvPolynomial.eval x P ≤ 0} = μ i univ / 2 ∧
      μ i {x | 0 ≤ MvPolynomial.eval x P} = μ i univ / 2 :=
  exists_polynomial_bisection_of_card_le (Nat.lt_pow_nthRoot_add_one hn.ne' m) μ hfin hac

theorem cast_nthRoot_le_rpow {n : ℕ} (hn : 0 < n) (m : ℕ) :
    (Nat.nthRoot n m : ℝ) ≤ (m : ℝ)^((n : ℝ)⁻¹) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (Nat.nthRoot n m : ℝ)^n ≤ (m : ℝ) := by
    exact_mod_cast Nat.pow_nthRoot_le (n := n) (a := m) (Or.inl hn.ne')
  have h := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg _) _) hpow (inv_nonneg.mpr hnR.le)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
    mul_inv_cancel₀ hnR.ne', Real.rpow_one] at h
  exact h

/-- The degree has the quantitative O_n(m^(1/n)) bound needed in the polynomial
method, with an explicit dimension constant n. -/
theorem exists_polynomial_bisection_quantitative {n m : ℕ} (hn : 0 < n)
    (μ : Fin m → Measure (Fin n → ℝ)) (hfin : ∀ i, IsFiniteMeasure (μ i))
    (hac : ∀ i, μ i ≪ volume) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧
      (P.totalDegree : ℝ) ≤ (n : ℝ)*(m : ℝ)^((n : ℝ)⁻¹) ∧ ∀ i,
      μ i {x | MvPolynomial.eval x P ≤ 0} = μ i univ / 2 ∧
      μ i {x | 0 ≤ MvPolynomial.eval x P} = μ i univ / 2 := by
  obtain ⟨P,hP,hD,hbisect⟩ := exists_polynomial_bisection_nthRoot hn μ hfin hac
  refine ⟨P,hP,?_,hbisect⟩
  calc
    (P.totalDegree : ℝ) ≤ (n : ℝ)*(Nat.nthRoot n m : ℝ) := by exact_mod_cast hD
    _ ≤ _ := by gcongr; exact cast_nthRoot_le_rpow hn m

/-- The finite-volume sets actually used for spatial polynomial bisection.
The restricted measures and their absolute continuity are constructed here. -/
theorem exists_polynomial_bisection_regions {n m : ℕ} (hn : 0 < n)
    (A : Fin m → Set (Fin n → ℝ)) (hA : ∀ i, volume (A i) < ⊤) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧
      (P.totalDegree : ℝ) ≤ (n : ℝ)*(m : ℝ)^((n : ℝ)⁻¹) ∧ ∀ i,
      volume (A i ∩ {x | MvPolynomial.eval x P ≤ 0}) = volume (A i) / 2 ∧
      volume (A i ∩ {x | 0 ≤ MvPolynomial.eval x P}) = volume (A i) / 2 := by
  let μ : Fin m → Measure (Fin n → ℝ) := fun i => volume.restrict (A i)
  have hfin (i : Fin m) : IsFiniteMeasure (μ i) := isFiniteMeasure_restrict.mpr (hA i).ne
  have hac (i : Fin m) : μ i ≪ volume := Measure.absolutelyContinuous_restrict
  obtain ⟨P,hP,hD,hbisect⟩ := exists_polynomial_bisection_quantitative hn μ hfin hac
  refine ⟨P,hP,hD,fun i => ?_⟩
  obtain ⟨hneg,hpos⟩ := hbisect i
  have hnegM : MeasurableSet {x | MvPolynomial.eval x P ≤ 0} :=
    (isClosed_le (MvPolynomial.continuous_eval P) continuous_const).measurableSet
  have hposM : MeasurableSet {x | 0 ≤ MvPolynomial.eval x P} :=
    (isClosed_le continuous_const (MvPolynomial.continuous_eval P)).measurableSet
  dsimp [μ] at hneg hpos
  rw [Measure.restrict_apply hnegM, Measure.restrict_apply_univ, inter_comm] at hneg
  rw [Measure.restrict_apply hposM, Measure.restrict_apply_univ, inter_comm] at hpos
  exact ⟨hneg,hpos⟩

theorem exists_polynomial_bisection_bounded_regions {n m : ℕ} (hn : 0 < n)
    (A : Fin m → Set (Fin n → ℝ)) (hA : ∀ i, Bornology.IsBounded (A i)) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧
      (P.totalDegree : ℝ) ≤ (n : ℝ)*(m : ℝ)^((n : ℝ)⁻¹) ∧ ∀ i,
      volume (A i ∩ {x | MvPolynomial.eval x P ≤ 0}) = volume (A i) / 2 ∧
      volume (A i ∩ {x | 0 ≤ MvPolynomial.eval x P}) = volume (A i) / 2 :=
  exists_polynomial_bisection_regions hn A (fun i => (hA i).measure_lt_top)

end Kakeya4.Hard.MultilinearKakeya
