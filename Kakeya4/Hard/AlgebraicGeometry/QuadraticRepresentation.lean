import Kakeya4.Hard.AlgebraicGeometry.QuadraticPolynomial

/-! The fixed finite coefficient family represents every real polynomial of total degree ≤ 2. -/

noncomputable section
open Set
open scoped Classical BigOperators

namespace Kakeya4.Hard.EligibleFormula

theorem exponent_injective : Function.Injective exponent := by
  intro a b h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrArg (fun d : Fin 4 →₀ ℕ => d i) h

theorem exists_exponent_of_degree_le (d : Fin 4 →₀ ℕ)
    (hd : ∑ i : Fin 4, d i ≤ 2) : ∃ a : QuadraticExponent, exponent a = d := by
  have hi (i : Fin 4) : d i < 3 := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
      Nat.zero_le (d j)) (Finset.mem_univ i)
    omega
  let a : QuadraticExponent := ⟨fun i => ⟨d i,hi i⟩,hd⟩
  exact ⟨a,by ext i; rfl⟩

def withQuadratic (p : Parameters) (Q : MvPolynomial (Fin 4) ℝ) : Parameters :=
  fun i => match i with
    | .quadratic a => Q.coeff (exponent a)
    | i => p i

/-- Inserting coefficients does not restrict the other chart parameters. -/
theorem quadraticPolynomial_withQuadratic (p : Parameters) (Q : MvPolynomial (Fin 4) ℝ)
    (hQ : Q.totalDegree ≤ 2) : quadraticPolynomial (withQuadratic p Q) = Q := by
  let E : Finset (Fin 4 →₀ ℕ) := Finset.univ.image exponent
  have hsub : Q.support ⊆ E := by
    intro d hd
    have hdeg := (MvPolynomial.le_totalDegree hd).trans hQ
    have hdeg' : ∑ i : Fin 4, d i ≤ 2 := by
      change d.sum (fun _ e => e) ≤ 2 at hdeg
      rw [Finsupp.sum_fintype _ _ (by intro; rfl)] at hdeg
      exact hdeg
    obtain ⟨a,ha⟩ := exists_exponent_of_degree_le d hdeg'
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,ha⟩
  change (∑ a : QuadraticExponent, MvPolynomial.monomial (exponent a)
    (Q.coeff (exponent a))) = Q
  calc
    _ = ∑ d ∈ E, MvPolynomial.monomial d (Q.coeff d) := by
      dsimp only [E]
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => exponent_injective h
    _ = ∑ d ∈ Q.support, MvPolynomial.monomial d (Q.coeff d) :=
      (Finset.sum_subset hsub (fun d _ hn => by
        rw [MvPolynomial.notMem_support_iff.mp hn, MvPolynomial.monomial_zero])).symm
    _ = Q := Q.as_sum.symm

theorem eval_test_withQuadratic (p : Parameters) (Q : MvPolynomial (Fin 4) ℝ)
    (hQ : Q.totalDegree ≤ 2) (b s : Point) (t : ℝ) :
    MvPolynomial.eval (timedCoordinates (((withQuadratic p Q,s),b),t)) test =
      MvPolynomial.eval (lineCoordinates b s t) Q := by
  rw [eval_test_eq,quadraticPolynomial_withQuadratic p Q hQ]

theorem eval_derivativeW_withQuadratic (p : Parameters) (Q : MvPolynomial (Fin 4) ℝ)
    (hQ : Q.totalDegree ≤ 2) (b s : Point) (t : ℝ) :
    MvPolynomial.eval (timedCoordinates (((withQuadratic p Q,s),b),t)) derivativeW =
      MvPolynomial.eval (lineCoordinates b s t) (MvPolynomial.pderiv 3 Q) := by
  rw [eval_derivativeW_eq,quadraticPolynomial_withQuadratic p Q hQ]

end Kakeya4.Hard.EligibleFormula
