import Kakeya4.Hard.AlgebraicGeometry.SelectorFamily

/-! Polynomial tests and real quantifiers for the geometric eligibility formula. -/

noncomputable section
open Set
open scoped Classical
open OAI.Release061 OAI.Release061.SignElimination

namespace Kakeya4.Hard

theorem polynomialSignSet_eval_le {X ι : Type*} (c : X → ι → ℝ)
    (p q : MvPolynomial ι ℝ) :
    PolynomialSignSet c {x | MvPolynomial.eval (c x) p ≤ MvPolynomial.eval (c x) q} := by
  convert (PolynomialSignSet.positive (c := c) (p-q)).compl using 1
  ext x
  simp only [mem_ofPred_eq, mem_compl_iff, map_sub, sub_pos, not_lt]

theorem polynomialSignSet_abs_eval_le {X ι : Type*} (c : X → ι → ℝ)
    (p q : MvPolynomial ι ℝ) :
    PolynomialSignSet c {x | |MvPolynomial.eval (c x) p| ≤ MvPolynomial.eval (c x) q} := by
  have hp := polynomialSignSet_eval_le c p q
  have hn := polynomialSignSet_eval_le c (-p) q
  convert hp.inter hn using 1
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, map_neg]
  constructor
  · intro h
    have hh := abs_le.mp h
    constructor <;> linarith
  · rintro ⟨h₁,h₂⟩
    apply abs_le.mpr
    constructor <;> linarith

theorem polynomialSignSet_forall_real {X ι : Type*} {c : X → ι → ℝ}
    {A : Set (X × ℝ)}
    (hA : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) A) :
    PolynomialSignSet c {x | ∀ t : ℝ, (x,t) ∈ A} := by
  have hh := (polynomialSignSet_projection_one hA.compl).compl
  convert hh using 1
  ext x
  simp only [mem_compl_iff, mem_ofPred_eq, not_exists, not_not]

theorem polynomialSignSet_eval_le_abs {X ι : Type*} (c : X → ι → ℝ)
    (p q : MvPolynomial ι ℝ) :
    PolynomialSignSet c {x | MvPolynomial.eval (c x) q ≤ |MvPolynomial.eval (c x) p|} := by
  convert (polynomialSignSet_eval_le c q p).union
    (polynomialSignSet_eval_le c q (-p)) using 1
  ext x
  simp only [mem_ofPred_eq, mem_union, map_neg]
  rcases le_total 0 (MvPolynomial.eval (c x) p) with h | h
  · rw [abs_of_nonneg h]
    constructor
    · exact Or.inl
    · rintro (hp | hn)
      · exact hp
      · linarith
  · rw [abs_of_nonpos h]
    constructor
    · exact Or.inr
    · rintro (hp | hn)
      · linarith
      · exact hn

end Kakeya4.Hard
