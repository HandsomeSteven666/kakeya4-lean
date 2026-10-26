import Mathlib

/-!
SPDX-License-Identifier: Apache-2.0
Extracted unchanged from OpenAI math, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Sources:
* lean/OAI/NumberTheory/PowerFree/Jacobians.lean (pderiv_totalDegree_lt)
* lean/OAI/AlgebraicGeometry/PlaneCurves/BinaryForms.lean (natDegree_eval₂_le_totalDegree)
Changes: retain only these two degree lemmas with Mathlib imports and original namespaces.
-/

open scoped BigOperators
namespace OAI.QuarticPowerFree
theorem pderiv_totalDegree_lt {σ K : Type*} [CommSemiring K]
    (i : σ) (p : MvPolynomial σ K) (h : MvPolynomial.pderiv i p ≠ 0) :
    (MvPolynomial.pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hs : ∀ m ∈ (MvPolynomial.pderiv i p).support,
      m.sum (fun _ e => e) < p.totalDegree := by
    intro m hm
    have hc := MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv] at hc
    have hp : m + Finsupp.single i 1 ∈ p.support :=
      MvPolynomial.mem_support_iff.mpr (fun he => hc (by rw [he, zero_mul]))
    have hh := MvPolynomial.le_totalDegree hp
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index (by rfl)] at hh
    exact hh
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr h
  have hpos : 0 < p.totalDegree := (Nat.zero_le _).trans_lt (hs m hm)
  exact (Finset.sup_lt_iff hpos).mpr hs

end OAI.QuarticPowerFree

namespace OAI.Nagata.W02
theorem natDegree_eval₂_le_totalDegree {σ K : Type*} [CommSemiring K]
    (P : MvPolynomial σ K) (f : σ → Polynomial K)
    (hf : ∀ i, (f i).natDegree ≤ 1) :
    (P.eval₂ Polynomial.C f).natDegree ≤ P.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  calc
    (Polynomial.C (P.coeff d) * ∏ i ∈ d.support, f i ^ d i).natDegree ≤
        (Polynomial.C (P.coeff d)).natDegree +
          (∏ i ∈ d.support, f i ^ d i).natDegree := Polynomial.natDegree_mul_le
    _ = (∏ i ∈ d.support, f i ^ d i).natDegree := by simp
    _ ≤ ∑ i ∈ d.support, (f i ^ d i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      simpa using Polynomial.natDegree_pow_le_of_le (d i) (hf i)
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hd

end OAI.Nagata.W02

