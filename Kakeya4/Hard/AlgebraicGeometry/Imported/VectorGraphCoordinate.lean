import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialSignSetProjection2

/-!
SPDX-License-Identifier: Apache-2.0
Extracted unchanged from OpenAI math, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/Analysis/SymmetricDomains/PolynomialSignSetVector.lean.
Changes: retain only the vector graph coordinate lemma and minimal import.
-/

noncomputable section
namespace OAI.Release061.SignElimination
open Set Metric
open scoped Classical

lemma polynomialSignSet_vector_graph_coordinate {X ι κ : Type*} [Finite κ]
    {c : X → ι → ℝ} {S : Set X} {f : X → κ → ℝ}
    (h : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.1 ∈ S ∧ z.2 = f z.1}) (j : κ) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.1 ∈ S ∧ z.2 = f z.1 j} := by
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  let e := fun z : (X × ℝ) × (κ → ℝ) => Sum.elim (d z.1) z.2
  have hh : PolynomialSignSet e {z | z.1.1 ∈ S ∧ z.2 = f z.1.1} :=
    h.coordinate_preimage (fun z : (X × ℝ) × (κ → ℝ) => (z.1.1,z.2)) (Sum.map some id)
      (by intro z i; cases i <;> rfl)
  have he : PolynomialSignSet e {z | z.1.2 = z.2 j} := by
    convert PolynomialSignSet.zero (c := e)
      (MvPolynomial.X (Sum.inl none)-MvPolynomial.X (Sum.inr j)) using 1
    ext z
    simp [e,d,sub_eq_zero]
  convert polynomialSignSet_projection_finite (hh.inter he) using 1
  ext z
  simp only [mem_ofPred_eq,mem_inter_iff]
  constructor
  · rintro ⟨hs,ht⟩
    exact ⟨f z.1,⟨hs,rfl⟩,ht⟩
  · rintro ⟨y,⟨hs,rfl⟩,ht⟩
    exact ⟨hs,ht⟩

end OAI.Release061.SignElimination
