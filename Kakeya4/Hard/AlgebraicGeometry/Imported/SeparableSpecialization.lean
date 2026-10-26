import Mathlib

/-!
SPDX-License-Identifier: Apache-2.0
`separable_map_of_leading_resultant_ne_zero` is extracted unchanged from
OpenAI math, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/Analysis/SymmetricDomains/GenericFinParameterPolynomial.lean.
The generic-resultant lemma is a local adapter of Mathlib's resultant_map_map
and resultant_ne_zero; no complex-geometric parameter machinery is imported.
-/

namespace OAI.Release061

theorem separable_map_of_leading_resultant_ne_zero
    {R K : Type*} [CommRing R] [Field K] (P : Polynomial R) (e : R →+* K)
    (hl : e P.leadingCoeff ≠ 0)
    (hd : e (P.resultant P.derivative) ≠ 0) : (P.map e).Separable := by
  by_cases hdeg : P.natDegree = 0
  · have hP : P = Polynomial.C P.leadingCoeff := by
      simpa only [Polynomial.leadingCoeff,hdeg] using Polynomial.eq_C_of_natDegree_eq_zero hdeg
    rw [hP,Polynomial.map_C]
    exact (Polynomial.separable_C _).mpr (isUnit_iff_ne_zero.mpr hl)
  · obtain ⟨a,b,_,_,hab⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
      P P.derivative le_rfl le_rfl (Or.inl hdeg)
    have hh := congrArg (Polynomial.map e) hab
    simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C] at hh
    refine ⟨Polynomial.C ((e (P.resultant P.derivative))⁻¹) * a.map e,
      Polynomial.C ((e (P.resultant P.derivative))⁻¹) * b.map e,?_⟩
    rw [Polynomial.derivative_map]
    calc
      _ = Polynomial.C ((e (P.resultant P.derivative))⁻¹) *
          (P.map e * a.map e + P.derivative.map e * b.map e) := by ring
      _ = 1 := by rw [hh,← Polynomial.C_mul,inv_mul_cancel₀ hd,Polynomial.C_1]

theorem resultant_derivative_ne_zero_of_generic_separable
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (P : Polynomial R)
    (hP : (P.map (algebraMap R K)).Separable) :
    P.resultant P.derivative ≠ 0 := by
  have hi := IsFractionRing.injective R K
  have hh := Polynomial.resultant_ne_zero _ _ ((Polynomial.separable_def _).mp hP)
  intro hz
  apply hh
  rw [Polynomial.derivative_map,
    Polynomial.natDegree_map_eq_of_injective hi,
    Polynomial.natDegree_map_eq_of_injective hi,
    Polynomial.resultant_map_map, hz, map_zero]

end OAI.Release061

