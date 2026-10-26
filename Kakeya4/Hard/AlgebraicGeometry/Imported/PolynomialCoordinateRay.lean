import Mathlib

/-!
SPDX-License-Identifier: Apache-2.0
Extracted unchanged from OpenAI math, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Source: lean/OAI/Combinatorics/ThinTrees/Barrier.lean.
Changes: retain ray, ray_eval, ray_derivative only, with Mathlib imports and original namespace.
-/

namespace OAI
universe uI uR uR2 uR3
noncomputable section
open Polynomial Finset Filter
namespace StrongThinTree.MSS
variable {I : Type uI} [DecidableEq I]

def ray {R : Type uR} [CommRing R] (p : MvPolynomial I R) (z : I → R) (i : I) : R[X] :=
  MvPolynomial.eval₂ Polynomial.C (fun j => Polynomial.C (z j)+if j=i then Polynomial.X else 0) p

lemma ray_eval {R : Type uR2} [CommRing R] (p : MvPolynomial I R) (z : I → R) (i : I) (t : R) :
    (ray p z i).eval t=MvPolynomial.eval (Function.update z i (z i+t)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [ray]
  | add p q hp hq => simpa [ray,MvPolynomial.eval₂_add] using congrArg₂ (·+·) hp hq
  | mul_X p j hp =>
    simp only [ray] at hp
    by_cases hji : j=i
    · subst j
      simp [ray,MvPolynomial.eval₂_mul,hp]
    · simp [ray,MvPolynomial.eval₂_mul,hji,hp]

lemma ray_derivative {R : Type uR3} [CommRing R] (p : MvPolynomial I R) (z : I → R) (i : I) :
    (ray p z i).derivative=ray (MvPolynomial.pderiv i p) z i := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [ray]
  | add p q hp hq =>
    simp only [ray] at hp hq
    simp [ray,MvPolynomial.eval₂_add,hp,hq]
  | mul_X p j hp =>
    simp only [ray] at hp
    rw [MvPolynomial.pderiv_mul]
    by_cases hji : j=i
    · subst j
      simp [ray,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_add,Polynomial.derivative_mul,hp]
    · simp [ray,MvPolynomial.eval₂_mul,Polynomial.derivative_mul,MvPolynomial.pderiv_X,hji,hp]

end StrongThinTree.MSS
end
end OAI

