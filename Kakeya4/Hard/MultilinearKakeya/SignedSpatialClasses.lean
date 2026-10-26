import Kakeya4.Hard.MultilinearKakeya.PolynomialSignMass
import Kakeya4.Hard.MultilinearKakeya.FiniteSignedClasses

/-! Actual polynomial sign bad sets on coefficient spheres. Finite same-colour
closed shape classes give separation from the closure of the antipodal bad set.
Empty regions are allowed, so shorter test lists can be padded faithfully. -/

noncomputable section
open Set MeasureTheory
open scoped Topology Pointwise

namespace Kakeya4.Hard.MultilinearKakeya

def sphereShapeClass {n m : ℕ} (B : Fin (m+1) → MvPolynomial (Fin n) ℝ)
    (ε : ℝ) (Q : Set (E n)) (T : E n ≃L[ℝ] E n) : Set (UnitSphere m) :=
  Subtype.val ⁻¹' coefficientShapeClass B ε Q T

theorem isClosed_sphereShapeClass {n m : ℕ} (B : Fin (m+1) → MvPolynomial (Fin n) ℝ)
    (ε : ℝ) {Q : Set (E n)} (hQ : IsCompact Q) (T : E n ≃L[ℝ] E n) :
    IsClosed (sphereShapeClass B ε Q T) :=
  (isClosed_coefficientShapeClass B ε hQ T).preimage continuous_subtype_val

theorem neg_mem_sphereShapeClass_iff {n m : ℕ} (B : Fin (m+1) → MvPolynomial (Fin n) ℝ)
    (ε : ℝ) (Q : Set (E n)) (T : E n ≃L[ℝ] E n) (u : UnitSphere m) :
    -u ∈ sphereShapeClass B ε Q T ↔ u ∈ sphereShapeClass B ε Q T :=
  neg_mem_coefficientShapeClass_iff B ε Q T u

def colouredSignBadSet {n m : ℕ} {ι γ : Type*}
    (B : Fin (m+1) → MvPolynomial (Fin n) ℝ) (ε : ℝ) (Q : Set (E n))
    (T : ι → E n ≃L[ℝ] E n) (colour : ι → γ) (A : ι → Set (E n)) (θ : γ) :
    Set (UnitSphere m) :=
  positiveClassUnion (fun i : {i : ι // colour i = θ} => sphereShapeClass B ε Q (T i.val))
    (fun i u => polynomialSignImbalance (coefficientPolynomial B u) (A i.val))

theorem disjoint_colouredSignBadSet_closure_neg {n m : ℕ} {ι γ : Type*} [Finite ι]
    (B : Fin (m+1) → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (ε : ℝ) {Q : Set (E n)} (hQ : IsCompact Q)
    (T : ι → E n ≃L[ℝ] E n) (colour : ι → γ) (A : ι → Set (E n))
    (hA : ∀ i, volume (A i) ≠ ⊤)
    (hd : ∀ i j, i ≠ j → colour i = colour j →
      Disjoint (coefficientShapeClass B ε Q (T i)) (coefficientShapeClass B ε Q (T j)))
    (θ : γ) :
    Disjoint (colouredSignBadSet B ε Q T colour A θ)
      (closure (-colouredSignBadSet B ε Q T colour A θ)) := by
  apply disjoint_positiveClassUnion_closure_neg
  · intro i
    exact isClosed_sphereShapeClass B ε hQ (T i.val)
  · intro i
    exact continuous_polynomialSignImbalance_sphere B hB (hA i.val)
  · intro i u
    exact neg_mem_sphereShapeClass_iff B ε Q (T i.val) u
  · intro i u
    change polynomialSignImbalance (coefficientPolynomial B (-(u : E (m+1)))) (A i.val) = _
    rw [coefficientPolynomial_neg, polynomialSignImbalance_neg]
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro u hi hj
    have hv : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    exact Set.disjoint_left.mp (hd i.val j.val hv (i.property.trans j.property.symm)) hi hj

theorem mem_colouredSignBadSet_or_neg_of_unbisected {n m : ℕ} {ι γ : Type*}
    (B : Fin (m+1) → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (ε : ℝ) (Q : Set (E n)) (T : ι → E n ≃L[ℝ] E n) (colour : ι → γ)
    (A : ι → Set (E n)) (i : ι) (hA : volume (A i) ≠ ⊤)
    (u : UnitSphere m) (hu : u ∈ sphereShapeClass B ε Q (T i))
    (hunbisected : ¬ polynomialBisects (coefficientPolynomial B u) (A i)) :
    u ∈ colouredSignBadSet B ε Q T colour A (colour i) ∨
      -u ∈ colouredSignBadSet B ε Q T colour A (colour i) := by
  have hs : polynomialSignImbalance (coefficientPolynomial B u) (A i) ≠ 0 :=
    fun hzero => hunbisected ((polynomialSignImbalance_eq_zero_iff_bisects _
      (coefficientPolynomial_sphere_ne_zero B hB u) hA).mp hzero)
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · right
    refine mem_iUnion.mpr ⟨⟨i,rfl⟩, (neg_mem_sphereShapeClass_iff B ε Q (T i) u).mpr hu, ?_⟩
    change 0 < polynomialSignImbalance (coefficientPolynomial B (-(u : E (m+1)))) (A i)
    rw [coefficientPolynomial_neg, polynomialSignImbalance_neg]
    linarith
  · left
    exact mem_iUnion.mpr ⟨⟨i,rfl⟩,hu,hpos⟩

end Kakeya4.Hard.MultilinearKakeya
