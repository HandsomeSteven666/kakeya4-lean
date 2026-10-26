import Kakeya4.Hard.MultilinearKakeya.SpatialSignCover
import Kakeya4.Hard.MultilinearKakeya.SpatialTestVolume

/-! A lower ellipsoid-volume cutoff bounds the common test index directly.
Antipodal covering then forces a coefficient with small actual visibility body.
All shape, test and energy hypotheses refer to the previously constructed objects. -/

noncomputable section
open Set MeasureTheory
open scoped Topology Pointwise BigOperators

namespace Kakeya4.Hard.MultilinearKakeya

theorem exists_small_visibilityBody_of_actual_tests {n m C : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι]
    (B : Fin (m+1) → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (ε : ℝ) {Q : Set (E n)} (hQ : IsCompact Q)
    (T : ι → E n ≃L[ℝ] E n) (colour : ι → Fin C) (tests : ι → Finset (E n))
    (hd : ∀ i j, i ≠ j → colour i = colour j →
      Disjoint (coefficientShapeClass B ε Q (T i)) (coefficientShapeClass B ε Q (T j)))
    (hcover : (⋃ i, coefficientShapeClass B ε Q (T i)) = univ)
    (hnot : ∀ u : UnitSphere m, ∀ i, u ∈ sphereShapeClass B ε Q (T i) →
      ∃ c ∈ tests i, ¬ polynomialBisects (coefficientPolynomial B u)
        (spatialTestCell (chartOfShape (T i)) c (spatialTestScale n)))
    {ρ V : ℝ} (hρ : 0 < ρ)
    (hupper : ∀ i, ((tests i).card : ℝ) *
      (volume (spatialTestCell (chartOfShape (T i)) 0 (spatialTestScale n))).toReal ≤ V)
    (hbudget : ⌈V/(spatialTestVolumeFactor n*ρ)⌉₊ * C ≤ m) :
    ∃ u : UnitSphere m,
      (volume (visibilityBody (smoothDirectionalSeminorm (coefficientPolynomial B u) ε Q hQ))).toReal <
        (2*Real.sqrt n)^n * ρ := by
  classical
  let I := {i : ι // ρ ≤ (volume (T i '' Metric.closedBall 0 1)).toReal}
  let TI : I → E n ≃L[ℝ] E n := fun i => T i.val
  let colI : I → Fin C := fun i => colour i.val
  let testsI : I → Finset (E n) := fun i => tests i.val
  have hdI (i j : I) (hij : i ≠ j) (hc : colI i = colI j) :
      Disjoint (coefficientShapeClass B ε Q (TI i)) (coefficientShapeClass B ε Q (TI j)) :=
    hd i.val j.val (fun h => hij (Subtype.ext h)) hc
  have hcard (i : I) : (testsI i).card ≤ ⌈V/(spatialTestVolumeFactor n*ρ)⌉₊ := by
    exact_mod_cast (le_trans
      (spatialTest_card_le_of_ellipsoid_volume_lower (T i.val) (tests i.val) hρ i.property (hupper i.val))
      (Nat.le_ceil _))
  have hN : spatialTestIndexBound testsI ≤ ⌈V/(spatialTestVolumeFactor n*ρ)⌉₊ :=
    spatialTestIndexBound_le testsI hcard
  have htotal : spatialTestIndexBound testsI * C ≤ m :=
    (Nat.mul_le_mul_right C hN).trans hbudget
  let A : Fin (spatialTestIndexBound testsI * C) → Set (UnitSphere m) := fun i =>
    let pair := finProdFinEquiv.symm i
    spatialSignBadSet B ε Q TI colI testsI pair.1.val pair.2
  have hsep (i : Fin (spatialTestIndexBound testsI * C)) : Disjoint (A i) (closure (-A i)) :=
    disjoint_spatialSignBadSet_closure_neg B hB ε hQ TI colI testsI hdI _ _
  obtain ⟨u,hu⟩ := exists_antipodally_uncovered_of_card_le htotal A hsep
  refine ⟨u,?_⟩
  by_contra hlarge
  have hlarge' : (2*Real.sqrt n)^n * ρ ≤
      (volume (visibilityBody (smoothDirectionalSeminorm (coefficientPolynomial B u) ε Q hQ))).toReal :=
    le_of_not_gt hlarge
  have huc : (u : E (m+1)) ∈ ⋃ i, coefficientShapeClass B ε Q (T i) := by rw [hcover]; trivial
  obtain ⟨i,hi⟩ := mem_iUnion.mp huc
  have hclass := (mem_coefficientShapeClass_iff B ε hQ (T i) u).mp hi
  have hvol := visibilityBody_realVolume_le_of_bodyShapeComparison _ (T i) hclass
  have hfactor : 0 < (2*Real.sqrt n)^n := by
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have himem : ρ ≤ (volume (T i '' Metric.closedBall 0 1)).toReal := by nlinarith
  let iI : I := ⟨i,himem⟩
  obtain ⟨c,hc,hnobisect⟩ := hnot u i hi
  obtain ⟨j,he⟩ := exists_fin_paddedSpatialTest_eq (fun i => chartOfShape (TI i)) testsI
    (spatialTestScale n) iI c hc
  have hs := mem_colouredSignBadSet_or_neg_of_unbisected B hB ε Q TI colI
    (fun i => paddedSpatialTest (chartOfShape (TI i)) (testsI i) (spatialTestScale n) j.val)
    iI (volume_paddedSpatialTest_ne_top _ _ _ _) u hi (by rwa [he])
  have hu' := hu (finProdFinEquiv (j,colI iI))
  have heq : A (finProdFinEquiv (j,colI iI)) = spatialSignBadSet B ε Q TI colI testsI j.val (colI iI) := by
    simp only [A,Equiv.symm_apply_apply]
  rw [heq] at hu'
  exact hs.elim hu'.1 hu'.2

theorem exists_small_visibilityBodies_of_actual_tests {n m C : ℕ} (hn : 0 < n)
    {κ : Type*} [Fintype κ] {ι : κ → Type*} [∀ q, Fintype (ι q)]
    (B : Fin (m+1) → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (ε : ℝ) (Q : κ → Set (E n)) (hQ : ∀ q, IsCompact (Q q))
    (T : ∀ q, ι q → E n ≃L[ℝ] E n) (colour : ∀ q, ι q → Fin C)
    (tests : ∀ q, ι q → Finset (E n))
    (hd : ∀ q i j, i ≠ j → colour q i = colour q j →
      Disjoint (coefficientShapeClass B ε (Q q) (T q i)) (coefficientShapeClass B ε (Q q) (T q j)))
    (hcover : ∀ q, (⋃ i, coefficientShapeClass B ε (Q q) (T q i)) = univ)
    (hnot : ∀ u : UnitSphere m, ∀ q i, u ∈ sphereShapeClass B ε (Q q) (T q i) →
      ∃ c ∈ tests q i, ¬ polynomialBisects (coefficientPolynomial B u)
        (spatialTestCell (chartOfShape (T q i)) c (spatialTestScale n)))
    (ρ V : κ → ℝ) (hρ : ∀ q, 0 < ρ q)
    (hupper : ∀ q i, ((tests q i).card : ℝ) *
      (volume (spatialTestCell (chartOfShape (T q i)) 0 (spatialTestScale n))).toReal ≤ V q)
    (hbudget : ∑ q, ⌈V q/(spatialTestVolumeFactor n*ρ q)⌉₊ * C ≤ m) :
    ∃ u : UnitSphere m, ∀ q,
      (volume (visibilityBody (smoothDirectionalSeminorm (coefficientPolynomial B u) ε (Q q) (hQ q)))).toReal <
        (2*Real.sqrt n)^n * ρ q := by
  classical
  let I (q : κ) := {i : ι q // ρ q ≤ (volume (T q i '' Metric.closedBall 0 1)).toReal}
  let TI (q : κ) : I q → E n ≃L[ℝ] E n := fun i => T q i.val
  let colI (q : κ) : I q → Fin C := fun i => colour q i.val
  let testsI (q : κ) : I q → Finset (E n) := fun i => tests q i.val
  let N (q : κ) := spatialTestIndexBound (testsI q)
  have hdI (q : κ) (i j : I q) (hij : i ≠ j) (hc : colI q i = colI q j) :
      Disjoint (coefficientShapeClass B ε (Q q) (TI q i)) (coefficientShapeClass B ε (Q q) (TI q j)) :=
    hd q i.val j.val (fun h => hij (Subtype.ext h)) hc
  have hN (q : κ) : N q ≤ ⌈V q/(spatialTestVolumeFactor n*ρ q)⌉₊ := by
    apply spatialTestIndexBound_le
    intro i
    exact_mod_cast (le_trans
      (spatialTest_card_le_of_ellipsoid_volume_lower (T q i.val) (tests q i.val) (hρ q) i.property (hupper q i.val))
      (Nat.le_ceil _))
  let J := Σ q : κ, Fin (N q * C)
  have htotal : Fintype.card J ≤ m := by
    calc
      _ = ∑ q, N q * C := by simp [J]
      _ ≤ ∑ q, ⌈V q/(spatialTestVolumeFactor n*ρ q)⌉₊ * C :=
        Finset.sum_le_sum (fun q _ => Nat.mul_le_mul_right C (hN q))
      _ ≤ m := hbudget
  let Araw (i : J) : Set (UnitSphere m) :=
    let pair := finProdFinEquiv.symm i.2
    spatialSignBadSet B ε (Q i.1) (TI i.1) (colI i.1) (testsI i.1) pair.1.val pair.2
  let A : Fin (Fintype.card J) → Set (UnitSphere m) := fun i => Araw ((Fintype.equivFin J).symm i)
  have hsep (i : Fin (Fintype.card J)) : Disjoint (A i) (closure (-A i)) :=
    disjoint_spatialSignBadSet_closure_neg B hB ε (hQ _) _ _ _ (hdI _) _ _
  obtain ⟨u,hu⟩ := exists_antipodally_uncovered_of_card_le htotal A hsep
  refine ⟨u,fun q => ?_⟩
  by_contra hlarge
  have hlarge' : (2*Real.sqrt n)^n * ρ q ≤
      (volume (visibilityBody (smoothDirectionalSeminorm (coefficientPolynomial B u) ε (Q q) (hQ q)))).toReal :=
    le_of_not_gt hlarge
  have huc : (u : E (m+1)) ∈ ⋃ i, coefficientShapeClass B ε (Q q) (T q i) := by rw [hcover q]; trivial
  obtain ⟨i,hi⟩ := mem_iUnion.mp huc
  have hclass := (mem_coefficientShapeClass_iff B ε (hQ q) (T q i) u).mp hi
  have hvol := visibilityBody_realVolume_le_of_bodyShapeComparison _ (T q i) hclass
  have hfactor : 0 < (2*Real.sqrt n)^n := by
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have himem : ρ q ≤ (volume (T q i '' Metric.closedBall 0 1)).toReal := by nlinarith
  let iI : I q := ⟨i,himem⟩
  obtain ⟨c,hc,hnobisect⟩ := hnot u q i hi
  obtain ⟨j,he⟩ := exists_fin_paddedSpatialTest_eq (fun i => chartOfShape (TI q i)) (testsI q)
    (spatialTestScale n) iI c hc
  have hs := mem_colouredSignBadSet_or_neg_of_unbisected B hB ε (Q q) (TI q) (colI q)
    (fun i => paddedSpatialTest (chartOfShape (TI q i)) (testsI q i) (spatialTestScale n) j.val)
    iI (volume_paddedSpatialTest_ne_top _ _ _ _) u hi (by rwa [he])
  let ji : J := ⟨q,finProdFinEquiv (j,colI q iI)⟩
  have hu' := hu (Fintype.equivFin J ji)
  have heq : A (Fintype.equivFin J ji) =
      spatialSignBadSet B ε (Q q) (TI q) (colI q) (testsI q) j.val (colI q iI) := by
    change Araw ((Fintype.equivFin J).symm ((Fintype.equivFin J) ji)) = _
    rw [(Fintype.equivFin J).symm_apply_apply]
    change (let pair := finProdFinEquiv.symm (finProdFinEquiv (j,colI q iI));
      spatialSignBadSet B ε (Q q) (TI q) (colI q) (testsI q) pair.1.val pair.2) = _
    rw [Equiv.symm_apply_apply]
  rw [heq] at hu'
  exact hs.elim hu'.1 hu'.2

end Kakeya4.Hard.MultilinearKakeya
