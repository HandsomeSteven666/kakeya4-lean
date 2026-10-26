import Kakeya4.Hard.MultilinearKakeya.SignedSpatialClasses

/-! Common test indices for differently sized finite spatial packings.
Missing slots are the empty region and hence have zero sign imbalance. -/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace Kakeya4.Hard.MultilinearKakeya

def paddedSpatialTest {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    (s : Finset (E n)) (r : ℝ) (j : ℕ) : Set (E n) :=
  if hj : j < s.card then spatialTestCell L ((s.equivFin).symm ⟨j,hj⟩).val r else ∅

theorem paddedSpatialTest_eq_empty {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    (s : Finset (E n)) (r : ℝ) {j : ℕ} (hj : s.card ≤ j) :
    paddedSpatialTest L s r j = ∅ := by simp only [paddedSpatialTest, dif_neg (not_lt.mpr hj)]

theorem volume_paddedSpatialTest_ne_top {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    (s : Finset (E n)) (r : ℝ) (j : ℕ) : volume (paddedSpatialTest L s r j) ≠ ⊤ := by
  unfold paddedSpatialTest
  split_ifs
  · exact volume_spatialTestCell_ne_top _ _ _
  · simp

theorem exists_paddedSpatialTest_eq {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] E n)
    (s : Finset (E n)) (r : ℝ) (c : E n) (hc : c ∈ s) :
    ∃ j < s.card, paddedSpatialTest L s r j = spatialTestCell L c r := by
  let j := s.equivFin ⟨c,hc⟩
  refine ⟨j.val,j.isLt,?_⟩
  simp only [paddedSpatialTest,dif_pos j.isLt]
  change spatialTestCell L ((s.equivFin).symm (s.equivFin ⟨c,hc⟩)).val r = _
  rw [Equiv.symm_apply_apply]

theorem polynomialSignImbalance_empty {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    polynomialSignImbalance P ∅ = 0 := by simp [polynomialSignImbalance]

def spatialTestIndexBound {n : ℕ} {ι : Type*} [Fintype ι] (s : ι → Finset (E n)) : ℕ :=
  Finset.univ.sup (fun i => (s i).card)

theorem card_le_spatialTestIndexBound {n : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Finset (E n)) (i : ι) : (s i).card ≤ spatialTestIndexBound s := by
  exact Finset.le_sup (f := fun i => (s i).card) (Finset.mem_univ i)

theorem spatialTestIndexBound_le {n : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Finset (E n)) {N : ℕ} (hN : ∀ i, (s i).card ≤ N) :
    spatialTestIndexBound s ≤ N := Finset.sup_le (fun i _ => hN i)

theorem exists_fin_paddedSpatialTest_eq {n : ℕ} {ι : Type*} [Fintype ι]
    (L : ι → (Fin n → ℝ) ≃L[ℝ] E n) (s : ι → Finset (E n)) (r : ℝ)
    (i : ι) (c : E n) (hc : c ∈ s i) :
    ∃ j : Fin (spatialTestIndexBound s), paddedSpatialTest (L i) (s i) r j.val = spatialTestCell (L i) c r := by
  obtain ⟨j,hj,he⟩ := exists_paddedSpatialTest_eq (L i) (s i) r c hc
  exact ⟨⟨j,hj.trans_le (card_le_spatialTestIndexBound s i)⟩,he⟩

end Kakeya4.Hard.MultilinearKakeya
