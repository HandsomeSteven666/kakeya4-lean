import Kakeya4.Hard.MultilinearKakeya.TopologicalInput

/-! The closed-cover form of Borsuk-Ulam used in CV's polynomial visibility
argument: n+1 closed sets covering S^n cannot all avoid antipodal pairs. -/

noncomputable section
open Set
open scoped Topology Pointwise

namespace Kakeya4.Hard.MultilinearKakeya

abbrev UnitSphere (n : ℕ) := Metric.sphere (0 : E (n+1)) 1

def signedCoverDistance {n : ℕ} (F : Fin (n+1) → Set (UnitSphere n))
    (i : Fin (n+1)) (x : UnitSphere n) : ℝ :=
  Metric.infDist x (F i) - Metric.infDist (-x) (F i)

theorem signedCoverDistance_neg {n : ℕ} (F : Fin (n+1) → Set (UnitSphere n))
    (i : Fin (n+1)) (x : UnitSphere n) :
    signedCoverDistance F i (-x) = -signedCoverDistance F i x := by
  simp only [signedCoverDistance, neg_neg]
  ring

theorem continuous_signedCoverDistance {n : ℕ} (F : Fin (n+1) → Set (UnitSphere n))
    (i : Fin (n+1)) : Continuous (signedCoverDistance F i) := by
  unfold signedCoverDistance
  apply (Metric.continuous_infDist_pt _).sub
  exact (Metric.continuous_infDist_pt _).comp continuous_neg

theorem exists_antipodal_pair_of_closed_cover {n : ℕ}
    (F : Fin (n+1) → Set (UnitSphere n)) (hclosed : ∀ i, IsClosed (F i))
    (hcover : ∀ x, ∃ i, x ∈ F i) :
    ∃ i, ∃ x : UnitSphere n, x ∈ F i ∧ -x ∈ F i := by
  let f : UnitSphere n → E n := fun x => WithLp.toLp 2
    (fun i : Fin n => signedCoverDistance F i.succ x - signedCoverDistance F 0 x)
  have hf : Continuous f := by
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi (fun i => (continuous_signedCoverDistance F i.succ).sub
      (continuous_signedCoverDistance F 0))
  have hodd (x : UnitSphere n) : f (-x) = -f x := by
    ext i
    change signedCoverDistance F i.succ (-x) - signedCoverDistance F 0 (-x) =
      -(signedCoverDistance F i.succ x - signedCoverDistance F 0 x)
    rw [signedCoverDistance_neg, signedCoverDistance_neg]
    ring
  obtain ⟨x,hx⟩ := odd_sphere_map_has_zero f hf hodd
  have heq (i : Fin (n+1)) : signedCoverDistance F i x = signedCoverDistance F 0 x := by
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
      have hj := congrArg (fun z : E n => z j) hx
      change signedCoverDistance F j.succ x - signedCoverDistance F 0 x = 0 at hj
      exact sub_eq_zero.mp hj
  obtain ⟨i,hi⟩ := hcover x
  obtain ⟨j,hj⟩ := hcover (-x)
  have hle : signedCoverDistance F i x ≤ 0 := by
    unfold signedCoverDistance
    rw [Metric.infDist_zero_of_mem hi]
    linarith [Metric.infDist_nonneg (x := -x) (s := F i)]
  have hge : 0 ≤ signedCoverDistance F j x := by
    unfold signedCoverDistance
    rw [Metric.infDist_zero_of_mem hj]
    linarith [Metric.infDist_nonneg (x := x) (s := F j)]
  have hzero : signedCoverDistance F i x = 0 := by
    rw [heq i] at hle ⊢
    rw [heq j] at hge
    exact le_antisymm hle hge
  have hdist : Metric.infDist (-x) (F i) = 0 := by
    unfold signedCoverDistance at hzero
    rw [Metric.infDist_zero_of_mem hi] at hzero
    linarith
  have hmem : -x ∈ F i := ((hclosed i).mem_iff_infDist_zero ⟨x,hi⟩).mpr hdist
  exact ⟨i,x,hi,hmem⟩

theorem exists_uncovered_of_antipodal_free {n : ℕ}
    (F : Fin (n+1) → Set (UnitSphere n)) (hclosed : ∀ i, IsClosed (F i))
    (hfree : ∀ i x, x ∈ F i → -x ∉ F i) :
    ∃ x : UnitSphere n, ∀ i, x ∉ F i := by
  by_contra! hcover
  obtain ⟨i,x,hx,hneg⟩ := exists_antipodal_pair_of_closed_cover F hclosed hcover
  exact hfree i x hx hneg

/- CV Lemma 7 needs separation from the closure of the antipodal set;
the individual sets need not be closed. -/
theorem exists_antipodally_uncovered_of_closure_separation {n : ℕ}
    (A : Fin n → Set (UnitSphere n))
    (hsep : ∀ i x, x ∈ A i → -x ∉ closure (A i)) :
    ∃ x : UnitSphere n, ∀ i, x ∉ A i ∧ -x ∉ A i := by
  let f : UnitSphere n → E n := fun x => WithLp.toLp 2
    (fun i => Metric.infDist x (A i) - Metric.infDist (-x) (A i))
  have hf : Continuous f := by
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi (fun i => (Metric.continuous_infDist_pt _).sub
      ((Metric.continuous_infDist_pt _).comp continuous_neg))
  have hodd (x : UnitSphere n) : f (-x) = -f x := by
    ext i
    change Metric.infDist (-x) (A i) - Metric.infDist (- -x) (A i) =
      -(Metric.infDist x (A i) - Metric.infDist (-x) (A i))
    rw [neg_neg]
    ring
  obtain ⟨x, hx⟩ := odd_sphere_map_has_zero f hf hodd
  have heq (i : Fin n) : Metric.infDist x (A i) = Metric.infDist (-x) (A i) := by
    have hi := congrArg (fun z : E n => z i) hx
    change Metric.infDist x (A i) - Metric.infDist (-x) (A i) = 0 at hi
    exact sub_eq_zero.mp hi
  refine ⟨x, fun i => ⟨?_, ?_⟩⟩
  · intro hi
    apply hsep i x hi
    apply (Metric.mem_closure_iff_infDist_zero ⟨x, hi⟩).mpr
    rw [← heq, Metric.infDist_zero_of_mem hi]
  · intro hi
    have h := hsep i (-x) hi
    rw [neg_neg] at h
    apply h
    apply (Metric.mem_closure_iff_infDist_zero ⟨-x, hi⟩).mpr
    rw [heq, Metric.infDist_zero_of_mem hi]

theorem exists_antipodally_uncovered_of_disjoint_closure_neg {n : ℕ}
    (A : Fin n → Set (UnitSphere n))
    (hsep : ∀ i, Disjoint (A i) (closure (-A i))) :
    ∃ x : UnitSphere n, ∀ i, x ∉ A i ∧ -x ∉ A i := by
  apply exists_antipodally_uncovered_of_closure_separation A
  intro i x hx hneg
  apply Set.disjoint_left.mp (hsep i) hx
  rw [← neg_closure]
  exact Set.mem_neg.mpr (by simpa using hneg)

theorem exists_antipodally_uncovered_of_card_le {n J : ℕ} (hJn : J ≤ n)
    (A : Fin J → Set (UnitSphere n))
    (hsep : ∀ i, Disjoint (A i) (closure (-A i))) :
    ∃ x : UnitSphere n, ∀ i, x ∉ A i ∧ -x ∉ A i := by
  let B : Fin n → Set (UnitSphere n) := fun i =>
    if hi : i.val < J then A ⟨i.val, hi⟩ else ∅
  have hB (i : Fin n) : Disjoint (B i) (closure (-B i)) := by
    dsimp [B]
    split_ifs with hi
    · exact hsep ⟨i.val, hi⟩
    · simp
  obtain ⟨x, hx⟩ := exists_antipodally_uncovered_of_disjoint_closure_neg B hB
  refine ⟨x, fun i => ?_⟩
  simpa [B, i.isLt] using hx (i.castLE hJn)

end Kakeya4.Hard.MultilinearKakeya
