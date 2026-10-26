import Kakeya4.Hard.RestrictedTriple.Similarity

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

/-- Produce actual unit-ball finite data from the original arbitrary sets and H.
All data are chosen together; no discretization or flatness certificate is supplied. -/
theorem exists_normalized_restricted_input {A B : Set Plane}
    (hA : A ⊆ unitSquare) (hB : B ⊆ unitSquare) {H : Set Triple}
    (hH : H ⊆ tripleCarrier A B) {p : ℝ} (hp : 0 < p) :
    ∃ PA PB : Set Plane, ∃ Q : Set Triple,
      PA.Finite ∧ PB.Finite ∧ Q.Finite ∧
      (∀ x ∈ PA, ‖x‖ ≤ 1) ∧ (∀ x ∈ PB, ‖x‖ ≤ 1) ∧
      (∀ x ∈ PA, ∀ y ∈ PA, x ≠ y → p/2 < dist x y) ∧
      (∀ x ∈ PB, ∀ y ∈ PB, x ≠ y → p/2 < dist x y) ∧
      Q ⊆ tripleCarrier PA PB ∧ tripleCover p H ≤ 4096*(Q.encard : ℝ≥0∞) ∧
      (∀ C : ℝ, ADUpperBound p C A → ∀ z w, p/2 ≤ w →
        ((PA ∩ closedBall z w).encard : ℝ≥0∞) ≤ ENNReal.ofReal (2*C*w/(p/2))) ∧
      (∀ C : ℝ, ADUpperBound p C B → ∀ z w, p/2 ≤ w →
        ((PB ∩ closedBall z w).encard : ℝ≥0∞) ≤ ENNReal.ofReal (2*C*w/(p/2))) ∧
      (∀ s a b : ℝ, p ≤ s →
        intervalCover (s/4) (Icc (a/4) (b/4) ∩ dotDifferenceImage Q) ≤
          16*intervalCover s (Icc (a-6*p) (b+6*p) ∩ dotDifferenceImage H)) := by
  obtain ⟨PA,PB,Q,hPA,hPB,hPAfin,hPBfin,hQfin,hPAsep,hPBsep,hQ,hlarge,_hca,_hcb,hlocal⟩ :=
    exists_discrete_restricted_input hA hB hH hp
  refine ⟨halfPlane '' PA,halfPlane '' PB,halfTriple '' Q,
    hPAfin.image halfPlane,hPBfin.image halfPlane,hQfin.image halfTriple,
    ?_,?_,halfPlane_separated hp.le hPAsep,halfPlane_separated hp.le hPBsep,
    halfTriple_image_subset_carrier hQ,?_,?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact halfPlane_norm_le_one (hA (hPA hx))
  · rintro _ ⟨x,hx,rfl⟩
    exact halfPlane_norm_le_one (hB (hPB hx))
  · rwa [halfTriple_encard]
  · intro C hAD z w hw
    exact halfPlane_closedBall_local_count hp hAD hPA hPAsep z hw
  · intro C hAD z w hw
    exact halfPlane_closedBall_local_count hp hAD hPB hPBsep z hw
  · intro s a b hs
    rw [intervalCover_halfTriple s (hp.trans_le hs).le]
    exact hlocal s a b hs

end Kakeya4.Hard.RestrictedTriple
