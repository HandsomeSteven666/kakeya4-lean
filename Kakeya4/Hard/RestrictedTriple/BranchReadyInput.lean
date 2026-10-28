import Kakeya4.Hard.RestrictedTriple.NormalizedConcentration

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

/-- The same actual normalized graph has verified consumers for either finite branch.
Existence of a finite branch remains the substantive unproved dichotomy. -/
theorem exists_branch_ready_standard_input {η ε : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1/6)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ < 1 ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∀ A B : Set Plane, A ⊆ unitSquare → B ⊆ unitSquare →
        ADUpperBound p (p^(-η)) A → ADUpperBound p (p^(-η)) B →
        ∀ H : Set Triple, H ⊆ tripleCarrier A B →
          ENNReal.ofReal (p^(η-3)) ≤ tripleCover p H →
          ∃ F G : Finset Plane, ∃ Q : Finset Triple,
            (F : Set Plane) ⊆ A ∧ (G : Set Plane) ⊆ B ∧
            IsSeparated (Real.toNNReal p) (planeCoordinates '' (F : Set Plane)) ∧
            IsSeparated (Real.toNNReal p) (planeCoordinates '' (G : Set Plane)) ∧
            (∀ t ∈ Q, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G) ∧ Q.Nonempty ∧
            p^(39*η-3)/8 ≤ (Q.card : ℝ) ∧
            (∀ j, p^(41*η-1)/128 ≤ ((activeTripleClasses Q j).card : ℝ)) ∧
            (∀ j, finiteFrostman p (p^(-43*η)) (activeTripleClasses Q j)) ∧
            coordinateDensity (p^(43*η)) (activeTripleClasses Q) (Q.image tripleVertexMap) ∧
            (∀ s a b : ℝ, p ≤ s →
              intervalCover s (Icc a b ∩ dotDifferenceImage (Q : Set Triple)) ≤
                16*intervalCover s (Icc (a-6*p) (b+6*p) ∩ dotDifferenceImage H)) ∧
            ∃ a b : ℝ, ∃ z : Plane, 0 < a ∧ 0 < b ∧
              (3/8 ≤ a ∧ a ≤ 3/(4*p^(6*η))) ∧ (3/16 ≤ b ∧ b ≤ 3/(4*p^(6*η))) ∧
              standardTripleGeometry (Q.image (endpointNormalization a b z)) ∧
              tripleSeparated (p/8) (Q.image (endpointNormalization a b z)) ∧
              (∀ j, finiteFrostman (p/8) ((p/8)^(-44*η))
                (activeTripleClasses (Q.image (endpointNormalization a b z)) j)) ∧
              coordinateDensity ((p/8)^(44*η))
                (activeTripleClasses (Q.image (endpointNormalization a b z)))
                ((Q.image (endpointNormalization a b z)).image tripleVertexMap) ∧
              (Q.image (endpointNormalization a b z)).card = Q.card ∧
              dotDifferenceImage (Q.image (endpointNormalization a b z) : Set Triple) =
                (fun x : ℝ ↦ (a*b)*x) '' dotDifferenceImage (Q : Set Triple) ∧
              (LongIntervalExpansion (p/8) (ε/4) (44*η)
                (Q.image (endpointNormalization a b z) : Set Triple) → LongIntervalExpansion p ε η H) ∧
              (NormalizedTripleLineCounts (p/8) (ε/4) (Q.image (endpointNormalization a b z)) →
                LineConcentration p ε A B) := by
  obtain ⟨input₀,hinput₀,hinput₀1,hinput⟩ := exists_expansion_ready_standard_input hη hηsmall hε hε1
  refine ⟨input₀,hinput₀,hinput₀1,?_⟩
  intro p hp hpp A B hA hB hADa hADb H hH hlarge
  obtain ⟨F,G,Q,hFA,hGB,hFsep,hGsep,hsup,hne,hmass,hlower,hfrost,hdense,hlocal,
    a,b,z,ha,hb,hab,hbb,hgeom,hsep,hnfrost,hndense,hcard,himage,hexpand⟩ :=
    hinput p hp hpp A B hA hB hADa hADb H hH hlarge
  refine ⟨F,G,Q,hFA,hGB,hFsep,hGsep,hsup,hne,hmass,hlower,hfrost,hdense,hlocal,
    a,b,z,ha,hb,hab,hbb,hgeom,hsep,hnfrost,hndense,hcard,himage,hexpand,?_⟩
  exact lineConcentration_of_active_normalized_counts hp (hpp.trans_lt hinput₀1).le hε1
    (by linarith) (by linarith [hab.1]) (by linarith [hbb.1]) z F G Q hFA hGB hFsep hGsep hsup

end Kakeya4.Hard.RestrictedTriple
