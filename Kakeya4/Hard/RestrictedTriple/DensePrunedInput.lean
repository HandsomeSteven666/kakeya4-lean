import Kakeya4.Hard.RestrictedTriple.FiberDensityPayment

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

/-- Produce every-coordinate-subset density in the same geometrically pruned graph,
starting from the original arbitrary H and its original entropy lower bound. -/
theorem exists_dense_pruned_input {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1/6) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ < 1 ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∀ A B : Set Plane, A ⊆ unitSquare → B ⊆ unitSquare →
        ADUpperBound p (p^(-η)) A → ADUpperBound p (p^(-η)) B →
        ∀ H : Set Triple, H ⊆ tripleCarrier A B →
          ENNReal.ofReal (p^(η-3)) ≤ tripleCover p H →
          ∃ F G : Finset Plane, ∃ Q : Finset Triple,
            (F : Set Plane) ⊆ A ∧ (G : Set Plane) ⊆ B ∧
            IsSeparated (Real.toNNReal p) (planeCoordinates '' (F : Set Plane)) ∧
            IsSeparated (Real.toNNReal p) (planeCoordinates '' (G : Set Plane)) ∧
            (∀ t ∈ Q, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G) ∧
            (∀ t ∈ Q, p^(6*η) < ‖t.1‖ ∧ p^(6*η) < dist t.2.1 t.2.2) ∧
            p^(2*η-3)/4 ≤ (Q.card : ℝ) ∧ Q.Nonempty ∧
            coordinateDensity (p^(6*η)) (tripleClasses F G) (Q.image tripleVertexMap) ∧
            (∀ s a b : ℝ, p ≤ s →
              intervalCover s (Icc a b ∩ dotDifferenceImage (Q : Set Triple)) ≤
                16*intervalCover s (Icc (a-6*p) (b+6*p) ∩ dotDifferenceImage H)) := by
  classical
  obtain ⟨prune₀,hprune₀,hprune₀1,hprune⟩ := exists_pruned_restricted_input hη hηsmall
  obtain ⟨pay₀,hpay₀,_hpay₀1,hpay⟩ := exists_constant_power_payment 2048 (by norm_num) hη
  refine ⟨min prune₀ pay₀,lt_min hprune₀ hpay₀,(min_le_left _ _).trans_lt hprune₀1,?_⟩
  intro p hp hpp A B hA hB hADa hADb H hH hlarge
  have hpprune : p ≤ prune₀ := hpp.trans (min_le_left _ _)
  have hppay : p ≤ pay₀ := hpp.trans (min_le_right _ _)
  have hp1 : p ≤ 1 := (hpprune.trans_lt hprune₀1).le
  obtain ⟨F,G,R,hFA,hGB,hFsep,hGsep,hsupport,hgeom,hmass,hne,hlocal⟩ :=
    hprune p hp hpprune A B hA hB hADa hADb H hH hlarge
  have hFcard := finset_card_le_of_AD_unitSquare hp hp1 (Real.rpow_pos_of_pos hp _).le hA hADa F hFA hFsep
  have hGcard := finset_card_le_of_AD_unitSquare hp hp1 (Real.rpow_pos_of_pos hp _).le hB hADb G hGB hGsep
  have hFne : F.Nonempty := by
    obtain ⟨t,ht⟩ := hne
    exact ⟨t.1,(hsupport t ht).1⟩
  have hGne : G.Nonempty := by
    obtain ⟨t,ht⟩ := hne
    exact ⟨t.2.1,(hsupport t ht).2.1⟩
  obtain ⟨Q,hQR,hQne,hret,hdensity⟩ := exists_tripartite_refinement F G R hne hsupport
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
  have hcoefficient := fiber_density_power_lower hp (hpay p hp hppay) F G R hFne hGne
    hFcard hGcard hmass
  refine ⟨F,G,Q,hFA,hGB,hFsep,hGsep,?_,?_,?_,hQne,
    coordinateDensity_mono hcoefficient hdensity,?_⟩
  · intro t ht
    exact hsupport t (hQR ht)
  · intro t ht
    exact hgeom t (hQR ht)
  · norm_num at hret
    linarith
  · intro s a b hs
    have hsub : (Q : Set Triple) ⊆ (R : Set Triple) := hQR
    exact (intervalCover_mono (inter_subset_inter_right _ (image_mono hsub))).trans (hlocal s a b hs)

end Kakeya4.Hard.RestrictedTriple
