import Kakeya4.Hard.RestrictedTriple.SquareGeometricInput

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem exists_square_dense_frostman_input {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1/6) :
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
              (∀ t ∈ Q.image (endpointNormalization a b z),
                t.1 ∈ unitSquare ∧ t.2.1 ∈ unitSquare ∧ t.2.2 ∈ unitSquare) ∧
              (Q.image (endpointNormalization a b z)).card = Q.card ∧
              dotDifferenceImage (Q.image (endpointNormalization a b z) : Set Triple) =
                (fun x : ℝ ↦ (a*b)*x) '' dotDifferenceImage (Q : Set Triple) := by
  classical
  obtain ⟨geom₀,hgeom₀,hgeom₀1,hinput⟩ := exists_square_geometric_input hη hηsmall
  obtain ⟨pay₀,hpay₀,_hpay₀1,hpay⟩ := exists_constant_power_payment 4096 (by norm_num) hη
  refine ⟨min geom₀ pay₀,lt_min hgeom₀ hpay₀,(min_le_left _ _).trans_lt hgeom₀1,?_⟩
  intro p hp hpp A B hA hB hADa hADb H hH hlarge
  have hpg : p ≤ geom₀ := hpp.trans (min_le_left _ _)
  have hppay : p ≤ pay₀ := hpp.trans (min_le_right _ _)
  have hp1 : p ≤ 1 := (hpg.trans_lt hgeom₀1).le
  have hpay4096 := hpay p hp hppay
  have hpay256 : 256 ≤ p^(-η) := by linarith
  have hpay8 : 8 ≤ p^(-η) := by linarith
  obtain ⟨F,G,R,hFA,hGB,hFsep,hGsep,hsupR,hRne,hmassR,hlocalR,
    a,b,z,ha,hb,hab,hbb,hstandard,hsep,hsquare,_hcard,_himage⟩ :=
    hinput p hp hpg A B hA hB hADa hADb H hH hlarge
  have hFcard := finset_card_le_of_AD_unitSquare hp hp1 (Real.rpow_pos_of_pos hp _).le hA hADa F hFA hFsep
  have hGcard := finset_card_le_of_AD_unitSquare hp hp1 (Real.rpow_pos_of_pos hp _).le hB hADb G hGB hGsep
  have hbase : ∀ j, ((tripleClasses F G j).card : ℝ) ≤ 4*p^(-η)/p := by
    intro j
    fin_cases j
    · exact hFcard
    · exact hGcard
    · exact hGcard
  have huR : ∀ j, ((activeTripleClasses R j).card : ℝ) ≤ 4*p^(-η)/p := by
    intro j
    have hh : ((activeTripleClasses R j).card : ℝ) ≤ (tripleClasses F G j).card := by
      exact_mod_cast Finset.card_le_card (activeTripleClasses_subset_of_support F G R hsupR j)
    exact hh.trans (hbase j)
  obtain ⟨Q,hQR,hQne,hmassQ,hlower,hdense⟩ :=
    exists_selected_dense_graph hp hpay4096 R hRne huR hmassR
  have hsupQ : ∀ t ∈ Q, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G := fun t ht ↦ hsupR t (hQR ht)
  have hclasses := activeTripleClasses_subset_of_support F G Q hsupQ
  have hproj0 : (activeTripleClasses Q 0 : Set Plane) ⊆ (F : Set Plane) := hclasses 0
  have hproj1 : (activeTripleClasses Q 1 : Set Plane) ⊆ (G : Set Plane) := hclasses 1
  have hproj2 : (activeTripleClasses Q 2 : Set Plane) ⊆ (G : Set Plane) := hclasses 2
  have hfrost : ∀ j, finiteFrostman p (p^(-43*η)) (activeTripleClasses Q j) := by
    intro j
    fin_cases j
    · exact finiteFrostman_of_selected_marginal hp hpay256 hADa _
        (hproj0.trans hFA) (hFsep.subset (image_mono hproj0)) (hlower 0)
    · exact finiteFrostman_of_selected_marginal hp hpay256 hADb _
        (hproj1.trans hGB) (hGsep.subset (image_mono hproj1)) (hlower 1)
    · exact finiteFrostman_of_selected_marginal hp hpay256 hADb _
        (hproj2.trans hGB) (hGsep.subset (image_mono hproj2)) (hlower 2)
  have hnormsub := Finset.image_subset_image (f := endpointNormalization a b z) hQR
  refine ⟨F,G,Q,hFA,hGB,hFsep,hGsep,hsupQ,hQne,hmassQ,hlower,hfrost,hdense,?_,
    a,b,z,ha,hb,hab,hbb,standardTripleGeometry_mono hnormsub hstandard,
    tripleSeparated_mono hnormsub hsep,
    finiteFrostman_active_endpointNormalization hp hη.le hpay8 (by linarith [hab.1])
      (by linarith [hbb.1]) z Q hfrost,
    coordinateDensity_active_endpoint_power hp hp1 hη.le ha.ne' hb.ne' z hdense,
    (fun t ht ↦ hsquare t (hnormsub ht)),
    Finset.card_image_of_injective _ (endpointNormalization_injective ha.ne' hb.ne' z),?_⟩
  · intro s l u hs
    have hsub : (Q : Set Triple) ⊆ (R : Set Triple) := hQR
    exact (intervalCover_mono (inter_subset_inter_right _ (image_mono hsub))).trans (hlocalR s l u hs)
  · rw [Finset.coe_image]
    exact dotDifferenceImage_endpointNormalization a b z (Q : Set Triple)

end Kakeya4.Hard.RestrictedTriple
