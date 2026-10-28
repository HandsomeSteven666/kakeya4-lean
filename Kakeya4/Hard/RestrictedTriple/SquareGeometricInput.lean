import Kakeya4.Hard.RestrictedTriple.SquareCells

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem exists_square_standard_subgraph {A B : Set Plane} (hA : A ⊆ unitSquare) (hB : B ⊆ unitSquare)
    (H : Finset Triple) (hne : H.Nonempty) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hsupport : ∀ t ∈ H, t.1 ∈ A ∧ t.2.1 ∈ B ∧ t.2.2 ∈ B)
    (hgeom : ∀ t ∈ H, r < ‖t.1‖ ∧ r < dist t.2.1 t.2.2) :
    ∃ Q : Finset Triple, Q ⊆ H ∧ Q.Nonempty ∧
      (H.card : ℝ) ≤ (102/r)^6*(Q.card : ℝ) ∧
      ∃ a b : ℝ, ∃ z : Plane, 0 < a ∧ 0 < b ∧
        (3/8 ≤ a ∧ a ≤ 3/(4*r)) ∧ (3/16 ≤ b ∧ b ≤ 3/(4*r)) ∧
        standardTripleGeometry (Q.image (endpointNormalization a b z)) ∧
        (∀ t ∈ Q.image (endpointNormalization a b z),
          t.1 ∈ unitSquare ∧ t.2.1 ∈ unitSquare ∧ t.2.2 ∈ unitSquare) ∧
        (Q.image (endpointNormalization a b z)).card = Q.card ∧
        dotDifferenceImage (Q.image (endpointNormalization a b z) : Set Triple) =
          (fun x : ℝ ↦ (a*b)*x) '' dotDifferenceImage (Q : Set Triple) := by
  classical
  obtain ⟨N,hN,hmesh,hNcard⟩ := exists_cell_mesh hr hr1
  obtain ⟨Q,hQH,hQne,hcard,hsmall⟩ := exists_small_cell_triples hA hB H hne hsupport hN
  have hcost : (H.card : ℝ) ≤ (102/r)^6*(Q.card : ℝ) := by
    refine hcard.trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hNcard 6) (Nat.cast_nonneg _)
  refine ⟨Q,hQH,hQne,hcost,?_⟩
  apply exists_square_standard_cell_graph Q hQne hr hmesh (fun t ht ↦ hgeom t (hQH ht)) _
    (fun t ht ↦ hA (hsupport t (hQH ht)).1) hsmall
  intro t ht
  have htH := hQH ht
  have hnormA := unitSquare_norm_le_two (hA (hsupport t htH).1)
  have hnormB := unitSquare_norm_le_two (hB (hsupport t htH).2.1)
  have hnormC := unitSquare_norm_le_two (hB (hsupport t htH).2.2)
  refine ⟨hnormA,?_⟩
  have hh := dist_triangle t.2.1 (0:Plane) t.2.2
  simp only [dist_zero_left,dist_zero_right] at hh
  linarith


theorem exists_square_geometric_input {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1/6) :
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
            p^(39*η-3)/4 ≤ (Q.card : ℝ) ∧
            (∀ s a b : ℝ, p ≤ s →
              intervalCover s (Icc a b ∩ dotDifferenceImage (Q : Set Triple)) ≤
                16*intervalCover s (Icc (a-6*p) (b+6*p) ∩ dotDifferenceImage H)) ∧
            ∃ a b : ℝ, ∃ z : Plane, 0 < a ∧ 0 < b ∧
              (3/8 ≤ a ∧ a ≤ 3/(4*p^(6*η))) ∧ (3/16 ≤ b ∧ b ≤ 3/(4*p^(6*η))) ∧
              standardTripleGeometry (Q.image (endpointNormalization a b z)) ∧
              tripleSeparated (p/8) (Q.image (endpointNormalization a b z)) ∧
              (∀ t ∈ Q.image (endpointNormalization a b z),
                t.1 ∈ unitSquare ∧ t.2.1 ∈ unitSquare ∧ t.2.2 ∈ unitSquare) ∧
              (Q.image (endpointNormalization a b z)).card = Q.card ∧
              dotDifferenceImage (Q.image (endpointNormalization a b z) : Set Triple) =
                (fun x : ℝ ↦ (a*b)*x) '' dotDifferenceImage (Q : Set Triple) := by
  classical
  obtain ⟨input₀,hinput₀,hinput₀1,hinput⟩ := exists_dense_frostman_input hη hηsmall
  obtain ⟨pay₀,hpay₀,_hpay₀1,hpay⟩ := exists_constant_power_payment ((102:ℝ)^6) (by positivity) hη
  refine ⟨min input₀ pay₀,lt_min hinput₀ hpay₀,(min_le_left _ _).trans_lt hinput₀1,?_⟩
  intro p hp hpp A B hA hB hADa hADb H hH hlarge
  have hpinput : p ≤ input₀ := hpp.trans (min_le_left _ _)
  have hppay : p ≤ pay₀ := hpp.trans (min_le_right _ _)
  have hp1 : p ≤ 1 := (hpinput.trans_lt hinput₀1).le
  obtain ⟨F,G,R,hFA,hGB,hFsep,hGsep,hsupport,hgeom,hmass,hne,_hlower,_hff,_hfg,
    _hnf,_hng,_hdense,_hndense,_hndensePower,hlocal⟩ :=
    hinput p hp hpinput A B hA hB hADa hADb H hH hlarge
  have hrpos : 0 < p^(6*η) := Real.rpow_pos_of_pos hp _
  have hr1 : p^(6*η) ≤ 1 := Real.rpow_le_one hp.le hp1 (by positivity)
  have hsupSet : ∀ t ∈ R, t.1 ∈ A ∧ t.2.1 ∈ B ∧ t.2.2 ∈ B := by
    intro t ht
    exact ⟨hFA (hsupport t ht).1,hGB (hsupport t ht).2.1,hGB (hsupport t ht).2.2⟩
  obtain ⟨Q,hQR,hQne,hcard,a,b,z,ha,hb,haBounds,hbBounds,hstandard,hsquare,hQcard,himage⟩ :=
    exists_square_standard_subgraph hA hB R hne hrpos hr1 hsupSet hgeom
  have hbudget := cell_cost_power_budget hp (hpay p hp hppay)
  have hcard' : (R.card : ℝ) ≤ p^(-37*η)*(Q.card : ℝ) := by
    refine hcard.trans ?_
    gcongr
  have hmass' : p^(39*η-3)/4 ≤ (Q.card : ℝ) := by
    have heq : p^(-37*η)*(p^(39*η-3)/4) = p^(2*η-3)/4 := by
      calc
        _ = (p^(-37*η)*p^(39*η-3))/4 := by ring
        _ = _ := by rw [← Real.rpow_add hp]; congr 2; ring
    have hh : p^(-37*η)*(p^(39*η-3)/4) ≤ p^(-37*η)*(Q.card : ℝ) := by
      rw [heq]
      exact hmass.trans hcard'
    exact le_of_mul_le_mul_left hh (Real.rpow_pos_of_pos hp _)
  have hsupQ : ∀ t ∈ Q, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G := fun t ht ↦ hsupport t (hQR ht)
  refine ⟨F,G,Q,hFA,hGB,hFsep,hGsep,hsupQ,hQne,hmass',?_,a,b,z,ha,hb,haBounds,hbBounds,
    hstandard,endpointNormalization_separated hp haBounds.1 hbBounds.1 z F G Q hFsep hGsep hsupQ,
    hsquare,hQcard,himage⟩
  intro s l u hs
  have hsub : (Q : Set Triple) ⊆ (R : Set Triple) := hQR
  exact (intervalCover_mono (inter_subset_inter_right _ (image_mono hsub))).trans (hlocal s l u hs)

end Kakeya4.Hard.RestrictedTriple
