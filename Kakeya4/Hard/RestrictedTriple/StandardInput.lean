import Kakeya4.Hard.RestrictedTriple.StandardCells

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

def tripleSeparated (δ : ℝ) (Q : Finset Triple) : Prop :=
  ∀ t ∈ Q, ∀ u ∈ Q,
    (t.1 ≠ u.1 → δ < dist t.1 u.1) ∧
    (t.2.1 ≠ u.2.1 → δ < dist t.2.1 u.2.1) ∧
    (t.2.2 ≠ u.2.2 → δ < dist t.2.2 u.2.2)

theorem endpointNormalization_separated {p a b : ℝ} (hp : 0 < p)
    (ha : 3/8 ≤ a) (hb : 3/16 ≤ b) (z : Plane)
    (F G : Finset Plane) (Q : Finset Triple)
    (hFsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (F : Set Plane)))
    (hGsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (G : Set Plane)))
    (hsupport : ∀ t ∈ Q, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G) :
    tripleSeparated (p/8) (Q.image (endpointNormalization a b z)) := by
  classical
  have hap : 0 < a := by linarith
  have hbp : 0 < b := by linarith
  have hdist (c : ℝ) (hc : 0 < c) (w x y : Plane) :
      dist (w+c • x) (w+c • y) = c*dist x y := by
    have heq : (w+c • x)-(w+c • y) = c • (x-y) := by module
    simp only [dist_eq_norm,heq,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  have hfirst (x y : Plane) (hx : x ∈ F) (hy : y ∈ F) (hne : a • x ≠ a • y) :
      p/8 < dist (a • x) (a • y) := by
    have hs := separated_coordinates_implies_Euclidean hp.le hFsep x hx y hy
      (fun heq ↦ hne (congrArg (fun v : Plane ↦ a • v) heq))
    have hh := mul_lt_mul_of_pos_left hs hap
    have hlo := mul_le_mul_of_nonneg_right ha hp.le
    have he := hdist a hap (0:Plane) x y
    simp only [zero_add] at he
    rw [he]
    nlinarith
  have hlast (x y : Plane) (hx : x ∈ G) (hy : y ∈ G) (hne : z+b • x ≠ z+b • y) :
      p/8 < dist (z+b • x) (z+b • y) := by
    have hs := separated_coordinates_implies_Euclidean hp.le hGsep x hx y hy
      (fun heq ↦ hne (congrArg (fun v : Plane ↦ z+b • v) heq))
    have hh := mul_lt_mul_of_pos_left hs hbp
    have hlo := mul_le_mul_of_nonneg_right hb hp.le
    rw [hdist b hbp]
    nlinarith
  intro t ht u hu
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
  exact ⟨hfirst s.1 v.1 (hsupport s hs).1 (hsupport v hv).1,
    hlast s.2.1 v.2.1 (hsupport s hs).2.1 (hsupport v hv).2.1,
    hlast s.2.2 v.2.2 (hsupport s hs).2.2 (hsupport v hv).2.2⟩

theorem cell_cost_power_budget {p η : ℝ} (hp : 0 < p) (hpay : (102:ℝ)^6 ≤ p^(-η)) :
    (102/p^(6*η))^6 ≤ p^(-37*η) := by
  have hpow : (p^(6*η))^6 = p^(36*η) := by
    rw [← Real.rpow_natCast (p^(6*η)) 6,← Real.rpow_mul hp.le]
    congr 1
    norm_num
    ring
  rw [div_pow,hpow]
  calc
    _ ≤ p^(-η)/p^(36*η) := by gcongr
    _ = _ := by rw [← Real.rpow_sub hp]; congr 1; ring

/-- Uniform actual original-H input with full constant geometric separation.
Uniform density/Frostman must be rebuilt after this cell selection; they are not claimed here. -/
theorem exists_standard_geometric_input {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1/6) :
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
  obtain ⟨Q,hQR,hQne,hcard,a,b,z,ha,hb,haBounds,hbBounds,hstandard,hQcard,himage⟩ :=
    exists_standard_subgraph hA hB R hne hrpos hr1 hsupSet hgeom
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
    hQcard,himage⟩
  intro s l u hs
  have hsub : (Q : Set Triple) ⊆ (R : Set Triple) := hQR
  exact (intervalCover_mono (inter_subset_inter_right _ (image_mono hsub))).trans (hlocal s l u hs)

end Kakeya4.Hard.RestrictedTriple
