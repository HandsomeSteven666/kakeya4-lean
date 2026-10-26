import Kakeya4.Hard.RestrictedTriple.CoordinateTransport

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem finiteFrostman_halfPlane_power {p η : ℝ} {F : Finset Plane}
    (hp : 0 < p) (hη : 0 ≤ η) (hpay : 2 ≤ p^(-η))
    (h : finiteFrostman p (p^(-6*η)) F) :
    finiteFrostman (p/2) ((p/2)^(-7*η)) (F.image halfPlane) := by
  have hcoef : 2*p^(-6*η) ≤ (p/2)^(-7*η) := by
    calc
      _ ≤ p^(-η)*p^(-6*η) := mul_le_mul_of_nonneg_right hpay (Real.rpow_pos_of_pos hp _).le
      _ = p^(-7*η) := by rw [← Real.rpow_add hp]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  exact finiteFrostman_mono (by positivity) hcoef (finiteFrostman_halfPlane h)

/-- Finite real cardinality bounds imply the source-style ENNReal normalized counts. -/
theorem finiteFrostman_enn {p K : ℝ} {F : Finset Plane} (hp : 0 ≤ p) (hK : 0 ≤ K)
    (h : finiteFrostman p K F) :
    ∀ (z : Plane) (r : ℝ), p ≤ r →
      ((F.filter (fun x ↦ dist z x ≤ r)).card : ℝ≥0∞) ≤
        ENNReal.ofReal K*ENNReal.ofReal r*(F.card : ℝ≥0∞) := by
  intro z r hr
  have hr0 : 0 ≤ r := hp.trans hr
  have hh := ENNReal.ofReal_le_ofReal (h z r hr)
  simpa only [ENNReal.ofReal_mul (mul_nonneg hK hr0),ENNReal.ofReal_mul hK,
    ENNReal.ofReal_natCast] using hh

theorem coordinateDensity_halfTriple_power {p η : ℝ} {F G : Finset Plane} {Q : Finset Triple}
    (hp : 0 < p) (hp1 : p ≤ 1) (hη : 0 ≤ η)
    (h : coordinateDensity (p^(6*η)) (tripleClasses F G) (Q.image tripleVertexMap)) :
    coordinateDensity ((p/2)^(7*η)) (tripleClasses (F.image halfPlane) (G.image halfPlane))
      ((Q.image halfTriple).image tripleVertexMap) := by
  have hcoef : (p/2)^(7*η) ≤ p^(6*η) := by
    calc
      _ ≤ (p/2)^(6*η) := Real.rpow_le_rpow_of_exponent_ge (by positivity) (by linarith) (by linarith)
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  exact coordinateDensity_mono hcoef (coordinateDensity_halfTriple h)

/-- Produce the same dense pruned graph with genuine normalized Frostman marginals.
The local lower-cardinality evidence is derived from its retained edges, not supplied. -/
theorem exists_dense_frostman_input {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1/6) :
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
            (p^(4*η-1)/64 ≤ (F.card : ℝ) ∧ p^(4*η-1)/64 ≤ (G.card : ℝ)) ∧
            finiteFrostman p (p^(-6*η)) F ∧ finiteFrostman p (p^(-6*η)) G ∧
            finiteFrostman (p/2) ((p/2)^(-7*η)) (F.image halfPlane) ∧
            finiteFrostman (p/2) ((p/2)^(-7*η)) (G.image halfPlane) ∧
            coordinateDensity (p^(6*η)) (tripleClasses F G) (Q.image tripleVertexMap) ∧
            coordinateDensity (p^(6*η)) (tripleClasses (F.image halfPlane) (G.image halfPlane))
              ((Q.image halfTriple).image tripleVertexMap) ∧
            coordinateDensity ((p/2)^(7*η)) (tripleClasses (F.image halfPlane) (G.image halfPlane))
              ((Q.image halfTriple).image tripleVertexMap) ∧
            (∀ s a b : ℝ, p ≤ s →
              intervalCover s (Icc a b ∩ dotDifferenceImage (Q : Set Triple)) ≤
                16*intervalCover s (Icc (a-6*p) (b+6*p) ∩ dotDifferenceImage H)) := by
  classical
  obtain ⟨dense₀,hdense₀,hdense₀1,hdense⟩ := exists_dense_pruned_input hη hηsmall
  obtain ⟨pay₀,hpay₀,_hpay₀1,hpay⟩ := exists_constant_power_payment 128 (by norm_num) hη
  refine ⟨min dense₀ pay₀,lt_min hdense₀ hpay₀,(min_le_left _ _).trans_lt hdense₀1,?_⟩
  intro p hp hpp A B hA hB hADa hADb H hH hlarge
  have hpdense : p ≤ dense₀ := hpp.trans (min_le_left _ _)
  have hppay : p ≤ pay₀ := hpp.trans (min_le_right _ _)
  have hp1 : p ≤ 1 := (hpdense.trans_lt hdense₀1).le
  have hpay128 := hpay p hp hppay
  have hpay2 : 2 ≤ p^(-η) := by linarith
  obtain ⟨F,G,Q,hFA,hGB,hFsep,hGsep,hsupport,hgeom,hmass,hne,hdensity,hlocal⟩ :=
    hdense p hp hpdense A B hA hB hADa hADb H hH hlarge
  have hFcard := finset_card_le_of_AD_unitSquare hp hp1 (Real.rpow_pos_of_pos hp _).le hA hADa F hFA hFsep
  have hGcard := finset_card_le_of_AD_unitSquare hp hp1 (Real.rpow_pos_of_pos hp _).le hB hADb G hGB hGsep
  have hlower := marginal_card_lower_of_edges hp F G Q hsupport hFcard hGcard hmass
  have hFrostF := finiteFrostman_of_AD_marginal hp hpay128 hADa F hFA hFsep hlower.1
  have hFrostG := finiteFrostman_of_AD_marginal hp hpay128 hADb G hGB hGsep hlower.2
  exact ⟨F,G,Q,hFA,hGB,hFsep,hGsep,hsupport,hgeom,hmass,hne,hlower,hFrostF,hFrostG,
    finiteFrostman_halfPlane_power hp hη.le hpay2 hFrostF,
    finiteFrostman_halfPlane_power hp hη.le hpay2 hFrostG,hdensity,
    coordinateDensity_halfTriple hdensity,coordinateDensity_halfTriple_power hp hp1 hη.le hdensity,hlocal⟩

end Kakeya4.Hard.RestrictedTriple
