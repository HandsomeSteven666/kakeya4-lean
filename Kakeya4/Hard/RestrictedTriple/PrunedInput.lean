import Kakeya4.Hard.RestrictedTriple.GeometricPayment

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

/-- Actual geometric pruning from the original arbitrary restricted H.
The small-scale threshold precedes A/B/H; surviving edges retain the original
local dot-image transport. Standard separation and uniform density are still not asserted. -/
theorem exists_pruned_restricted_input {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1/6) :
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
            p^(2*η-3)/2 ≤ (Q.card : ℝ) ∧ Q.Nonempty ∧
            (∀ s a b : ℝ, p ≤ s →
              intervalCover s (Icc a b ∩ dotDifferenceImage (Q : Set Triple)) ≤
                16*intervalCover s (Icc (a-6*p) (b+6*p) ∩ dotDifferenceImage H)) := by
  classical
  obtain ⟨p₀,hp₀,hp₀1,hpay⟩ := exists_constant_power_payment 4096 (by norm_num) hη
  refine ⟨p₀,hp₀,hp₀1,?_⟩
  intro p hp hpp A B hA hB hADa hADb H hH hlarge
  have hp1 : p ≤ 1 := (hpp.trans_lt hp₀1).le
  have hpay4096 := hpay p hp hpp
  have hpay128 : 128 ≤ p^(-η) := by linarith
  have hr : p ≤ p^(6*η) := by
    have hh := Real.rpow_le_rpow_of_exponent_ge hp hp1 (show 6*η ≤ 1 by linarith)
    simpa only [Real.rpow_one] using hh
  obtain ⟨PA,PB,QR,hPA,hPB,hPAfin,hPBfin,hQRfin,hsepA,hsepB,hQR,hcard,_hca,_hcb,hlocal⟩ :=
    exists_discrete_restricted_input hA hB hH hp
  let F := hPAfin.toFinset
  let G := hPBfin.toFinset
  let R := hQRfin.toFinset
  have hFco : (F : Set Plane) = PA := by simp [F]
  have hGco : (G : Set Plane) = PB := by simp [G]
  have hRco : (R : Set Triple) = QR := by simp [R]
  have hFA : (F : Set Plane) ⊆ A := by rwa [hFco]
  have hGB : (G : Set Plane) ⊆ B := by rwa [hGco]
  have hFsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (F : Set Plane)) := by rwa [hFco]
  have hGsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (G : Set Plane)) := by rwa [hGco]
  have hsupport : ∀ t ∈ R, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G := by
    intro t ht
    have ht' : t ∈ QR := by rw [← hRco]; exact ht
    have hh := hQR ht'
    simpa only [tripleCarrier,Set.mem_setOf_eq,← hFco,← hGco,Finset.mem_coe] using hh
  have hraw : ENNReal.ofReal (p^(η-3)) ≤ ENNReal.ofReal (4096:ℝ)*(QR.encard : ℝ≥0∞) := by
    norm_num only [ENNReal.ofReal_ofNat]
    exact hlarge.trans hcard
  have hmass := absorb_cardinality_constant (η := η) (θ := η) hp hpay4096 hraw
  have heq : η+η-3 = 2*η-3 := by ring
  rw [heq,← hRco,Set.encard_coe_eq_coe_finsetCard] at hmass
  have hmass' : p^(2*η-3) ≤ (R.card : ℝ) := by
    apply (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg R.card)).mp
    simpa only [ENNReal.ofReal_natCast,ENat.toENNReal_coe] using hmass
  obtain ⟨hret,hnonempty⟩ := retained_half_of_power_budget hp hp1 hr hpay128
    hA hB hADa hADb F G R hFA hGB hFsep hGsep hsupport hmass'
  refine ⟨F,G,separatedTriples (p^(6*η)) R,hFA,hGB,hFsep,hGsep,?_,?_,hret,hnonempty,?_⟩
  · intro t ht
    exact hsupport t ((mem_separatedTriples.mp ht).1)
  · intro t ht
    exact (mem_separatedTriples.mp ht).2
  · intro s a b hs
    have hsub : (separatedTriples (p^(6*η)) R : Set Triple) ⊆ QR := by
      rw [← hRco]
      exact separatedTriples_subset _ _
    exact (intervalCover_mono (inter_subset_inter_right _ (image_mono hsub))).trans (hlocal s a b hs)

end Kakeya4.Hard.RestrictedTriple
