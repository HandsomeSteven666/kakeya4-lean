import Kakeya4.Hard.RestrictedTriple.StripWidthMesh

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Classical

namespace Kakeya4.Hard.RestrictedTriple

/-- Finite point-set two-ends selection on a genuine finite mesh of strip widths.
All lines are quantified, without supplying a non-concentration certificate. -/
theorem exists_two_ends_strip_on_mesh {p ζ : ℝ} (hp : 0 < p) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (E : Finset Plane) (hne : E.Nonempty) (hunit : ∀ x ∈ E, ‖x‖ ≤ 1)
    (W : Finset ℝ) (hone : 1 ∈ W) (hW : ∀ w ∈ W, 0 < w ∧ w ≤ 1)
    (hmesh : ∀ r : ℝ, p ≤ r → r ≤ 1 → ∃ s ∈ W, r ≤ s ∧ s ≤ 2*r) :
    ∃ w ∈ W, ∃ L : AffineLine, ∃ P : Finset Plane,
      P = E.filter (fun x ↦ x ∈ lineNeighborhood w L) ∧ P.Nonempty ∧
      w^ζ*(E.card : ℝ) ≤ (P.card : ℝ) ∧
      ∀ r : ℝ, p ≤ r → ∀ M : AffineLine,
        ((P.filter (fun x ↦ x ∈ lineNeighborhood r M)).card : ℝ) ≤
          2*(r/w)^ζ*(P.card : ℝ) := by
  classical
  let L₀ := horizontalLine (0:Plane)
  have hwide : E.filter (fun x ↦ x ∈ lineNeighborhood 1 L₀) = E := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    apply mem_cthickening_of_dist_le x 0 1 (lineCarrier L₀)
    · refine ⟨0,?_⟩
      simp [L₀,horizontalLine]
    · simpa only [dist_zero_right] using hunit x hx
  let C := (W ×ˢ E.powerset).filter (fun c : ℝ × Finset Plane ↦
    ∃ L : AffineLine, c.2 = E.filter (fun x ↦ x ∈ lineNeighborhood c.1 L))
  have hwideC : (1,E) ∈ C := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hone,Finset.mem_powerset.mpr (Finset.Subset.refl _)⟩,?_⟩
    exact ⟨L₀,hwide.symm⟩
  let score : ℝ × Finset Plane → ℝ := fun c ↦ (c.2.card : ℝ)/c.1^ζ
  obtain ⟨c,hc,hmax⟩ := Finset.exists_max_image C score ⟨(1,E),hwideC⟩
  obtain ⟨hcprod,L,hP⟩ := Finset.mem_filter.mp hc
  have hwW : c.1 ∈ W := (Finset.mem_product.mp hcprod).1
  have hw : 0 < c.1 := (hW c.1 hwW).1
  have hw1 : c.1 ≤ 1 := (hW c.1 hwW).2
  have hwpow : 0 < c.1^ζ := Real.rpow_pos_of_pos hw _
  have hscore : (E.card : ℝ) ≤ (c.2.card : ℝ)/c.1^ζ := by
    simpa only [score,Real.one_rpow,div_one] using hmax (1,E) hwideC
  have hmass : c.1^ζ*(E.card : ℝ) ≤ (c.2.card : ℝ) := by
    have hh := (le_div_iff₀ hwpow).mp hscore
    nlinarith
  have hPne : c.2.Nonempty := by
    apply Finset.card_pos.mp
    have hEpos : (0:ℝ) < E.card := by exact_mod_cast Finset.card_pos.mpr hne
    exact_mod_cast (mul_pos hwpow hEpos).trans_le hmass
  have hPsub : c.2 ⊆ E := by rw [hP]; exact Finset.filter_subset _ _
  refine ⟨c.1,hwW,L,c.2,hP,hPne,hmass,?_⟩
  intro r hpr M
  have hr : 0 < r := hp.trans_le hpr
  by_cases hr1 : r ≤ 1
  · obtain ⟨s,hsW,hrs,hsr⟩ := hmesh r hpr hr1
    have hs : 0 < s := (hW s hsW).1
    let R := E.filter (fun x ↦ x ∈ lineNeighborhood s M)
    have hRC : (s,R) ∈ C := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hsW,Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩,?_⟩
      exact ⟨M,rfl⟩
    have hRscore : (R.card : ℝ)/s^ζ ≤ (c.2.card : ℝ)/c.1^ζ := hmax (s,R) hRC
    have hRmass : (R.card : ℝ) ≤ (s/c.1)^ζ*(c.2.card : ℝ) := by
      have hh := (div_le_div_iff₀ (Real.rpow_pos_of_pos hs _) hwpow).mp hRscore
      rw [Real.div_rpow hs.le hw.le]
      have hh' : (R.card : ℝ) ≤ ((c.2.card : ℝ)*s^ζ)/c.1^ζ := (le_div_iff₀ hwpow).mpr hh
      convert hh' using 1 <;> ring
    have hsub : c.2.filter (fun x ↦ x ∈ lineNeighborhood r M) ⊆ R := by
      intro x hx
      obtain ⟨hxP,hxr⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hPsub hxP,cthickening_mono hrs _ hxr⟩
    have hcount : ((c.2.filter (fun x ↦ x ∈ lineNeighborhood r M)).card : ℝ) ≤ R.card := by
      exact_mod_cast Finset.card_le_card hsub
    have htwo : (2:ℝ)^ζ ≤ 2 := by
      calc
        _ ≤ (2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hζ1
        _ = _ := Real.rpow_one _
    have hpower : (s/c.1)^ζ ≤ 2*(r/c.1)^ζ := by
      calc
        _ ≤ ((2*r)/c.1)^ζ := Real.rpow_le_rpow (by positivity)
          ((div_le_div_iff_of_pos_right hw).mpr hsr) hζ
        _ = (2:ℝ)^ζ*(r/c.1)^ζ := by
          rw [show (2*r)/c.1 = 2*(r/c.1) by ring,Real.mul_rpow (by norm_num) (by positivity)]
        _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (by positivity) _)
    exact hcount.trans (hRmass.trans (mul_le_mul_of_nonneg_right hpower (Nat.cast_nonneg _)))
  · have hratio : 1 ≤ r/c.1 := (le_div_iff₀ hw).mpr (by linarith)
    have hpow : 1 ≤ (r/c.1)^ζ := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hratio hζ
    have hcount : ((c.2.filter (fun x ↦ x ∈ lineNeighborhood r M)).card : ℝ) ≤ c.2.card := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hprod := mul_le_mul_of_nonneg_right hpow (show (0:ℝ) ≤ c.2.card from Nat.cast_nonneg _)
    nlinarith

/-- Finite point-set form of the two-ends strip reduction (paper Lemma 8.10).
The r>=p cutoff is necessary for atomic finite sets; all such radii and all lines are controlled. -/
theorem exists_two_ends_strip {p ζ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (E : Finset Plane) (hne : E.Nonempty)
    (hunit : ∀ x ∈ E, ‖x‖ ≤ 1) :
    ∃ w : ℝ, p/2 ≤ w ∧ w ≤ 1 ∧ ∃ L : AffineLine, ∃ P : Finset Plane,
      P = E.filter (fun x ↦ x ∈ lineNeighborhood w L) ∧ P.Nonempty ∧
      w^ζ*(E.card : ℝ) ≤ (P.card : ℝ) ∧
      ∀ r : ℝ, p ≤ r → ∀ M : AffineLine,
        ((P.filter (fun x ↦ x ∈ lineNeighborhood r M)).card : ℝ) ≤
          2*(r/w)^ζ*(P.card : ℝ) := by
  classical
  obtain ⟨W,hone,hW,hmesh⟩ := exists_strip_width_mesh hp hp1
  obtain ⟨w,hw,L,P,hP,hneP,hmass,hnonconc⟩ := exists_two_ends_strip_on_mesh hp hζ hζ1 E hne hunit
    W hone (fun w hw ↦ ⟨lt_of_lt_of_le (by positivity : 0 < p/2) (hW w hw).1,(hW w hw).2⟩) hmesh
  exact ⟨w,(hW w hw).1,(hW w hw).2,L,P,hP,hneP,hmass,hnonconc⟩

end Kakeya4.Hard.RestrictedTriple
