import Kakeya4.Hard.RestrictedTriple.TwoEndsStrip

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Classical

namespace Kakeya4.Hard.RestrictedTriple

/-- A retained cardinality fraction gives the precise normalized Frostman loss.
No local lower regularity of either set is assumed. -/
theorem finiteFrostman_of_retained_fraction {p K θ : ℝ} (hp : 0 ≤ p) (hK : 0 ≤ K) (hθ : 0 < θ)
    (E P : Finset Plane) (hPE : P ⊆ E) (hmass : θ*(E.card : ℝ) ≤ P.card)
    (hF : finiteFrostman p K E) : finiteFrostman p (K/θ) P := by
  classical
  have hcard : (E.card : ℝ) ≤ (P.card : ℝ)/θ := (le_div_iff₀ hθ).mpr (by nlinarith)
  intro z r hpr
  have hr : 0 ≤ r := hp.trans hpr
  have hsub : P.filter (fun x ↦ dist z x ≤ r) ⊆ E.filter (fun x ↦ dist z x ≤ r) :=
    Finset.filter_subset_filter _ hPE
  have hcount : ((P.filter (fun x ↦ dist z x ≤ r)).card : ℝ) ≤
      (E.filter (fun x ↦ dist z x ≤ r)).card := by exact_mod_cast Finset.card_le_card hsub
  calc
    _ ≤ _ := hcount
    _ ≤ K*r*(E.card : ℝ) := hF z r hpr
    _ ≤ K*r*((P.card : ℝ)/θ) := mul_le_mul_of_nonneg_left hcard (mul_nonneg hK hr)
    _ = _ := by ring

/-- Actual finite two-ends selection together with the exact inherited Frostman constant. -/
theorem exists_two_ends_frostman_strip {p ζ K : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hK : 0 ≤ K)
    (E : Finset Plane) (hne : E.Nonempty) (hunit : ∀ x ∈ E, ‖x‖ ≤ 1)
    (hF : finiteFrostman p K E) :
    ∃ w : ℝ, p/2 ≤ w ∧ w ≤ 1 ∧ ∃ L : AffineLine, ∃ P : Finset Plane,
      P = E.filter (fun x ↦ x ∈ lineNeighborhood w L) ∧ P.Nonempty ∧
      w^ζ*(E.card : ℝ) ≤ (P.card : ℝ) ∧ finiteFrostman p (K/w^ζ) P ∧
      ∀ r : ℝ, p ≤ r → ∀ M : AffineLine,
        ((P.filter (fun x ↦ x ∈ lineNeighborhood r M)).card : ℝ) ≤
          2*(r/w)^ζ*(P.card : ℝ) := by
  obtain ⟨w,hpw,hw1,L,P,hP,hPne,hmass,hnonconc⟩ := exists_two_ends_strip hp hp1 hζ hζ1 E hne hunit
  have hw : 0 < w := lt_of_lt_of_le (by positivity : 0 < p/2) hpw
  have hPE : P ⊆ E := by rw [hP]; exact Finset.filter_subset _ _
  exact ⟨w,hpw,hw1,L,P,hP,hPne,hmass,
    finiteFrostman_of_retained_fraction hp.le hK (Real.rpow_pos_of_pos hw _) E P hPE hmass hF,hnonconc⟩

end Kakeya4.Hard.RestrictedTriple
