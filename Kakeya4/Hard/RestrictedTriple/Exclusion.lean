import Kakeya4.Hard.RestrictedTriple.Covering

/-! Conditional consumers of the H-003 dichotomy. The dichotomy itself remains
an explicit hypothesis; none of these results proves it. -/

set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

def LongIntervalExpansion (p ε η : ℝ) (H : Set Triple) : Prop :=
  ∃ s a b : ℝ, p ≤ s ∧ a ≤ b ∧ p^(-η)*s ≤ b-a ∧
    ENNReal.ofReal (((b-a)/s)^(1-ε)) ≤
      intervalCover s (Icc a b ∩ dotDifferenceImage H)

/-- A subpower constant cannot pay a strictly positive dimensional gap on a long interval. -/
theorem dimension_gap {p ε η d β C R : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hgap : 0 < 1-ε-d)
    (hβ : β < η*(1-ε-d)) (hC : C ≤ p^(-β)) (hR : p^(-η) ≤ R) :
    C*R^d < R^(1-ε) := by
  have hpη : 0 < p^(-η) := Real.rpow_pos_of_pos hp _
  have hRpos : 0 < R := hpη.trans_le hR
  have hsmall : p^(-β) < (p^(-η))^(1-ε-d) := by
    rw [← Real.rpow_mul hp.le]
    apply Real.rpow_lt_rpow_of_exponent_gt hp hp1
    nlinarith
  have hlarge : (p^(-η))^(1-ε-d) ≤ R^(1-ε-d) :=
    Real.rpow_le_rpow hpη.le hR hgap.le
  have hconst : C < R^(1-ε-d) := hC.trans_lt (hsmall.trans_le hlarge)
  calc
    C*R^d < R^(1-ε-d)*R^d := mul_lt_mul_of_pos_right hconst (Real.rpow_pos_of_pos hRpos _)
    _ = R^((1-ε-d)+d) := (Real.rpow_add hRpos _ _).symm
    _ = R^(1-ε) := by congr 1; ring

/-- A real interval upper-cover estimate excludes the expansion branch for this actual H. -/
theorem not_longIntervalExpansion_of_cover_bound {p ε η d β C : ℝ} {H : Set Triple}
    (hp : 0 < p) (hp1 : p < 1) (hgap : 0 < 1-ε-d)
    (hβ : β < η*(1-ε-d)) (hC0 : 0 ≤ C) (hC : C ≤ p^(-β))
    (hcover : ∀ s a b : ℝ, p ≤ s → a ≤ b → p^(-η)*s ≤ b-a →
      intervalCover s (Icc a b ∩ dotDifferenceImage H) ≤
        ENNReal.ofReal (C*((b-a)/s)^d)) :
    ¬ LongIntervalExpansion p ε η H := by
  rintro ⟨s, a, b, hs, hab, hwidth, hexpand⟩
  have hspos : 0 < s := hp.trans_le hs
  have hR : p^(-η) ≤ (b-a)/s := (le_div_iff₀ hspos).mpr hwidth
  have hRpos : 0 < (b-a)/s := (Real.rpow_pos_of_pos hp _).trans_le hR
  have hle : ((b-a)/s)^(1-ε) ≤ C*((b-a)/s)^d :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0 (Real.rpow_pos_of_pos hRpos _).le)).mp
      (hexpand.trans (hcover s a b hs hab hwidth))
  exact (not_lt_of_ge hle) (dimension_gap hp hp1 hgap hβ hC hR)

/-- Apply a supplied dichotomy to one sufficiently large restricted triple set.
The actual cover estimate, large-H premise and dichotomy are not manufactured here. -/
theorem lineConcentration_of_dichotomy_and_cover_bound
    {p ε η d β C : ℝ} {A B : Set Plane} {H : Set Triple}
    (hdichotomy : LineConcentration p ε A B ∨ RestrictedExpansion p ε η A B)
    (hH : H ⊆ tripleCarrier A B)
    (hlarge : ENNReal.ofReal (p^(η-3)) ≤ tripleCover p H)
    (hp : 0 < p) (hp1 : p < 1) (hgap : 0 < 1-ε-d)
    (hβ : β < η*(1-ε-d)) (hC0 : 0 ≤ C) (hC : C ≤ p^(-β))
    (hcover : ∀ s a b : ℝ, p ≤ s → a ≤ b → p^(-η)*s ≤ b-a →
      intervalCover s (Icc a b ∩ dotDifferenceImage H) ≤
        ENNReal.ofReal (C*((b-a)/s)^d)) :
    LineConcentration p ε A B := by
  rcases hdichotomy with hline | hexpand
  · exact hline
  · exact False.elim (not_longIntervalExpansion_of_cover_bound hp hp1 hgap hβ hC0 hC hcover
      (hexpand H hH hlarge))

#print axioms dimension_gap
#print axioms not_longIntervalExpansion_of_cover_bound
#print axioms lineConcentration_of_dichotomy_and_cover_bound

end Kakeya4.Hard.RestrictedTriple
