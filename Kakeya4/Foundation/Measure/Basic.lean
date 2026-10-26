import Kakeya4.Foundation.Defs.Kakeya

/-!
# Elementary Hausdorff-dimension bounds

The upper bound `dimH K ≤ 4` for every subset of `ℝ⁴` is elementary and is proved here
without `sorry`. It is the easy half of the main theorem.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Kakeya4

/-- The full space `ℝⁿ` has Hausdorff dimension `n`. -/
lemma dimH_univ_E (n : ℕ) : dimH (Set.univ : Set (E n)) = (n : ℝ≥0∞) := by
  rw [Real.dimH_univ_eq_finrank]
  simp [E]

/-- Every subset of `ℝ⁴` has Hausdorff dimension at most four. -/
lemma dimH_le_four (K : Set (E 4)) : dimH K ≤ (4 : ℝ≥0∞) := by
  calc dimH K ≤ dimH (Set.univ : Set (E 4)) := dimH_mono (Set.subset_univ K)
    _ = (4 : ℝ≥0∞) := dimH_univ_E 4

end Kakeya4
