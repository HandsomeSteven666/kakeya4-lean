import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Basic conventions

The ambient space is `E n = ℝⁿ`, realized as `EuclideanSpace ℝ (Fin n)`.
All definitions in this repository are stated for arbitrary `n` when possible;
the four-dimensional theorem is the case `n = 4`.

We deliberately do **not** assume measurability, compactness or any regularity
on Kakeya sets: the manuscript's Theorem 1.1 is stated for arbitrary subsets of `ℝ⁴`.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Kakeya4

/-- The ambient Euclidean space `ℝⁿ`. -/
abbrev E (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

end Kakeya4
