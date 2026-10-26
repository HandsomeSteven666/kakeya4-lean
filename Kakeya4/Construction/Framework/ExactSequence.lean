import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Fixed exact sequences for §2

This file encodes the resolution sequence and the scale `a_r = N₀^{-r}`.
Subpower semantics, subsequence closure, and configuration-uniform bounds are intentionally
left to the Foundation F-001 interface.
-/

set_option autoImplicit false

open Filter Topology

namespace Kakeya4.Framework

/-- One exact sequence with resolution tending to infinity and a fixed positive length. -/
structure ExactSequence where
  resolution : ℕ → ℝ
  resolution_ge_one : ∀ n, 1 ≤ resolution n
  resolution_tendsto_top : Tendsto resolution atTop atTop
  length : ℝ
  length_pos : 0 < length

/-- A legal depth in the fixed interval `[0,L]` of an exact sequence. -/
structure Depth (seq : ExactSequence) where
  value : ℝ
  value_nonneg : 0 ≤ value
  value_le_length : value ≤ seq.length

/-- The resolution scale `a_r=N₀^{-r}` along an exact sequence. -/
noncomputable def ExactSequence.scale (seq : ExactSequence) (r : ℝ) (n : ℕ) : ℝ :=
  seq.resolution n ^ (-r)

/-- Every exact-sequence scale is positive. -/
theorem ExactSequence.scale_pos (seq : ExactSequence) (r : ℝ) (n : ℕ) :
    0 < seq.scale r n := by
  unfold ExactSequence.scale
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (seq.resolution_ge_one n)) _

/-- At nonnegative depth, the resolution scale is at most one. -/
theorem ExactSequence.scale_le_one (seq : ExactSequence) (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    seq.scale r n ≤ 1 := by
  unfold ExactSequence.scale
  exact Real.rpow_le_one_of_one_le_of_nonpos (seq.resolution_ge_one n) (neg_nonpos.mpr hr)

/-- Depth zero has unit scale. -/
theorem ExactSequence.scale_zero (seq : ExactSequence) (n : ℕ) :
    seq.scale 0 n = 1 := by
  simp [ExactSequence.scale]

/-- Resolution depth packaged with its sequence, matching the manuscript's `0 ≤ r ≤ L`. -/
noncomputable def ExactSequence.depthScale (seq : ExactSequence) (r : Depth seq) (n : ℕ) : ℝ :=
  seq.scale r.value n

theorem ExactSequence.depthScale_pos (seq : ExactSequence) (r : Depth seq) (n : ℕ) :
    0 < seq.depthScale r n :=
  seq.scale_pos r.value n

theorem ExactSequence.depthScale_le_one (seq : ExactSequence) (r : Depth seq) (n : ℕ) :
    seq.depthScale r n ≤ 1 :=
  seq.scale_le_one r.value r.value_nonneg n

end Kakeya4.Framework
