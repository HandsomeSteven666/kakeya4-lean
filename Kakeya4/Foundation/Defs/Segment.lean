import Kakeya4.Foundation.Basic

/-!
# Unit segments and directions

The manuscript's basic objects: a *unit segment* starting at `a` in direction `e`, and the
unit sphere of directions `S^{n-1}`.

Note that `unitSegment a e` is the closed segment from `a` to `a + e`. The manuscript writes
`{a + t e : 0 ≤ t ≤ 1}`; `mem_unitSegment_iff` below records exactly this equivalence.
-/

set_option autoImplicit false

namespace Kakeya4

variable {n : ℕ}

/-- The closed unit segment `{a + t • e : 0 ≤ t ≤ 1}`. -/
def unitSegment (a e : E n) : Set (E n) := segment ℝ a (a + e)

/-- Membership in a unit segment, in the form used throughout the manuscript. -/
lemma mem_unitSegment_iff {a e x : E n} :
    x ∈ unitSegment a e ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ a + t • e = x := by
  constructor
  · rintro ⟨α, β, hα, hβ, hαβ, rfl⟩
    refine ⟨β, hβ, by linarith, ?_⟩
    rw [show α = 1 - β by linarith]
    module
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨1 - t, t, by linarith, ht0, by ring, by module⟩

/-- A unit segment is monotone in the ambient set. -/
lemma unitSegment_subset_iff {K : Set (E n)} {a e : E n} :
    unitSegment a e ⊆ K ↔ ∀ t : ℝ, 0 ≤ t → t ≤ 1 → a + t • e ∈ K := by
  constructor
  · intro h t ht0 ht1
    exact h (mem_unitSegment_iff.2 ⟨t, ht0, ht1, rfl⟩)
  · rintro h x hx
    obtain ⟨t, ht0, ht1, rfl⟩ := mem_unitSegment_iff.1 hx
    exact h t ht0 ht1

@[simp]
lemma left_mem_unitSegment (a e : E n) : a ∈ unitSegment a e := by
  rw [mem_unitSegment_iff]
  exact ⟨0, le_rfl, zero_le_one, by simp⟩

@[simp]
lemma right_mem_unitSegment (a e : E n) : a + e ∈ unitSegment a e := by
  rw [mem_unitSegment_iff]
  exact ⟨1, zero_le_one, le_rfl, by simp⟩

/-- The unit sphere of directions `S^{n-1}`. -/
def dirSphere (n : ℕ) : Set (E n) := Metric.sphere (0 : E n) 1

@[simp]
lemma mem_dirSphere {e : E n} : e ∈ dirSphere n ↔ ‖e‖ = 1 := by
  simp [dirSphere]

/-- In positive dimension there is at least one unit direction. -/
lemma exists_unitVec (n : ℕ) (hn : 0 < n) : ∃ e : E n, ‖e‖ = 1 := by
  refine ⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ), ?_⟩
  simp

/-- A nondegenerate unit segment has Hausdorff dimension one. -/
lemma dimH_unitSegment {a e : E n} (he : e ≠ 0) : dimH (unitSegment a e) = 1 := by
  rw [unitSegment, Real.dimH_segment]
  simpa using he

end Kakeya4
