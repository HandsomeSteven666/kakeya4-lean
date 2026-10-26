import Kakeya4.Foundation.Defs.Segment

/-!
# Kakeya sets

The manuscript's Theorem 1.1 is stated for **arbitrary** subsets of `ℝ⁴`: no measurability,
compactness or regularity is assumed. We therefore define `IsKakeya` without any such
hypothesis, and keep the compact version `IsBesicovitch` as a separate predicate for the
comparison with the three-dimensional formalization of Project Numina.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Kakeya4

variable {n : ℕ}

/-- A set is Kakeya if it contains a unit segment in every direction.

This is the hypothesis of the manuscript's Theorem 1.1, with no measurability, compactness
or regularity assumptions. -/
def IsKakeya (n : ℕ) (K : Set (E n)) : Prop :=
  ∀ e ∈ dirSphere n, ∃ a : E n, unitSegment a e ⊆ K

/-- Kakeya property is monotone with respect to inclusion. -/
lemma isKakeya_mono {K L : Set (E n)} (hKL : K ⊆ L) (hK : IsKakeya n K) : IsKakeya n L := by
  intro e he
  obtain ⟨a, ha⟩ := hK e he
  exact ⟨a, ha.trans hKL⟩

/-- The whole space is Kakeya (in every direction, start at the origin). -/
lemma isKakeya_univ : IsKakeya n Set.univ := by
  intro e _
  exact ⟨0, Set.subset_univ _⟩

/-- A compact Kakeya set, i.e. a Besicovitch set. -/
def IsBesicovitch (n : ℕ) (K : Set (E n)) : Prop :=
  IsCompact K ∧ IsKakeya n K

/-- A Besicovitch set is in particular a Kakeya set. -/
lemma IsBesicovitch.isKakeya {K : Set (E n)} (h : IsBesicovitch n K) : IsKakeya n K :=
  h.2

/-- The Kakeya set conjecture in dimension `n` (compact form). -/
def KakeyaSetConjecture (n : ℕ) : Prop :=
  ∀ K : Set (E n), IsBesicovitch n K → dimH K = (n : ℝ≥0∞)

/-- A singleton is not a Kakeya set in positive dimension. -/
lemma not_isKakeya_singleton {n : ℕ} (hn : 0 < n) (x : E n) : ¬ IsKakeya n {x} := by
  rintro h
  obtain ⟨e, he⟩ := exists_unitVec n hn
  obtain ⟨a, ha⟩ := h e (mem_dirSphere.2 he)
  have h1 : a = x := ha (left_mem_unitSegment a e)
  have h2 : a + e = x := ha (right_mem_unitSegment a e)
  have he0 : e = 0 := by
    have h3 : a + e = a := by rw [h2, h1]
    simpa using h3
  rw [he0] at he
  simp at he

end Kakeya4
