import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Basic.Real.ENatENNReal

/-! The full H-003 manuscript target, independently stated from the mathematical
source arXiv:2210.09581v2, Definition 4.2 and Section 8's Theorem 5.2 restatement.
This module states the target; it does not assert or prove the dichotomy.
Arbitrary sets and every sufficiently large restricted triple set are retained.
Side-h cube covers use radius h/2 closed balls in coordinate l-infinity space.
No source from the unlicensed community candidate is imported or copied. -/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Triple := Plane × Plane × Plane

/-- Side-r closed axis-aligned cubes, with arbitrary centres. Infinite counts stay infinite. -/
def cubeCover {ι : Type*} [Fintype ι] (r : ℝ) (E : Set (ι → ℝ)) : ℝ≥0∞ :=
  (Metric.externalCoveringNumber (Real.toNNReal (r/2)) E : ℝ≥0∞)

def planeCoordinates (z : Plane) : Fin 2 → ℝ := fun i ↦ z i

def tripleCoordinates (t : Triple) : (Fin 3 × Fin 2) → ℝ :=
  fun ji ↦ (![t.1, t.2.1, t.2.2] ji.1) ji.2

def planeCover (r : ℝ) (E : Set Plane) : ℝ≥0∞ := cubeCover r (planeCoordinates '' E)

def tripleCover (r : ℝ) (H : Set Triple) : ℝ≥0∞ := cubeCover r (tripleCoordinates '' H)

/-- Side-r intervals, in the same convention as side-r planar/six-dimensional cubes. -/
def intervalCover (r : ℝ) (E : Set ℝ) : ℝ≥0∞ :=
  (Metric.externalCoveringNumber (Real.toNNReal (r/2)) E : ℝ≥0∞)

def unitSquare : Set Plane := {z | ∀ i, 0 ≤ z i ∧ z i ≤ 1}

/-- Only an upper bound; there is no Ahlfors lower bound or cardinality assumption. -/
def ADUpperBound (p C : ℝ) (E : Set Plane) : Prop :=
  ∀ (z : Plane) (s w : ℝ), p ≤ s → s ≤ w →
    planeCover s (E ∩ ball z w) ≤ ENNReal.ofReal (C*w/s)

structure AffineLine where
  anchor : Plane
  direction : Plane
  direction_unit : ‖direction‖ = 1

def lineCarrier (L : AffineLine) : Set Plane := Set.range (fun t : ℝ ↦ L.anchor + t • L.direction)

def lineNeighborhood (p : ℝ) (L : AffineLine) : Set Plane := cthickening p (lineCarrier L)

/-- Both affine lines are free; their directions must be exactly perpendicular. -/
def LineConcentration (p ε : ℝ) (A B : Set Plane) : Prop :=
  ∃ L M : AffineLine, inner ℝ L.direction M.direction = 0 ∧
    ENNReal.ofReal (p^(ε-1)) ≤ planeCover p (A ∩ lineNeighborhood p L) ∧
    ENNReal.ofReal (p^(ε-1)) ≤ planeCover p (B ∩ lineNeighborhood p M)

def tripleCarrier (A B : Set Plane) : Set Triple :=
  {t | t.1 ∈ A ∧ t.2.1 ∈ B ∧ t.2.2 ∈ B}

def dotDifference (t : Triple) : ℝ := inner ℝ t.1 (t.2.1-t.2.2)

def dotDifferenceImage (H : Set Triple) : Set ℝ := dotDifference '' H

/-- Every large restricted triple set, not just the full Cartesian product. -/
def RestrictedExpansion (p ε η : ℝ) (A B : Set Plane) : Prop :=
  ∀ H : Set Triple, H ⊆ tripleCarrier A B →
    ENNReal.ofReal (p^(η-3)) ≤ tripleCover p H →
      ∃ s a b : ℝ, p ≤ s ∧ a ≤ b ∧ p^(-η)*s ≤ b-a ∧
        ENNReal.ofReal (((b-a)/s)^(1-ε)) ≤
          intervalCover s (Icc a b ∩ dotDifferenceImage H)

/-- Full manuscript H-003 statement. The proof and source-convention adapters remain obligations. -/
def ManuscriptDotProductAlternative : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
    ∀ p : ℝ, 0 < p → p ≤ δ₀ → ∀ A B : Set Plane,
      A ⊆ unitSquare → B ⊆ unitSquare →
      ADUpperBound p (p^(-η)) A → ADUpperBound p (p^(-η)) B →
        LineConcentration p ε A B ∨ RestrictedExpansion p ε η A B

end Kakeya4.Hard.RestrictedTriple
