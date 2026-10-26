import Kakeya4.Foundation.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The weighted full-time plank estimate

Statement of the manuscript's `lem:weighted-planks`
(`vendor/openai-math/sections/02-framework.tex#L885-L926`).

Provenance: the 4D manuscript cites this as `[Lemma 2.3]{ThreeDimensional}`, where
`ThreeDimensional` is **OpenAI's own 3D preprint** *The Kakeya maximal conjecture in three
dimensions* (2026-09-23), lemma `lem:weighted-set`. It is **not** a peer-reviewed
Wang–Zahl result. The 3D proof is conditional on the plank cap hypothesis and uses the
preprint's `lem:weighted-convex-set` (weighted convex clustering); neither is formalized.
See `docs/LANDSCAPE.md`.

This module **states** the estimate; it does not prove it. `WeightedPlanks` is a real
proposition (no `sorry`), but it remains an explicit hypothesis of the main theorem.

## Dictionary

| Manuscript | Lean |
| --- | --- |
| `ℝ²` | `Vec2 := E 2` |
| orthonormal frame `(e₁,e₂)` | `OrthonormalFrame` |
| plank `P` of widths `aρ`, `bρ` | `plankSet κ a b ρ c v f` |
| trace `M_i(t) = b_i + t u_i` | `trace (base i) (dir i) t` |
| `M_i ⊂ P` (full time) | `traceContained ...` |
| `∑_{i : M_i ⊂ P} ω_i ≤ A a b` | `CapCondition κ D A ρ base dir ω` |
| time bins `J_i` | `J : Fin n → Finset ℝ` (bin centres on the `ρ`-mesh) |
| `E_vis` | `visitedCells ρ J base dir` |

## Modelling conventions (read before reviewing)

* `chart` is an arbitrary **bounded** set of parameters `(b,u)`. Only boundedness is used by
  the estimate; the affine-line chart structure of the manuscript is not formalized here.
* `κ ≥ 1` is the fixed permitted dilation of the plank tests. It is quantified before `ε`,
  so `η` and `C` may depend on it. The cap condition is required for the dilated tests, with
  right-hand side `A * a * b` as in the manuscript.
* Mesh cells are exact `ρ`-cells. Fixed enlargements are omitted: a fixed enlargement changes
  `#E_vis` by a fixed factor, absorbed into the existential constant `C`. The unenlarged
  version stated here is stronger.
* `J_i` records bin centres `t = kρ`; the mesh condition removes the `⌊·/ρ⌋` boundary
  ambiguity. `#J_i` is the number of bin centres.
* `A = 0` is a degenerate case: the cap condition is then unsatisfiable for any nonempty
  trace family. This is inherited from the manuscript's formulation.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace BigOperators

noncomputable section

namespace Kakeya4

/-- The planar Euclidean space `ℝ²`. -/
abbrev Vec2 : Type := E 2

/-- An orthonormal spatial frame `(e₁,e₂)`. -/
structure OrthonormalFrame where
  e₁ : Vec2
  e₂ : Vec2
  norm_e₁ : ‖e₁‖ = 1
  norm_e₂ : ‖e₂‖ = 1
  inner_eq_zero : inner ℝ e₁ e₂ = 0

namespace Plank

/-- The full-time plank with widths `κ a ρ`, `κ b ρ` and centre line `t ↦ c + t v`,
in the frame `f`. `κ` is the fixed dilation factor. -/
def plankSet (κ a b ρ : ℝ) (c v : Vec2) (f : OrthonormalFrame) : Set (ℝ × Vec2) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧
    |inner ℝ (p.2 - c - p.1 • v) f.e₁| ≤ κ * a * ρ ∧
    |inner ℝ (p.2 - c - p.1 • v) f.e₂| ≤ κ * b * ρ}

/-- The trace `t ↦ base + t • dir`. -/
def trace (base dir : Vec2) (t : ℝ) : Vec2 := base + t • dir

/-- The full trace `t ↦ base + t • dir`, `0 ≤ t ≤ 1`, is contained in the plank. -/
def traceContained (κ a b ρ : ℝ) (c v : Vec2) (f : OrthonormalFrame)
    (base dir : Vec2) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, (t, trace base dir t) ∈ plankSet κ a b ρ c v f

/-- `∑_{i : M_i ⊂ P} ω_i`. -/
def capLHS {n : ℕ} (κ a b ρ : ℝ) (c v : Vec2) (f : OrthonormalFrame)
    (base dir : Fin n → Vec2) (ω : Fin n → ℝ) : ℝ := by
  classical
  exact ∑ i ∈ Finset.univ.filter
    (fun i => traceContained κ a b ρ c v f (base i) (dir i)), ω i

/-- Every full-time plank with `1 ≤ a ≤ b ≤ D` satisfies `∑_{i : M_i ⊂ P} ω_i ≤ A a b`. -/
def CapCondition {n : ℕ} (κ D A ρ : ℝ) (base dir : Fin n → Vec2) (ω : Fin n → ℝ) : Prop :=
  ∀ (a b : ℝ) (c v : Vec2) (f : OrthonormalFrame),
    1 ≤ a → a ≤ b → b ≤ D → capLHS κ a b ρ c v f base dir ω ≤ A * a * b

/-- The index of the spatial-time `ρ`-cell containing `p`. -/
def cellIndex (ρ : ℝ) (p : ℝ × Vec2) : ℤ × ℤ × ℤ :=
  (⌊p.1 / ρ⌋, ⌊p.2 0 / ρ⌋, ⌊p.2 1 / ρ⌋)

/-- The spatial-time mesh cells visited by the traces at the bin centres. -/
def visitedCells {n : ℕ} (ρ : ℝ) (J : Fin n → Finset ℝ) (base dir : Fin n → Vec2) :
    Finset (ℤ × ℤ × ℤ) :=
  Finset.univ.biUnion (fun i =>
    (J i).image (fun t => cellIndex ρ (t, trace (base i) (dir i) t)))

/-- **Weighted full-time plank estimate** (manuscript `lem:weighted-planks`).

Quantifier ledger (the order is part of the statement):
`κ, chart` are fixed before `ε`, so `η` and `C` may depend on them; `n, base, dir, ω, D, A, J`
are universally quantified after `C`, so `C` is uniform in them. -/
def WeightedPlanks : Prop :=
  ∀ (κ : ℝ), 1 ≤ κ →
  ∀ (chart : Set (Vec2 × Vec2)), Bornology.IsBounded chart →
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
  ∀ (n : ℕ) (base dir : Fin n → Vec2), (∀ i, (base i, dir i) ∈ chart) →
  ∀ (ω : Fin n → ℝ), (∀ i, 0 < ω i) →
  ∀ D A : ℝ, 1 ≤ D → 0 ≤ A →
  ∀ J : Fin n → Finset ℝ,
    (∀ i t, t ∈ J i → 0 ≤ t ∧ t ≤ 1 ∧ ∃ k : ℤ, t = k * D⁻¹) →
    (∀ i, D ^ (1 - η) ≤ ((J i).card : ℝ)) →
    CapCondition κ D A D⁻¹ base dir ω →
    (∑ i, ω i * ((J i).card : ℝ)) ≤
      C * A * D ^ ε * ((visitedCells D⁻¹ J base dir).card : ℝ)

/-- `A = ∑ ω` makes the cap condition satisfiable: `CapCondition` is not a contradictory
hypothesis. This is a sanity check on the statement, not part of the manuscript. -/
lemma capCondition_total {n : ℕ} (κ D ρ : ℝ) (base dir : Fin n → Vec2) (ω : Fin n → ℝ)
    (hω : ∀ i, 0 ≤ ω i) : CapCondition κ D (∑ i, ω i) ρ base dir ω := by
  classical
  intro a b c v f ha hab _
  have hle : capLHS κ a b ρ c v f base dir ω ≤ ∑ i, ω i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun i => traceContained κ a b ρ c v f (base i) (dir i))
        Finset.univ) ?_
    intro i _ _
    exact hω i
  have hsum : 0 ≤ ∑ i, ω i := Finset.sum_nonneg (fun i _ => hω i)
  have hab1 : 1 ≤ a * b := by nlinarith
  nlinarith

end Plank

end Kakeya4
