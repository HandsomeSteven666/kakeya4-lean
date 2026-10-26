import Kakeya4.Hard.Analysis.RegularFibers
import Kakeya4.Hard.Analysis.SelectorVolume

/-!
# Component bounds supply the regular-fiber input to selector volume

The only component-count assumption is stated explicitly. The passage from nonzero
Jacobian to isolated fiber point and then to the required multiplicity bound is proved.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace Kakeya4.Hard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A single regular `C¹` point has a genuinely injective open neighborhood, without
restricting that neighborhood to the regular locus. -/
theorem exists_open_injOn_of_regular_derivative (f : E → E) (A : E →L[ℝ] E) (x : E)
    (hC : ContDiffAt ℝ 1 f x) (hD : HasFDerivAt f A x) (hdet : A.det ≠ 0) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ InjOn f U := by
  let L := A.toContinuousLinearEquivOfDetNeZero hdet
  have hL : HasFDerivAt f (L : E →L[ℝ] E) x := by
    simpa only [L, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using hD
  let e := hC.toOpenPartialHomeomorph f hL one_ne_zero
  exact ⟨e.source, e.open_source, hC.mem_toOpenPartialHomeomorph_source hL one_ne_zero, e.injOn⟩

/-- A component bound on the full selected-line fiber bounds its regular preimages. -/
theorem regular_slope_fiber_bound_of_components (b₀ : E → E) (Db : E → E →L[ℝ] E)
    (S : Set E) (hbC : ∀ s ∈ S, ContDiffAt ℝ 1 b₀ s)
    (hbD : ∀ s ∈ S, HasFDerivAt b₀ (Db s) s) (t : ℝ) (N : ℕ)
    (hcomponents : ∀ y, ENat.card (ConnectedComponents {s ∈ S | slopeMap b₀ t s = y}) ≤ N) :
    ∀ y, {s ∈ S | (slopeDerivative Db t s).det ≠ 0 ∧ slopeMap b₀ t s = y}.encard ≤ N := by
  apply encard_regular_fiber_le_of_components_bound (slopeMap b₀ t) S
    (fun s => (slopeDerivative Db t s).det ≠ 0) N ?_ hcomponents
  intro s hs hdet
  obtain ⟨U, hU, hsU, hinj⟩ := exists_open_injOn_of_regular_derivative (slopeMap b₀ t)
    (slopeDerivative Db t s) s (contDiffAt_slopeMap (hbC s hs) t)
    (hasFDerivAt_slopeMap (hbD s hs) t) hdet
  exact ⟨U, hU, hsU, hinj.mono inter_subset_right⟩

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Selector volume with the exact topological input that the parameter-uniform
semialgebraic argument is required to produce. This component bound is not proved here. -/
theorem selector_volume_bound_of_components (μ : Measure E) [IsAddHaarMeasure μ]
    (b₀ : E → E) (Db : E → E →L[ℝ] E) (u v : E → ℝ)
    (hDim : Module.finrank ℝ E = 3)
    (S : Set E) (hS : MeasurableSet S) (a b M : ℝ) (hab : a < b) (hM : 0 < M)
    (hDb : Measurable Db) (hu : Measurable u) (hv : Measurable v)
    (hbC : ∀ s ∈ S, ContDiffAt ℝ 1 b₀ s)
    (hbD : ∀ s ∈ S, HasFDerivAt b₀ (Db s) s)
    (hwitness : ∀ s ∈ S, ∃ t₀ ∈ Icc a b, M ≤ |u s * t₀ + v s|)
    (T : ℝ → Set E) (hT : ∀ t, MeasurableSet (T t)) (N : ℕ)
    (hmap : ∀ t ∈ Icc a b, MapsTo (slopeMap b₀ t)
      {s ∈ S | (t, s) ∈ selectorGoodSet Db u v (b - a) M} (T t))
    (hcomponents : ∀ t ∈ Icc a b, ∀ y,
      ENat.card (ConnectedComponents {s ∈ S | slopeMap b₀ t s = y}) ≤ N)
    (H : ℝ) (hvol : ∀ t ∈ Icc a b, μ (T t) ≤ ENNReal.ofReal H) :
    μ S ≤ ENNReal.ofReal (27648 * (N : ℝ) * H / (b - a) ^ 3) := by
  exact selector_volume_bound μ b₀ Db u v hDim S hS a b M hab hM hDb hu hv hbC hbD
    hwitness T hT N hmap
    (fun t ht => regular_slope_fiber_bound_of_components b₀ Db S hbC hbD t N (hcomponents t ht))
    H hvol

end Kakeya4.Hard
