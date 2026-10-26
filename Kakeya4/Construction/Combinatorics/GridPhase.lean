import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.ZMod.Basic
import Kakeya4.Foundation.Basic
import Kakeya4.Construction.Combinatorics.DisjointUnionMass

/-!
# Midpoint grid phase for three-dimensional spatial localization

A midpoint is assigned to its half-open unit cube by coordinatewise integer floors. The residue
class modulo five is a finite phase label; this file records only the discrete arithmetic contract.
Geometric separation of tube shades with equal phase is a separate theorem and is not asserted here.
-/

set_option autoImplicit false

namespace Kakeya4.Construction

open scoped ENNReal NNReal

/-- The integer unit-grid cell containing a point of three-dimensional coefficient space. -/
noncomputable def midpointGridCell3 (x : Fin 3 → ℝ) : Fin 3 → ℤ := fun j => ⌊x j⌋

/-- A five-residue coloring of three-dimensional unit-grid cells. -/
noncomputable def midpointGridPhase3 (x : Fin 3 → ℝ) : Fin 3 → ZMod 5 :=
  fun j => (midpointGridCell3 x j : ZMod 5)

/-- Equal midpoint phases force each pair of cell coordinates to differ by a multiple of five. -/
theorem midpointGridPhase3_eq_implies_five_dvd_cell_difference
    (x y : Fin 3 → ℝ) (h : midpointGridPhase3 x = midpointGridPhase3 y) (j : Fin 3) :
    (5 : ℤ) ∣ midpointGridCell3 x j - midpointGridCell3 y j := by
  have hzero : ((midpointGridCell3 x j - midpointGridCell3 y j : ℤ) : ZMod 5) = 0 := by
    rw [Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun h j)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero

/-- Distinct unit-grid cells with the same phase have midpoints separated by more than four
units in at least one coordinate. This is the metric-scale arithmetic input for a later shade
separation proof; it says nothing by itself about tube supports. -/
theorem exists_coordinate_midpoint_separation_of_same_phase
    (x y : Fin 3 → ℝ) (hphase : midpointGridPhase3 x = midpointGridPhase3 y)
    (hcell : midpointGridCell3 x ≠ midpointGridCell3 y) :
    ∃ j, 4 < |x j - y j| := by
  classical
  have hcoord : ∃ j, midpointGridCell3 x j ≠ midpointGridCell3 y j := by
    by_contra h
    push Not at h
    exact hcell (funext h)
  obtain ⟨j, hj⟩ := hcoord
  have hdvd := midpointGridPhase3_eq_implies_five_dvd_cell_difference x y hphase j
  obtain ⟨n, hn⟩ := hdvd
  have hn0 : n ≠ 0 := by
    intro hnzero
    apply hj
    omega
  have hxlo : (midpointGridCell3 x j : ℝ) ≤ x j := Int.floor_le _
  have hyhi : y j < (midpointGridCell3 y j : ℝ) + 1 := Int.lt_floor_add_one _
  have hylo : (midpointGridCell3 y j : ℝ) ≤ y j := Int.floor_le _
  have hxhi : x j < (midpointGridCell3 x j : ℝ) + 1 := Int.lt_floor_add_one _
  by_cases hnpos : 0 < n
  · have hcellGap : (5 : ℤ) ≤ midpointGridCell3 x j - midpointGridCell3 y j := by
      rw [hn]
      omega
    have hcellGapReal : (5 : ℝ) ≤
        (midpointGridCell3 x j : ℝ) - (midpointGridCell3 y j : ℝ) := by
      exact_mod_cast hcellGap
    refine ⟨j, ?_⟩
    rw [abs_of_pos (by linarith)]
    linarith
  · have hnneg : n < 0 := by omega
    have hcellGap : (5 : ℤ) ≤ midpointGridCell3 y j - midpointGridCell3 x j := by
      omega
    have hcellGapReal : (5 : ℝ) ≤
        (midpointGridCell3 y j : ℝ) - (midpointGridCell3 x j : ℝ) := by
      exact_mod_cast hcellGap
    refine ⟨j, ?_⟩
    rw [abs_of_neg (by linarith)]
    linarith

/-- One coordinate displacement in `EuclideanSpace` is bounded by the full Euclidean distance. -/
theorem euclidean_coordinate_abs_sub_le_dist (x y : Kakeya4.E 3) (j : Fin 3) :
    |x.ofLp j - y.ofLp j| ≤ dist x y := by
  rw [dist_eq_norm]
  have h := PiLp.norm_apply_le (x - y) j
  simpa [Pi.sub_apply, Real.norm_eq_abs] using h

/-- Membership in a closed ball in `E 3` yields the coordinate-cube support bound used by the
midpoint-grid separation theorem. -/
theorem euclidean_coordinate_abs_sub_le_of_mem_closedBall
    {x y : Kakeya4.E 3} {R : ℝ} (hxy : x ∈ Metric.closedBall y R) (j : Fin 3) :
    |x.ofLp j - y.ofLp j| ≤ R := by
  exact (euclidean_coordinate_abs_sub_le_dist x y j).trans (Metric.mem_closedBall.mp hxy)

/-- A shade family contained in midpoint-centered closed balls has the explicit coordinate
support required by `exists_midpointGridPhase3_union_measure_ge_const_mul_mass`. -/
theorem euclidean_coordinate_support_of_subset_closedBall
    {ι : Type*} (cells : Finset ι) (midpoint : ι → Kakeya4.E 3)
    (shade : ι → Set (Kakeya4.E 3)) (R : ℝ)
    (hshade : ∀ i ∈ cells, shade i ⊆ Metric.closedBall (midpoint i) R) :
    ∀ i ∈ cells, ∀ z ∈ shade i, ∀ j : Fin 3,
      |z.ofLp j - (midpoint i).ofLp j| ≤ R := by
  intro i hi z hz j
  exact euclidean_coordinate_abs_sub_le_of_mem_closedBall (hshade i hi hz) j

/-- Two points in the same half-open unit grid cell differ by less than one in each
coordinate. -/
theorem abs_sub_lt_one_of_midpointGridCell3_eq
    (x y : Fin 3 → ℝ) (h : midpointGridCell3 x = midpointGridCell3 y) (j : Fin 3) :
    |x j - y j| < 1 := by
  have hxlo : (midpointGridCell3 x j : ℝ) ≤ x j := Int.floor_le _
  have hxhi : x j < (midpointGridCell3 x j : ℝ) + 1 := Int.lt_floor_add_one _
  have hylo : (midpointGridCell3 y j : ℝ) ≤ y j := Int.floor_le _
  have hyhi : y j < (midpointGridCell3 y j : ℝ) + 1 := Int.lt_floor_add_one _
  have hcell : midpointGridCell3 x j = midpointGridCell3 y j := congrFun h j
  have hcellR : (midpointGridCell3 x j : ℝ) = (midpointGridCell3 y j : ℝ) := by
    exact_mod_cast hcell
  rw [abs_lt]
  constructor <;> linarith

/-- The finite type of grid cells occupied by the midpoints of a finite indexed family. -/
def midpointGridCellIndex3 {ι : Type*} (s : Finset ι) (gridCell : ι → Fin 3 → ℤ) :=
  { k : Fin 3 → ℤ // k ∈ s.image gridCell }

noncomputable instance midpointGridCellIndex3.fintype {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (gridCell : ι → Fin 3 → ℤ) :
    Fintype (midpointGridCellIndex3 s gridCell) :=
  Fintype.ofFinset (s.image gridCell) (fun _ => Iff.rfl)

/-- Choose one indexed midpoint as a geometric representative of each occupied grid cell. -/
noncomputable def midpointGridCellRepresentative3 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (gridCell : ι → Fin 3 → ℤ)
    (k : midpointGridCellIndex3 s gridCell) : ι :=
  Classical.choose (Finset.mem_image.mp k.property)

theorem midpointGridCellRepresentative3_spec {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (gridCell : ι → Fin 3 → ℤ)
    (k : midpointGridCellIndex3 s gridCell) :
    midpointGridCellRepresentative3 s gridCell k ∈ s ∧
      gridCell (midpointGridCellRepresentative3 s gridCell k) = k.val :=
  Classical.choose_spec (Finset.mem_image.mp k.property)

/-- The shading carried by every original index whose midpoint occupies a specified grid
cell. Repeated geometric cells are grouped before phase selection, so no injectivity assumption
on the original family is needed. -/
def midpointGridCellShade3 {α ι : Type*}
    (s : Finset ι) (gridCell : ι → Fin 3 → ℤ) (shade : ι → Set α)
    (k : midpointGridCellIndex3 s gridCell) : Set α :=
  ⋃ i ∈ s.filter (fun i => gridCell i = k.val), shade i

/-- The shade carried by all original indices in a given (possibly unoccupied) grid cell. -/
def midpointGridCellShade3At {α ι : Type*}
    (s : Finset ι) (gridCell : ι → Fin 3 → ℤ) (shade : ι → Set α)
    (k : Fin 3 → ℤ) : Set α :=
  ⋃ i ∈ s.filter (fun i => gridCell i = k), shade i

/-- Grouping a finite tube-indexed family by its midpoint grid cells yields one shade per
occupied cell. If every original shade lies in a midpoint-centered closed ball of radius `R<1`,
each grouped shade lies in a coordinate cube of radius `R+1<2` about a representative midpoint.
This is the finite-index adapter needed before applying the mod-five phase-union estimate. -/
theorem midpointGridCellShade3_coordinate_support
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (midpoint : ι → Kakeya4.E 3) (shade : ι → Set (Kakeya4.E 3)) (R : ℝ)
    (hR : R < 1)
    (hshade : ∀ i ∈ s, shade i ⊆ Metric.closedBall (midpoint i) R)
    (k : midpointGridCellIndex3 s (fun i => midpointGridCell3 (midpoint i).ofLp)) :
    (∀ z ∈ midpointGridCellShade3 s
        (fun i => midpointGridCell3 (midpoint i).ofLp) shade k, ∀ j : Fin 3,
      |z.ofLp j - (midpoint (midpointGridCellRepresentative3 s
        (fun i => midpointGridCell3 (midpoint i).ofLp) k)).ofLp j| ≤ R + 1) ∧ R + 1 < 2 := by
  classical
  have hcoord : ∀ z ∈ midpointGridCellShade3 s
      (fun i => midpointGridCell3 (midpoint i).ofLp) shade k, ∀ j : Fin 3,
      |z.ofLp j - (midpoint (midpointGridCellRepresentative3 s
        (fun i => midpointGridCell3 (midpoint i).ofLp) k)).ofLp j| ≤ R + 1 := by
    intro z hz j
    rcases Set.mem_iUnion.mp hz with ⟨i, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hi, hzi⟩
    have hi' := Finset.mem_filter.mp hi
    have hrep := midpointGridCellRepresentative3_spec s
      (fun i => midpointGridCell3 (midpoint i).ofLp) k
    have hcell : midpointGridCell3 (midpoint i).ofLp =
        midpointGridCell3 (midpoint (midpointGridCellRepresentative3 s
          (fun i => midpointGridCell3 (midpoint i).ofLp) k)).ofLp :=
      hi'.2.trans hrep.2.symm
    have hmid := abs_sub_lt_one_of_midpointGridCell3_eq
      (midpoint i).ofLp
      (midpoint (midpointGridCellRepresentative3 s
        (fun i => midpointGridCell3 (midpoint i).ofLp) k)).ofLp hcell j
    have hzi' := euclidean_coordinate_abs_sub_le_of_mem_closedBall
      (hshade i hi'.1 hzi) j
    have htriangle := abs_sub_le (z.ofLp j) ((midpoint i).ofLp j)
      ((midpoint (midpointGridCellRepresentative3 s
        (fun i => midpointGridCell3 (midpoint i).ofLp) k)).ofLp j)
    exact htriangle.trans (add_le_add hzi' hmid.le)
  exact ⟨hcoord, by linarith⟩

/-- A grouped cell shade is measurable whenever every original indexed shade is measurable. -/
theorem measurableSet_midpointGridCellShade3
    {α ι : Type*} [MeasurableSpace α] [DecidableEq ι]
    (s : Finset ι) (gridCell : ι → Fin 3 → ℤ) (shade : ι → Set α)
    (hmeas : ∀ i ∈ s, MeasurableSet (shade i))
    (k : midpointGridCellIndex3 s gridCell) :
    MeasurableSet (midpointGridCellShade3 s gridCell shade k) := by
  classical
  exact Finset.measurableSet_biUnion (s.filter (fun i => gridCell i = k.val))
    (fun i hi => hmeas i (Finset.mem_filter.mp hi).1)

theorem measurableSet_midpointGridCellShade3At
    {α ι : Type*} [MeasurableSpace α] [DecidableEq ι]
    (s : Finset ι) (gridCell : ι → Fin 3 → ℤ) (shade : ι → Set α)
    (hmeas : ∀ i ∈ s, MeasurableSet (shade i)) (k : Fin 3 → ℤ) :
    MeasurableSet (midpointGridCellShade3At s gridCell shade k) := by
  classical
  exact Finset.measurableSet_biUnion (s.filter (fun i => gridCell i = k))
    (fun i hi => hmeas i (Finset.mem_filter.mp hi).1)

/-- Shades contained in coordinate cubes of radius `R < 2` around distinct same-phase
midpoints are pairwise disjoint. The support bound is explicit so callers must separately prove
it for their actual tube shades. -/
theorem midpointGridPhase3_shade_pairwiseDisjoint
    {α ι : Type*} [DecidableEq ι] (cells : Finset ι)
    (coordinates : α → Fin 3 → ℝ) (midpoint : ι → α) (shade : ι → Set α)
    (R : ℝ) (hR : R < 2)
    (hcell : ∀ i ∈ cells, ∀ k ∈ cells, i ≠ k →
      midpointGridCell3 (coordinates (midpoint i)) ≠
        midpointGridCell3 (coordinates (midpoint k)))
    (hsupport : ∀ i ∈ cells, ∀ z ∈ shade i, ∀ j,
      |coordinates z j - coordinates (midpoint i) j| ≤ R) :
    ∀ phase, Set.PairwiseDisjoint
      (↑(cells.filter fun i => midpointGridPhase3 (coordinates (midpoint i)) = phase)) shade := by
  classical
  intro phase i hi k hk hik
  have hi' := Finset.mem_filter.mp hi
  have hk' := Finset.mem_filter.mp hk
  have hi_cells : i ∈ cells ∧ midpointGridPhase3 (coordinates (midpoint i)) = phase := hi'
  have hk_cells : k ∈ cells ∧ midpointGridPhase3 (coordinates (midpoint k)) = phase := hk'
  have hgrid : midpointGridCell3 (coordinates (midpoint i)) ≠
      midpointGridCell3 (coordinates (midpoint k)) :=
    hcell i hi_cells.1 k hk_cells.1 hik
  obtain ⟨j, hsep⟩ := exists_coordinate_midpoint_separation_of_same_phase
    (coordinates (midpoint i)) (coordinates (midpoint k))
    (hi_cells.2.trans hk_cells.2.symm) hgrid
  apply Set.disjoint_left.mpr
  intro z hzi hzk
  have hbi := hsupport i hi_cells.1 z hzi j
  have hbk := hsupport k hk_cells.1 z hzk j
  have hcenters :
      |coordinates (midpoint i) j - coordinates (midpoint k) j| ≤ 2 * R := by
    apply abs_le.mpr
    constructor <;> have hbi' := abs_le.mp hbi <;> have hbk' := abs_le.mp hbk <;>
      dsimp at * <;> linarith
  linarith

/-- End-to-end finite aggregation for midpoint-grid colors. The caller supplies distinct grid
cells, coordinate support bounds of radius less than two, measurable shades, and the local mass
estimates; the phase coloring and its disjointness are derived here. -/
theorem exists_midpointGridPhase3_union_measure_ge_const_mul_mass
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
    (μ : MeasureTheory.Measure α) (cells : Finset ι)
    (coordinates : α → Fin 3 → ℝ) (midpoint : ι → α) (shade : ι → Set α)
    (R : ℝ) (hR : R < 2)
    (hcell : ∀ i ∈ cells, ∀ k ∈ cells, i ≠ k →
      midpointGridCell3 (coordinates (midpoint i)) ≠
        midpointGridCell3 (coordinates (midpoint k)))
    (hsupport : ∀ i ∈ cells, ∀ z ∈ shade i, ∀ j,
      |coordinates z j - coordinates (midpoint i) j| ≤ R)
    (mass : ι → ℝ≥0) (c b : ℝ≥0)
    (hphaseMass : (Fintype.card (Fin 3 → ZMod 5) : ℕ) • b ≤ ∑ i ∈ cells, mass i)
    (hmeas : ∀ i ∈ cells, MeasurableSet (shade i))
    (hlocal : ∀ i ∈ cells,
      (c : ℝ≥0∞) * (mass i : ℝ≥0∞) ≤ μ (shade i)) :
    ∃ phase, (c : ℝ≥0∞) * b ≤ μ (⋃ i ∈ cells.filter
      (fun i => midpointGridPhase3 (coordinates (midpoint i)) = phase), shade i) := by
  refine exists_phase_union_measure_ge_const_mul_mass_of_fintype μ cells
    (fun i => midpointGridPhase3 (coordinates (midpoint i))) shade mass c b hphaseMass ?_ hmeas hlocal
  intro phase
  exact midpointGridPhase3_shade_pairwiseDisjoint cells coordinates midpoint shade R hR
    hcell hsupport phase

/-- Closed-ball form of the midpoint-grid weighted union estimate in `E 3`. This is the
Construction-side interface for tube carrier bounds: tube-specific carrier containment, cell
uniqueness, measurability, and local mass estimates remain explicit inputs. -/
theorem exists_midpointGridPhase3_union_measure_ge_const_mul_mass_of_closedBall
    {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace (Kakeya4.E 3)]
    (μ : MeasureTheory.Measure (Kakeya4.E 3)) (cells : Finset ι)
    (midpoint : ι → Kakeya4.E 3) (shade : ι → Set (Kakeya4.E 3))
    (R : ℝ) (hR : R < 2)
    (hcell : ∀ i ∈ cells, ∀ k ∈ cells, i ≠ k →
      midpointGridCell3 ((midpoint i).ofLp) ≠ midpointGridCell3 ((midpoint k).ofLp))
    (hshade : ∀ i ∈ cells, shade i ⊆ Metric.closedBall (midpoint i) R)
    (mass : ι → ℝ≥0) (c b : ℝ≥0)
    (hphaseMass : (Fintype.card (Fin 3 → ZMod 5) : ℕ) • b ≤ ∑ i ∈ cells, mass i)
    (hmeas : ∀ i ∈ cells, MeasurableSet (shade i))
    (hlocal : ∀ i ∈ cells,
      (c : ℝ≥0∞) * (mass i : ℝ≥0∞) ≤ μ (shade i)) :
    ∃ phase, (c : ℝ≥0∞) * b ≤ μ (⋃ i ∈ cells.filter
      (fun i => midpointGridPhase3 ((midpoint i).ofLp) = phase), shade i) := by
  exact exists_midpointGridPhase3_union_measure_ge_const_mul_mass μ cells
    (fun x : Kakeya4.E 3 => x.ofLp) midpoint shade R hR hcell
    (euclidean_coordinate_support_of_subset_closedBall cells midpoint shade R hshade)
    mass c b hphaseMass hmeas hlocal

/-- Group an arbitrary finite indexed midpoint family by its actual unit grid cells and then
apply the mod-five phase union estimate. Duplicate cells in the original family are retained
inside their grouped shade, so callers need not assume tube midpoints occupy distinct cells.
The local mass lower bound is stated for each grouped shade and remains the caller's geometric
obligation. -/
theorem exists_midpointGridPhase3_grouped_union_measure_ge_const_mul_mass
    {ι : Type*} [DecidableEq ι] [MeasurableSpace (Kakeya4.E 3)] (s : Finset ι)
    (μ : MeasureTheory.Measure (Kakeya4.E 3))
    (midpoint : ι → Kakeya4.E 3) (shade : ι → Set (Kakeya4.E 3))
    (R : ℝ) (hR : R < 1)
    (hshade : ∀ i ∈ s, shade i ⊆ Metric.closedBall (midpoint i) R)
    (hmeas : ∀ i ∈ s, MeasurableSet (shade i))
    (mass : midpointGridCellIndex3 s (fun i => midpointGridCell3 (midpoint i).ofLp) → ℝ≥0)
    (c b : ℝ≥0)
    (hphaseMass : (Fintype.card (Fin 3 → ZMod 5) : ℕ) • b ≤ ∑ k, mass k)
    (hlocal : ∀ k, (c : ℝ≥0∞) * (mass k : ℝ≥0∞) ≤
      μ (midpointGridCellShade3 s (fun i => midpointGridCell3 (midpoint i).ofLp) shade k)) :
    ∃ phase, (c : ℝ≥0∞) * b ≤ μ (⋃ k ∈ Finset.univ.filter
      (fun k : midpointGridCellIndex3 s (fun i => midpointGridCell3 (midpoint i).ofLp) =>
        midpointGridPhase3 (midpoint (midpointGridCellRepresentative3 s
          (fun i => midpointGridCell3 (midpoint i).ofLp) k)).ofLp = phase),
      midpointGridCellShade3 s (fun i => midpointGridCell3 (midpoint i).ofLp) shade k) := by
  classical
  let gridCell : ι → Fin 3 → ℤ := fun i => midpointGridCell3 (midpoint i).ofLp
  let Cell := midpointGridCellIndex3 s gridCell
  let grouped : Cell → Set (Kakeya4.E 3) := fun k =>
    midpointGridCellShade3 s gridCell shade k
  let rep : Cell → ι := midpointGridCellRepresentative3 s gridCell
  have hcell : ∀ k : Cell, ∀ hk : k ∈ Finset.univ, ∀ l : Cell,
      l ∈ Finset.univ → k ≠ l →
        midpointGridCell3 (midpoint (rep k)).ofLp ≠
          midpointGridCell3 (midpoint (rep l)).ofLp := by
    intro k hk l hl hne heq
    apply hne
    apply Subtype.ext
    calc
      k.val = gridCell (rep k) := (midpointGridCellRepresentative3_spec s gridCell k).2.symm
      _ = gridCell (rep l) := heq
      _ = l.val := (midpointGridCellRepresentative3_spec s gridCell l).2
  have hsupport : ∀ k ∈ (Finset.univ : Finset Cell), ∀ z ∈ grouped k, ∀ j : Fin 3,
      |z.ofLp j - (midpoint (rep k)).ofLp j| ≤ R + 1 := by
    intro k hk z hz j
    exact (midpointGridCellShade3_coordinate_support s midpoint shade R hR hshade k).1 z hz j
  have hmeasGrouped : ∀ k ∈ (Finset.univ : Finset Cell), MeasurableSet (grouped k) := by
    intro k hk
    exact measurableSet_midpointGridCellShade3 s gridCell shade hmeas k
  have hmass : (Fintype.card (Fin 3 → ZMod 5) : ℕ) • b ≤
      ∑ k ∈ (Finset.univ : Finset Cell), mass k := by
    simpa using hphaseMass
  have hlocalGrouped : ∀ k ∈ (Finset.univ : Finset Cell),
      (c : ℝ≥0∞) * (mass k : ℝ≥0∞) ≤ μ (grouped k) := by
    intro k hk
    simpa [grouped, gridCell] using hlocal k
  exact exists_midpointGridPhase3_union_measure_ge_const_mul_mass μ Finset.univ
    (fun x : Kakeya4.E 3 => x.ofLp) (fun k : Cell => midpoint (rep k)) grouped (R + 1)
    (by linarith) hcell hsupport mass c b hmass hmeasGrouped hlocalGrouped

end Kakeya4.Construction



