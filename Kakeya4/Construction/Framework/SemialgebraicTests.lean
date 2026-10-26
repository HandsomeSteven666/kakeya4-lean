import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Algebra.MvPolynomial
import Kakeya4.Construction.Framework.PriorDensity

/-!
# Finite semialgebraic test syntax and complexity

This file encodes a real polynomial sign formula by a finite syntax tree. It records actual
variable count, atom count, and maximal individual total degree, and proves that the denoted set
is measurable. It is a reusable component for the complexity clause of tempered data; it does
not assert polynomial dependence on the exact-sequence scale or encode every other tempered
field.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Framework

/-- A finite Boolean combination of polynomial equality and nonnegativity tests on `ℝ^n`.
Arbitrary real coefficients are allowed; no height bound is part of the syntax. -/
inductive PolynomialBooleanFormula (n : ℕ) : Type
  | truth : PolynomialBooleanFormula n
  | falsity : PolynomialBooleanFormula n
  | nonnegative (p : MvPolynomial (Fin n) ℝ) : PolynomialBooleanFormula n
  | equalZero (p : MvPolynomial (Fin n) ℝ) : PolynomialBooleanFormula n
  | complement (φ : PolynomialBooleanFormula n) : PolynomialBooleanFormula n
  | conjunction (φ ψ : PolynomialBooleanFormula n) : PolynomialBooleanFormula n
  | disjunction (φ ψ : PolynomialBooleanFormula n) : PolynomialBooleanFormula n

namespace PolynomialBooleanFormula

/-- Truth value of a polynomial Boolean formula at a point. -/
def Holds {n : ℕ} : PolynomialBooleanFormula n → (Fin n → ℝ) → Prop
  | .truth, _ => True
  | .falsity, _ => False
  | .nonnegative p, x => 0 ≤ MvPolynomial.eval x p
  | .equalZero p, x => MvPolynomial.eval x p = 0
  | .complement φ, x => ¬ Holds φ x
  | .conjunction φ ψ, x => Holds φ x ∧ Holds ψ x
  | .disjunction φ ψ, x => Holds φ x ∨ Holds ψ x

/-- The set defined by a polynomial Boolean formula. -/
def models {n : ℕ} (φ : PolynomialBooleanFormula n) : Set (Fin n → ℝ) :=
  {x | Holds φ x}

/-- Number of polynomial test occurrences in the syntax tree, counting repetitions. -/
def atomCount {n : ℕ} : PolynomialBooleanFormula n → ℕ
  | .truth | .falsity => 0
  | .nonnegative _ | .equalZero _ => 1
  | .complement φ => atomCount φ
  | .conjunction φ ψ | .disjunction φ ψ => atomCount φ + atomCount ψ

/-- Maximum total degree of any polynomial atom; constants and atom-free formulas have degree 0. -/
def maxAtomDegree {n : ℕ} : PolynomialBooleanFormula n → ℕ
  | .truth | .falsity => 0
  | .nonnegative p | .equalZero p => p.totalDegree
  | .complement φ => maxAtomDegree φ
  | .conjunction φ ψ | .disjunction φ ψ => max (maxAtomDegree φ) (maxAtomDegree ψ)

/-- Polynomial sign formulas denote measurable (hence Borel) subsets of their Euclidean
coordinate space. The proof uses continuity of multivariate polynomial evaluation. -/
theorem measurableSet_models {n : ℕ} (φ : PolynomialBooleanFormula n)
    [MeasurableSpace (Fin n → ℝ)] [BorelSpace (Fin n → ℝ)] :
    MeasurableSet φ.models := by
  induction φ with
  | truth => exact MeasurableSet.univ
  | falsity => exact MeasurableSet.empty
  | nonnegative p =>
      change MeasurableSet {x : Fin n → ℝ | 0 ≤ MvPolynomial.eval x p}
      have hclosed : IsClosed {x : Fin n → ℝ | 0 ≤ MvPolynomial.eval x p} :=
        isClosed_Ici.preimage (MvPolynomial.continuous_eval p)
      exact hclosed.measurableSet
  | equalZero p =>
      change MeasurableSet {x : Fin n → ℝ | MvPolynomial.eval x p = 0}
      have hclosed : IsClosed {x : Fin n → ℝ | MvPolynomial.eval x p = 0} :=
        isClosed_singleton.preimage (MvPolynomial.continuous_eval p)
      exact hclosed.measurableSet
  | complement φ ih =>
      change MeasurableSet (φ.modelsᶜ)
      exact ih.compl
  | conjunction φ ψ ihφ ihψ =>
      change MeasurableSet (φ.models ∩ ψ.models)
      exact ihφ.inter ihψ
  | disjunction φ ψ ihφ ihψ =>
      change MeasurableSet (φ.models ∪ ψ.models)
      exact ihφ.union ihψ

end PolynomialBooleanFormula

/-- One polynomial predicate together with explicit uniform bounds on its arity, number of
polynomial atoms, and degree. This represents complexity inputs; it does not claim that the
bounds are polynomial in a scale parameter. -/
structure BoundedPolynomialTest (variableBound atomBound degreeBound : ℕ) where
  variableCount : ℕ
  variableCount_le : variableCount ≤ variableBound
  formula : PolynomialBooleanFormula variableCount
  atomCount_le : formula.atomCount ≤ atomBound
  degree_le : formula.maxAtomDegree ≤ degreeBound

/-- A finite family of polynomial predicates with explicit bounds on family size, variable
count, atoms per test, and individual total degree. -/
structure BoundedPolynomialTestFamily
    (testBound variableBound atomBound degreeBound : ℕ) where
  testCount : ℕ
  testCount_le : testCount ≤ testBound
  test : Fin testCount → BoundedPolynomialTest variableBound atomBound degreeBound

/-- A finite piecewise-constant density certificate whose pieces are genuinely represented by
polynomial Boolean formulas. Every complexity bound is an explicit finite-scale input; this
structure does not assert that these bounds are polynomial functions of `N₀`. -/
structure SemialgebraicPiecewiseDensityCertificate
    {n : ℕ} [MeasurableSpace (Fin n → ℝ)] [BorelSpace (Fin n → ℝ)]
    (reference prior : Measure (Fin n → ℝ))
    (pieceBound variableBound atomBound degreeBound : ℕ)
    (densityBound : ℝ≥0∞) where
  pieceCount : ℕ
  pieceCount_le : pieceCount ≤ pieceBound
  variableCount_le : n ≤ variableBound
  pieces : Fin pieceCount → PolynomialBooleanFormula n
  atoms_per_piece_le : ∀ i, (pieces i).atomCount ≤ atomBound
  degree_per_piece_le : ∀ i, (pieces i).maxAtomDegree ≤ degreeBound
  pieces_pairwise_disjoint :
    Set.PairwiseDisjoint Set.univ (fun i => (pieces i).models)
  pieces_cover : (⋃ i, (pieces i).models) = Set.univ
  density : (Fin n → ℝ) → ℝ≥0∞
  density_measurable : Measurable density
  value : Fin pieceCount → ℝ≥0∞
  density_eq_value : ∀ i x, x ∈ (pieces i).models → density x = value i
  densityBound_lt_top : densityBound < ∞
  density_le_bound : ∀ x, density x ≤ densityBound
  prior_eq_withDensity : prior = reference.withDensity density

namespace SemialgebraicPiecewiseDensityCertificate

variable {n : ℕ} [MeasurableSpace (Fin n → ℝ)] [BorelSpace (Fin n → ℝ)]
  {reference prior : Measure (Fin n → ℝ)}
  {pieceBound variableBound atomBound degreeBound : ℕ} {densityBound : ℝ≥0∞}

private def duplicatedPieceIndex (p : ℕ) (i : Fin (2 * p)) : Fin p :=
  if h : i.val < p then ⟨i.val, h⟩ else ⟨i.val - p, by have hi := i.isLt; omega⟩

private def eventSplitFormula {n : ℕ} (p : ℕ)
    (piece : Fin p → PolynomialBooleanFormula n) (event : PolynomialBooleanFormula n)
    (i : Fin (2 * p)) : PolynomialBooleanFormula n :=
  .conjunction (piece (duplicatedPieceIndex p i))
    (if i.val < p then event else .complement event)

/-- Forget the polynomial syntax while preserving the finite measurable piecewise-density
certificate used by the existing prior-density transport API. -/
noncomputable def toFinitePiecewiseDensityCertificate
    (C : SemialgebraicPiecewiseDensityCertificate reference prior
      pieceBound variableBound atomBound degreeBound densityBound) :
    FinitePiecewiseDensityCertificate reference prior where
  pieceCount := C.pieceCount
  pieces i := (C.pieces i).models
  pieces_measurable _ := PolynomialBooleanFormula.measurableSet_models _
  pieces_pairwise_disjoint := C.pieces_pairwise_disjoint
  pieces_cover := C.pieces_cover
  density := C.density
  density_measurable := C.density_measurable
  value := C.value
  density_eq_value := C.density_eq_value
  prior_eq_withDensity := C.prior_eq_withDensity

/-- Restrict a semialgebraic density-certified prior to a measurable event without losing the
finite polynomial-piece data. The reference measure is restricted in parallel, so the same
density and the same piece/variable/atom/degree bounds remain valid. The result is an
unnormalized restricted prior; no positive-mass or normalization claim is made. -/
noncomputable def restrict
    (C : SemialgebraicPiecewiseDensityCertificate reference prior
      pieceBound variableBound atomBound degreeBound densityBound)
    (s : Set (Fin n → ℝ)) (hs : MeasurableSet s) :
    SemialgebraicPiecewiseDensityCertificate (reference.restrict s) (prior.restrict s)
      pieceBound variableBound atomBound degreeBound densityBound where
  pieceCount := C.pieceCount
  pieceCount_le := C.pieceCount_le
  variableCount_le := C.variableCount_le
  pieces := C.pieces
  atoms_per_piece_le := C.atoms_per_piece_le
  degree_per_piece_le := C.degree_per_piece_le
  pieces_pairwise_disjoint := C.pieces_pairwise_disjoint
  pieces_cover := C.pieces_cover
  density := C.density
  density_measurable := C.density_measurable
  value := C.value
  density_eq_value := C.density_eq_value
  densityBound_lt_top := C.densityBound_lt_top
  density_le_bound := C.density_le_bound
  prior_eq_withDensity := by
    calc
      prior.restrict s = (reference.withDensity C.density).restrict s := by
        exact congrArg (fun μ : Measure (Fin n → ℝ) => μ.restrict s) C.prior_eq_withDensity
      _ = (reference.restrict s).withDensity C.density := restrict_withDensity hs C.density

/-- Restrict a semialgebraic prior to an event formula while keeping the original reference
measure. The event indicator is absorbed into the density; each old partition piece is split
into its event and complement parts. The output records the resulting losses explicitly:
twice as many pieces, atom bound increased by the event's atom count, and degree bound the maximum
of the old and event degrees. The prior remains unnormalized. -/
noncomputable def restrictByFormula
    (C : SemialgebraicPiecewiseDensityCertificate reference prior
      pieceBound variableBound atomBound degreeBound densityBound)
    (event : PolynomialBooleanFormula n) :
    SemialgebraicPiecewiseDensityCertificate reference (prior.restrict event.models)
      (2 * pieceBound) variableBound (atomBound + event.atomCount)
      (max degreeBound event.maxAtomDegree) densityBound := by
  classical
  let splitPiece : Fin (2 * C.pieceCount) → PolynomialBooleanFormula n :=
    eventSplitFormula C.pieceCount C.pieces event
  let splitDensity : (Fin n → ℝ) → ℝ≥0∞ :=
    fun x => if x ∈ event.models then C.density x else 0
  let splitValue : Fin (2 * C.pieceCount) → ℝ≥0∞ := fun i =>
    if h : i.val < C.pieceCount then
      C.value (duplicatedPieceIndex C.pieceCount i)
    else 0
  refine
    { pieceCount := 2 * C.pieceCount
      pieceCount_le := Nat.mul_le_mul_left 2 C.pieceCount_le
      variableCount_le := C.variableCount_le
      pieces := splitPiece
      atoms_per_piece_le := ?_
      degree_per_piece_le := ?_
      pieces_pairwise_disjoint := ?_
      pieces_cover := ?_
      density := splitDensity
      density_measurable := ?_
      value := splitValue
      density_eq_value := ?_
      densityBound_lt_top := C.densityBound_lt_top
      density_le_bound := ?_
      prior_eq_withDensity := ?_ }
  · intro i
    change (C.pieces (duplicatedPieceIndex C.pieceCount i)).atomCount +
        (if i.val < C.pieceCount then event else .complement event).atomCount ≤
          atomBound + event.atomCount
    have hsplit :
        (if i.val < C.pieceCount then event else .complement event).atomCount =
          event.atomCount := by
      by_cases h : i.val < C.pieceCount <;>
        simp [h, PolynomialBooleanFormula.atomCount]
    rw [hsplit]
    exact Nat.add_le_add (C.atoms_per_piece_le (duplicatedPieceIndex C.pieceCount i)) le_rfl
  · intro i
    change (eventSplitFormula C.pieceCount C.pieces event i).maxAtomDegree ≤
      max degreeBound event.maxAtomDegree
    have hdegree :
        (eventSplitFormula C.pieceCount C.pieces event i).maxAtomDegree =
          max (C.pieces (duplicatedPieceIndex C.pieceCount i)).maxAtomDegree
            event.maxAtomDegree := by
      by_cases hi : i.val < C.pieceCount <;>
        simp [eventSplitFormula, PolynomialBooleanFormula.maxAtomDegree, hi]
    rw [hdegree]
    exact max_le_max (C.degree_per_piece_le _) le_rfl
  · intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro x hix hjx
    change (splitPiece i).Holds x at hix
    change (splitPiece j).Holds x at hjx
    by_cases hi : i.val < C.pieceCount <;> by_cases hj : j.val < C.pieceCount
    · simp [splitPiece, eventSplitFormula, hi, hj, PolynomialBooleanFormula.Holds] at hix hjx
      have hidx : duplicatedPieceIndex C.pieceCount i ≠ duplicatedPieceIndex C.pieceCount j := by
        intro heq
        apply hij
        apply Fin.ext
        have hval := congrArg Fin.val heq
        simp [duplicatedPieceIndex, hi, hj] at hval
        omega
      exact (Set.disjoint_left.mp
        (C.pieces_pairwise_disjoint (Set.mem_univ _) (Set.mem_univ _) hidx)) hix.1 hjx.1
    · simp [splitPiece, eventSplitFormula, hi, hj, PolynomialBooleanFormula.Holds] at hix hjx
      exact hjx.2 hix.2
    · simp [splitPiece, eventSplitFormula, hi, hj, PolynomialBooleanFormula.Holds] at hix hjx
      exact hix.2 hjx.2
    · simp [splitPiece, eventSplitFormula, hi, hj, PolynomialBooleanFormula.Holds] at hix hjx
      have hidx : duplicatedPieceIndex C.pieceCount i ≠ duplicatedPieceIndex C.pieceCount j := by
        intro heq
        apply hij
        apply Fin.ext
        have hval := congrArg Fin.val heq
        simp [duplicatedPieceIndex, hi, hj] at hval
        omega
      exact (Set.disjoint_left.mp
        (C.pieces_pairwise_disjoint (Set.mem_univ _) (Set.mem_univ _) hidx)) hix.1 hjx.1
  · ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      have hxcover : x ∈ ⋃ i : Fin C.pieceCount, (C.pieces i).models := by
        rw [C.pieces_cover]
        exact Set.mem_univ x
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxcover
      change (C.pieces i).Holds x at hi
      by_cases hevent : x ∈ event.models
      · change event.Holds x at hevent
        let j : Fin (2 * C.pieceCount) := ⟨i.val, by have hi' := i.isLt; omega⟩
        have hj : j.val < C.pieceCount := by
          change i.val < C.pieceCount
          exact i.isLt
        have hidx : duplicatedPieceIndex C.pieceCount j = i := by
          apply Fin.ext
          simp [duplicatedPieceIndex, j, hj]
        refine Set.mem_iUnion.mpr ⟨j, ?_⟩
        simp only [splitPiece, eventSplitFormula, PolynomialBooleanFormula.models,
          PolynomialBooleanFormula.Holds, Set.mem_ofPred_eq]
        simpa [hj, hidx] using And.intro hi hevent
      · let j : Fin (2 * C.pieceCount) :=
          ⟨C.pieceCount + i.val, by have hi' := i.isLt; omega⟩
        change ¬ event.Holds x at hevent
        have hj : ¬ j.val < C.pieceCount := by
          have hi' := i.isLt
          simp only [j]
          omega
        have hidx : duplicatedPieceIndex C.pieceCount j = i := by
          apply Fin.ext
          simp [duplicatedPieceIndex, j, hj]
        refine Set.mem_iUnion.mpr ⟨j, ?_⟩
        simp only [splitPiece, eventSplitFormula, PolynomialBooleanFormula.models,
          PolynomialBooleanFormula.Holds, Set.mem_ofPred_eq]
        have hevent' : event.complement.Holds x := by
          change ¬ event.Holds x
          exact hevent
        simpa [hj, hidx] using And.intro hi hevent'
  · dsimp [splitDensity]
    exact Measurable.ite event.measurableSet_models C.density_measurable measurable_const
  · intro i x hx
    change (splitPiece i).Holds x at hx
    by_cases hi : i.val < C.pieceCount
    · simp [splitPiece, eventSplitFormula, hi, PolynomialBooleanFormula.Holds] at hx
      have hvalue := C.density_eq_value (duplicatedPieceIndex C.pieceCount i) x hx.1
      simp [splitDensity, splitValue, hi, hx.2, hvalue, PolynomialBooleanFormula.models]
    · simp [splitPiece, eventSplitFormula, hi, PolynomialBooleanFormula.Holds] at hx
      simp [splitDensity, splitValue, hi, hx.2, PolynomialBooleanFormula.models]
  · intro x
    by_cases hx : x ∈ event.models <;> simp [splitDensity, hx]
    · exact C.density_le_bound x
  · calc
      prior.restrict event.models =
          (reference.withDensity C.density).restrict event.models := by
            exact congrArg (fun μ : Measure (Fin n → ℝ) => μ.restrict event.models)
              C.prior_eq_withDensity
      _ = (reference.restrict event.models).withDensity C.density :=
        restrict_withDensity event.measurableSet_models C.density
      _ = reference.withDensity (event.models.indicator C.density) :=
        (withDensity_indicator event.measurableSet_models C.density).symm
      _ = reference.withDensity splitDensity := by
        congr 1

end SemialgebraicPiecewiseDensityCertificate

end Kakeya4.Framework
