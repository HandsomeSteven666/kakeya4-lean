import Kakeya4.Hard.AlgebraicGeometry.SignFormula

/-!
Fixed-format eligibility tests from 02-framework.tex:1489–1509.
All quadratic coefficients, inverse spatial-matrix entries, affine center data,
box bounds, interval endpoints, and thresholds are numerical parameters.
`invK` is supplied separately; actual chart instantiation must set it to K⁻¹.
-/

noncomputable section
open Set
open scoped Classical BigOperators
open OAI.Release061 OAI.Release061.SignElimination

namespace Kakeya4.Hard.EligibleFormula

abbrev QuadraticExponent := {a : Fin 4 → Fin 3 // ∑ i, (a i : ℕ) ≤ 2}

inductive Coefficient
  | lo | hi | K | invK | thickness | slopeRadius | interceptRadius
  | inverseMatrix (i j : Fin 2)
  | centerBase (i : Fin 2)
  | centerVelocity (i : Fin 2)
  | quadratic (a : QuadraticExponent)
  deriving DecidableEq, Fintype

abbrev Parameters := Coefficient → ℝ
abbrev Point := Fin 3 → ℝ
abbrev Pair := (Parameters × Point) × Point
abbrev Variable := (Coefficient ⊕ Fin 3) ⊕ Fin 3
abbrev TimedVariable := Option Variable
abbrev Poly := MvPolynomial TimedVariable ℝ

def coordinates (z : Pair) : Variable → ℝ := Sum.elim (Sum.elim z.1.1 z.1.2) z.2
def timedCoordinates (z : Pair × ℝ) : TimedVariable → ℝ :=
  fun o => Option.elim o z.2 (coordinates z.1)

def parameter (i : Coefficient) : Poly := MvPolynomial.X (some (Sum.inl (Sum.inl i)))
def slope (i : Fin 3) : Poly := MvPolynomial.X (some (Sum.inl (Sum.inr i)))
def intercept (i : Fin 3) : Poly := MvPolynomial.X (some (Sum.inr i))
def time : Poly := MvPolynomial.X none
def spatial (i : Fin 3) : Poly := intercept i + time * slope i
def spacetime : Fin 4 → Poly := Fin.cases time spatial

/-- The universal real polynomial of total degree at most two in (t,y₀,y₁,w). -/
def test : Poly := ∑ a : QuadraticExponent,
  parameter (.quadratic a) * ∏ i : Fin 4, spacetime i ^ (a.val i : ℕ)

/-- The formal w derivative, evaluated on the same affine line. -/
def derivativeW : Poly := ∑ a : QuadraticExponent,
  parameter (.quadratic a) * MvPolynomial.C ((a.val 3 : ℕ) : ℝ) *
    ∏ i : Fin 4, spacetime i ^ ((a.val i : ℕ) - if i = 3 then 1 else 0)

def normalizedY (i : Fin 2) : Poly := ∑ j : Fin 2,
  parameter (.inverseMatrix i j) * (spatial j.castSucc -
    parameter (.centerBase j) - time * parameter (.centerVelocity j))

def spatialEnergy : Poly := ∑ i : Fin 2, normalizedY i ^ 2

def intervalTest : Set (Pair × ℝ) := {z |
  MvPolynomial.eval (timedCoordinates z) (parameter .lo) ≤ z.2 ∧
  z.2 ≤ MvPolynomial.eval (timedCoordinates z) (parameter .hi)}

def pointTest : Set (Pair × ℝ) := {z |
  MvPolynomial.eval (timedCoordinates z) spatialEnergy ≤
      MvPolynomial.eval (timedCoordinates z) (parameter .K ^ 2) ∧
  |MvPolynomial.eval (timedCoordinates z) test| ≤
      MvPolynomial.eval (timedCoordinates z) (parameter .K * parameter .thickness) ∧
  |MvPolynomial.eval (timedCoordinates z) derivativeW| ≤
      MvPolynomial.eval (timedCoordinates z) (parameter .K)}

def lowerDerivativeTest : Set (Pair × ℝ) := {z |
  MvPolynomial.eval (timedCoordinates z) (parameter .invK) ≤
    |MvPolynomial.eval (timedCoordinates z) derivativeW|}

def boxTest : Set Pair := {z | ∀ j,
  |z.1.2 j| ≤ z.1.1 .slopeRadius ∧ |z.2 j| ≤ z.1.1 .interceptRadius}

/-- No crop, density, witness identity or incidence restriction enters eligibility. -/
def eligible : Set Pair := {z | z ∈ boxTest ∧
  (∀ t : ℝ, (z,t) ∈ intervalTest → (z,t) ∈ pointTest) ∧
  ∃ t : ℝ, (z,t) ∈ intervalTest ∧ (z,t) ∈ lowerDerivativeTest}

theorem intervalTest_signSet : PolynomialSignSet timedCoordinates intervalTest := by
  have h₁ := polynomialSignSet_eval_le timedCoordinates (parameter .lo) time
  have h₂ := polynomialSignSet_eval_le timedCoordinates time (parameter .hi)
  convert h₁.inter h₂ using 1
  apply Set.ext
  intro z
  simp only [intervalTest, mem_ofPred_eq, mem_inter_iff, time,
    MvPolynomial.eval_X, timedCoordinates, Option.elim_none]

theorem pointTest_signSet : PolynomialSignSet timedCoordinates pointTest :=
  (polynomialSignSet_eval_le timedCoordinates spatialEnergy (parameter .K ^ 2)).inter
    ((polynomialSignSet_abs_eval_le timedCoordinates test (parameter .K * parameter .thickness)).inter
      (polynomialSignSet_abs_eval_le timedCoordinates derivativeW (parameter .K)))

theorem lowerDerivativeTest_signSet : PolynomialSignSet timedCoordinates lowerDerivativeTest :=
  polynomialSignSet_eval_le_abs timedCoordinates derivativeW (parameter .invK)

theorem boxTest_signSet : PolynomialSignSet coordinates boxTest := by
  apply PolynomialSignSet.forall_finite
  intro j
  have hs := polynomialSignSet_abs_eval_le coordinates
    (MvPolynomial.X (Sum.inl (Sum.inr j)))
    (MvPolynomial.X (Sum.inl (Sum.inl Coefficient.slopeRadius)))
  have hb := polynomialSignSet_abs_eval_le coordinates
    (MvPolynomial.X (Sum.inr j))
    (MvPolynomial.X (Sum.inl (Sum.inl Coefficient.interceptRadius)))
  convert hs.inter hb using 1
  apply Set.ext
  intro z
  simp only [mem_ofPred_eq, mem_inter_iff, MvPolynomial.eval_X, coordinates,
    Sum.elim_inl, Sum.elim_inr]

theorem eligible_signSet : PolynomialSignSet coordinates eligible := by
  have hAll := polynomialSignSet_forall_real (c := coordinates)
    (intervalTest_signSet.compl.union pointTest_signSet)
  have hSome := polynomialSignSet_projection_one (c := coordinates)
    (intervalTest_signSet.inter lowerDerivativeTest_signSet)
  convert boxTest_signSet.inter (hAll.inter hSome) using 1
  apply Set.ext
  intro z
  simp only [eligible, mem_ofPred_eq, mem_inter_iff, mem_union, mem_compl_iff]
  constructor
  · rintro ⟨hb,ha,he⟩
    refine ⟨hb,fun t => ?_,he⟩
    by_cases hi : (z,t) ∈ intervalTest
    · exact Or.inr (ha t hi)
    · exact Or.inl hi
  · rintro ⟨hb,ha,he⟩
    exact ⟨hb,fun t ht => (ha t).resolve_left (not_not.mpr ht),he⟩

end Kakeya4.Hard.EligibleFormula
