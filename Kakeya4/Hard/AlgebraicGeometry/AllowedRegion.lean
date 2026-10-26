import Kakeya4.Hard.AlgebraicGeometry.AffineDerivative

/-! The actual spatial region allowed by the original chart tests and good derivative floor. -/

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace Kakeya4.Hard.EligibleFormula

def spatialEnergyValue (p : Parameters) (t : ℝ) (x : Point) : ℝ :=
  ∑ i : Fin 2, (∑ j : Fin 2, p (.inverseMatrix i j) *
    (x j.castSucc - p (.centerBase j) - t * p (.centerVelocity j))) ^ 2

def testValue (p : Parameters) (t : ℝ) (x : Point) : ℝ :=
  MvPolynomial.eval (Fin.cases t x) (quadraticPolynomial p)

def spatialDerivativeValue (p : Parameters) (t : ℝ) (x : Point) : ℝ :=
  MvPolynomial.eval (Fin.cases t x) (MvPolynomial.pderiv 3 (quadraticPolynomial p))

def allowedRegion (p : Parameters) (t : ℝ) : Set Point := {x |
  spatialEnergyValue p t x ≤ p .K ^ 2 ∧
  |testValue p t x| ≤ p .K * p .thickness ∧
  p .invK / 32 ≤ |spatialDerivativeValue p t x|}

theorem eval_spatialEnergy (p : Parameters) (b s : Point) (t : ℝ) :
    MvPolynomial.eval (timedCoordinates (((p,s),b),t)) spatialEnergy =
      spatialEnergyValue p t (b + t • s) := by
  simp [spatialEnergy,normalizedY,spatial,parameter,intercept,slope,time,
    timedCoordinates,coordinates,spatialEnergyValue,Pi.add_apply,Pi.smul_apply,smul_eq_mul]

theorem lineCoordinates_eq (b s : Point) (t : ℝ) :
    lineCoordinates b s t = Fin.cases t (b + t • s) := by
  funext i
  cases i using Fin.cases <;> rfl

theorem measurableSet_allowedRegion (p : Parameters) (t : ℝ) : MeasurableSet (allowedRegion p t) := by
  have hE : Continuous (spatialEnergyValue p t) := by
    unfold spatialEnergyValue
    fun_prop
  have hX : Continuous (fun x : Point => (Fin.cases t x : Fin 4 → ℝ)) := by
    apply continuous_pi
    intro i
    cases i using Fin.cases with
    | zero => exact continuous_const
    | succ j => exact continuous_apply j
  have hP : Continuous (testValue p t) := (MvPolynomial.continuous_eval _).comp hX
  have hD : Continuous (spatialDerivativeValue p t) := (MvPolynomial.continuous_eval _).comp hX
  have hPa : Continuous (fun x => |testValue p t x|) := hP.abs
  have hDa : Continuous (fun x => |spatialDerivativeValue p t x|) := hD.abs
  exact (isClosed_le hE continuous_const).measurableSet.inter
    ((isClosed_le hPa continuous_const).measurableSet.inter
      (isClosed_le continuous_const hDa).measurableSet)

/-- Whole-interval eligibility and the actual derivative good-time test place
the line image in the allowed spatial region. -/
theorem eligible_image_mem_allowedRegion (p : Parameters) (b s : Point) (t : ℝ)
    (h : ((p,s),b) ∈ eligible) (ht : t ∈ Icc (p .lo) (p .hi))
    (hg : p .invK / 32 ≤ |derivativeSlope p b s * t + derivativeOffset p b s|) :
    b + t • s ∈ allowedRegion p t := by
  have hI : ((((p,s),b),t) : Pair × ℝ) ∈ intervalTest := by
    simpa [intervalTest,parameter,timedCoordinates,coordinates] using ht
  have hpoint := h.2.1 t hI
  refine ⟨?_,?_,?_⟩
  · rw [← eval_spatialEnergy]
    simpa [pointTest,parameter,timedCoordinates,coordinates] using hpoint.1
  · change |MvPolynomial.eval (Fin.cases t (b + t • s)) (quadraticPolynomial p)| ≤ _
    rw [← lineCoordinates_eq, ← eval_test_eq]
    simpa [pointTest,parameter,timedCoordinates,coordinates] using hpoint.2.1
  · change p .invK / 32 ≤ |MvPolynomial.eval (Fin.cases t (b + t • s))
      (MvPolynomial.pderiv 3 (quadraticPolynomial p))|
    rw [← lineCoordinates_eq]
    change p .invK / 32 ≤ |derivativeValue p b s t|
    rwa [derivativeValue_affine]

end Kakeya4.Hard.EligibleFormula
