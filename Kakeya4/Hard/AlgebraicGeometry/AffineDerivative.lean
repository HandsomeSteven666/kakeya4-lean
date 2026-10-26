import Kakeya4.Hard.AlgebraicGeometry.QuadraticPolynomial
import Kakeya4.Hard.AlgebraicGeometry.MeasurableSelector

/-! The actual derivative test supplies measurable affine coefficients and the good-time witness. -/

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Kakeya4.Hard.EligibleFormula

def derivativeValue (p : Parameters) (b s : Point) (t : ℝ) : ℝ :=
  MvPolynomial.eval (lineCoordinates b s t) (MvPolynomial.pderiv 3 (quadraticPolynomial p))
def derivativeSlope (p : Parameters) (b s : Point) : ℝ :=
  derivativeValue p b s 1 - derivativeValue p b s 0
def derivativeOffset (p : Parameters) (b s : Point) : ℝ := derivativeValue p b s 0

theorem derivativeValue_affine (p : Parameters) (b s : Point) (t : ℝ) :
    derivativeValue p b s t = derivativeSlope p b s * t + derivativeOffset p b s := by
  obtain ⟨u,v,h⟩ := derivativeW_affine p b s
  have hh (t : ℝ) : derivativeValue p b s t = u*t+v := by
    rw [derivativeValue, ← eval_derivativeW_eq]
    exact h t
  simp only [derivativeSlope, derivativeOffset, hh]
  ring

theorem measurable_derivativeValue (p : Parameters) (b₀ : Point → Point)
    (hb : Measurable b₀) (t : ℝ) : Measurable (fun s => derivativeValue p (b₀ s) s t) := by
  have hc : Measurable (fun s : Point => lineCoordinates (b₀ s) s t) := by
    apply Measurable.of_eval
    intro i
    cases i using Fin.cases with
    | zero => exact measurable_const
    | succ j =>
      change Measurable (fun s => b₀ s j + t * s j)
      exact ((measurable_pi_apply j).comp hb).add
        (measurable_const.mul (measurable_pi_apply j))
  exact (MvPolynomial.continuous_eval _).measurable.comp hc

theorem measurable_derivativeSlope (p : Parameters) (b₀ : Point → Point) (hb : Measurable b₀) :
    Measurable (fun s => derivativeSlope p (b₀ s) s) :=
  (measurable_derivativeValue p b₀ hb 1).sub (measurable_derivativeValue p b₀ hb 0)

theorem measurable_derivativeOffset (p : Parameters) (b₀ : Point → Point) (hb : Measurable b₀) :
    Measurable (fun s => derivativeOffset p (b₀ s) s) := measurable_derivativeValue p b₀ hb 0

theorem eligible_derivative_witness (p : Parameters) (b s : Point)
    (h : ((p,s),b) ∈ eligible) :
    ∃ t ∈ Icc (p .lo) (p .hi),
      p .invK ≤ |derivativeSlope p b s * t + derivativeOffset p b s| := by
  obtain ⟨t,ht,hfloor⟩ := h.2.2
  refine ⟨t,?_,?_⟩
  · simpa [intervalTest,parameter,timedCoordinates,coordinates] using ht
  · rw [← derivativeValue_affine]
    change p .invK ≤ |MvPolynomial.eval (lineCoordinates b s t)
      (MvPolynomial.pderiv 3 (quadraticPolynomial p))|
    rw [← eval_derivativeW_eq]
    simpa [lowerDerivativeTest,parameter,timedCoordinates,coordinates] using hfloor

end Kakeya4.Hard.EligibleFormula
