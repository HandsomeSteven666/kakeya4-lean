import Kakeya4.Hard.AlgebraicGeometry.PhysicalChartData
import Kakeya4.Hard.AlgebraicGeometry.CompactTimeTests

/-! The original supremum-based geometric eligibility, with its actual physical
matrix and quadratic polynomial, equals the semialgebraic parameterized set. -/

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace Kakeya4.Hard.EligibleFormula

def PhysicalChart.normalizedBase (c : PhysicalChart) (b s : Point) (t : ℝ) : Plane :=
  c.spatialMap.symm (fun j => b j.castSucc + t*s j.castSucc - c.centerBase j - t*c.centerVelocity j)

/-- Euclidean radius of the normalized two-dimensional base coordinate. -/
def PhysicalChart.spatialRadius (c : PhysicalChart) (b s : Point) (t : ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin 2, (c.normalizedBase b s t i)^2)

def PhysicalChart.testOnLine (c : PhysicalChart) (b s : Point) (t : ℝ) : ℝ :=
  MvPolynomial.eval (lineCoordinates b s t) c.polynomial

def PhysicalChart.derivativeOnLine (c : PhysicalChart) (b s : Point) (t : ℝ) : ℝ :=
  MvPolynomial.eval (lineCoordinates b s t) (MvPolynomial.pderiv 3 c.polynomial)

def PhysicalChart.supEligible (c : PhysicalChart) (b s : Point) : Prop :=
  (∀ j, |s j| ≤ c.slopeRadius ∧ |b j| ≤ c.interceptRadius) ∧
  sSup ((c.spatialRadius b s) '' Icc c.lowerTime c.upperTime) ≤ c.K ∧
  sSup ((fun t => |c.testOnLine b s t|) '' Icc c.lowerTime c.upperTime) ≤ c.K*c.thickness ∧
  sSup ((fun t => |c.derivativeOnLine b s t|) '' Icc c.lowerTime c.upperTime) ≤ c.K ∧
  c.K⁻¹ ≤ sSup ((fun t => |c.derivativeOnLine b s t|) '' Icc c.lowerTime c.upperTime)

def PhysicalChart.manuscriptSlopes (c : PhysicalChart) : Set Point :=
  {s | ∃ b, c.supEligible b s}

theorem PhysicalChart.spatialRadius_eq_euclidean_norm (c : PhysicalChart)
    (b s : Point) (t : ℝ) : c.spatialRadius b s t =
      ‖(WithLp.toLp 2 (c.normalizedBase b s t) : EuclideanSpace ℝ (Fin 2))‖ := by
  simp only [EuclideanSpace.norm_eq,PhysicalChart.spatialRadius,Real.norm_eq_abs,sq_abs]

theorem PhysicalChart.energy_parameters (c : PhysicalChart) (b s : Point) (t : ℝ) :
    spatialEnergyValue c.parameters t (b+t • s) =
      ∑ i : Fin 2, (c.normalizedBase b s t i)^2 := by
  have hE : spatialEnergyValue c.parameters t (b+t • s) =
      spatialEnergyValue c.parameters t (Fin.snoc (fun j => (b+t • s) j.castSucc) 0) := by
    simp only [spatialEnergyValue,Fin.snoc_castSucc]
  rw [hE,spatialEnergyValue_base,c.inverseSpatialMap_parameters]
  have hv : (fun j : Fin 2 => (b+t • s) j.castSucc) - physicalCenter c.parameters t =
      (fun j => b j.castSucc + t*s j.castSucc - c.centerBase j - t*c.centerVelocity j) := by
    funext j
    change b j.castSucc + t*s j.castSucc - (c.centerBase j + t*c.centerVelocity j) = _
    ring
  rw [hv]
  rfl

theorem PhysicalChart.pointTest_parameters (c : PhysicalChart) (b s : Point) (t : ℝ) :
    ((((c.parameters,s),b),t) : Pair × ℝ) ∈ pointTest ↔
      c.spatialRadius b s t ≤ c.K ∧ |c.testOnLine b s t| ≤ c.K*c.thickness ∧
        |c.derivativeOnLine b s t| ≤ c.K := by
  change (_ ∧ _ ∧ _) ↔ _
  rw [eval_spatialEnergy,c.energy_parameters,c.test_parameters,c.derivative_parameters]
  simp only [parameter,MvPolynomial.eval_pow,MvPolynomial.eval_mul,MvPolynomial.eval_X,
    timedCoordinates,coordinates,Option.elim_some,Sum.elim_inl,PhysicalChart.parameters]
  rw [show c.spatialRadius b s t ≤ c.K ↔
      (∑ i : Fin 2, (c.normalizedBase b s t i)^2) ≤ c.K^2 from
      Real.sqrt_le_left (le_trans zero_le_one c.K_ge_one)]
  rfl

theorem PhysicalChart.continuous_spatialRadius (c : PhysicalChart) (b s : Point) :
    Continuous (c.spatialRadius b s) := by
  unfold PhysicalChart.spatialRadius PhysicalChart.normalizedBase
  fun_prop

theorem PhysicalChart.continuous_testOnLine (c : PhysicalChart) (b s : Point) :
    Continuous (c.testOnLine b s) := by
  apply (MvPolynomial.continuous_eval _).comp
  apply continuous_pi
  intro i
  cases i using Fin.cases with
  | zero => exact continuous_id
  | succ j =>
    change Continuous (fun t : ℝ => b j + t*s j)
    fun_prop

theorem PhysicalChart.continuous_derivativeOnLine (c : PhysicalChart) (b s : Point) :
    Continuous (c.derivativeOnLine b s) := by
  apply (MvPolynomial.continuous_eval _).comp
  apply continuous_pi
  intro i
  cases i using Fin.cases with
  | zero => exact continuous_id
  | succ j =>
    change Continuous (fun t : ℝ => b j + t*s j)
    fun_prop

theorem PhysicalChart.eligible_iff_supEligible (c : PhysicalChart) (b s : Point) :
    ((c.parameters,s),b) ∈ eligible ↔ c.supEligible b s := by
  have hR := c.continuous_spatialRadius b s
  have hP := (c.continuous_testOnLine b s).abs
  have hD := (c.continuous_derivativeOnLine b s).abs
  unfold PhysicalChart.supEligible
  rw [compact_interval_sSup_le_iff _ _ _ c.interval_pos.le _ hR.continuousOn,
    compact_interval_sSup_le_iff _ _ _ c.interval_pos.le _ hP.continuousOn,
    compact_interval_sSup_le_iff _ _ _ c.interval_pos.le _ hD.continuousOn,
    compact_interval_le_sSup_iff _ _ _ c.interval_pos.le _ hD.continuousOn]
  change (_ ∧ _ ∧ _) ↔ _
  have hI (t : ℝ) : ((((c.parameters,s),b),t) : Pair × ℝ) ∈ intervalTest ↔
      t ∈ Icc c.lowerTime c.upperTime := by
    simp [intervalTest,parameter,timedCoordinates,coordinates,PhysicalChart.parameters]
  have hL (t : ℝ) : ((((c.parameters,s),b),t) : Pair × ℝ) ∈ lowerDerivativeTest ↔
      c.K⁻¹ ≤ |c.derivativeOnLine b s t| := by
    simp only [lowerDerivativeTest,mem_ofPred_eq,c.derivative_parameters,parameter,
      MvPolynomial.eval_X,timedCoordinates,coordinates,Option.elim_some,Sum.elim_inl,
      PhysicalChart.parameters,PhysicalChart.derivativeOnLine]
  simp only [boxTest,mem_ofPred_eq,PhysicalChart.parameters,hI,c.pointTest_parameters,hL]
  constructor
  · rintro ⟨hb,hall,hex⟩
    exact ⟨hb,(fun t ht => (hall t ht).1), (fun t ht => (hall t ht).2.1),
      (fun t ht => (hall t ht).2.2),hex⟩
  · rintro ⟨hb,hR,hP,hD,hex⟩
    exact ⟨hb,fun t ht => ⟨hR t ht,hP t ht,hD t ht⟩,hex⟩

theorem PhysicalChart.manuscriptSlopes_eq (c : PhysicalChart) :
    c.manuscriptSlopes = eligibleSlopes c.parameters := by
  ext s
  exact exists_congr (fun b => (c.eligible_iff_supEligible b s).symm)

end Kakeya4.Hard.EligibleFormula
