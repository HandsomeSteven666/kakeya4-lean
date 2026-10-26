import Kakeya4.Hard.MultilinearKakeya.LineMeasureGeometry

/-! The actual determinant-weighted integral kernel for Borel line laws.
All line measures are independent inputs; atomicity and bounded anchors are
not assumptions. This file states the endpoint but does not assert its proof. -/

noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal NNReal RealInnerProductSpace BigOperators

namespace Kakeya4.Hard.MultilinearKakeya

theorem continuous_parameter_determinant (n : ℕ) :
    Continuous (fun p : Fin n → LineParameter n =>
      |Matrix.det (fun i j => (p j).2.val i)|) := by
  apply Continuous.abs
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fun_prop

def parameterTupleIncidence (n : ℕ) (r : ℝ) : Set ((Fin n → LineParameter n) × E n) :=
  {z | ∀ i, (z.1 i,z.2) ∈ parameterTubeIncidence n r}

theorem isClosed_parameterTupleIncidence (n : ℕ) (r : ℝ) :
    IsClosed (parameterTupleIncidence n r) := by
  have he : parameterTupleIncidence n r =
      ⋂ i : Fin n, {z : (Fin n → LineParameter n) × E n | (z.1 i,z.2) ∈ parameterTubeIncidence n r} := by
    ext z
    simp [parameterTupleIncidence]
  rw [he]
  exact isClosed_iInter (fun i => (isClosed_parameterTubeIncidence n r).preimage (by fun_prop))

def lineMeasureIntegrand (n : ℕ) (r : ℝ) (z : (Fin n → LineParameter n) × E n) : ℝ≥0∞ :=
  (parameterTupleIncidence n r).indicator
    (fun z => determinantWeight (fun i => (z.1 i).toLine)) z

theorem measurable_lineMeasureIntegrand (n : ℕ) (r : ℝ) :
    Measurable (lineMeasureIntegrand n r) := by
  have hd : Measurable (fun z : (Fin n → LineParameter n) × E n =>
      determinantWeight (fun i => (z.1 i).toLine)) :=
    ((continuous_parameter_determinant n).measurable.comp measurable_fst).ennreal_ofReal
  exact hd.indicator (isClosed_parameterTupleIncidence n r).measurableSet

theorem lineMeasureIntegrand_eq_tupleRegion {n : ℕ} (r : ℝ)
    (p : Fin n → LineParameter n) (x : E n) :
    lineMeasureIntegrand n r (p,x) =
      (tupleRegion (fun i => (p i).toLine) r).indicator
        (fun _ => determinantWeight (fun i => (p i).toLine)) x := by
  have he : (p,x) ∈ parameterTupleIncidence n r ↔
      x ∈ tupleRegion (fun i => (p i).toLine) r := by
    exact forall_congr' (fun i => mem_parameterTubeIncidence r (p i) x)
  by_cases h : (p,x) ∈ parameterTupleIncidence n r
  · simp only [lineMeasureIntegrand,Set.indicator_of_mem h,Set.indicator_of_mem (he.mp h)]
  · simp only [lineMeasureIntegrand,Set.indicator_of_notMem h,
      Set.indicator_of_notMem (mt he.mpr h)]

def lineMeasureKernel {n : ℕ} (μ : Fin n → Measure (LineParameter n)) (r : ℝ) (x : E n) : ℝ≥0∞ :=
  ∫⁻ p, lineMeasureIntegrand n r (p,x) ∂Measure.pi μ

theorem measurable_lineMeasureKernel {n : ℕ} (μ : Fin n → Measure (LineParameter n))
    [∀ i, SigmaFinite (μ i)] (r : ℝ) : Measurable (lineMeasureKernel μ r) := by
  apply Measurable.lintegral_prod_left
  exact measurable_lineMeasureIntegrand n r

theorem measurable_lineMeasureEndpointKernel {n : ℕ} (μ : Fin n → Measure (LineParameter n))
    [∀ i, SigmaFinite (μ i)] (r p : ℝ) : Measurable (fun x => (lineMeasureKernel μ r x)^p) :=
  (measurable_lineMeasureKernel μ r).pow_const p

/-- The general finite line-law endpoint, with its dimensional constant before
all measures and positive radii. This proposition is not assumed as a theorem. -/
def LineMeasureEndpointBound (n : ℕ) : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧ ∀ (μ : Fin n → Measure (LineParameter n)) [∀ i, IsFiniteMeasure (μ i)]
    (r : ℝ), 0 < r →
    (∫⁻ x, (lineMeasureKernel μ r x)^endpointExponent n ∂volume) ≤
      (C : ℝ≥0∞) * ENNReal.ofReal (r^n) * ∏ i, (μ i Set.univ)^endpointExponent n

end Kakeya4.Hard.MultilinearKakeya
