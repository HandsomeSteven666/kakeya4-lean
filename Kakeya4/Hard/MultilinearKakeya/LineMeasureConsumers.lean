import Kakeya4.Hard.MultilinearKakeya.LineMeasureScaling

/-! Section-6 consumers: measurable line parameters from arbitrary finite
source laws and actual successful-tuple mass. These retain repetitions and
unnormalized prior mass without requesting injective line maps. -/

noncomputable section
open Set MeasureTheory Classical
open scoped BigOperators ENNReal NNReal

namespace Kakeya4.Hard.MultilinearKakeya

def ParameterizedLineMeasureEndpointBound (n : ℕ) : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧ ∀ (α : Fin n → Type) [∀ i, MeasurableSpace (α i)]
    (ν : ∀ i, Measure (α i)) [∀ i, IsFiniteMeasure (ν i)]
    (f : ∀ i, α i → LineParameter n), (∀ i, Measurable (f i)) → ∀ r : ℝ, 0 < r →
    (∫⁻ x, (∫⁻ p, lineMeasureIntegrand n r ((fun i => f i (p i)),x) ∂Measure.pi ν)^endpointExponent n ∂volume) ≤
      (C : ℝ≥0∞)*ENNReal.ofReal (r^n)*∏ i, (ν i univ)^endpointExponent n

theorem parameterizedLineMeasureEndpointBound_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    ParameterizedLineMeasureEndpointBound n := by
  obtain ⟨C,hC,h⟩ := lineMeasureEndpointBound_of_two_le hn
  refine ⟨C,hC,fun α _ ν _ f hf r hr => ?_⟩
  have hi := h (fun i => (ν i).map (f i)) r hr
  have hmass (i : Fin n) : ((ν i).map (f i)) univ = ν i univ :=
    lineLaw_map_univ (ν i) (f i) (hf i)
  simp_rw [lineMeasureKernel_map_parameters ν f hf,hmass] at hi
  exact hi

/-- The actual prior product mass of successful tuples lower-bounds the
line-law kernel, with the actual determinant threshold. -/
theorem lineMeasureKernel_map_ge_success_mass {n : ℕ} {α : Fin n → Type*}
    [∀ i, MeasurableSpace (α i)] (ν : ∀ i, Measure (α i)) [∀ i, IsFiniteMeasure (ν i)]
    (f : ∀ i, α i → LineParameter n) (hf : ∀ i, Measurable (f i))
    (r : ℝ) (x : E n) (A : Set (∀ i, α i)) (hA : MeasurableSet A) (τ : ℝ)
    (hinside : ∀ p ∈ A, ∀ i, x ∈ (f i (p i)).toLine.tube r)
    (hdet : ∀ p ∈ A, τ ≤ |Matrix.det (fun i j => (f j (p j)).2.val i)|) :
    ENNReal.ofReal τ * (Measure.pi ν) A ≤
      lineMeasureKernel (fun i => (ν i).map (f i)) r x := by
  rw [lineMeasureKernel_map_parameters ν f hf]
  rw [← lintegral_indicator_const hA (ENNReal.ofReal τ)]
  apply lintegral_mono
  intro p
  change A.indicator (fun _ => ENNReal.ofReal τ) p ≤
    lineMeasureIntegrand n r ((fun i => f i (p i)),x)
  by_cases hp : p ∈ A
  · rw [Set.indicator_of_mem hp,lineMeasureIntegrand_eq_tupleRegion r (fun i => f i (p i)) x,
      Set.indicator_of_mem (show x ∈ tupleRegion (fun i => (f i (p i)).toLine) r from hinside p hp)]
    exact ENNReal.ofReal_le_ofReal (hdet p hp)
  · rw [Set.indicator_of_notMem hp]
    exact zero_le

end Kakeya4.Hard.MultilinearKakeya
