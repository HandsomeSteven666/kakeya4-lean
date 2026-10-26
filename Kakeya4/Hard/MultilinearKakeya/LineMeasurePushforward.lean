import Kakeya4.Hard.MultilinearKakeya.LineMeasureKernel

/-! Actual parameter-law pushforwards, preserving arbitrary source indices
and all mass. No injectivity or non-atomicity is required. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem measurable_lineParameter_of_anchor_direction {n : ℕ} {α : Type*} [MeasurableSpace α]
    (a v : α → E n) (ha : Measurable a) (hv : Measurable v) (hunit : ∀ x, ‖v x‖ = 1) :
    Measurable (fun x : α => (a x,⟨v x,hunit x⟩) : α → LineParameter n) :=
  ha.prodMk (hv.subtype_mk (h := hunit))

theorem lineLaw_map_univ {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (f : α → β) (hf : Measurable f) : (ν.map f) univ = ν univ := by
  rw [Measure.map_apply hf MeasurableSet.univ]
  simp

theorem lineMeasureKernel_map_parameters {n : ℕ} {α : Fin n → Type*}
    [∀ i, MeasurableSpace (α i)] (ν : ∀ i, Measure (α i)) [∀ i, IsFiniteMeasure (ν i)]
    (f : ∀ i, α i → LineParameter n) (hf : ∀ i, Measurable (f i)) (r : ℝ) (x : E n) :
    lineMeasureKernel (fun i => (ν i).map (f i)) r x =
      ∫⁻ p, lineMeasureIntegrand n r ((fun i => f i (p i)),x) ∂Measure.pi ν := by
  have hm : Measurable (fun p : Fin n → LineParameter n => lineMeasureIntegrand n r (p,x)) :=
    (measurable_lineMeasureIntegrand n r).comp (measurable_id.prodMk measurable_const)
  have hg : Measurable (fun p : ∀ i, α i => fun i => f i (p i)) := by
    fun_prop
  rw [lineMeasureKernel,← Measure.pi_map_pi (μ := ν) (f := f) (fun i => (hf i).aemeasurable)]
  exact lintegral_map hm hg

end Kakeya4.Hard.MultilinearKakeya
