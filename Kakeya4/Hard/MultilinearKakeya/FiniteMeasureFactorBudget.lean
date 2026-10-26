import Kakeya4.Hard.MultilinearKakeya.MeasurableBallTubeFactors
import Mathlib.MeasureTheory.Integral.Pi

/-! Integrating a nonnegative finite-factor budget against any finite measure.
The bounds precede the measure and require neither atoms nor compact support. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem factor_le_finite_sum_budget {α κ : Type*} [Fintype κ]
    (S : α → κ → ℝ) (hS : ∀ x q, 0 ≤ S x q) {B : ℝ}
    (hB : ∀ x, ∑ q, S x q ≤ B) (x : α) (q : κ) : S x q ≤ B :=
  (Finset.single_le_sum (fun q _ => hS x q) (Finset.mem_univ q)).trans (hB x)

theorem integrable_factor_of_finite_sum_budget {α κ : Type*} [MeasurableSpace α] [Fintype κ]
    (μ : Measure α) [IsFiniteMeasure μ] (S : α → κ → ℝ)
    (hM : ∀ q, Measurable (fun x => S x q)) (hS : ∀ x q, 0 ≤ S x q)
    {B : ℝ} (hB : ∀ x, ∑ q, S x q ≤ B) (q : κ) :
    Integrable (fun x => S x q) μ := by
  apply Integrable.of_bound (hM q).aestronglyMeasurable B
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hS x q)]
    exact factor_le_finite_sum_budget S hS hB x q)

theorem sum_integral_factor_le_of_finite_sum_budget {α κ : Type*}
    [MeasurableSpace α] [Fintype κ] (μ : Measure α) [IsFiniteMeasure μ]
    (S : α → κ → ℝ) (hM : ∀ q, Measurable (fun x => S x q))
    (hS : ∀ x q, 0 ≤ S x q) {B : ℝ} (hB : ∀ x, ∑ q, S x q ≤ B) :
    (∑ q, ∫ x, S x q ∂μ) ≤ μ.real univ * B := by
  rw [← integral_finset_sum Finset.univ
    (fun q _ => integrable_factor_of_finite_sum_budget μ S hM hS hB q)]
  have h := integral_mono
    (integrable_finset_sum Finset.univ
      (fun q _ => integrable_factor_of_finite_sum_budget μ S hM hS hB q))
    (integrable_const B) hB
  simpa only [integral_const,smul_eq_mul] using h

theorem lintegral_ofReal_coordinate_product {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, α i → ℝ) (hf : ∀ i, Integrable (f i) (μ i))
    (hnonneg : ∀ i x, 0 ≤ f i x) :
    (∫⁻ x, ENNReal.ofReal (∏ i, f i (x i)) ∂Measure.pi μ) =
      ENNReal.ofReal (∏ i, ∫ x, f i x ∂μ i) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod_dep hf)
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hnonneg i (x i)))),
    integral_fintype_prod_eq_prod]

end Kakeya4.Hard.MultilinearKakeya
