import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The actual product law and Fourier convention for H-004

The law is the image of independent real coordinates under their product, with no
restriction away from zero. Fourier frequency uses exp(-2 pi i xi x), rather than
the probability convention exp(i t x). Source: Orponen--de Saxce--Shmerkin,
arXiv:2309.03068v2, Theorem 1.5 and the notation following it.
This file proves transport identities, not the Fourier decay theorem.
All measure and characteristic-function machinery is reused from fixed Mathlib.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Multiplication of independently sampled coordinates, including zero values. -/
def productLaw {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ) : Measure ℝ :=
  (Measure.pi μ).map (fun x : ι → ℝ ↦ ∏ i, x i)

/-- The paper's Fourier transform, with the negative `2π` convention. -/
def fourier (μ : Measure ℝ) (ξ : ℝ) : ℂ := charFun μ (-(2 * Real.pi) * ξ)

/-- No atomicity, support separation or density is needed for the product law. -/
instance productLaw_isProbabilityMeasure {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (productLaw μ) := by
  unfold productLaw
  exact MeasureTheory.Measure.isProbabilityMeasure_map_iff (by fun_prop) |>.mpr inferInstance

/-- The product law retains the full product of total masses. -/
theorem productLaw_univ {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] :
    productLaw μ univ = ∏ i, μ i univ := by
  rw [productLaw, Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simpa only [Set.preimage_univ] using Measure.pi_univ μ

/-- The Fourier definition is the literal oscillatory integral in the paper. -/
theorem fourier_eq_integral (μ : Measure ℝ) (ξ : ℝ) :
    fourier μ ξ = ∫ x, Complex.exp (((-(2 * Real.pi) * ξ * x : ℝ) : ℂ) * Complex.I) ∂μ := by
  simpa only [fourier, Complex.ofReal_mul] using
    (charFun_apply_real (μ := μ) (-(2 * Real.pi) * ξ))

/-- Exact substitution of the product random variable into the Fourier kernel. -/
theorem fourier_productLaw {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    (ξ : ℝ) :
    fourier (productLaw μ) ξ =
      ∫ x : ι → ℝ, Complex.exp
        (((-(2 * Real.pi) * ξ * ∏ i, x i : ℝ) : ℂ) * Complex.I) ∂Measure.pi μ := by
  rw [fourier_eq_integral, productLaw,
    integral_map (by fun_prop) (by fun_prop)]

/-- Unit mass yields the usual unit Fourier bound. This is not power decay. -/
theorem norm_fourier_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (ξ : ℝ) :
    ‖fourier μ ξ‖ ≤ 1 := norm_charFun_le_one _

/-- Zero frequency records the mass; no normalization is silently applied. -/
theorem fourier_zero (μ : Measure ℝ) :
    fourier μ 0 = (μ.real univ : ℂ) := by simp [fourier]

/-- Real measures give conjugate Fourier values at opposite frequencies. -/
theorem fourier_neg (μ : Measure ℝ) (ξ : ℝ) :
    fourier μ (-ξ) = star (fourier μ ξ) := by
  simpa [fourier] using charFun_neg (μ := μ) (-(2 * Real.pi) * ξ)

/-- The negative-frequency bound is exactly the positive-frequency bound. -/
theorem norm_fourier_neg (μ : Measure ℝ) (ξ : ℝ) :
    ‖fourier μ (-ξ)‖ = ‖fourier μ ξ‖ := by rw [fourier_neg, norm_star]

/-- Additive convolution is already supplied by Mathlib; its Fourier rule is reused. -/
theorem fourier_additiveConvolution (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ξ : ℝ) :
    fourier (μ ∗ ν) ξ = fourier μ ξ * fourier ν ξ := by
  exact charFun_conv _

/-- Independent additive sums multiply Fourier transforms for arbitrary probability laws. -/
theorem fourier_sumLaw {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (ξ : ℝ) :
    fourier ((Measure.pi μ).map (fun x : ι → ℝ ↦ ∑ i, x i)) ξ =
      ∏ i, fourier (μ i) ξ := by
  simpa only [fourier, Finset.prod_apply] using
    congrFun (ProbabilityTheory.charFun_map_sum_pi_eq_prod μ) (-(2 * Real.pi) * ξ)

/-- Laws supported on the closed unit interval in absolute value; zero is allowed. -/
def UnitSupported (μ : Measure ℝ) : Prop := ∀ᵐ x ∂μ, |x| ≤ 1

/-- Independent products preserve unit support without any lower bound on factors. -/
theorem productLaw_unitSupported {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (hμ : ∀ i, UnitSupported (μ i)) :
    UnitSupported (productLaw μ) := by
  apply (ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)).2
  have h : ∀ᵐ x ∂Measure.pi μ, ∀ i, |x i| ≤ 1 :=
    Filter.eventually_all.2 fun i ↦ Measure.tendsto_eval_ae_ae.eventually (hμ i)
  filter_upwards [h] with x hx
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _) (fun i _ ↦ hx i)

/-- Product laws commute with measurable coordinate-law pushforwards exactly. -/
theorem productLaw_map_parameters {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (ν : ∀ i, Measure (α i))
    [∀ i, IsFiniteMeasure (ν i)] (f : ∀ i, α i → ℝ) (hf : ∀ i, Measurable (f i)) :
    productLaw (fun i ↦ (ν i).map (f i)) =
      (Measure.pi ν).map (fun x ↦ ∏ i, f i (x i)) := by
  rw [productLaw, ← Measure.pi_map_pi (fun i ↦ (hf i).aemeasurable),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Fourier transform of the binary product law as an average of rescaled transforms.
This is the exact starting identity of the two-factor argument, with no decay input. -/
theorem fourier_multiplicativeConvolution (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ξ : ℝ) :
    fourier (μ ∗ₘ ν) ξ = ∫ x, fourier ν (ξ * x) ∂μ := by
  rw [fourier_eq_integral, integral_mconv]
  · apply integral_congr_ae
    filter_upwards [] with x
    rw [fourier_eq_integral]
    congr 1
    funext y
    congr 2
    push_cast
    ring
  · apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with x
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)

end Kakeya4.Hard.MultiplicativeConvolution
