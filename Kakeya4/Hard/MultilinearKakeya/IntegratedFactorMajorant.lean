import Kakeya4.Hard.MultilinearKakeya.FiniteMeasureFactorBudget
import Kakeya4.Hard.MultilinearKakeya.LineMeasureKernel

/-! Integrating the actual determinant/tube majorant over independent line laws.
Finite positive coefficients imply finiteness before any use of toReal. -/

noncomputable section
open Set MeasureTheory Classical
open scoped BigOperators ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem lineMeasureIntegrand_le_product_factors {n : ℕ} (r : ℝ) (b : E n)
    (S : Fin n → LineParameter n → ℝ) (hS : ∀ i p, 0 ≤ S i p)
    {c a : ℝ} (hca : 0 ≤ c*a)
    (hdet : ∀ p : Fin n → LineParameter n, (∀ i, b ∈ (p i).toLine.tube r) →
      c*a*|Matrix.det (fun i j => (p j).2.val i)| ≤ ∏ i, S i (p i))
    (p : Fin n → LineParameter n) :
    ENNReal.ofReal (c*a)*lineMeasureIntegrand n r (p,b) ≤
      ENNReal.ofReal (∏ i, S i (p i)) := by
  rw [lineMeasureIntegrand_eq_tupleRegion]
  by_cases hp : ∀ i, b ∈ (p i).toLine.tube r
  · rw [Set.indicator_of_mem (show b ∈ tupleRegion (fun i => (p i).toLine) r from hp)]
    change ENNReal.ofReal (c*a)*ENNReal.ofReal |Matrix.det (fun i j => (p j).2.val i)| ≤ _
    rw [← ENNReal.ofReal_mul hca]
    exact ENNReal.ofReal_le_ofReal (hdet p hp)
  · rw [Set.indicator_of_notMem (show b ∉ tupleRegion (fun i => (p i).toLine) r from hp),mul_zero]
    exact zero_le

theorem lineMeasureKernel_le_integrated_product {n : ℕ}
    (μ : Fin n → Measure (LineParameter n)) [∀ i, SigmaFinite (μ i)]
    (r : ℝ) (b : E n) (S : Fin n → LineParameter n → ℝ)
    (hI : ∀ i, Integrable (S i) (μ i)) (hS : ∀ i p, 0 ≤ S i p)
    {c a : ℝ} (hca : 0 ≤ c*a)
    (hdet : ∀ p : Fin n → LineParameter n, (∀ i, b ∈ (p i).toLine.tube r) →
      c*a*|Matrix.det (fun i j => (p j).2.val i)| ≤ ∏ i, S i (p i)) :
    ENNReal.ofReal (c*a)*lineMeasureKernel μ r b ≤
      ENNReal.ofReal (∏ i, ∫ p, S i p ∂μ i) := by
  rw [lineMeasureKernel,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_ofReal_coordinate_product μ S hI hS]
  exact lintegral_mono (fun p => lineMeasureIntegrand_le_product_factors r b S hS hca hdet p)

theorem kernel_ne_top_of_positive_integrated_majorant {X : ℝ≥0∞} {a B : ℝ}
    (ha : 0 < a) (h : ENNReal.ofReal a*X ≤ ENNReal.ofReal B) : X ≠ ⊤ := by
  intro ht
  rw [ht] at h
  have he : ENNReal.ofReal a*⊤ = ⊤ := ENNReal.mul_eq_top.mpr
    (Or.inl ⟨(ENNReal.ofReal_pos.mpr ha).ne',rfl⟩)
  rw [he] at h
  exact ENNReal.ofReal_ne_top (top_unique h)

theorem real_lineMeasureKernel_le_integrated_product {n : ℕ}
    (μ : Fin n → Measure (LineParameter n)) [∀ i, SigmaFinite (μ i)]
    (r : ℝ) (b : E n) (S : Fin n → LineParameter n → ℝ)
    (hI : ∀ i, Integrable (S i) (μ i)) (hS : ∀ i p, 0 ≤ S i p)
    {c a : ℝ} (hca : 0 < c*a)
    (hdet : ∀ p : Fin n → LineParameter n, (∀ i, b ∈ (p i).toLine.tube r) →
      c*a*|Matrix.det (fun i j => (p j).2.val i)| ≤ ∏ i, S i (p i)) :
    lineMeasureKernel μ r b ≠ ⊤ ∧
      c*a*(lineMeasureKernel μ r b).toReal ≤ ∏ i, ∫ p, S i p ∂μ i := by
  have h := lineMeasureKernel_le_integrated_product μ r b S hI hS hca.le hdet
  refine ⟨kernel_ne_top_of_positive_integrated_majorant hca h,?_⟩
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hca.le,
    ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ => integral_nonneg (hS i)))] at hr
  exact hr

end Kakeya4.Hard.MultilinearKakeya
