import Kakeya4.Hard.MultilinearKakeya.BallTubeFactors

/-! Finite real form of the original determinant-weighted kernel. The exact
ofReal identity retains the original indexed families, repetitions and zeros. -/

noncomputable section
open Set MeasureTheory Classical
open scoped Topology BigOperators ENNReal NNReal

namespace Kakeya4.Hard.MultilinearKakeya

def realTupleCoefficient {n : ℕ} {ι : Fin n → Type*}
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (a : ∀ i, ι i) : ℝ :=
  |Matrix.det (fun i j => (L j (a j)).direction i)| * ∏ i, (w i (a i) : ℝ)

theorem realTupleCoefficient_nonneg {n : ℕ} {ι : Fin n → Type*}
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (a : ∀ i, ι i) :
    0 ≤ realTupleCoefficient L w a := by unfold realTupleCoefficient; positivity

theorem ofReal_realTupleCoefficient {n : ℕ} {ι : Fin n → Type*}
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (a : ∀ i, ι i) :
    ENNReal.ofReal (realTupleCoefficient L w a) = tupleCoefficient L w a := by
  simp only [realTupleCoefficient,tupleCoefficient,determinantWeight,ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => (w i (a i)).coe_nonneg),ENNReal.ofReal_coe_nnreal]

def realKernel {n : ℕ} {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (r : ℝ) (x : E n) : ℝ :=
  ∑ a : ∀ i, ι i, if ∀ i, x ∈ (L i (a i)).tube r then realTupleCoefficient L w a else 0

theorem realKernel_nonneg {n : ℕ} {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (r : ℝ) (x : E n) :
    0 ≤ realKernel L w r x := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact realTupleCoefficient_nonneg L w a
  · exact le_rfl

theorem ofReal_realKernel {n : ℕ} {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (r : ℝ) (x : E n) :
    ENNReal.ofReal (realKernel L w r x) = kernel L w r x := by
  unfold realKernel kernel
  rw [ENNReal.ofReal_sum_of_nonneg (by intro a _; split_ifs; exact realTupleCoefficient_nonneg L w a; exact le_rfl)]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Set.indicator_apply,tupleRegion,mem_ofPred_eq]
  split_ifs
  · exact ofReal_realTupleCoefficient L w a
  · exact ENNReal.ofReal_zero

theorem kernel_ne_top {n : ℕ} {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (r : ℝ) (x : E n) : kernel L w r x ≠ ⊤ := by
  rw [← ofReal_realKernel]
  exact ENNReal.ofReal_ne_top

theorem kernel_toReal {n : ℕ} {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (r : ℝ) (x : E n) :
    (kernel L w r x).toReal = realKernel L w r x := by
  rw [← ofReal_realKernel,ENNReal.toReal_ofReal (realKernel_nonneg L w r x)]

end Kakeya4.Hard.MultilinearKakeya
