import Mathlib
import Kakeya4.Foundation.Basic

/-!
# The actual determinant-weighted multilinear Kakeya statement

Finite indexed families of full affine lines are used; repeated lines are allowed.
The tube is the closed Euclidean radius-r neighborhood of the entire line.
This file states the endpoint estimate without asserting its proof.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Kakeya4.Hard.MultilinearKakeya

/-- An anchored unit direction; the anchor need not lie in a bounded region. -/
structure Line (n : ℕ) where
  anchor : E n
  direction : E n
  norm_direction : ‖direction‖ = 1

def Line.carrier {n : ℕ} (L : Line n) : Set (E n) :=
  {x | ∃ t : ℝ, x = L.anchor + t • L.direction}

def Line.tube {n : ℕ} (L : Line n) (r : ℝ) : Set (E n) :=
  {x | Metric.infDist x L.carrier ≤ r}

theorem Line.carrier_nonempty {n : ℕ} (L : Line n) : L.carrier.Nonempty :=
  ⟨L.anchor, 0, by simp⟩

theorem Line.isClosed_tube {n : ℕ} (L : Line n) (r : ℝ) : IsClosed (L.tube r) :=
  isClosed_le (Metric.continuous_infDist_pt _) continuous_const

theorem Line.measurableSet_tube {n : ℕ} (L : Line n) (r : ℝ) :
    MeasurableSet (L.tube r) := (L.isClosed_tube r).measurableSet

/-- Columns are the selected unit directions, in the standard orthonormal coordinates. -/
def determinantWeight {n : ℕ} (L : Fin n → Line n) : ℝ≥0∞ :=
  ENNReal.ofReal |Matrix.det (fun i j : Fin n => (L j).direction i)|

def tupleRegion {n : ℕ} (L : Fin n → Line n) (r : ℝ) : Set (E n) :=
  {x | ∀ i, x ∈ (L i).tube r}

theorem measurableSet_tupleRegion {n : ℕ} (L : Fin n → Line n) (r : ℝ) :
    MeasurableSet (tupleRegion L r) := by
  rw [show tupleRegion L r = ⋂ i, (L i).tube r by ext x; simp [tupleRegion]]
  exact MeasurableSet.iInter (fun i => (L i).measurableSet_tube r)

def tupleCoefficient {n : ℕ} {ι : Fin n → Type*}
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (a : ∀ i, ι i) : ℝ≥0∞ :=
  determinantWeight (fun i => L i (a i)) * ∏ i, (w i (a i) : ℝ≥0∞)

/-- The sum inside the manuscript's endpoint power, before integration. -/
def kernel {n : ℕ} {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (r : ℝ) (x : E n) : ℝ≥0∞ :=
  ∑ a : ∀ i, ι i, (tupleRegion (fun i => L i (a i)) r).indicator
    (fun _ => tupleCoefficient L w a) x

theorem measurable_kernel {n : ℕ} {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (r : ℝ) :
    Measurable (kernel L w r) := by
  exact Finset.measurable_sum _ (fun a _ =>
    measurable_const.indicator (measurableSet_tupleRegion _ r))

/-- The finite weighted sum can be integrated without any tube-intersection finiteness
assumption. In particular, zero determinant times infinite volume is handled in ENNReal. -/
theorem lintegral_kernel {n : ℕ} {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (r : ℝ) :
    (∫⁻ x, kernel L w r x ∂volume) =
      ∑ a : ∀ i, ι i, tupleCoefficient L w a *
        volume (tupleRegion (fun i => L i (a i)) r) := by
  unfold kernel
  rw [lintegral_finsetSum _ (fun a _ =>
    measurable_const.indicator (measurableSet_tupleRegion _ r))]
  apply Finset.sum_congr rfl
  intro a _
  rw [lintegral_indicator (measurableSet_tupleRegion _ r)]
  simp

theorem measurable_endpointKernel {n : ℕ} {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (r p : ℝ) :
    Measurable (fun x => (kernel L w r x)^p) :=
  (measurable_kernel L w r).pow_const p

/-- Finite weighted aggregation of a geometric tuple-volume bound. No distinctness,
positive-weight or nonempty-family assumptions are introduced by the aggregation. -/
theorem lintegral_kernel_le_of_tuple_bound {n : ℕ} {ι : Fin n → Type*}
    [∀ i, Fintype (ι i)] (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0)
    (r : ℝ) (B : ℝ≥0∞)
    (hB : ∀ a : ∀ i, ι i, determinantWeight (fun i => L i (a i)) *
      volume (tupleRegion (fun i => L i (a i)) r) ≤ B) :
    (∫⁻ x, kernel L w r x ∂volume) ≤
      B * ∏ i, ∑ a, (w i a : ℝ≥0∞) := by
  rw [lintegral_kernel]
  calc
    _ ≤ ∑ a : ∀ i, ι i, B * ∏ i, (w i (a i) : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro a _
      unfold tupleCoefficient
      calc
        _ = (determinantWeight (fun i => L i (a i)) *
            volume (tupleRegion (fun i => L i (a i)) r)) *
              ∏ i, (w i (a i) : ℝ≥0∞) := by ac_rfl
        _ ≤ _ := by
          simpa only [mul_comm] using
            mul_le_mul_right (hB a) (∏ i, (w i (a i) : ℝ≥0∞))
    _ = _ := by rw [← Finset.mul_sum, Fintype.prod_sum]

def endpointExponent (n : ℕ) : ℝ := 1 / ((n : ℝ) - 1)

/-- The genuine finite-family theorem, with the constant before every numerical input. -/
def EndpointBound (n : ℕ) : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧ ∀ (ι : Fin n → Type) [∀ i, Fintype (ι i)]
    (L : ∀ i, ι i → Line n) (w : ∀ i, ι i → ℝ≥0) (r : ℝ), 0 < r →
    (∫⁻ x, (kernel L w r x) ^ endpointExponent n ∂volume) ≤
      (C : ℝ≥0∞) * ENNReal.ofReal (r^n) *
        ∏ i, (∑ a, (w i a : ℝ≥0∞)) ^ endpointExponent n

/-- The exact dimensional range needed in manuscript a05:determinant-kakeya. -/
def ManuscriptBound : Prop := ∀ n : ℕ, 2 ≤ n → n ≤ 4 → EndpointBound n

end Kakeya4.Hard.MultilinearKakeya
