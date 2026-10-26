import Kakeya4.Hard.MultiplicativeConvolution.RescaledSmoothing

/-! # Actual bounded-noise errors for the six-variable OSS projection expression -/

noncomputable section
open MeasureTheory

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Coordinates are a1,a2,b1,b2,x,y, in that order. -/
def projectionValue (v : Fin 6 → ℝ) : ℝ := (v 2-v 3)*v 4+(v 0-v 1)*v 5

/-- The projection expression has the expected common-scaling factor. -/
theorem projectionValue_scale (v : Fin 6 → ℝ) (c : ℝ) :
    projectionValue (fun i ↦ c*v i) = c^2 * projectionValue v := by
  unfold projectionValue
  ring

/-- Absolute product errors retain both actual coefficient magnitudes. -/
theorem abs_mul_sub_mul_le_parts (a b c d : ℝ) :
    |a*b-c*d| ≤ |a| * |b-d| + |a-c| * |d| := by
  have he : a*b-c*d = a*(b-d)+(a-c)*d := by ring
  rw [he]
  exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])

/-- A difference of two perturbed coordinates costs twice the individual error. -/
theorem abs_sub_sub_sub_le {a b c d δ : ℝ} (ha : |a-c| ≤ δ) (hb : |b-d| ≤ δ) :
    |(a-b)-(c-d)| ≤ 2*δ := by
  have he : (a-b)-(c-d) = (a-c)-(b-d) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

/-- On the actual unit cube the projection has a uniform six-coordinate perturbation bound. -/
theorem projectionValue_perturb_le (p q : Fin 6 → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hp : ∀ i, |p i| ≤ 1) (hq : ∀ i, |q i| ≤ 1) (he : ∀ i, |q i-p i| ≤ δ) :
    |projectionValue q-projectionValue p| ≤ 8*δ := by
  have hterm (i j k : Fin 6) : |(q i-q j)*q k-(p i-p j)*p k| ≤ 4*δ := by
    have h := abs_mul_sub_mul_le_parts (q i-q j) (q k) (p i-p j) (p k)
    have hc : |q i-q j| ≤ 2 := (abs_sub _ _).trans (by linarith [hq i,hq j])
    have hd := abs_sub_sub_sub_le (he i) (he j)
    have hm1 := mul_le_mul hc (he k) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    have hm2 := mul_le_mul hd (hp k) (abs_nonneg _) (by positivity : 0 ≤ 2*δ)
    linarith
  have hsplit : projectionValue q-projectionValue p =
      ((q 2-q 3)*q 4-(p 2-p 3)*p 4)+((q 0-q 1)*q 5-(p 0-p 1)*p 5) := by
    unfold projectionValue
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (by linarith [hterm 2 3 4,hterm 0 1 5])

/-- The literal perturbation used in the extracted law. -/
def noisyHalf (r x u : ℝ) : ℝ := (x+r*u)/2

/-- Unit noise gives the exact half-scale coordinate error. -/
theorem noisyHalf_error {r x u : ℝ} (hr : 0 ≤ r) (hu : |u| ≤ 1) :
    |noisyHalf r x u-x/2| ≤ r/2 := by
  have he : noisyHalf r x u-x/2 = r*u/2 := by unfold noisyHalf; ring
  rw [he, abs_div, abs_mul, abs_of_nonneg hr, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hr hu) (by norm_num)

/-- The actual perturbed half-coordinate lies in the unit interval. -/
theorem noisyHalf_unit {r x u : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (hx : |x| ≤ 1) (hu : |u| ≤ 1) :
    |noisyHalf r x u| ≤ 1 := by
  rw [noisyHalf, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), div_le_one (by norm_num : (0:ℝ) < 2)]
  have hm : |r*u| ≤ r := by rw [abs_mul, abs_of_nonneg hr]; exact mul_le_of_le_one_right hr hu
  linarith [abs_add_le x (r*u)]

/-- The actual smoothed projection differs from one quarter of the original by at most 4r. -/
theorem projectionValue_noisyHalf_error (v u : Fin 6 → ℝ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hv : ∀ i, |v i| ≤ 1) (hu : ∀ i, |u i| ≤ 1) :
    |projectionValue (fun i ↦ noisyHalf r (v i) (u i)) - projectionValue v / 4| ≤ 4*r := by
  have hp : ∀ i, |v i/2| ≤ 1 := by
    intro i
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), div_le_one (by norm_num : (0:ℝ) < 2)]
    linarith [hv i]
  have h := projectionValue_perturb_le (fun i ↦ v i/2) (fun i ↦ noisyHalf r (v i) (u i))
    (by positivity : 0 ≤ r/2) hp (fun i ↦ noisyHalf_unit hr hr1 (hv i) (hu i))
    (fun i ↦ noisyHalf_error hr (hu i))
  have he : projectionValue (fun i ↦ v i/2) = projectionValue v/4 := by
    unfold projectionValue
    ring
  rw [he] at h
  linarith

end Kakeya4.Hard.MultiplicativeConvolution
