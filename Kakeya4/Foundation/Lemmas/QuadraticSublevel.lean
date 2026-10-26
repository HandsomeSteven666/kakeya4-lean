import Kakeya4.Foundation.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Quadratic sublevel sets

Formalization of the manuscript's `lem:quadratic-sublevel`:
for a real polynomial `Q` of degree at most two and `ε, b > 0`, the set
`{w : |Q w| ≤ ε, |Q' w| ≥ b}` has length at most `4 ε / b` and meets at most
`C (1 + ε / (b δ))` bins of any grid of width `δ`.

The proof splits at the vertex of the quadratic: on each side `Q` is monotone, and the
one-dimensional change-of-variables formula bounds the length by `2 ε / b`.
-/

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure Set Metric Polynomial
open scoped ENNReal NNReal BigOperators

namespace Kakeya4

/-- A real polynomial of degree at most two is determined by its three lowest coefficients. -/
lemma polynomial_eq_quadratic (Q : ℝ[X]) (hQ : Q.degree ≤ 2) :
    Q = C (Q.coeff 2) * X ^ 2 + C (Q.coeff 1) * X + C (Q.coeff 0) := by
  ext n
  match n with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | n + 3 =>
    have hcoeff : Q.coeff (n + 3) = 0 := by
      apply Polynomial.coeff_eq_zero_of_degree_lt
      have hlt : (2 : ℕ) < n + 3 := by omega
      exact lt_of_le_of_lt hQ (WithBot.coe_lt_coe.mpr hlt)
    simp [hcoeff]

/-- Evaluation of a quadratic polynomial. -/
lemma eval_quadratic (a b c x : ℝ) :
    (C a * X ^ 2 + C b * X + C c : ℝ[X]).eval x = a * x ^ 2 + b * x + c := by
  simp [eval_add, eval_mul, eval_pow, eval_C, eval_X]

/-- Derivative of a quadratic polynomial. -/
lemma derivative_quadratic (a b c : ℝ) :
    (C a * X ^ 2 + C b * X + C c : ℝ[X]).derivative = C (2 * a) * X + C b := by
  simp [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_pow]
  ring

/-- Evaluation of the derivative of a quadratic polynomial. -/
lemma eval_derivative_quadratic (a b c x : ℝ) :
    (C a * X ^ 2 + C b * X + C c : ℝ[X]).derivative.eval x = 2 * a * x + b := by
  rw [derivative_quadratic]
  simp

/-- Derivative of an explicit quadratic polynomial, in `HasDerivAt` form. -/
lemma hasDerivAt_quadratic (a b₁ c x : ℝ) :
    HasDerivAt (fun w => a * w ^ 2 + b₁ * w + c) (2 * a * x + b₁) x := by
  have h := Polynomial.hasDerivAt (C a * X ^ 2 + C b₁ * X + C c : ℝ[X]) x
  have hfun : (fun x => (C a * X ^ 2 + C b₁ * X + C c : ℝ[X]).eval x) =
      (fun w => a * w ^ 2 + b₁ * w + c) := by
    funext w
    simp [eval_quadratic]
  have hder : (C a * X ^ 2 + C b₁ * X + C c : ℝ[X]).derivative.eval x = 2 * a * x + b₁ := by
    rw [eval_derivative_quadratic]
  rw [hfun, hder] at h
  exact h

/-- The derivative threshold of a nondegenerate quadratic: `|Q' w| ≥ b` is the union of the
two half-lines cut out by the vertex and `b / (2|a|)`. -/
lemma quadratic_deriv_threshold (a b₁ b w : ℝ) (ha : a ≠ 0) (hb : 0 < b) :
    b ≤ |2 * a * w + b₁| ↔
      w ≤ -b₁ / (2 * a) - b / (2 * |a|) ∨
      -b₁ / (2 * a) + b / (2 * |a|) ≤ w := by
  have ha' : 0 < |a| := abs_pos.mpr ha
  have h2a : 0 < 2 * |a| := by positivity
  set r : ℝ := -b₁ / (2 * a) with hr
  set δ : ℝ := b / (2 * |a|) with hδ
  have hδpos : 0 < δ := by positivity
  have h2a_abs : |2 * a| = 2 * |a| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hfactor : 2 * a * w + b₁ = 2 * a * (w - r) := by
    rw [hr]
    field_simp
    ring
  rw [hfactor, abs_mul, h2a_abs]
  have hdiv : b ≤ 2 * |a| * |w - r| ↔ δ ≤ |w - r| := by
    rw [hδ]
    constructor
    · intro h
      rw [div_le_iff₀ h2a]
      linarith
    · intro h
      rw [div_le_iff₀ h2a] at h
      linarith
  rw [hdiv, le_abs]
  rw [hr, hδ] at *
  constructor
  · rintro (h | h)
    · right; linarith
    · left; linarith
  · rintro (h | h)
    · right; linarith
    · left; linarith

/-- Length bound on a set where a monotone function has derivative at least `B` and values
in `[-ε, ε]`. -/
lemma volume_le_of_monotoneOn_deriv_ge
    {f f' : ℝ → ℝ} {s : Set ℝ} {ε B : ℝ}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hmono : MonotoneOn f s)
    (hB : 0 < B)
    (hderiv : ∀ x ∈ s, B ≤ f' x)
    (hε : ∀ x ∈ s, |f x| ≤ ε) :
    volume s ≤ ENNReal.ofReal (2 * ε / B) := by
  have h_int : ∫⁻ x in s, ENNReal.ofReal B ≤ ∫⁻ x in s, ENNReal.ofReal (f' x) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hs] with x hx
    exact ENNReal.ofReal_le_ofReal (hderiv x hx)
  rw [lintegral_deriv_eq_volume_image_of_monotoneOn hs hf' hmono] at h_int
  have h_image : volume (f '' s) ≤ ENNReal.ofReal (2 * ε) := by
    calc
      volume (f '' s) ≤ volume (Set.Icc (-ε) ε) := by
        refine measure_mono ?_
        rintro y ⟨x, hx, rfl⟩
        exact abs_le.mp (hε x hx)
      _ = ENNReal.ofReal (2 * ε) := by
        rw [Real.volume_Icc]
        congr 1
        ring
  have h_const : ∫⁻ x in s, ENNReal.ofReal B = ENNReal.ofReal B * volume s := by
    simp [lintegral_const]
  rw [h_const] at h_int
  have hB0 : ENNReal.ofReal B ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hB
  have hBtop : ENNReal.ofReal B ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    volume s = (ENNReal.ofReal B)⁻¹ * (ENNReal.ofReal B * volume s) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hB0 hBtop, one_mul]
    _ ≤ (ENNReal.ofReal B)⁻¹ * ENNReal.ofReal (2 * ε) := by
      gcongr
      exact h_int.trans h_image
    _ = ENNReal.ofReal (2 * ε / B) := by
      rw [ENNReal.ofReal_div_of_pos hB, div_eq_mul_inv, mul_comm]

/-- Length bound on a set where an antitone function has derivative at most `-B` and values
in `[-ε, ε]`. -/
lemma volume_le_of_antitoneOn_deriv_ge
    {f f' : ℝ → ℝ} {s : Set ℝ} {ε B : ℝ}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hanti : AntitoneOn f s)
    (hB : 0 < B)
    (hderiv : ∀ x ∈ s, B ≤ -f' x)
    (hε : ∀ x ∈ s, |f x| ≤ ε) :
    volume s ≤ ENNReal.ofReal (2 * ε / B) := by
  have h_int : ∫⁻ x in s, ENNReal.ofReal B ≤ ∫⁻ x in s, ENNReal.ofReal (-f' x) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hs] with x hx
    exact ENNReal.ofReal_le_ofReal (hderiv x hx)
  rw [lintegral_deriv_eq_volume_image_of_antitoneOn hs hf' hanti] at h_int
  have h_image : volume (f '' s) ≤ ENNReal.ofReal (2 * ε) := by
    calc
      volume (f '' s) ≤ volume (Set.Icc (-ε) ε) := by
        refine measure_mono ?_
        rintro y ⟨x, hx, rfl⟩
        exact abs_le.mp (hε x hx)
      _ = ENNReal.ofReal (2 * ε) := by
        rw [Real.volume_Icc]
        congr 1
        ring
  have h_const : ∫⁻ x in s, ENNReal.ofReal B = ENNReal.ofReal B * volume s := by
    simp [lintegral_const]
  rw [h_const] at h_int
  have hB0 : ENNReal.ofReal B ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hB
  have hBtop : ENNReal.ofReal B ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    volume s = (ENNReal.ofReal B)⁻¹ * (ENNReal.ofReal B * volume s) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hB0 hBtop, one_mul]
    _ ≤ (ENNReal.ofReal B)⁻¹ * ENNReal.ofReal (2 * ε) := by
      gcongr
      exact h_int.trans h_image
    _ = ENNReal.ofReal (2 * ε / B) := by
      rw [ENNReal.ofReal_div_of_pos hB, div_eq_mul_inv, mul_comm]

/-- Length bound for an affine polynomial. -/
lemma affine_sublevel_volume (b₁ c ε b : ℝ) (hε : 0 < ε) (hb : 0 < b) :
    volume {w : ℝ | |b₁ * w + c| ≤ ε ∧ b ≤ |b₁|} ≤ ENNReal.ofReal (4 * ε / b) := by
  by_cases hlt : |b₁| < b
  · have hS : {w : ℝ | |b₁ * w + c| ≤ ε ∧ b ≤ |b₁|} = ∅ := by
      ext w
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun _ => not_le_of_gt hlt
    rw [hS]
    simp
  · have hb₁ : b ≤ |b₁| := le_of_not_gt hlt
    have hb₁ne : b₁ ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hb₁
      linarith
    have h₂ : (2 * ε / b) ≤ 4 * ε / b := by
      apply div_le_div_of_nonneg_right _ hb.le
      linarith
    by_cases hpos : 0 < b₁
    · have hvol := volume_le_of_monotoneOn_deriv_ge
        (s := {w : ℝ | |b₁ * w + c| ≤ ε ∧ b ≤ |b₁|})
        (f := fun w => b₁ * w + c) (f' := fun _ => b₁) (ε := ε) (B := b)
        ?_ ?_ ?_ hb ?_ ?_
      · exact hvol.trans (ENNReal.ofReal_le_ofReal h₂)
      · have hset : {w : ℝ | |b₁ * w + c| ≤ ε ∧ b ≤ |b₁|} =
            {w : ℝ | b₁ * w + c ∈ Set.Icc (-ε) ε} := by
          ext w
          simp [abs_le, hb₁]
        rw [hset]
        exact isClosed_Icc.preimage (by fun_prop) |>.measurableSet
      · intro x _
        simpa using ((hasDerivAt_id x).const_mul b₁).add_const c |>.hasDerivWithinAt
      · intro x _ y _ hxy
        nlinarith
      · intro x _
        rw [abs_of_pos hpos] at hb₁
        exact hb₁
      · intro x hx
        exact hx.1
    · have hneg : b₁ < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hb₁ne
      have hvol := volume_le_of_antitoneOn_deriv_ge
        (s := {w : ℝ | |b₁ * w + c| ≤ ε ∧ b ≤ |b₁|})
        (f := fun w => b₁ * w + c) (f' := fun _ => b₁) (ε := ε) (B := b)
        ?_ ?_ ?_ hb ?_ ?_
      · exact hvol.trans (ENNReal.ofReal_le_ofReal h₂)
      · have hset : {w : ℝ | |b₁ * w + c| ≤ ε ∧ b ≤ |b₁|} =
            {w : ℝ | b₁ * w + c ∈ Set.Icc (-ε) ε} := by
          ext w
          simp [abs_le, hb₁]
        rw [hset]
        exact isClosed_Icc.preimage (by fun_prop) |>.measurableSet
      · intro x _
        simpa using ((hasDerivAt_id x).const_mul b₁).add_const c |>.hasDerivWithinAt
      · intro x _ y _ hxy
        nlinarith
      · intro x _
        rw [abs_of_neg hneg] at hb₁
        linarith
      · intro x hx
        exact hx.1

/-- On the left of the vertex, a convex quadratic is antitone. -/
lemma quadratic_antitoneOn_left (a b₁ c r₁ : ℝ) (ha : 0 < a)
    (hr₁ : r₁ ≤ -b₁ / (2 * a)) :
    AntitoneOn (fun w => a * w ^ 2 + b₁ * w + c) (Set.Iic r₁) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hroot : 2 * a * (-b₁ / (2 * a)) + b₁ = 0 := by
    field_simp
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Iic r₁)
  · fun_prop
  · fun_prop
  · intro w hw
    rw [interior_Iic] at hw
    have hwle : w ≤ -b₁ / (2 * a) := hw.le.trans hr₁
    have hfac : 2 * a * w + b₁ = 2 * a * (w - (-b₁ / (2 * a))) := by
      nlinarith [hroot]
    have hderiv : deriv (fun w => a * w ^ 2 + b₁ * w + c) w = 2 * a * w + b₁ :=
      (hasDerivAt_quadratic a b₁ c w).deriv
    rw [hderiv, hfac]
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

/-- On the right of the vertex, a convex quadratic is monotone. -/
lemma quadratic_monotoneOn_right (a b₁ c r₂ : ℝ) (ha : 0 < a)
    (hr₂ : -b₁ / (2 * a) ≤ r₂) :
    MonotoneOn (fun w => a * w ^ 2 + b₁ * w + c) (Set.Ici r₂) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hroot : 2 * a * (-b₁ / (2 * a)) + b₁ = 0 := by
    field_simp
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Ici r₂)
  · fun_prop
  · fun_prop
  · intro w hw
    rw [interior_Ici] at hw
    have hwge : -b₁ / (2 * a) ≤ w := hr₂.trans hw.le
    have hfac : 2 * a * w + b₁ = 2 * a * (w - (-b₁ / (2 * a))) := by
      nlinarith [hroot]
    have hderiv : deriv (fun w => a * w ^ 2 + b₁ * w + c) w = 2 * a * w + b₁ :=
      (hasDerivAt_quadratic a b₁ c w).deriv
    rw [hderiv, hfac]
    exact mul_nonneg (by linarith) (by linarith)

/-- On the left of the vertex, a concave quadratic is monotone. -/
lemma quadratic_monotoneOn_left (a b₁ c r₁ : ℝ) (ha : a < 0)
    (hr₁ : r₁ ≤ -b₁ / (2 * a)) :
    MonotoneOn (fun w => a * w ^ 2 + b₁ * w + c) (Set.Iic r₁) := by
  have ha0 : a ≠ 0 := ne_of_lt ha
  have hroot : 2 * a * (-b₁ / (2 * a)) + b₁ = 0 := by
    field_simp
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Iic r₁)
  · fun_prop
  · fun_prop
  · intro w hw
    rw [interior_Iic] at hw
    have hwle : w ≤ -b₁ / (2 * a) := hw.le.trans hr₁
    have hfac : 2 * a * w + b₁ = 2 * a * (w - (-b₁ / (2 * a))) := by
      nlinarith [hroot]
    have hderiv : deriv (fun w => a * w ^ 2 + b₁ * w + c) w = 2 * a * w + b₁ :=
      (hasDerivAt_quadratic a b₁ c w).deriv
    rw [hderiv, hfac]
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

/-- On the right of the vertex, a concave quadratic is antitone. -/
lemma quadratic_antitoneOn_right (a b₁ c r₂ : ℝ) (ha : a < 0)
    (hr₂ : -b₁ / (2 * a) ≤ r₂) :
    AntitoneOn (fun w => a * w ^ 2 + b₁ * w + c) (Set.Ici r₂) := by
  have ha0 : a ≠ 0 := ne_of_lt ha
  have hroot : 2 * a * (-b₁ / (2 * a)) + b₁ = 0 := by
    field_simp
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici r₂)
  · fun_prop
  · fun_prop
  · intro w hw
    rw [interior_Ici] at hw
    have hwge : -b₁ / (2 * a) ≤ w := hr₂.trans hw.le
    have hfac : 2 * a * w + b₁ = 2 * a * (w - (-b₁ / (2 * a))) := by
      nlinarith [hroot]
    have hderiv : deriv (fun w => a * w ^ 2 + b₁ * w + c) w = 2 * a * w + b₁ :=
      (hasDerivAt_quadratic a b₁ c w).deriv
    rw [hderiv, hfac]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

/-- Length bound for an explicit quadratic polynomial. -/
theorem quadratic_sublevel_volume_explicit (a b₁ c ε b : ℝ) (hε : 0 < ε) (hb : 0 < b) :
    volume {w : ℝ | |a * w ^ 2 + b₁ * w + c| ≤ ε ∧ b ≤ |2 * a * w + b₁|} ≤
      ENNReal.ofReal (4 * ε / b) := by
  by_cases ha : a = 0
  · subst a
    simpa using affine_sublevel_volume b₁ c ε b hε hb
  · have hroot : 2 * a * (-b₁ / (2 * a)) + b₁ = 0 := by
      field_simp
      ring
    set r : ℝ := -b₁ / (2 * a) with hr
    set δ : ℝ := b / (2 * |a|) with hδ
    have hδpos : 0 < δ := by rw [hδ]; positivity
    let S : Set ℝ := {w : ℝ | |a * w ^ 2 + b₁ * w + c| ≤ ε ∧ b ≤ |2 * a * w + b₁|}
    let S₁ : Set ℝ := {w : ℝ | w ≤ r - δ ∧ |a * w ^ 2 + b₁ * w + c| ≤ ε}
    let S₂ : Set ℝ := {w : ℝ | r + δ ≤ w ∧ |a * w ^ 2 + b₁ * w + c| ≤ ε}
    have hS : S = S₁ ∪ S₂ := by
      ext w
      change (|a * w ^ 2 + b₁ * w + c| ≤ ε ∧ b ≤ |2 * a * w + b₁|) ↔
        (w ≤ r - δ ∧ |a * w ^ 2 + b₁ * w + c| ≤ ε) ∨
        (r + δ ≤ w ∧ |a * w ^ 2 + b₁ * w + c| ≤ ε)
      rw [quadratic_deriv_threshold a b₁ b w ha hb]
      tauto
    have hS₁meas : MeasurableSet S₁ := by
      have hset : S₁ = {w : ℝ | w ≤ r - δ} ∩ {w : ℝ | a * w ^ 2 + b₁ * w + c ∈ Set.Icc (-ε) ε} := by
        ext w
        simp [S₁, abs_le]
      rw [hset]
      exact measurableSet_Iic.inter (isClosed_Icc.preimage (by fun_prop) |>.measurableSet)
    have hS₂meas : MeasurableSet S₂ := by
      have hset : S₂ = {w : ℝ | r + δ ≤ w} ∩ {w : ℝ | a * w ^ 2 + b₁ * w + c ∈ Set.Icc (-ε) ε} := by
        ext w
        simp [S₂, abs_le]
      rw [hset]
      exact measurableSet_Ici.inter (isClosed_Icc.preimage (by fun_prop) |>.measurableSet)
    have hS₁bound : volume S₁ ≤ ENNReal.ofReal (2 * ε / b) := by
      by_cases hapos : 0 < a
      · have h2aδ : 2 * a * δ = b := by
          rw [hδ, abs_of_pos hapos]
          field_simp
        have hanti : AntitoneOn (fun w => a * w ^ 2 + b₁ * w + c) S₁ :=
          (quadratic_antitoneOn_left a b₁ c (r - δ) hapos (by linarith)).mono (by
            intro w hw
            exact hw.1)
        refine volume_le_of_antitoneOn_deriv_ge (f' := fun w => 2 * a * w + b₁) hS₁meas ?_ hanti hb ?_ ?_
        · intro x _
          exact (hasDerivAt_quadratic a b₁ c x).hasDerivWithinAt
        · intro x hx
          have hxle : x ≤ r - δ := hx.1
          have hfac : 2 * a * x + b₁ = 2 * a * (x - r) := by nlinarith [hroot]
          have : 2 * a * (x - r) ≤ -b := by nlinarith
          linarith
        · intro x hx
          exact hx.2
      · have haneg : a < 0 := lt_of_le_of_ne (le_of_not_gt hapos) ha
        have h2aδ : 2 * a * δ = -b := by
          rw [hδ, abs_of_neg haneg]
          field_simp
        have hmono : MonotoneOn (fun w => a * w ^ 2 + b₁ * w + c) S₁ :=
          (quadratic_monotoneOn_left a b₁ c (r - δ) haneg (by linarith)).mono (by
            intro w hw
            exact hw.1)
        refine volume_le_of_monotoneOn_deriv_ge (f' := fun w => 2 * a * w + b₁) hS₁meas ?_ hmono hb ?_ ?_
        · intro x _
          exact (hasDerivAt_quadratic a b₁ c x).hasDerivWithinAt
        · intro x hx
          have hxle : x ≤ r - δ := hx.1
          have hfac : 2 * a * x + b₁ = 2 * a * (x - r) := by nlinarith [hroot]
          have : b ≤ 2 * a * (x - r) := by nlinarith
          linarith
        · intro x hx
          exact hx.2
    have hS₂bound : volume S₂ ≤ ENNReal.ofReal (2 * ε / b) := by
      by_cases hapos : 0 < a
      · have h2aδ : 2 * a * δ = b := by
          rw [hδ, abs_of_pos hapos]
          field_simp
        have hmono : MonotoneOn (fun w => a * w ^ 2 + b₁ * w + c) S₂ :=
          (quadratic_monotoneOn_right a b₁ c (r + δ) hapos (by linarith)).mono (by
            intro w hw
            exact hw.1)
        refine volume_le_of_monotoneOn_deriv_ge (f' := fun w => 2 * a * w + b₁) hS₂meas ?_ hmono hb ?_ ?_
        · intro x _
          exact (hasDerivAt_quadratic a b₁ c x).hasDerivWithinAt
        · intro x hx
          have hxge : r + δ ≤ x := hx.1
          have hfac : 2 * a * x + b₁ = 2 * a * (x - r) := by nlinarith [hroot]
          have : b ≤ 2 * a * (x - r) := by nlinarith
          linarith
        · intro x hx
          exact hx.2
      · have haneg : a < 0 := lt_of_le_of_ne (le_of_not_gt hapos) ha
        have h2aδ : 2 * a * δ = -b := by
          rw [hδ, abs_of_neg haneg]
          field_simp
        have hanti : AntitoneOn (fun w => a * w ^ 2 + b₁ * w + c) S₂ :=
          (quadratic_antitoneOn_right a b₁ c (r + δ) haneg (by linarith)).mono (by
            intro w hw
            exact hw.1)
        refine volume_le_of_antitoneOn_deriv_ge (f' := fun w => 2 * a * w + b₁) hS₂meas ?_ hanti hb ?_ ?_
        · intro x _
          exact (hasDerivAt_quadratic a b₁ c x).hasDerivWithinAt
        · intro x hx
          have hxge : r + δ ≤ x := hx.1
          have hfac : 2 * a * x + b₁ = 2 * a * (x - r) := by nlinarith [hroot]
          have : 2 * a * (x - r) ≤ -b := by nlinarith
          linarith
        · intro x hx
          exact hx.2
    change volume S ≤ ENNReal.ofReal (4 * ε / b)
    rw [hS]
    calc
      volume (S₁ ∪ S₂) ≤ volume S₁ + volume S₂ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (2 * ε / b) + ENNReal.ofReal (2 * ε / b) := by
        exact add_le_add hS₁bound hS₂bound
      _ = ENNReal.ofReal (4 * ε / b) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **Quadratic sublevel sets** (manuscript `lem:quadratic-sublevel`), length bound:
for a real polynomial of degree at most two, the set `{|Q| ≤ ε, |Q'| ≥ b}` has length at
most `4 ε / b`. -/
theorem quadratic_sublevel_volume (Q : ℝ[X]) (hQ : Q.degree ≤ 2) {ε b : ℝ}
    (hε : 0 < ε) (hb : 0 < b) :
    volume {w : ℝ | |Q.eval w| ≤ ε ∧ b ≤ |Q.derivative.eval w|} ≤
      ENNReal.ofReal (4 * ε / b) := by
  have hQeq := polynomial_eq_quadratic Q hQ
  rw [hQeq]
  have htwo : ∀ w : ℝ,
      Q.coeff 2 * ((1 + 1) * w) + Q.coeff 1 = 2 * Q.coeff 2 * w + Q.coeff 1 := by
    intro w
    ring
  simpa [eval_quadratic, eval_derivative_quadratic, htwo] using
    quadratic_sublevel_volume_explicit (Q.coeff 2) (Q.coeff 1) (Q.coeff 0) ε b hε hb

/-- Diameter bound for a quadratic sublevel set on a half-line where `|Q'| ≥ b`. -/
lemma quadratic_diameter_le_left
    (a b₁ c ε b r : ℝ) (hε : 0 < ε) (hb : 0 < b)
    (hderiv : ∀ w ≤ r, b ≤ |2 * a * w + b₁|)
    {x y : ℝ} (hx : x ≤ r) (hy : y ≤ r)
    (hxε : |a * x ^ 2 + b₁ * x + c| ≤ ε)
    (hyε : |a * y ^ 2 + b₁ * y + c| ≤ ε) :
    |x - y| ≤ 2 * ε / b := by
  have core : ∀ {u v : ℝ}, u ≤ r → v ≤ r →
      |a * u ^ 2 + b₁ * u + c| ≤ ε → |a * v ^ 2 + b₁ * v + c| ≤ ε →
      u ≤ v → |u - v| ≤ 2 * ε / b := by
    intro u v hu hv huε hvε huv
    rcases lt_or_eq_of_le huv with huvlt | rfl
    · obtain ⟨z, hz, hzslope⟩ := exists_deriv_eq_slope
        (fun w => a * w ^ 2 + b₁ * w + c) huvlt (by fun_prop) (by fun_prop)
      have hzr : z ≤ r := by linarith [hz.2, hv]
      have hzd : b ≤ |deriv (fun w => a * w ^ 2 + b₁ * w + c) z| := by
        rw [(hasDerivAt_quadratic a b₁ c z).deriv]
        exact hderiv z hzr
      have hval : |(a * v ^ 2 + b₁ * v + c) - (a * u ^ 2 + b₁ * u + c)| ≤ 2 * ε := by
        calc
          _ ≤ |a * v ^ 2 + b₁ * v + c| + |a * u ^ 2 + b₁ * u + c| := by
            calc
              |(a * v ^ 2 + b₁ * v + c) - (a * u ^ 2 + b₁ * u + c)|
                  = |(a * v ^ 2 + b₁ * v + c) + (-(a * u ^ 2 + b₁ * u + c))| := by ring_nf
              _ ≤ |a * v ^ 2 + b₁ * v + c| + |-(a * u ^ 2 + b₁ * u + c)| := abs_add_le _ _
              _ = |a * v ^ 2 + b₁ * v + c| + |a * u ^ 2 + b₁ * u + c| := by rw [abs_neg]
          _ ≤ ε + ε := add_le_add hvε huε
          _ = 2 * ε := by ring
      have hden : 0 < v - u := by linarith
      have hrepr : |(a * v ^ 2 + b₁ * v + c) - (a * u ^ 2 + b₁ * u + c)| =
          |deriv (fun w => a * w ^ 2 + b₁ * w + c) z| * (v - u) := by
        rw [hzslope, abs_div, abs_of_pos hden]
        field_simp
      have hmain : b * (v - u) ≤ 2 * ε := by
        calc
          b * (v - u) ≤ |deriv (fun w => a * w ^ 2 + b₁ * w + c) z| * (v - u) :=
            mul_le_mul_of_nonneg_right hzd (by linarith)
          _ = |(a * v ^ 2 + b₁ * v + c) - (a * u ^ 2 + b₁ * u + c)| := hrepr.symm
          _ ≤ 2 * ε := hval
      have : v - u ≤ 2 * ε / b := by
        rw [le_div_iff₀ hb]
        linarith
      have habs : |u - v| = v - u := by
        rw [abs_of_nonpos (by linarith : u - v ≤ 0)]
        ring
      rw [habs]
      exact this
    · simp
      positivity
  by_cases hxy : x ≤ y
  · exact core hx hy hxε hyε hxy
  · have hyx : y ≤ x := le_of_lt (not_le.mp hxy)
    have := core hy hx hyε hxε hyx
    rwa [abs_sub_comm]

/-- Diameter bound for a quadratic sublevel set on a right half-line where `|Q'| ≥ b`. -/
lemma quadratic_diameter_le_right
    (a b₁ c ε b r : ℝ) (hε : 0 < ε) (hb : 0 < b)
    (hderiv : ∀ w, r ≤ w → b ≤ |2 * a * w + b₁|)
    {x y : ℝ} (hx : r ≤ x) (hy : r ≤ y)
    (hxε : |a * x ^ 2 + b₁ * x + c| ≤ ε)
    (hyε : |a * y ^ 2 + b₁ * y + c| ≤ ε) :
    |x - y| ≤ 2 * ε / b := by
  have core : ∀ {u v : ℝ}, r ≤ u → r ≤ v →
      |a * u ^ 2 + b₁ * u + c| ≤ ε → |a * v ^ 2 + b₁ * v + c| ≤ ε →
      u ≤ v → |u - v| ≤ 2 * ε / b := by
    intro u v hu hv huε hvε huv
    rcases lt_or_eq_of_le huv with huvlt | rfl
    · obtain ⟨z, hz, hzslope⟩ := exists_deriv_eq_slope
        (fun w => a * w ^ 2 + b₁ * w + c) huvlt (by fun_prop) (by fun_prop)
      have hzr : r ≤ z := by linarith [hu, hz.1]
      have hzd : b ≤ |deriv (fun w => a * w ^ 2 + b₁ * w + c) z| := by
        rw [(hasDerivAt_quadratic a b₁ c z).deriv]
        exact hderiv z hzr
      have hval : |(a * v ^ 2 + b₁ * v + c) - (a * u ^ 2 + b₁ * u + c)| ≤ 2 * ε := by
        calc
          _ ≤ |a * v ^ 2 + b₁ * v + c| + |a * u ^ 2 + b₁ * u + c| := by
            calc
              |(a * v ^ 2 + b₁ * v + c) - (a * u ^ 2 + b₁ * u + c)|
                  = |(a * v ^ 2 + b₁ * v + c) + (-(a * u ^ 2 + b₁ * u + c))| := by ring_nf
              _ ≤ |a * v ^ 2 + b₁ * v + c| + |-(a * u ^ 2 + b₁ * u + c)| := abs_add_le _ _
              _ = |a * v ^ 2 + b₁ * v + c| + |a * u ^ 2 + b₁ * u + c| := by rw [abs_neg]
          _ ≤ ε + ε := add_le_add hvε huε
          _ = 2 * ε := by ring
      have hden : 0 < v - u := by linarith
      have hrepr : |(a * v ^ 2 + b₁ * v + c) - (a * u ^ 2 + b₁ * u + c)| =
          |deriv (fun w => a * w ^ 2 + b₁ * w + c) z| * (v - u) := by
        rw [hzslope, abs_div, abs_of_pos hden]
        field_simp
      have hmain : b * (v - u) ≤ 2 * ε := by
        calc
          b * (v - u) ≤ |deriv (fun w => a * w ^ 2 + b₁ * w + c) z| * (v - u) :=
            mul_le_mul_of_nonneg_right hzd (by linarith)
          _ = |(a * v ^ 2 + b₁ * v + c) - (a * u ^ 2 + b₁ * u + c)| := hrepr.symm
          _ ≤ 2 * ε := hval
      have : v - u ≤ 2 * ε / b := by
        rw [le_div_iff₀ hb]
        linarith
      have habs : |u - v| = v - u := by
        rw [abs_of_nonpos (by linarith : u - v ≤ 0)]
        ring
      rw [habs]
      exact this
    · simp
      positivity
  by_cases hxy : x ≤ y
  · exact core hx hy hxε hyε hxy
  · have hyx : y ≤ x := le_of_lt (not_le.mp hxy)
    have := core hy hx hyε hxε hyx
    rwa [abs_sub_comm]

/-- The number of `δ`-bins meeting an interval `[a,b]` is at most `(b-a)/δ + 2`. -/
lemma card_bins_le_of_interval
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    (K : Finset ℤ)
    (hK : ∀ k ∈ K, ∃ w : ℝ, w ∈ Set.Icc a b ∧ w ∈ Set.Ico (k * δ) ((k + 1) * δ)) :
    (K.card : ℝ) ≤ (b - a) / δ + 2 := by
  have hKsub : K ⊆ Finset.Icc (⌊a / δ⌋) (⌊b / δ⌋) := by
    intro k hk
    obtain ⟨w, hwab, hwbin⟩ := hK k hk
    rw [Finset.mem_Icc]
    constructor
    · have h1 : a / δ - 1 < (k : ℝ) := by
        have h2 : a / δ < (k : ℝ) + 1 := by
          rw [div_lt_iff₀ hδ]
          nlinarith [hwab.1, hwbin.2]
        linarith
      have h3 : (⌊a / δ⌋ : ℝ) - 1 < (k : ℝ) := by
        have := Int.floor_le (a / δ)
        linarith
      have h4 : (⌊a / δ⌋ - 1 : ℤ) < k := by exact_mod_cast h3
      omega
    · have h1 : (k : ℝ) ≤ b / δ := by
        rw [le_div_iff₀ hδ]
        nlinarith [hwbin.1, hwab.2]
      exact Int.le_floor.mpr h1
  have hcard : K.card ≤ (⌊b / δ⌋ - ⌊a / δ⌋ + 1).toNat := by
    calc
      K.card ≤ (Finset.Icc (⌊a / δ⌋) (⌊b / δ⌋)).card := Finset.card_le_card hKsub
      _ = (⌊b / δ⌋ - ⌊a / δ⌋ + 1).toNat := by
        rw [Int.card_Icc]
        ring_nf
  have hfloors : (⌊a / δ⌋) ≤ (⌊b / δ⌋) := by
    apply Int.floor_mono
    gcongr
  have hnonneg : 0 ≤ ⌊b / δ⌋ - ⌊a / δ⌋ + 1 := by omega
  have hcast : ((⌊b / δ⌋ - ⌊a / δ⌋ + 1).toNat : ℝ) =
      ((⌊b / δ⌋ - ⌊a / δ⌋ + 1 : ℤ) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hnonneg)
  have hbound : ((⌊b / δ⌋ - ⌊a / δ⌋ + 1 : ℤ) : ℝ) ≤ (b - a) / δ + 2 := by
    have hbfloor : ((⌊b / δ⌋ : ℤ) : ℝ) ≤ b / δ := Int.floor_le _
    have hafloor : a / δ - 1 < ((⌊a / δ⌋ : ℤ) : ℝ) := by
      have := Int.lt_floor_add_one (a / δ)
      linarith
    have hdiv : (b - a) / δ = b / δ - a / δ := by
      field_simp
    rw [hdiv]
    push_cast
    linarith
  calc
    (K.card : ℝ) ≤ ((⌊b / δ⌋ - ⌊a / δ⌋ + 1).toNat : ℝ) := by exact_mod_cast hcard
    _ = ((⌊b / δ⌋ - ⌊a / δ⌋ + 1 : ℤ) : ℝ) := hcast
    _ ≤ (b - a) / δ + 2 := hbound

/-- The number of `δ`-bins meeting a nonempty set of diameter at most `D` is at most
`2 D / δ + 2`. -/
lemma card_bins_le_of_diameter
    {S : Set ℝ} {δ D : ℝ} (hδ : 0 < δ) (hD : 0 ≤ D)
    (hne : S.Nonempty)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ D)
    (K : Finset ℤ)
    (hK : ∀ k ∈ K, ∃ w ∈ S, w ∈ Set.Ico (k * δ) ((k + 1) * δ)) :
    (K.card : ℝ) ≤ 2 * D / δ + 2 := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hsub : ∀ k ∈ K, ∃ w : ℝ,
      w ∈ Set.Icc (x₀ - D) (x₀ + D) ∧ w ∈ Set.Ico (k * δ) ((k + 1) * δ) := by
    intro k hk
    obtain ⟨w, hwS, hwbin⟩ := hK k hk
    have hdist := hdiam w hwS x₀ hx₀
    have hmem : w ∈ Set.Icc (x₀ - D) (x₀ + D) := by
      have := abs_le.mp hdist
      constructor <;> linarith
    exact ⟨w, hmem, hwbin⟩
  have hab : x₀ - D ≤ x₀ + D := by linarith
  have h := card_bins_le_of_interval (δ := δ) (a := x₀ - D) (b := x₀ + D) hδ hab K hsub
  convert h using 2
  ring_nf

/-- **Quadratic sublevel sets** (manuscript `lem:quadratic-sublevel`), full statement:
the length bound and the grid-bin count. -/
def QuadraticSublevelStatement : Prop :=
  ∀ (Q : ℝ[X]), Q.degree ≤ 2 → ∀ ε b δ : ℝ, 0 < ε → 0 < b → 0 < δ →
    volume {w : ℝ | |Q.eval w| ≤ ε ∧ b ≤ |Q.derivative.eval w|} ≤
        ENNReal.ofReal (4 * ε / b) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ K : Finset ℤ,
        (∀ k ∈ K, ∃ w : ℝ, |Q.eval w| ≤ ε ∧ b ≤ |Q.derivative.eval w| ∧
          w ∈ Set.Ico (k * δ) ((k + 1) * δ)) →
        (K.card : ℝ) ≤ C * (1 + ε / (b * δ))

/-- Grid-bin count for an explicit quadratic polynomial: the sublevel set meets at most
`C (1 + ε/(bδ))` bins of any `δ`-grid, for an absolute constant `C` (we take `C = 8`). -/
theorem quadratic_sublevel_bins_explicit (a b₁ c ε b δ : ℝ)
    (hε : 0 < ε) (hb : 0 < b) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Finset ℤ,
      (∀ k ∈ K, ∃ w : ℝ, |a * w ^ 2 + b₁ * w + c| ≤ ε ∧ b ≤ |2 * a * w + b₁| ∧
        w ∈ Set.Ico (k * δ) ((k + 1) * δ)) →
      (K.card : ℝ) ≤ C * (1 + ε / (b * δ)) := by
  classical
  refine ⟨8, by norm_num, ?_⟩
  intro K hK
  let S : Set ℝ := {w : ℝ | |a * w ^ 2 + b₁ * w + c| ≤ ε ∧ b ≤ |2 * a * w + b₁|}
  have hK' : ∀ k ∈ K, ∃ w ∈ S, w ∈ Set.Ico (k * δ) ((k + 1) * δ) := by
    intro k hk
    obtain ⟨w, hw, hwd, hwbin⟩ := hK k hk
    exact ⟨w, ⟨hw, hwd⟩, hwbin⟩
  have hrewrite : 2 * (2 * ε / b) / δ + 2 = 4 * ε / (b * δ) + 2 := by
    field_simp
    ring
  have emptyFinset : ∀ {K' : Finset ℤ}, ¬ K'.Nonempty →
      (K'.card : ℝ) ≤ 8 * (1 + ε / (b * δ)) := by
    intro K' hne
    have hcard0 : K'.card = 0 := by
      by_contra h
      exact hne (Finset.card_pos.mp (Nat.pos_of_ne_zero h))
    have hempty : K' = ∅ := Finset.card_eq_zero.mp hcard0
    simp [hempty]
    positivity
  have hdiv4 : 4 * ε / (b * δ) = 4 * (ε / (b * δ)) := by
    field_simp
  have hdiv8 : 8 * ε / (b * δ) = 8 * (ε / (b * δ)) := by
    field_simp
  have emptyFinset' : ∀ {K' : Finset ℤ}, ¬ K'.Nonempty →
      (K'.card : ℝ) ≤ 4 * ε / (b * δ) + 2 := by
    intro K' hne
    have hcard0 : K'.card = 0 := by
      by_contra h
      exact hne (Finset.card_pos.mp (Nat.pos_of_ne_zero h))
    have hempty : K' = ∅ := Finset.card_eq_zero.mp hcard0
    simp [hempty]
    positivity
  have hle8 : 4 * ε / (b * δ) + 2 ≤ 8 * (1 + ε / (b * δ)) := by
    rw [hdiv4]
    have hnonneg : 0 ≤ ε / (b * δ) := by positivity
    nlinarith
  have hle8' : 8 * ε / (b * δ) + 4 ≤ 8 * (1 + ε / (b * δ)) := by
    rw [hdiv8]
    nlinarith
  by_cases hane : a = 0
  · by_cases hb1lt : |b₁| < b
    · have hKnotne : ¬ K.Nonempty := by
        intro hne
        obtain ⟨k, hk⟩ := hne
        obtain ⟨w, hwS, _⟩ := hK' k hk
        exact not_le_of_gt hb1lt (by simpa [S, hane] using hwS.2)
      exact emptyFinset hKnotne
    · have hb₁ : b ≤ |b₁| := le_of_not_gt hb1lt
      by_cases hKne : K.Nonempty
      · have hSne : S.Nonempty := by
          obtain ⟨k, hk⟩ := hKne
          obtain ⟨w, hwS, _⟩ := hK' k hk
          exact ⟨w, hwS⟩
        have hdiam : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * ε / b := by
          intro x hx y hy
          have := quadratic_diameter_le_left (a := 0) (b₁ := b₁) (c := c) (ε := ε) (b := b)
            (r := max x y) hε hb (fun _ _ => by simpa using hb₁)
            (le_max_left x y) (le_max_right x y)
            (by simpa [S, hane] using hx.1) (by simpa [S, hane] using hy.1)
          simpa using this
        have hc := card_bins_le_of_diameter (S := S) (δ := δ) (D := 2 * ε / b) hδ
          (by positivity : 0 ≤ 2 * ε / b) hSne hdiam K hK'
        have hc' : (K.card : ℝ) ≤ 4 * ε / (b * δ) + 2 := by
          rwa [hrewrite] at hc
        exact hc'.trans hle8
      · exact emptyFinset hKne
  · have ha : a ≠ 0 := hane
    set r : ℝ := -b₁ / (2 * a) with hr
    set eta : ℝ := b / (2 * |a|) with heta
    let S₁ : Set ℝ := {w : ℝ | w ≤ r - eta ∧ |a * w ^ 2 + b₁ * w + c| ≤ ε}
    let S₂ : Set ℝ := {w : ℝ | r + eta ≤ w ∧ |a * w ^ 2 + b₁ * w + c| ≤ ε}
    have hS : S = S₁ ∪ S₂ := by
      ext w
      change (|a * w ^ 2 + b₁ * w + c| ≤ ε ∧ b ≤ |2 * a * w + b₁|) ↔
        (w ≤ r - eta ∧ |a * w ^ 2 + b₁ * w + c| ≤ ε) ∨
        (r + eta ≤ w ∧ |a * w ^ 2 + b₁ * w + c| ≤ ε)
      rw [quadratic_deriv_threshold a b₁ b w ha hb]
      rw [hr, heta]
      tauto
    let K₁ : Finset ℤ := K.filter (fun k => ∃ w ∈ S₁, w ∈ Set.Ico (k * δ) ((k + 1) * δ))
    let K₂ : Finset ℤ := K.filter (fun k => ∃ w ∈ S₂, w ∈ Set.Ico (k * δ) ((k + 1) * δ))
    have hKsub : K ⊆ K₁ ∪ K₂ := by
      intro k hk
      obtain ⟨w, hwS, hwbin⟩ := hK' k hk
      have hwS' : w ∈ S₁ ∪ S₂ := by simpa [hS] using hwS
      rw [Set.mem_union] at hwS'
      rcases hwS' with hw1 | hw2
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hk, ⟨w, hw1, hwbin⟩⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hk, ⟨w, hw2, hwbin⟩⟩))
    have hKcard : K.card ≤ K₁.card + K₂.card := by
      calc
        K.card ≤ (K₁ ∪ K₂).card := Finset.card_le_card hKsub
        _ ≤ K₁.card + K₂.card := Finset.card_union_le K₁ K₂
    have hderivL : ∀ w, w ≤ r - eta → b ≤ |2 * a * w + b₁| := by
      intro w hw
      have hw' : w ≤ -b₁ / (2 * a) - b / (2 * |a|) := by
        rw [hr, heta] at hw
        exact hw
      exact (quadratic_deriv_threshold a b₁ b w ha hb).mpr (Or.inl hw')
    have hderivR : ∀ w, r + eta ≤ w → b ≤ |2 * a * w + b₁| := by
      intro w hw
      have hw' : -b₁ / (2 * a) + b / (2 * |a|) ≤ w := by
        rw [hr, heta] at hw
        exact hw
      exact (quadratic_deriv_threshold a b₁ b w ha hb).mpr (Or.inr hw')
    have hpiece (S' : Set ℝ) (K' : Finset ℤ)
        (hfilter : ∀ k ∈ K', ∃ w ∈ S', w ∈ Set.Ico (k * δ) ((k + 1) * δ))
        (hdiam : ∀ x ∈ S', ∀ y ∈ S', |x - y| ≤ 2 * ε / b)
        (hSne : S'.Nonempty) :
        (K'.card : ℝ) ≤ 4 * ε / (b * δ) + 2 := by
      have hc := card_bins_le_of_diameter (S := S') (δ := δ) (D := 2 * ε / b) hδ
        (by positivity : 0 ≤ 2 * ε / b) hSne hdiam K' hfilter
      rwa [hrewrite] at hc
    have hbound1 : (K₁.card : ℝ) ≤ 4 * ε / (b * δ) + 2 := by
      by_cases hK1ne : K₁.Nonempty
      · obtain ⟨k, hk⟩ := hK1ne
        obtain ⟨x₀, hx₀S, _⟩ := (Finset.mem_filter.mp hk).2
        have hdiam : ∀ x ∈ S₁, ∀ y ∈ S₁, |x - y| ≤ 2 * ε / b := by
          intro x hx y hy
          exact quadratic_diameter_le_left a b₁ c ε b (r - eta) hε hb hderivL hx.1 hy.1 hx.2 hy.2
        exact hpiece S₁ K₁ (fun k hk => (Finset.mem_filter.mp hk).2) hdiam ⟨x₀, hx₀S⟩
      · exact emptyFinset' hK1ne
    have hbound2 : (K₂.card : ℝ) ≤ 4 * ε / (b * δ) + 2 := by
      by_cases hK2ne : K₂.Nonempty
      · obtain ⟨k, hk⟩ := hK2ne
        obtain ⟨x₀, hx₀S, _⟩ := (Finset.mem_filter.mp hk).2
        have hdiam : ∀ x ∈ S₂, ∀ y ∈ S₂, |x - y| ≤ 2 * ε / b := by
          intro x hx y hy
          exact quadratic_diameter_le_right a b₁ c ε b (r + eta) hε hb hderivR hx.1 hy.1 hx.2 hy.2
        exact hpiece S₂ K₂ (fun k hk => (Finset.mem_filter.mp hk).2) hdiam ⟨x₀, hx₀S⟩
      · exact emptyFinset' hK2ne
    have hsum : (K.card : ℝ) ≤ (K₁.card : ℝ) + (K₂.card : ℝ) := by
      exact_mod_cast hKcard
    have hbnds : (K₁.card : ℝ) + (K₂.card : ℝ) ≤ 8 * ε / (b * δ) + 4 := by
      nlinarith [hbound1, hbound2]
    exact hsum.trans (hbnds.trans hle8')

/-- Grid-bin count for a quadratic sublevel set. -/
theorem quadratic_sublevel_bins (Q : ℝ[X]) (hQ : Q.degree ≤ 2)
    {ε b δ : ℝ} (hε : 0 < ε) (hb : 0 < b) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Finset ℤ,
      (∀ k ∈ K, ∃ w : ℝ, |Q.eval w| ≤ ε ∧ b ≤ |Q.derivative.eval w| ∧
        w ∈ Set.Ico (k * δ) ((k + 1) * δ)) →
      (K.card : ℝ) ≤ C * (1 + ε / (b * δ)) := by
  obtain ⟨C₀, hCpos, hC⟩ :=
    quadratic_sublevel_bins_explicit (Q.coeff 2) (Q.coeff 1) (Q.coeff 0) ε b δ hε hb hδ
  refine ⟨C₀, hCpos, ?_⟩
  intro K hK
  apply hC K
  intro k hk
  obtain ⟨w, hw, hwd, hwbin⟩ := hK k hk
  have hQeq : Q = C (Q.coeff 2) * X ^ 2 + C (Q.coeff 1) * X + C (Q.coeff 0) := polynomial_eq_quadratic Q hQ
  have hw' : |Q.coeff 2 * w ^ 2 + Q.coeff 1 * w + Q.coeff 0| ≤ ε := by
    have h := hw
    rw [hQeq] at h
    simpa [eval_quadratic] using h
  have hwd' : b ≤ |2 * Q.coeff 2 * w + Q.coeff 1| := by
    have h := hwd
    rw [hQeq] at h
    have hh : (C (Q.coeff 2) * X ^ 2 + C (Q.coeff 1) * X + C (Q.coeff 0) : ℝ[X]).derivative.eval w =
        2 * Q.coeff 2 * w + Q.coeff 1 := by
      rw [eval_derivative_quadratic]
    rwa [hh] at h
  exact ⟨w, hw', hwd', hwbin⟩

/-- The full quadratic sublevel statement, from the length bound and the bin count. -/
theorem quadratic_sublevel : QuadraticSublevelStatement := by
  intro Q hQ ε b δ hε hb hδ
  exact ⟨quadratic_sublevel_volume Q hQ hε hb, quadratic_sublevel_bins Q hQ hε hb hδ⟩

end Kakeya4
