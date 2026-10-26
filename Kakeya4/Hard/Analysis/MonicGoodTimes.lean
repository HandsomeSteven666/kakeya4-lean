import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Tactic

/-!
# Good real times for a monic polynomial

Remove radius-`r` intervals around the real parts of all complex roots.
The removed measure is at most `2 * degree * r`; on the complement the absolute
polynomial value is at least `r ^ degree`. This is uniform in every coefficient,
as needed for the monic cubic Jacobian in the slope-volume argument.

Complex roots, their multiplicities, and the factorization are supplied by Mathlib.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Polynomial
open scoped ENNReal

namespace Kakeya4.Hard

/-- The excluded time intervals; duplicate roots are removed only from the union,
not from the product used to estimate the polynomial. -/
def badRootTimes (p : ℝ[X]) (r : ℝ) : Set ℝ :=
  ⋃ z ∈ (p.map Complex.ofRealHom).roots.toFinset, Ioo (z.re - r) (z.re + r)

theorem measurableSet_badRootTimes (p : ℝ[X]) (r : ℝ) :
    MeasurableSet (badRootTimes p r) := by
  exact MeasurableSet.biUnion (to_countable _) (fun _ _ => measurableSet_Ioo)

/-- The number of excluded intervals is at most the degree, even with repeated roots. -/
theorem volume_badRootTimes_le (p : ℝ[X]) (r : ℝ) :
    volume (badRootTimes p r) ≤ (p.natDegree : ℝ≥0∞) * ENNReal.ofReal (2 * r) := by
  classical
  let P := p.map Complex.ofRealHom
  have hcard : P.roots.toFinset.card ≤ p.natDegree := by
    calc
      P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
      _ = P.natDegree := (IsAlgClosed.splits P).natDegree_eq_card_roots.symm
      _ = p.natDegree := Polynomial.natDegree_map _
  have hvol (z : ℂ) : volume (Ioo (z.re - r) (z.re + r)) = ENNReal.ofReal (2 * r) := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  calc
    volume (badRootTimes p r) ≤
        ∑ z ∈ P.roots.toFinset, volume (Ioo (z.re - r) (z.re + r)) :=
      measure_biUnion_finset_le _ _
    _ = (P.roots.toFinset.card : ℝ≥0∞) * ENNReal.ofReal (2 * r) := by
      simp only [hvol, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (p.natDegree : ℝ≥0∞) * ENNReal.ofReal (2 * r) := by
      gcongr

/-- Every root factor has magnitude at least `r` outside the excluded intervals. -/
theorem radius_le_norm_sub_root (p : ℝ[X]) {r t : ℝ} (ht : t ∉ badRootTimes p r)
    {z : ℂ} (hz : z ∈ (p.map Complex.ofRealHom).roots) :
    r ≤ ‖(t : ℂ) - z‖ := by
  classical
  have hreal : r ≤ |t - z.re| := by
    by_contra h
    have habs : |t - z.re| < r := lt_of_not_ge h
    apply ht
    apply mem_iUnion.mpr
    refine ⟨z, mem_iUnion.mpr ⟨Multiset.mem_toFinset.mpr hz, ?_⟩⟩
    exact ⟨by linarith [(abs_lt.mp habs).1], by linarith [(abs_lt.mp habs).2]⟩
  exact hreal.trans (by simpa using Complex.abs_re_le_norm ((t : ℂ) - z))

/-- Uniform lower bound for a monic polynomial away from the real parts of its roots. -/
theorem pow_natDegree_le_abs_eval_of_not_mem_badRootTimes (p : ℝ[X]) (hp : p.Monic)
    {r t : ℝ} (hr : 0 ≤ r) (ht : t ∉ badRootTimes p r) :
    r ^ p.natDegree ≤ |p.eval t| := by
  let P := p.map Complex.ofRealHom
  have hPm : P.Monic := hp.map _
  have hcard : P.roots.card = p.natDegree := by
    rw [← (IsAlgClosed.splits P).natDegree_eq_card_roots, Polynomial.natDegree_map]
  have hprod := Multiset.prod_map_le_prod_map₀ (s := P.roots)
    (fun _ : ℂ => r) (fun z => ‖(t : ℂ) - z‖)
    (fun _ _ => hr) (fun z hz => radius_le_norm_sub_root p ht hz)
  have heval : P.eval (t : ℂ) = Complex.ofReal (p.eval t) := by
    simpa only [P, Polynomial.eval_map, Complex.ofRealHom_eq_coe] using
      (Polynomial.eval₂_at_apply (p := p) Complex.ofRealHom t)
  calc
    r ^ p.natDegree = (P.roots.map (fun _ : ℂ => r)).prod := by
      simp [hcard]
    _ ≤ (P.roots.map (fun z => ‖(t : ℂ) - z‖)).prod := hprod
    _ = ‖P.eval (t : ℂ)‖ := by
      rw [(IsAlgClosed.splits P).eval_eq_prod_roots_of_monic hPm]
      change _ = (normHom : ℂ →*₀ ℝ) _
      rw [map_multiset_prod (normHom : ℂ →*₀ ℝ), Multiset.map_map]
      rfl
    _ = |p.eval t| := by rw [heval, Complex.norm_real, Real.norm_eq_abs]

/-- Removing root intervals loses at most their total length from any real interval. -/
theorem volume_interval_sdiff_badRootTimes_ge (p : ℝ[X]) (a b : ℝ) {r : ℝ}
    (hr : 0 ≤ r) :
    ENNReal.ofReal ((b - a) - (p.natDegree : ℝ) * (2 * r)) ≤
      volume (Icc a b \ badRootTimes p r) := by
  have hbound : volume (badRootTimes p r) ≤
      ENNReal.ofReal ((p.natDegree : ℝ) * (2 * r)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    exact volume_badRootTimes_le p r
  calc
    ENNReal.ofReal ((b - a) - (p.natDegree : ℝ) * (2 * r)) =
        volume (Icc a b) - ENNReal.ofReal ((p.natDegree : ℝ) * (2 * r)) := by
      rw [Real.volume_Icc, ENNReal.ofReal_sub _ (by positivity)]
    _ ≤ volume (Icc a b) - volume (badRootTimes p r) := tsub_le_tsub_left hbound _
    _ ≤ volume (Icc a b \ badRootTimes p r) := le_measure_sdiff

/-- Explicit coefficient-uniform cubic estimate: remove at most one quarter of an interval,
and the determinant has size at least `(length / 24)^3` at every remaining time. -/
theorem cubic_good_times (p : ℝ[X]) (hp : p.Monic) (hdegree : p.natDegree = 3)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ B : Set ℝ, MeasurableSet B ∧
      volume B ≤ ENNReal.ofReal ((b - a) / 4) ∧
      ENNReal.ofReal (3 * (b - a) / 4) ≤ volume (Icc a b \ B) ∧
      ∀ t ∉ B, ((b - a) / 24) ^ 3 ≤ |p.eval t| := by
  let r : ℝ := (b - a) / 24
  have hr : 0 ≤ r := by dsimp [r]; positivity
  refine ⟨badRootTimes p r, measurableSet_badRootTimes p r, ?_, ?_, ?_⟩
  · have h := volume_badRootTimes_le p r
    have heq : (p.natDegree : ℝ≥0∞) * ENNReal.ofReal (2 * r) =
        ENNReal.ofReal ((b - a) / 4) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      rw [hdegree]
      dsimp [r]
      ring
    exact h.trans_eq heq
  · have heq : (b - a) - (p.natDegree : ℝ) * (2 * r) = 3 * (b - a) / 4 := by
      rw [hdegree]
      dsimp [r]
      ring
    rw [← heq]
    exact volume_interval_sdiff_badRootTimes_ge p a b hr
  · intro t ht
    simpa only [hdegree] using pow_natDegree_le_abs_eval_of_not_mem_badRootTimes p hp hr ht

end Kakeya4.Hard
