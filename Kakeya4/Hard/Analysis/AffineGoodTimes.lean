import Kakeya4.Hard.Analysis.MonicGoodTimes
import Kakeya4.Foundation.Lemmas.QuadraticSublevel

/-!
# Simultaneous good times for a monic cubic and an affine derivative

An affine function that is large at one time cannot be small on most of the interval.
Combining this with the monic-polynomial root exclusion gives the simultaneous good-time
set used in the slope-volume proof. No independence of the two tests is assumed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Polynomial
open scoped ENNReal

namespace Kakeya4.Hard

/-- Times in the interval where the affine derivative is below its relative threshold. -/
def affineBadTimes (u v a b ε M : ℝ) : Set ℝ :=
  {t | t ∈ Icc a b ∧ |u * t + v| < ε * M}

theorem measurableSet_affineBadTimes (u v a b ε M : ℝ) :
    MeasurableSet (affineBadTimes u v a b ε M) := by
  change MeasurableSet (Icc a b ∩ {t : ℝ | |u * t + v| < ε * M})
  exact measurableSet_Icc.inter
    (isOpen_lt (show Continuous (fun t : ℝ => |u * t + v|) by fun_prop)
      continuous_const).measurableSet

/-- Coefficient-uniform affine small-value estimate. The deliberately generous factor `8`
lets us reuse the project's already proved affine sublevel estimate directly. -/
theorem volume_affineBadTimes_le (u v a b ε M : ℝ) (hab : a < b)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hM : 0 < M)
    (hwitness : ∃ t₀ ∈ Icc a b, M ≤ |u * t₀ + v|) :
    volume (affineBadTimes u v a b ε M) ≤ ENNReal.ofReal (8 * ε * (b - a)) := by
  obtain ⟨t₀, ht₀, hlarge⟩ := hwitness
  have hq : 0 < b - a := sub_pos.mpr hab
  by_cases hsmall : |u| * (b - a) < M / 2
  · have hempty : affineBadTimes u v a b ε M = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have hspan : |t₀ - t| ≤ b - a :=
        abs_le.mpr ⟨by linarith [ht.1.2, ht₀.1], by linarith [ht.1.1, ht₀.2]⟩
      have hdiff : |u| * |t₀ - t| ≤ |u| * (b - a) :=
        mul_le_mul_of_nonneg_left hspan (abs_nonneg u)
      have htriangle : |u * t₀ + v| ≤ |u * t + v| + |u| * |t₀ - t| := by
        calc
          |u * t₀ + v| = |(u * t + v) + u * (t₀ - t)| := by congr 1; ring
          _ ≤ |u * t + v| + |u * (t₀ - t)| := abs_add_le _ _
          _ = _ := by rw [abs_mul]
      have hbad := ht.2
      nlinarith
    rw [hempty, measure_empty]
    exact bot_le
  · have hslope : M / (2 * (b - a)) ≤ |u| := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * (b - a))).mpr
      nlinarith [le_of_not_gt hsmall]
    have hsub : affineBadTimes u v a b ε M ⊆
        {t : ℝ | |u * t + v| ≤ ε * M ∧ M / (2 * (b - a)) ≤ |u|} := by
      intro t ht
      exact ⟨ht.2.le, hslope⟩
    have hbound := Kakeya4.affine_sublevel_volume u v (ε * M)
      (M / (2 * (b - a))) (by positivity) (by positivity)
    have heq : 4 * (ε * M) / (M / (2 * (b - a))) = 8 * ε * (b - a) := by
      field_simp; ring
    exact (measure_mono hsub).trans (hbound.trans_eq (congrArg ENNReal.ofReal heq))

/-- At least half the interval passes both the cubic Jacobian test and the affine
derivative test. All constants are independent of the polynomial coefficients. -/
theorem simultaneous_cubic_affine_good_times (p : ℝ[X]) (hp : p.Monic)
    (hdegree : p.natDegree = 3) (u v a b M : ℝ) (hab : a < b) (hM : 0 < M)
    (hwitness : ∃ t₀ ∈ Icc a b, M ≤ |u * t₀ + v|) :
    ∃ B : Set ℝ, MeasurableSet B ∧
      volume B ≤ ENNReal.ofReal ((b - a) / 2) ∧
      ENNReal.ofReal ((b - a) / 2) ≤ volume (Icc a b \ B) ∧
      ∀ t ∈ Icc a b \ B,
        ((b - a) / 24) ^ 3 ≤ |p.eval t| ∧ M / 32 ≤ |u * t + v| := by
  obtain ⟨B₀, hB₀, hvol₀, _, hgood₀⟩ := cubic_good_times p hp hdegree a b hab.le
  let B₁ := affineBadTimes u v a b (1 / 32) M
  have hvol₁ : volume B₁ ≤ ENNReal.ofReal ((b - a) / 4) := by
    have h := volume_affineBadTimes_le u v a b (1 / 32) M hab
      (by norm_num) (by norm_num) hM hwitness
    convert h using 2; ring
  have hquarter : 0 ≤ (b - a) / 4 := by positivity
  have hB : volume (B₀ ∪ B₁) ≤ ENNReal.ofReal ((b - a) / 2) := by
    calc
      volume (B₀ ∪ B₁) ≤ volume B₀ + volume B₁ := measure_union_le _ _
      _ ≤ ENNReal.ofReal ((b - a) / 4) + ENNReal.ofReal ((b - a) / 4) :=
        add_le_add hvol₀ hvol₁
      _ = ENNReal.ofReal ((b - a) / 2) := by
        rw [← ENNReal.ofReal_add hquarter hquarter]
        congr 1
        ring
  refine ⟨B₀ ∪ B₁, hB₀.union (measurableSet_affineBadTimes _ _ _ _ _ _), hB, ?_, ?_⟩
  · have hhalf : 0 ≤ (b - a) / 2 := by positivity
    calc
      ENNReal.ofReal ((b - a) / 2) = volume (Icc a b) - ENNReal.ofReal ((b - a) / 2) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_sub _ hhalf]
        congr 1
        ring
      _ ≤ volume (Icc a b) - volume (B₀ ∪ B₁) := tsub_le_tsub_left hB _
      _ ≤ volume (Icc a b \ (B₀ ∪ B₁)) := le_measure_sdiff
  · intro t ht
    have hn₀ : t ∉ B₀ := fun h => ht.2 (Or.inl h)
    have hn₁ : t ∉ B₁ := fun h => ht.2 (Or.inr h)
    refine ⟨hgood₀ t hn₀, ?_⟩
    have hnot : ¬ |u * t + v| < (1 / 32 : ℝ) * M :=
      fun h => hn₁ ⟨ht.1, h⟩
    nlinarith [le_of_not_gt hnot]

end Kakeya4.Hard
