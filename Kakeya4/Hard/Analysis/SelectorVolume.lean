import Kakeya4.Hard.Analysis.SlopeJacobian
import Kakeya4.Hard.Analysis.AffineGoodTimes
import Kakeya4.Hard.Analysis.TimeSliceVolume

/-!
# Analytic assembly of the selector-volume inequality

This module assembles the actual line-position map, coefficient-uniform simultaneous
good times, finite-multiplicity change of variables and Tonelli. The semialgebraic
selector and its parameter-uniform regular-fiber bound remain explicit inputs.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace Kakeya4.Hard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Both good-time tests, written directly in terms of the derivative determinant.
No measurable choice of polynomial roots is needed. -/
def selectorGoodSet (Db : E → E →L[ℝ] E) (u v : E → ℝ) (q M : ℝ) : Set (ℝ × E) :=
  {p | (q / 24) ^ 3 ≤ |(slopeDerivative Db p.1 p.2).det| ∧
    M / 32 ≤ |u p.2 * p.1 + v p.2|}

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [BorelSpace E] in
theorem measurableSet_selectorGoodSet (Db : E → E →L[ℝ] E) (u v : E → ℝ) (q M : ℝ)
    (hDb : Measurable Db) (hu : Measurable u) (hv : Measurable v) :
    MeasurableSet (selectorGoodSet Db u v q M) := by
  have hD : Measurable (fun p : ℝ × E => slopeDerivative Db p.1 p.2) :=
    (hDb.comp measurable_snd).add (measurable_fst.smul measurable_const)
  have hdetabs : Measurable (fun p : ℝ × E => |(slopeDerivative Db p.1 p.2).det|) := by
    simpa only [Real.norm_eq_abs, Function.comp_apply] using
      (ContinuousLinearMap.continuous_det.measurable.comp hD).norm
  have haffabs : Measurable (fun p : ℝ × E => |u p.2 * p.1 + v p.2|) := by
    simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.add_apply, Pi.mul_apply] using
      (((hu.comp measurable_snd).mul measurable_fst).add (hv.comp measurable_snd)).norm
  exact (measurableSet_le measurable_const hdetabs).inter
    (measurableSet_le measurable_const haffabs)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Every slope has at least half the interval as simultaneous good times. -/
theorem selector_good_time_mass (Db : E → E →L[ℝ] E) (u v : E → ℝ)
    (hDim : Module.finrank ℝ E = 3) (a b M : ℝ) (hab : a < b) (hM : 0 < M)
    (s : E) (hwitness : ∃ t₀ ∈ Icc a b, M ≤ |u s * t₀ + v s|) :
    ENNReal.ofReal ((b - a) / 2) ≤
      volume {t ∈ Icc a b | (t, s) ∈ selectorGoodSet Db u v (b - a) M} := by
  obtain ⟨B, _, _, hmass, hgood⟩ := simultaneous_cubic_affine_good_times
    (jacobianPolynomial (Db s)) (jacobianPolynomial_monic _)
    ((jacobianPolynomial_natDegree _).trans hDim) (u s) (v s) a b M hab hM hwitness
  apply hmass.trans
  apply measure_mono
  intro t ht
  refine ⟨ht.1, ?_⟩
  have h := hgood t ht
  exact ⟨by simpa only [det_slopeDerivative] using h.1, h.2⟩

/-- The time-integrated selector-volume inequality. Only genuine geometric information
about the chosen intercept map and the regular fibers is assumed, not the desired bound. -/
theorem integrated_selector_volume_bound (μ : Measure E) [IsAddHaarMeasure μ]
    (b₀ : E → E) (Db : E → E →L[ℝ] E) (u v : E → ℝ)
    (hDim : Module.finrank ℝ E = 3)
    (S : Set E) (hS : MeasurableSet S) (a b M : ℝ) (hab : a < b) (hM : 0 < M)
    (hDb : Measurable Db) (hu : Measurable u) (hv : Measurable v)
    (hbC : ∀ s ∈ S, ContDiffAt ℝ 1 b₀ s)
    (hbD : ∀ s ∈ S, HasFDerivAt b₀ (Db s) s)
    (hwitness : ∀ s ∈ S, ∃ t₀ ∈ Icc a b, M ≤ |u s * t₀ + v s|)
    (T : ℝ → Set E) (hT : ∀ t, MeasurableSet (T t)) (N : ℕ)
    (hmap : ∀ t ∈ Icc a b, MapsTo (slopeMap b₀ t)
      {s ∈ S | (t, s) ∈ selectorGoodSet Db u v (b - a) M} (T t))
    (hfiber : ∀ t ∈ Icc a b, ∀ y,
      {s ∈ S | (slopeDerivative Db t s).det ≠ 0 ∧ slopeMap b₀ t s = y}.encard ≤ N) :
    ENNReal.ofReal (((b - a) / 24) ^ 3) * (ENNReal.ofReal ((b - a) / 2) * μ S) ≤
      (N : ℝ≥0∞) * ∫⁻ t in Icc a b, μ (T t) := by
  let G := selectorGoodSet Db u v (b - a) M
  have hG : MeasurableSet G := measurableSet_selectorGoodSet Db u v (b - a) M hDb hu hv
  apply integrated_slice_volume_bound μ volume S hS (Icc a b) measurableSet_Icc G hG
    (ENNReal.ofReal ((b - a) / 2)) (ENNReal.ofReal (((b - a) / 24) ^ 3))
    ENNReal.ofReal_ne_top N (fun t => μ (T t))
    (fun s hs => selector_good_time_mass Db u v hDim a b M hab hM s (hwitness s hs))
  intro t ht
  let A : Set E := {s ∈ S | (t, s) ∈ G}
  have hA : MeasurableSet A := hS.inter (hG.preimage measurable_prodMk_left)
  have hsub : A ⊆ S := inter_subset_left
  have hnonzero : ∀ s ∈ A, (slopeDerivative Db t s).det ≠ 0 := by
    intro s hs hz
    have hlo : ((b - a) / 24) ^ 3 ≤ |(slopeDerivative Db t s).det| := hs.2.1
    rw [hz, abs_zero] at hlo
    have hpos : 0 < ((b - a) / 24) ^ 3 := by positivity
    linarith
  have hfiberA : ∀ y, {s ∈ A | slopeMap b₀ t s = y}.encard ≤ N := by
    intro y
    apply (Set.encard_le_encard (show {s ∈ A | slopeMap b₀ t s = y} ⊆
      {s ∈ S | (slopeDerivative Db t s).det ≠ 0 ∧ slopeMap b₀ t s = y} from ?_)).trans
      (hfiber t ht y)
    intro s hs
    exact ⟨hsub hs.1, hnonzero s hs.1, hs.2⟩
  exact mul_measure_le_of_regular_fibers μ (slopeMap b₀ t) (slopeDerivative Db t) A hA
    (fun s hs => contDiffAt_slopeMap (hbC s (hsub hs)) t)
    (fun s hs => hasFDerivAt_slopeMap (hbD s (hsub hs)) t)
    hnonzero (T t) (hT t) N _ (hmap t ht) hfiberA
    (fun _s hs => ENNReal.ofReal_le_ofReal hs.2.1)

/-- Divide the analytic selector estimate by its explicit positive `q^4` factor. -/
theorem selector_mass_bound_of_scaled (mass imageIntegral : ℝ≥0∞) (q H : ℝ)
    (hq : 0 < q) (N : ℕ)
    (hscaled : ENNReal.ofReal ((q / 24) ^ 3) * (ENNReal.ofReal (q / 2) * mass) ≤
      (N : ℝ≥0∞) * imageIntegral)
    (himage : imageIntegral ≤ ENNReal.ofReal (q * H)) :
    mass ≤ ENNReal.ofReal (27648 * (N : ℝ) * H / q ^ 3) := by
  let A : ℝ := (q / 24) ^ 3 * (q / 2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hmul : mass * ENNReal.ofReal A ≤ ENNReal.ofReal ((N : ℝ) * (q * H)) := by
    calc
      mass * ENNReal.ofReal A =
          ENNReal.ofReal ((q / 24) ^ 3) * (ENNReal.ofReal (q / 2) * mass) := by
        dsimp only [A]
        rw [ENNReal.ofReal_mul (by positivity)]
        ring
      _ ≤ (N : ℝ≥0∞) * imageIntegral := hscaled
      _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal (q * H) := by gcongr
      _ = ENNReal.ofReal ((N : ℝ) * (q * H)) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hdiv := (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hA)) (Or.inl ENNReal.ofReal_ne_top)).mpr hmul
  have heq : (N : ℝ) * (q * H) / A = 27648 * (N : ℝ) * H / q ^ 3 := by
    dsimp [A]
    field_simp; ring
  rw [← ENNReal.ofReal_div_of_pos hA, heq] at hdiv
  exact hdiv

/-- The explicit `q⁻³` slope-volume bound from the measurable selector and a uniform
regular-fiber bound, once the allowed spatial region has slice volume at most `H`. -/
theorem selector_volume_bound (μ : Measure E) [IsAddHaarMeasure μ]
    (b₀ : E → E) (Db : E → E →L[ℝ] E) (u v : E → ℝ)
    (hDim : Module.finrank ℝ E = 3)
    (S : Set E) (hS : MeasurableSet S) (a b M : ℝ) (hab : a < b) (hM : 0 < M)
    (hDb : Measurable Db) (hu : Measurable u) (hv : Measurable v)
    (hbC : ∀ s ∈ S, ContDiffAt ℝ 1 b₀ s)
    (hbD : ∀ s ∈ S, HasFDerivAt b₀ (Db s) s)
    (hwitness : ∀ s ∈ S, ∃ t₀ ∈ Icc a b, M ≤ |u s * t₀ + v s|)
    (T : ℝ → Set E) (hT : ∀ t, MeasurableSet (T t)) (N : ℕ)
    (hmap : ∀ t ∈ Icc a b, MapsTo (slopeMap b₀ t)
      {s ∈ S | (t, s) ∈ selectorGoodSet Db u v (b - a) M} (T t))
    (hfiber : ∀ t ∈ Icc a b, ∀ y,
      {s ∈ S | (slopeDerivative Db t s).det ≠ 0 ∧ slopeMap b₀ t s = y}.encard ≤ N)
    (H : ℝ) (hvol : ∀ t ∈ Icc a b, μ (T t) ≤ ENNReal.ofReal H) :
    μ S ≤ ENNReal.ofReal (27648 * (N : ℝ) * H / (b - a) ^ 3) := by
  have hscaled := integrated_selector_volume_bound μ b₀ Db u v hDim S hS a b M hab hM
    hDb hu hv hbC hbD hwitness T hT N hmap hfiber
  apply selector_mass_bound_of_scaled (μ S) _ (b - a) H (sub_pos.mpr hab) N hscaled
  calc
    (∫⁻ t in Icc a b, μ (T t)) ≤ ∫⁻ _t in Icc a b, ENNReal.ofReal H :=
      setLIntegral_mono' measurableSet_Icc hvol
    _ = ENNReal.ofReal ((b - a) * H) := by
      rw [setLIntegral_const, Real.volume_Icc, mul_comm,
        ← ENNReal.ofReal_mul (sub_nonneg.mpr hab.le)]

end Kakeya4.Hard
