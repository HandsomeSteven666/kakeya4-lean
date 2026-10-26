import Kakeya4.Hard.MultilinearKakeya.SpatialBisectionEnergy
import Kakeya4.Hard.MultilinearKakeya.AntipodalCover

/-! Actual negative/positive polynomial masses on finite-volume Euclidean
regions. On nonzero coefficient spheres their difference is continuous and
odd, and vanishes exactly at true volume bisections. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

def polynomialSignImbalance {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (A : Set (E n)) : ℝ :=
  ((volume.restrict A) {x | MvPolynomial.eval (WithLp.ofLp x) P ≤ 0}).toReal -
    ((volume.restrict A) {x | 0 ≤ MvPolynomial.eval (WithLp.ofLp x) P}).toReal

theorem polynomialSignImbalance_neg {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (A : Set (E n)) :
    polynomialSignImbalance (-P) A = -polynomialSignImbalance P A := by
  simp only [polynomialSignImbalance, MvPolynomial.eval_neg, neg_nonpos, neg_nonneg]
  ring

theorem euclidean_polynomial_zero_volume {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (hP : P ≠ 0) :
    volume {x : E n | MvPolynomial.eval (WithLp.ofLp x) P = 0} = 0 := by
  have hm : MeasurableSet {x : Fin n → ℝ | MvPolynomial.eval x P = 0} :=
    (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet
  exact ((PiLp.volume_preserving_ofLp (Fin n)).measure_preimage hm.nullMeasurableSet).trans
    (real_polynomial_zero_volume P hP)

theorem continuousAt_euclidean_polynomial_sublevel_mass {n k : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) {A : Set (E n)} (hA : volume A ≠ ⊤)
    {α : Type*} [TopologicalSpace α] [FirstCountableTopology α]
    (g : α → E k) (hg : Continuous g) (a : α)
    (hP : coefficientPolynomial B (g a) ≠ 0) :
    ContinuousAt (fun b => ((volume.restrict A)
      {x | MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B (g b)) ≤ 0}).toReal) a := by
  let μ := volume.restrict A
  letI : IsFiniteMeasure μ := ⟨by simpa [μ] using hA.lt_top⟩
  have hmeas (b : α) : MeasurableSet
      {x : E n | MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B (g b)) ≤ 0} :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).continuous.measurable
      (isClosed_le (MvPolynomial.continuous_eval _) continuous_const).measurableSet
  have hzmeas : MeasurableSet {x : E n |
      MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B (g a)) = 0} :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).continuous.measurable
      (isClosed_eq (MvPolynomial.continuous_eval _) continuous_const).measurableSet
  have hnull : μ {x | MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B (g a)) = 0} = 0 := by
    rw [Measure.restrict_apply hzmeas]
    exact measure_mono_null inter_subset_left (euclidean_polynomial_zero_volume _ hP)
  have hc : ContinuousAt (fun b => μ
      {x | MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B (g b)) ≤ 0}) a := by
    apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (𝓝 a) (hmeas a) hmeas
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    have hne : MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B (g a)) ≠ 0 := hx
    have he : ContinuousAt (fun b => MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B (g b))) a :=
      ((continuous_eval_coefficientPolynomial B (WithLp.ofLp x)).comp hg).continuousAt
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · filter_upwards [he.eventually (Iio_mem_nhds hneg)] with b hb
      exact iff_of_true hb.le hneg.le
    · filter_upwards [he.eventually (Ioi_mem_nhds hpos)] with b hb
      exact iff_of_false (not_le.mpr hb) (not_le.mpr hpos)
  exact ContinuousAt.comp
    (f := fun b => μ {x | MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B (g b)) ≤ 0})
    (g := ENNReal.toReal) (x := a) (ENNReal.continuousAt_toReal (measure_ne_top μ _)) hc

theorem continuous_polynomialSignImbalance_sphere {n m : ℕ}
    (B : Fin (m+1) → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    {A : Set (E n)} (hA : volume A ≠ ⊤) :
    Continuous (fun u : UnitSphere m => polynomialSignImbalance (coefficientPolynomial B u) A) := by
  have hn : Continuous (fun u : UnitSphere m => ((volume.restrict A)
      {x | MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B u) ≤ 0}).toReal) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact continuousAt_euclidean_polynomial_sublevel_mass B hA Subtype.val continuous_subtype_val u
      (coefficientPolynomial_sphere_ne_zero B hB u)
  have hp := hn.comp (continuous_neg : Continuous (fun u : UnitSphere m => -u))
  change Continuous (fun u : UnitSphere m => ((volume.restrict A)
    {x | MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B (-(u : E (m+1)))) ≤ 0}).toReal) at hp
  have hp' : Continuous (fun u : UnitSphere m => ((volume.restrict A)
      {x | 0 ≤ MvPolynomial.eval (WithLp.ofLp x) (coefficientPolynomial B u)}).toReal) := by
    simpa only [coefficientPolynomial_neg, MvPolynomial.eval_neg, neg_nonpos] using hp
  exact hn.sub hp'

theorem polynomialSignImbalance_eq_zero_iff_bisects {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P ≠ 0)
    {A : Set (E n)} (hA : volume A ≠ ⊤) :
    polynomialSignImbalance P A = 0 ↔ polynomialBisects P A := by
  let μ := volume.restrict A
  letI : IsFiniteMeasure μ := ⟨by simpa [μ] using hA.lt_top⟩
  constructor
  · intro h
    have heqReal := sub_eq_zero.mp h
    have heq : μ {x | MvPolynomial.eval (WithLp.ofLp x) P ≤ 0} =
        μ {x | 0 ≤ MvPolynomial.eval (WithLp.ofLp x) P} :=
      (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top μ _)).mp heqReal
    have hnull : μ {x | MvPolynomial.eval (WithLp.ofLp x) P = 0} = 0 := by
      have hm : MeasurableSet {x : E n | MvPolynomial.eval (WithLp.ofLp x) P = 0} :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).continuous.measurable
          (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet
      rw [Measure.restrict_apply hm]
      exact measure_mono_null inter_subset_left (euclidean_polynomial_zero_volume P hP)
    have hunion : {x : E n | MvPolynomial.eval (WithLp.ofLp x) P ≤ 0} ∪
        {x | 0 ≤ MvPolynomial.eval (WithLp.ofLp x) P} = univ := by
      ext x
      simp only [mem_union,mem_ofPred_eq,mem_univ,iff_true]
      exact le_total _ _
    have hinter : {x : E n | MvPolynomial.eval (WithLp.ofLp x) P ≤ 0} ∩
        {x | 0 ≤ MvPolynomial.eval (WithLp.ofLp x) P} =
        {x | MvPolynomial.eval (WithLp.ofLp x) P = 0} := by
      ext x
      exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le,h.ge⟩⟩
    have hm : MeasurableSet {x : E n | 0 ≤ MvPolynomial.eval (WithLp.ofLp x) P} :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).continuous.measurable
        (isClosed_le continuous_const (MvPolynomial.continuous_eval P)).measurableSet
    have hs := measure_union_add_inter (μ := μ) {x | MvPolynomial.eval (WithLp.ofLp x) P ≤ 0} hm
    rw [hunion,hinter,hnull,add_zero] at hs
    have hh : μ {x | MvPolynomial.eval (WithLp.ofLp x) P ≤ 0} = μ univ / 2 := by
      apply (ENNReal.eq_div_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mpr
      rw [two_mul]
      simpa only [← heq] using hs.symm
    constructor
    · simpa only [μ,Measure.restrict_apply_univ] using hh
    · simpa only [μ,Measure.restrict_apply_univ] using heq.symm.trans hh
  · intro h
    simp only [polynomialSignImbalance, h.1, h.2, sub_self]

end Kakeya4.Hard.MultilinearKakeya
