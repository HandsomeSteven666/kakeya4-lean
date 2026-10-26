






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.BundledIncidence
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

/-! OpenAI math Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a. See COPYING.
Isolated validation extension: unchanged proof bodies in independent sections.
No production integration or kernel acceptance is claimed by assembly. -/

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPointMoment. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope0


namespace OAI

/-! # Point-pair overlap under the Gaussian slicing parameters -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianPointBand_pair_parameter_bound (A : Fin h → Space d) (x y : Space d)
    {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space h)) {z | x ∈ gaussianPointBand A z r ∧ y ∈ gaussianPointBand A z r} ≤
      if ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r then ENNReal.ofReal ((2*r)^h) else 0 := by
  split_ifs with hh
  · exact (measure_mono (fun _ hz => hz.1)).trans_eq (gaussianPointBand_parameter_measure A x hr)
  · have he : {z : Space h | x ∈ gaussianPointBand A z r ∧ y ∈ gaussianPointBand A z r} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hh (gaussianPointBand_pair_difference A z hz.1 hz.2)
    rw [he,measure_empty]

theorem gaussianPointBand_pair_average (x y : Space d) {r : ℝ} (hr : 0 ≤ r) :
    ((gaussianRows d h).prod (volume : Measure (Space h)))
      {p | x ∈ gaussianPointBand p.1 p.2 r ∧ y ∈ gaussianPointBand p.1 p.2 r} ≤
      ENNReal.ofReal ((2*r)^h)*gaussianRows d h {A | ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r} := by
  let D : Set (Fin h → Space d) := {A | ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r}
  have hD : MeasurableSet D := by
    simp only [D,ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  have hS : MeasurableSet {p : (Fin h → Space d) × Space h |
      x ∈ gaussianPointBand p.1 p.2 r ∧ y ∈ gaussianPointBand p.1 p.2 r} := by
    change MeasurableSet {p : (Fin h → Space d) × Space h |
      (∀ i, |inner ℝ x (p.1 i)-p.2 i| ≤ r) ∧ (∀ i, |inner ℝ y (p.1 i)-p.2 i| ≤ r)}
    simp only [ofPred_and,ofPred_forall]
    apply MeasurableSet.inter <;> apply MeasurableSet.iInter <;> intro i <;>
      exact measurableSet_le (by fun_prop) measurable_const
  rw [Measure.prod_apply hS]
  calc
    _ ≤ ∫⁻ A, D.indicator (fun _ => ENNReal.ofReal ((2*r)^h)) A ∂gaussianRows d h := by
      apply lintegral_mono
      intro A
      change (volume : Measure (Space h))
        {z | x ∈ gaussianPointBand A z r ∧ y ∈ gaussianPointBand A z r} ≤ _
      simpa only [D,indicator_apply,mem_ofPred_eq] using gaussianPointBand_pair_parameter_bound A x y hr
    _ = _ := lintegral_indicator_const hD _

theorem gaussian_point_band_second_moment (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ p : (Fin h → Space d) × Space h, (μ (gaussianPointBand p.1 p.2 r))^2
      ∂(gaussianRows d h).prod volume) ≤
      ∫⁻ z : Space d × Space d, ENNReal.ofReal ((2*r)^h)*
        gaussianRows d h {A | ∀ i, |inner ℝ (z.1-z.2) (A i)| ≤ 2*r} ∂μ.prod μ := by
  let S : Set (((Fin h → Space d) × Space h) × (Space d × Space d)) :=
    {p | p.2.1 ∈ gaussianPointBand p.1.1 p.1.2 r ∧ p.2.2 ∈ gaussianPointBand p.1.1 p.1.2 r}
  have hS : MeasurableSet S := by
    change MeasurableSet {p : ((Fin h → Space d) × Space h) × (Space d × Space d) |
      (∀ i, |inner ℝ p.2.1 (p.1.1 i)-p.1.2 i| ≤ r) ∧
      (∀ i, |inner ℝ p.2.2 (p.1.1 i)-p.1.2 i| ≤ r)}
    simp only [ofPred_and,ofPred_forall]
    apply MeasurableSet.inter <;> apply MeasurableSet.iInter <;> intro i <;>
      exact measurableSet_le (by fun_prop) measurable_const
  have hsection (p : (Fin h → Space d) × Space h) :
      Prod.mk p ⁻¹' S = (gaussianPointBand p.1 p.2 r) ×ˢ (gaussianPointBand p.1 p.2 r) := rfl
  calc
    _ = (((gaussianRows d h).prod volume).prod (μ.prod μ)) S := by
      rw [Measure.prod_apply hS]
      apply lintegral_congr
      intro p
      rw [hsection,Measure.prod_prod,pow_two]
    _ = ∫⁻ z : Space d × Space d, ((gaussianRows d h).prod volume)
        {p | z.1 ∈ gaussianPointBand p.1 p.2 r ∧ z.2 ∈ gaussianPointBand p.1 p.2 r} ∂μ.prod μ :=
      Measure.prod_apply_symm hS
    _ ≤ _ := lintegral_mono (fun z => gaussianPointBand_pair_average z.1 z.2 hr)

end Falconer

end OAI

end ExtensionScope0

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPointBound. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope1



namespace OAI

/-! # Point-slice second moments from the original finite-scale ball bounds -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_pair_kernel (x y : Space d) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ((2*r)^h)*gaussianRows d h
      {A | ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r} ≤
      ENNReal.ofReal ((4*gaussianVectorBandConstant*r^2/(dist x y+r))^h) := by
  have hC := gaussianVectorBandConstant_pos
  calc
    _ ≤ ENNReal.ofReal ((2*r)^h)*
        ENNReal.ofReal ((gaussianVectorBandConstant*(2*r)/(‖x-y‖+2*r))^h) :=
      mul_le_mul_right (gaussianRows_vector_band (x-y) (by positivity)) _
    _ = ENNReal.ofReal ((4*gaussianVectorBandConstant*r^2/(dist x y+2*r))^h) := by
      rw [← ENNReal.ofReal_mul (by positivity),← mul_pow]
      congr 2
      rw [dist_eq_norm]
      field_simp
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply pow_le_pow_left₀ (by positivity)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith

theorem gaussian_point_band_second_moment_frostman
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (k : ℕ)
    (hmass : μ univ ≤ 1)
    (hball : ∀ x : Space d, ∀ n : ℕ, n ≤ k →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      (μ (gaussianPointBand p.1 p.2 (1/(2:ℝ)^k)))^2 ∂(gaussianRows d h).prod volume) ≤
      ENNReal.ofReal ((4*gaussianVectorBandConstant*(1/(2:ℝ)^k)^2)^h)*
        (ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1) := by
  let r : ℝ := 1/(2:ℝ)^k
  let C : ℝ≥0∞ := ENNReal.ofReal ((4*gaussianVectorBandConstant*r^2)^h)
  let B : ℝ≥0∞ := ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1
  have hC := gaussianVectorBandConstant_pos
  have hp (x : Space d) : (∫⁻ y, ENNReal.ofReal ((1/(dist x y+r))^(h:ℝ)) ∂μ) ≤ B :=
    regularized_potential_global μ x hK (Nat.cast_nonneg _) hq k hmass (hball x)
  apply (gaussian_point_band_second_moment μ (by positivity)).trans
  calc
    _ ≤ ∫⁻ z : Space d × Space d,
        ENNReal.ofReal ((4*gaussianVectorBandConstant*r^2/(dist z.1 z.2+r))^h) ∂μ.prod μ :=
      lintegral_mono (fun z => gaussian_point_pair_kernel z.1 z.2 (by dsimp [r]; positivity))
    _ = C * ∫⁻ z : Space d × Space d,
        ENNReal.ofReal ((1/(dist z.1 z.2+r))^(h:ℝ)) ∂μ.prod μ := by
      rw [← lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      rw [Real.rpow_natCast,← ENNReal.ofReal_mul (by positivity),← mul_pow]
      congr 2
      ring
    _ = C * ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((1/(dist x y+r))^(h:ℝ)) ∂μ ∂μ := by
      rw [lintegral_prod _ (by fun_prop)]
    _ ≤ C * ∫⁻ _ : Space d, B ∂μ := mul_le_mul_right (lintegral_mono hp) C
    _ = C*(B*μ univ) := by rw [lintegral_const]
    _ ≤ C*(B*1) := by gcongr
    _ = _ := by simp [C,B,r]

end Falconer

end OAI

end ExtensionScope1

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPointMass. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope2


namespace OAI

/-! # Normalized point slices in Gaussian row coordinates -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianPointSliceMeasure (μ : Measure (Space d))
    (A : Fin h → Space d) (z : Space h) (r : ℝ) : Measure (Space d) :=
  ENNReal.ofReal (r^(-(h:ℝ))) • μ.restrict (gaussianPointBand A z r)

noncomputable def gaussianPointMass (μ : Measure (Space d)) (r : ℝ)
    (p : (Fin h → Space d) × Space h) : ℝ≥0∞ :=
  ENNReal.ofReal (r^(-(h:ℝ)))*μ (gaussianPointBand p.1 p.2 r)

theorem gaussianPointSliceMeasure_univ (μ : Measure (Space d))
    (A : Fin h → Space d) (z : Space h) (r : ℝ) :
    gaussianPointSliceMeasure μ A z r univ = gaussianPointMass μ r (A,z) := by
  simp [gaussianPointSliceMeasure,gaussianPointMass,Measure.smul_apply]

theorem gaussianPointMass_measurable (μ : Measure (Space d)) [SFinite μ] (r : ℝ) :
    Measurable (gaussianPointMass (h := h) μ r) := by
  apply Measurable.const_mul
  let S : Set (((Fin h → Space d) × Space h) × Space d) :=
    {p | p.2 ∈ gaussianPointBand p.1.1 p.1.2 r}
  have hS : MeasurableSet S := by
    change MeasurableSet {p : ((Fin h → Space d) × Space h) × Space d |
      ∀ i, |inner ℝ p.2 (p.1.1 i)-p.1.2 i| ≤ r}
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  exact measurable_measure_prodMk_left hS

theorem gaussianPointMass_integrated (μ : Measure (Space d)) [SFinite μ]
    (A : Fin h → Space d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ z : Space h, gaussianPointMass μ r (A,z)) = ENNReal.ofReal ((2:ℝ)^h)*μ univ := by
  simp only [gaussianPointMass]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,gaussianPointBand_integrated_mass μ A hr.le,
    ← mul_assoc,gaussian_band_normalization hr (by norm_num : (0:ℝ) ≤ 2)]

theorem gaussian_point_mass_second_moment (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (k : ℕ)
    (hmass : μ univ ≤ 1)
    (hball : ∀ x : Space d, ∀ n : ℕ, n ≤ k →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      (gaussianPointMass μ (1/(2:ℝ)^k) p)^2 ∂(gaussianRows d h).prod volume) ≤
      ENNReal.ofReal ((4*gaussianVectorBandConstant)^h)*
        (ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1) := by
  simp only [gaussianPointMass,mul_pow]
  rw [lintegral_const_mul' _ _ (by
    rw [pow_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  calc
    _ ≤ (ENNReal.ofReal ((1/(2:ℝ)^k)^(-(h:ℝ))))^2*
        (ENNReal.ofReal ((4*gaussianVectorBandConstant*(1/(2:ℝ)^k)^2)^h)*
          (ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1)) :=
      mul_le_mul_right (gaussian_point_band_second_moment_frostman μ hK hq k hmass hball) _
    _ = _ := by
      rw [← mul_assoc,gaussian_squared_band_normalization (by positivity)
        (mul_nonneg (by norm_num) gaussianVectorBandConstant_pos.le),mul_pow]

end Falconer

end OAI

end ExtensionScope2

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPointClose. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope3



namespace OAI

/-! # Localized pairs of Gaussian point slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianPointCloseMass (μ : Measure (Space d))
    (p : (Fin h → Space d) × Space h) (r ρ : ℝ) : ℝ≥0∞ :=
  (μ.prod μ) ({z | dist z.1 z.2 < ρ} ∩
    ((gaussianPointBand p.1 p.2 r) ×ˢ (gaussianPointBand p.1 p.2 r)))

instance gaussianPointSliceMeasure_finite (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (A : Fin h → Space d) (z : Space h) (r : ℝ) : IsFiniteMeasure (gaussianPointSliceMeasure μ A z r) := by
  refine ⟨?_⟩
  change ENNReal.ofReal (r^(-(h:ℝ)))*(μ.restrict (gaussianPointBand A z r)) univ < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem gaussianPointSlice_close_identity (μ : Measure (Space d)) [SFinite μ]
    (p : (Fin h → Space d) × Space h) (r ρ : ℝ) :
    ((gaussianPointSliceMeasure μ p.1 p.2 r).prod (gaussianPointSliceMeasure μ p.1 p.2 r))
        {z | dist z.1 z.2 < ρ} =
      (ENNReal.ofReal (r^(-(h:ℝ))))^2*gaussianPointCloseMass μ p r ρ := by
  have hD : MeasurableSet {z : Space d × Space d | dist z.1 z.2 < ρ} :=
    measurableSet_lt (by fun_prop) measurable_const
  simp only [gaussianPointSliceMeasure,Measure.prod_smul_left,Measure.prod_smul_right,
    Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,Measure.restrict_apply hD,
    gaussianPointCloseMass,pow_two,mul_assoc]

theorem gaussian_point_close_average (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 ≤ r) (ρ : ℝ) :
    (∫⁻ p : (Fin h → Space d) × Space h, gaussianPointCloseMass μ p r ρ
      ∂(gaussianRows d h).prod volume) ≤
      ∫⁻ z in {z : Space d × Space d | dist z.1 z.2 < ρ}, ENNReal.ofReal ((2*r)^h)*
        gaussianRows d h {A | ∀ i, |inner ℝ (z.1-z.2) (A i)| ≤ 2*r} ∂μ.prod μ := by
  let D : Set (Space d × Space d) := {z | dist z.1 z.2 < ρ}
  let S : Set (((Fin h → Space d) × Space h) × (Space d × Space d)) :=
    {p | p.2.1 ∈ gaussianPointBand p.1.1 p.1.2 r ∧ p.2.2 ∈ gaussianPointBand p.1.1 p.1.2 r}
  have hS : MeasurableSet S := by
    change MeasurableSet {p : ((Fin h → Space d) × Space h) × (Space d × Space d) |
      (∀ i, |inner ℝ p.2.1 (p.1.1 i)-p.1.2 i| ≤ r) ∧
      (∀ i, |inner ℝ p.2.2 (p.1.1 i)-p.1.2 i| ≤ r)}
    simp only [ofPred_and,ofPred_forall]
    apply MeasurableSet.inter <;> apply MeasurableSet.iInter <;> intro i <;>
      exact measurableSet_le (by fun_prop) measurable_const
  have hsection (p : (Fin h → Space d) × Space h) : Prod.mk p ⁻¹' S =
      (gaussianPointBand p.1 p.2 r) ×ˢ (gaussianPointBand p.1 p.2 r) := rfl
  calc
    _ = ∫⁻ p : (Fin h → Space d) × Space h, ((μ.prod μ).restrict D) (Prod.mk p ⁻¹' S)
        ∂(gaussianRows d h).prod volume := by
      apply lintegral_congr
      intro p
      rw [hsection,Measure.restrict_apply
        ((gaussianPointBand_measurable p.1 p.2 r).prod (gaussianPointBand_measurable p.1 p.2 r))]
      simp only [gaussianPointCloseMass,D,inter_comm]
    _ = (((gaussianRows d h).prod volume).prod ((μ.prod μ).restrict D)) S :=
      (Measure.prod_apply hS).symm
    _ = ∫⁻ z in D, ((gaussianRows d h).prod (volume : Measure (Space h)))
        {p | z.1 ∈ gaussianPointBand p.1 p.2 r ∧ z.2 ∈ gaussianPointBand p.1 p.2 r} ∂μ.prod μ :=
      Measure.prod_apply_symm hS
    _ ≤ _ := lintegral_mono (fun z => gaussianPointBand_pair_average z.1 z.2 hr)

end Falconer

end OAI

end ExtensionScope3

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianBallMeasurable. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope4



namespace OAI

/-! # Joint measurability of the ball tests used to prune Gaussian slices -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_direction_ball_mass_measurable (ν : Measure (Sphere d)) [SFinite ν] (r ρ : ℝ) :
    Measurable (fun p : (Fin h → Space d) × Sphere d =>
      gaussianDirectionSliceMeasure ν p.1 r (ball p.2 ρ)) := by
  simp only [gaussianDirectionSliceMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply measurableSet_ball]
  apply Measurable.const_mul
  let S : Set (((Fin h → Space d) × Sphere d) × Sphere d) :=
    {p | dist p.2 p.1.2 < ρ ∧ ∀ i, |inner ℝ (p.2:Space d) (p.1.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_and,ofPred_forall]
    apply MeasurableSet.inter (measurableSet_lt (by fun_prop) measurable_const)
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  convert (measurable_measure_prodMk_left (ν := ν) hS) using 1
  ext p
  congr 1

theorem gaussian_point_ball_mass_measurable (μ : Measure (Space d)) [SFinite μ] (r ρ : ℝ) :
    Measurable (fun p : ((Fin h → Space d) × Space h) × Space d =>
      gaussianPointSliceMeasure μ p.1.1 p.1.2 r (ball p.2 ρ)) := by
  simp only [gaussianPointSliceMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply measurableSet_ball]
  apply Measurable.const_mul
  let S : Set ((((Fin h → Space d) × Space h) × Space d) × Space d) :=
    {p | dist p.2 p.1.2 < ρ ∧ ∀ i, |inner ℝ p.2 (p.1.1.1 i)-p.1.1.2 i| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_and,ofPred_forall]
    apply MeasurableSet.inter (measurableSet_lt (by fun_prop) measurable_const)
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  convert (measurable_measure_prodMk_left (ν := μ) hS) using 1
  ext p
  congr 1

end Falconer

end OAI

end ExtensionScope4

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianRestrictedMass. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope5


namespace OAI

/-! # Jointly measurable restrictions of the actual Gaussian slice laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem parameter_restricted_mass_measurable {P X : Type*} [MeasurableSpace P] [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (B G : Set (P × X)) (hB : MeasurableSet B) (hG : MeasurableSet G) :
    Measurable (fun p : P => (μ.restrict {x | (p,x) ∈ B}) {x | (p,x) ∈ G}) := by
  convert (measurable_measure_prodMk_left (ν := μ) (hG.inter hB)) using 1
  ext p
  rw [Measure.restrict_apply (show MeasurableSet {x | (p,x) ∈ G} from
    hG.preimage measurable_prodMk_left)]
  rfl

theorem gaussian_direction_restriction_mass_measurable
    (ν : Measure (Sphere d)) [SFinite ν] (r : ℝ)
    (G : Set ((Fin h → Space d) × Sphere d)) (hG : MeasurableSet G) :
    Measurable (fun A : Fin h → Space d =>
      gaussianDirectionSliceMeasure ν A r {w | (A,w) ∈ G}) := by
  simp only [gaussianDirectionSliceMeasure,Measure.smul_apply,smul_eq_mul]
  apply Measurable.const_mul
  let B : Set ((Fin h → Space d) × Sphere d) :=
    {p | ∀ i, |inner ℝ (p.2:Space d) (p.1 i)| ≤ r}
  have hB : MeasurableSet B := by
    simp only [B,ofPred_forall]
    exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  exact parameter_restricted_mass_measurable ν B G hB hG

theorem gaussian_point_restriction_mass_measurable
    (μ : Measure (Space d)) [SFinite μ] (r : ℝ)
    (G : Set (((Fin h → Space d) × Space h) × Space d)) (hG : MeasurableSet G) :
    Measurable (fun p : (Fin h → Space d) × Space h =>
      gaussianPointSliceMeasure μ p.1 p.2 r {x | (p,x) ∈ G}) := by
  simp only [gaussianPointSliceMeasure,Measure.smul_apply,smul_eq_mul]
  apply Measurable.const_mul
  let B : Set (((Fin h → Space d) × Space h) × Space d) :=
    {p | ∀ i, |inner ℝ p.2 (p.1.1 i)-p.1.2 i| ≤ r}
  have hB : MeasurableSet B := by
    simp only [B,ofPred_forall]
    exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  exact parameter_restricted_mass_measurable μ B G hB hG

theorem gaussian_direction_bad_ball_mass_measurable
    (ν : Measure (Sphere d)) [SFinite ν] (r ρ : ℝ) (T : ℝ≥0∞) :
    Measurable (fun A : Fin h → Space d =>
      gaussianDirectionSliceMeasure ν A r
        {w | T < gaussianDirectionSliceMeasure ν A r (Metric.ball w ρ)}) :=
  gaussian_direction_restriction_mass_measurable ν r _
    (measurableSet_lt measurable_const (gaussian_direction_ball_mass_measurable ν r ρ))

theorem gaussian_point_bad_ball_mass_measurable
    (μ : Measure (Space d)) [SFinite μ] (r ρ : ℝ) (T : ℝ≥0∞) :
    Measurable (fun p : (Fin h → Space d) × Space h =>
      gaussianPointSliceMeasure μ p.1 p.2 r
        {x | T < gaussianPointSliceMeasure μ p.1 p.2 r (Metric.ball x ρ)}) :=
  gaussian_point_restriction_mass_measurable μ r _
    (measurableSet_lt measurable_const (gaussian_point_ball_mass_measurable μ r ρ))

end Falconer

end OAI

end ExtensionScope5

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPairRestrictions. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope6


namespace OAI

/-! # Measurable original-pair relations in Gaussian slices -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_pair_restriction_mass_measurable
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [SFinite μ] [SFinite ν]
    (r : ℝ) (G : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)))
    (hG : MeasurableSet G) :
    Measurable (fun p : (Fin h → Space d) × Space h =>
      (gaussianPointSliceMeasure μ p.1 p.2 r).prod (gaussianDirectionSliceMeasure ν p.1 r)
        {t | (p,t) ∈ G}) := by
  let B : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)) :=
    {p | p.2.1 ∈ gaussianPointBand p.1.1 p.1.2 r ∧ p.2.2 ∈ gaussianDirectionBand p.1.1 r}
  have hB : MeasurableSet B := by
    change MeasurableSet {p : ((Fin h → Space d) × Space h) × (Space d × Sphere d) |
      (∀ i, |inner ℝ p.2.1 (p.1.1 i)-p.1.2 i| ≤ r) ∧
      ∀ i, |inner ℝ (p.2.2:Space d) (p.1.1 i)| ≤ r}
    simp only [ofPred_and,ofPred_forall]
    apply MeasurableSet.inter
    · exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
    · exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  have hm := parameter_restricted_mass_measurable (μ.prod ν) B G hB hG
  convert (hm.const_mul (ENNReal.ofReal (r^(-(h:ℝ))))).const_mul
    (ENNReal.ofReal (r^(-(h:ℝ)))) using 1
  ext p
  simp only [gaussianPointSliceMeasure,gaussianDirectionSliceMeasure,Measure.prod_smul_left,
    Measure.prod_smul_right,Measure.smul_apply,smul_eq_mul,Measure.prod_restrict]
  rfl

end Falconer

end OAI

end ExtensionScope6

/- Source: OAI.MeasureTheory.Falconer.Geometry.BallTruncation. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope7



namespace OAI

/-! # Enforcing ball bounds by deleting points of excessive local mass -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

theorem measurable_ball_mass (μ : Measure X) [SFinite μ] (r : ℝ) :
    Measurable (fun x => μ (ball x r)) := by
  have hS : MeasurableSet {z : X × X | dist z.1 z.2 < r} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hm := measurable_measure_prodMk_left (ν := μ) hS
  convert hm using 1
  ext x
  congr 1
  ext y
  simp only [mem_preimage,mem_ofPred_eq,mem_ball,dist_comm]

theorem ball_mass_pair_integral (μ : Measure X) [SFinite μ] (r : ℝ) :
    (∫⁻ x, μ (ball x r) ∂μ) = (μ.prod μ) {z | dist z.1 z.2 < r} := by
  rw [Measure.prod_apply (measurableSet_lt (by fun_prop) measurable_const)]
  apply lintegral_congr
  intro x
  congr 1
  ext y
  simp only [mem_preimage,mem_ofPred_eq,mem_ball,dist_comm]

theorem excessive_ball_mass (μ : Measure X) [SFinite μ] (r : ℝ)
    {B : ℝ≥0∞} (hB : B ≠ 0) :
    μ {x | B < μ (ball x r)} ≤ B⁻¹*(μ.prod μ) {z | dist z.1 z.2 < r} := by
  by_cases hTop : B = ∞
  · simp [hTop]
  calc
    _ ≤ μ {x | B ≤ μ (ball x r)} := measure_mono (show {x | B < μ (ball x r)} ⊆
        {x | B ≤ μ (ball x r)} from by
      intro x hx
      change B < μ (ball x r) at hx
      exact hx.le)
    _ ≤ (∫⁻ x, μ (ball x r) ∂μ)/B :=
      meas_ge_le_lintegral_div (measurable_ball_mass μ r).aemeasurable hB hTop
    _ = _ := by rw [ball_mass_pair_integral,div_eq_mul_inv,mul_comm]

omit [SecondCountableTopology X] in
theorem restricted_good_ball_bound (μ : Measure X) [SFinite μ] (r : ℝ) (B : ℝ≥0∞) :
    ∀ a : X, (μ.restrict {x | μ (ball x (2*r)) ≤ B}) (ball a r) ≤ B := by
  intro a
  rw [Measure.restrict_apply measurableSet_ball]
  by_cases hne : (ball a r ∩ {x | μ (ball x (2*r)) ≤ B}).Nonempty
  · obtain ⟨x,hxa,hx⟩ := hne
    have hsub : ball a r ∩ {x | μ (ball x (2*r)) ≤ B} ⊆ ball x (2*r) := by
      rintro y ⟨hy,_⟩
      rw [mem_ball] at hxa hy ⊢
      have htri := dist_triangle y a x
      rw [dist_comm a x] at htri
      linarith
    exact (measure_mono hsub).trans hx
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,measure_empty]
    exact bot_le

end Falconer

end OAI

end ExtensionScope7

/- Source: OAI.MeasureTheory.Falconer.Incidence.FiniteBallPruning. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope8


namespace OAI

/-! # Simultaneously enforcing the finitely many slice ball bounds -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X ι : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]

def finiteBallGood (μ : Measure X) (r : ι → ℝ) (B : ι → ℝ≥0∞) : Set X :=
  {x | ∀ i, μ (ball x (2*r i)) ≤ B i}

theorem finiteBallGood_measurable (μ : Measure X) [SFinite μ]
    (r : ι → ℝ) (B : ι → ℝ≥0∞) : MeasurableSet (finiteBallGood μ r B) := by
  simp only [finiteBallGood,ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le (measurable_ball_mass μ (2*r i)) measurable_const)

omit [SecondCountableTopology X] [BorelSpace X] in
theorem finiteBallGood_compl_mass (μ : Measure X) [SFinite μ]
    (r : ι → ℝ) (B : ι → ℝ≥0∞) :
    μ (finiteBallGood μ r B)ᶜ ≤ ∑ i, μ {x | B i < μ (ball x (2*r i))} := by
  have he : (finiteBallGood μ r B)ᶜ = ⋃ i, {x | B i < μ (ball x (2*r i))} := by
    ext x
    simp [finiteBallGood,not_forall,not_le]
  rw [he]
  exact measure_iUnion_fintype_le _ _

theorem finiteBallGood_pair_loss (μ : Measure X) [SFinite μ]
    (r : ι → ℝ) (B : ι → ℝ≥0∞) (hB : ∀ i, B i ≠ 0) :
    μ (finiteBallGood μ r B)ᶜ ≤
      ∑ i, (B i)⁻¹*(μ.prod μ) {z | dist z.1 z.2 < 2*r i} :=
  (finiteBallGood_compl_mass μ r B).trans
    (Finset.sum_le_sum (fun i _ => excessive_ball_mass μ (2*r i) (hB i)))

omit [SecondCountableTopology X] [Fintype ι] in
theorem finiteBallGood_ball_bound (μ : Measure X) [SFinite μ]
    (r : ι → ℝ) (B : ι → ℝ≥0∞) (i : ι) (a : X) :
    (μ.restrict (finiteBallGood μ r B)) (ball a (r i)) ≤ B i := by
  calc
    _ ≤ (μ.restrict {x | μ (ball x (2*r i)) ≤ B i}) (ball a (r i)) :=
      Measure.restrict_mono_set μ (s := finiteBallGood μ r B)
        (t := {x | μ (ball x (2*r i)) ≤ B i}) (fun _ hx => hx i) _
    _ ≤ _ := restricted_good_ball_bound μ (r i) (B i) a

theorem finiteBallGood_mass_accounting (μ : Measure X) [SFinite μ]
    (r : ι → ℝ) (B : ι → ℝ≥0∞) :
    μ univ ≤ (μ.restrict (finiteBallGood μ r B)) univ +
      ∑ i, μ {x | B i < μ (ball x (2*r i))} := by
  rw [Measure.restrict_apply_univ]
  calc
    _ = μ (finiteBallGood μ r B)+μ (finiteBallGood μ r B)ᶜ :=
      (measure_add_measure_compl (finiteBallGood_measurable μ r B)).symm
    _ ≤ _ := add_le_add_right (finiteBallGood_compl_mass μ r B) _

end Falconer

end OAI

end ExtensionScope8

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPointCloseBound. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope9


namespace OAI

/-! # Localized finite-scale second moments for point slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_close_frostman (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : μ univ ≤ 1)
    (hball : ∀ x : Space d, ∀ n : ℕ, n ≤ N →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      gaussianPointCloseMass μ p (1/(2:ℝ)^N) (1/(2:ℝ)^g) ∂(gaussianRows d h).prod volume) ≤
      ENNReal.ofReal ((4*gaussianVectorBandConstant*(1/(2:ℝ)^N)^2)^h)*
        ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
          (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q)))) := by
  let r : ℝ := 1/(2:ℝ)^N
  let D : Set (Space d × Space d) := {z | dist z.1 z.2 < 1/(2:ℝ)^g}
  let C := ENNReal.ofReal ((4*gaussianVectorBandConstant*r^2)^h)
  let B := ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
    (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))
  have hC := gaussianVectorBandConstant_pos
  apply (gaussian_point_close_average μ (by positivity) (1/(2:ℝ)^g)).trans
  calc
    _ ≤ ∫⁻ z in D, ENNReal.ofReal
        ((4*gaussianVectorBandConstant*r^2/(dist z.1 z.2+r))^h) ∂μ.prod μ :=
      lintegral_mono (fun z => gaussian_point_pair_kernel z.1 z.2 (by dsimp [r]; positivity))
    _ = C * ∫⁻ z in D, ENNReal.ofReal ((1/(dist z.1 z.2+r))^(h:ℝ)) ∂μ.prod μ := by
      rw [← lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      rw [Real.rpow_natCast,← ENNReal.ofReal_mul (by positivity),← mul_pow]
      congr 2
      ring
    _ ≤ C*B := mul_le_mul_right
      (regularized_pair_potential μ hK (Nat.cast_nonneg _) hq g N hg hmass hball) C

theorem gaussian_point_slice_close_frostman (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : μ univ ≤ 1)
    (hball : ∀ x : Space d, ∀ n : ℕ, n ≤ N →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 (1/(2:ℝ)^N)).prod
        (gaussianPointSliceMeasure μ p.1 p.2 (1/(2:ℝ)^N)))
          {z | dist z.1 z.2 < 1/(2:ℝ)^g} ∂(gaussianRows d h).prod volume) ≤
      ENNReal.ofReal ((4*gaussianVectorBandConstant)^h)*
        ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
          (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q)))) := by
  simp_rw [gaussianPointSlice_close_identity]
  rw [lintegral_const_mul' _ _ (by
    rw [pow_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply (mul_le_mul_right (gaussian_point_close_frostman μ hK hq g N hg hmass hball) _).trans_eq
  rw [← mul_assoc,gaussian_squared_band_normalization (by positivity)
    (mul_nonneg (by norm_num) gaussianVectorBandConstant_pos.le)]

end Falconer

end OAI

end ExtensionScope9

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianCloseBound. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope10


namespace OAI

/-! # Finite-scale close-pair bounds for normalized direction slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_direction_close_frostman (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : ν univ ≤ 1)
    (hball : ∀ w : Sphere d, ∀ n : ℕ, n ≤ N →
      ν (ball w (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d)) :
    (∫⁻ A : Fin h → Space d,
      gaussianDirectionCloseMass ν A (1/(2:ℝ)^N) (1/(2:ℝ)^g) ∂gaussianRows d h) ≤
      ENNReal.ofReal ((2*gaussianPairBandConstant*(1/(2:ℝ)^N)^2)^h)*
        ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
          (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q)))) := by
  let r : ℝ := 1/(2:ℝ)^N
  let D : Set (Sphere d × Sphere d) := {z | dist z.1 z.2 < 1/(2:ℝ)^g}
  let C := ENNReal.ofReal ((2*gaussianPairBandConstant*r^2)^h)
  let B := ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
    (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))
  rw [gaussian_direction_close_average]
  calc
    _ ≤ ∫⁻ z in D, ENNReal.ofReal
        ((2*gaussianPairBandConstant*r^2/(dist z.1 z.2+r))^h) ∂ν.prod ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hchart] with z hz
      simpa only [Subtype.dist_eq] using gaussianRows_pair_band_chart (h := h)
        (sphere_norm z.1) (sphere_norm z.2) hz (by positivity)
    _ = C * ∫⁻ z in D, ENNReal.ofReal ((1/(dist z.1 z.2+r))^(h:ℝ)) ∂ν.prod ν := by
      rw [← lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      rw [gaussian_pair_kernel_factor,ENNReal.ofReal_mul
        (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          gaussianPairBandConstant_pos.le) (sq_nonneg r)) h)]
    _ ≤ C*B := mul_le_mul_right
      (regularized_pair_potential ν hK (Nat.cast_nonneg _) hq g N hg hmass hball) C

theorem gaussian_direction_slice_close_frostman (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : ν univ ≤ 1)
    (hball : ∀ w : Sphere d, ∀ n : ℕ, n ≤ N →
      ν (ball w (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d)) :
    (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).prod
        (gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)))
          {z | dist z.1 z.2 < 1/(2:ℝ)^g} ∂gaussianRows d h) ≤
      ENNReal.ofReal ((2*gaussianPairBandConstant)^h)*
        ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
          (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q)))) := by
  simp_rw [gaussianDirectionSlice_close_identity]
  rw [lintegral_const_mul' _ _ (by
    rw [pow_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply (mul_le_mul_right (gaussian_direction_close_frostman ν hK hq g N hg hmass hball hchart) _).trans_eq
  rw [← mul_assoc,gaussian_squared_band_normalization (by positivity)
    (mul_nonneg (by norm_num) gaussianPairBandConstant_pos.le)]

end Falconer

end OAI

end ExtensionScope10

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianBallTruncation. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope11



namespace OAI

/-! # Ball-mass deletion for the Gaussian direction slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_direction_ball_deletion (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {r ρ : ℝ} {T B : ℝ≥0∞} (hT : 0 < T)
    (hpair : (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A r).prod (gaussianDirectionSliceMeasure ν A r))
        {z | dist z.1 z.2 < ρ} ∂gaussianRows d h) ≤ B) :
    (∫⁻ A : Fin h → Space d,
      gaussianDirectionSliceMeasure ν A r
        {w | T < gaussianDirectionSliceMeasure ν A r (ball w ρ)} ∂gaussianRows d h) ≤ T⁻¹*B := by
  calc
    _ ≤ ∫⁻ A : Fin h → Space d, T⁻¹*
        ((gaussianDirectionSliceMeasure ν A r).prod (gaussianDirectionSliceMeasure ν A r))
          {z | dist z.1 z.2 < ρ} ∂gaussianRows d h :=
      lintegral_mono (fun A => excessive_ball_mass (gaussianDirectionSliceMeasure ν A r) ρ hT.ne')
    _ = T⁻¹*∫⁻ A : Fin h → Space d,
        ((gaussianDirectionSliceMeasure ν A r).prod (gaussianDirectionSliceMeasure ν A r))
          {z | dist z.1 z.2 < ρ} ∂gaussianRows d h :=
      lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hT.ne')
    _ ≤ _ := mul_le_mul_right hpair _

theorem gaussian_direction_good_ball (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    (A : Fin h → Space d) (r ρ : ℝ) (T : ℝ≥0∞) (a : Sphere d) :
    ((gaussianDirectionSliceMeasure ν A r).restrict
      {w | gaussianDirectionSliceMeasure ν A r (ball w (2*ρ)) ≤ T}) (ball a ρ) ≤ T :=
  restricted_good_ball_bound (gaussianDirectionSliceMeasure ν A r) ρ T a

end Falconer

end OAI

end ExtensionScope11

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPointTruncation. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope12



namespace OAI

/-! # Ball-mass deletion for the Gaussian point slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_ball_deletion (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {r ρ : ℝ} {T B : ℝ≥0∞} (hT : 0 < T)
    (hpair : (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 r).prod (gaussianPointSliceMeasure μ p.1 p.2 r))
        {z | dist z.1 z.2 < ρ} ∂(gaussianRows d h).prod volume) ≤ B) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      gaussianPointSliceMeasure μ p.1 p.2 r
        {x | T < gaussianPointSliceMeasure μ p.1 p.2 r (ball x ρ)}
          ∂(gaussianRows d h).prod volume) ≤ T⁻¹*B := by
  calc
    _ ≤ ∫⁻ p : (Fin h → Space d) × Space h, T⁻¹*
        ((gaussianPointSliceMeasure μ p.1 p.2 r).prod (gaussianPointSliceMeasure μ p.1 p.2 r))
          {z | dist z.1 z.2 < ρ} ∂(gaussianRows d h).prod volume :=
      lintegral_mono (fun p => excessive_ball_mass (gaussianPointSliceMeasure μ p.1 p.2 r) ρ hT.ne')
    _ = T⁻¹*∫⁻ p : (Fin h → Space d) × Space h,
        ((gaussianPointSliceMeasure μ p.1 p.2 r).prod (gaussianPointSliceMeasure μ p.1 p.2 r))
          {z | dist z.1 z.2 < ρ} ∂(gaussianRows d h).prod volume :=
      lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hT.ne')
    _ ≤ _ := mul_le_mul_right hpair _

theorem gaussian_point_good_ball (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (A : Fin h → Space d) (z : Space h) (r ρ : ℝ) (T : ℝ≥0∞) (a : Space d) :
    ((gaussianPointSliceMeasure μ A z r).restrict
      {x | gaussianPointSliceMeasure μ A z r (ball x (2*ρ)) ≤ T}) (ball a ρ) ≤ T :=
  restricted_good_ball_bound (gaussianPointSliceMeasure μ A z r) ρ T a

end Falconer

end OAI

end ExtensionScope12

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianFinitePruning. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope13




namespace OAI

/-! # Simultaneous Gaussian slice pruning at the required finite scales -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_direction_finite_ball_deletion
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (δ : ℝ)
    (r : ι → ℝ) (T C : ι → ℝ≥0∞) (hT : ∀ i, 0 < T i)
    (hp : ∀ i, (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows d h) ≤ C i) :
    (∫⁻ A : Fin h → Space d, gaussianDirectionSliceMeasure ν A δ
      (finiteBallGood (gaussianDirectionSliceMeasure ν A δ) r T)ᶜ ∂gaussianRows d h) ≤
        ∑ i, (T i)⁻¹*C i := by
  classical
  calc
    _ ≤ ∫⁻ A : Fin h → Space d, ∑ i,
        gaussianDirectionSliceMeasure ν A δ
          {w | T i < gaussianDirectionSliceMeasure ν A δ (ball w (2*r i))}
          ∂gaussianRows d h :=
      lintegral_mono (fun A => finiteBallGood_compl_mass _ r T)
    _ = ∑ i, ∫⁻ A : Fin h → Space d, gaussianDirectionSliceMeasure ν A δ
        {w | T i < gaussianDirectionSliceMeasure ν A δ (ball w (2*r i))}
        ∂gaussianRows d h := lintegral_finsetSum _
          (fun i _ => gaussian_direction_bad_ball_mass_measurable ν δ (2*r i) (T i))
    _ ≤ _ := Finset.sum_le_sum (fun i _ => gaussian_direction_ball_deletion ν (hT i) (hp i))

theorem gaussian_point_finite_ball_deletion
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (δ : ℝ)
    (r : ι → ℝ) (T C : ι → ℝ≥0∞) (hT : ∀ i, 0 < T i)
    (hp : ∀ i, (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows d h).prod volume) ≤ C i) :
    (∫⁻ p : (Fin h → Space d) × Space h, gaussianPointSliceMeasure μ p.1 p.2 δ
      (finiteBallGood (gaussianPointSliceMeasure μ p.1 p.2 δ) r T)ᶜ
        ∂(gaussianRows d h).prod volume) ≤ ∑ i, (T i)⁻¹*C i := by
  classical
  calc
    _ ≤ ∫⁻ p : (Fin h → Space d) × Space h, ∑ i,
        gaussianPointSliceMeasure μ p.1 p.2 δ
          {x | T i < gaussianPointSliceMeasure μ p.1 p.2 δ (ball x (2*r i))}
          ∂(gaussianRows d h).prod volume :=
      lintegral_mono (fun p => finiteBallGood_compl_mass _ r T)
    _ = ∑ i, ∫⁻ p : (Fin h → Space d) × Space h, gaussianPointSliceMeasure μ p.1 p.2 δ
        {x | T i < gaussianPointSliceMeasure μ p.1 p.2 δ (ball x (2*r i))}
        ∂(gaussianRows d h).prod volume := lintegral_finsetSum _
          (fun i _ => gaussian_point_bad_ball_mass_measurable μ δ (2*r i) (T i))
    _ ≤ _ := Finset.sum_le_sum (fun i _ => gaussian_point_ball_deletion μ (hT i) (hp i))

end Falconer

end OAI

end ExtensionScope13

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPruningSets. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope14




namespace OAI

/-! # The actual measurable restrictions used in Gaussian slice selection -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

def gaussianPointGood (μ : Measure (Space d)) (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞)
    (p : (Fin h → Space d) × Space h) : Set (Space d) :=
  finiteBallGood (gaussianPointSliceMeasure μ p.1 p.2 δ) r T

def gaussianDirectionGood (ν : Measure (Sphere d)) (δ : ℝ) (r : ι → ℝ)
    (T : ι → ℝ≥0∞) (M : ℝ≥0∞) (A : Fin h → Space d) : Set (Sphere d) :=
  {w | gaussianDirectionMass ν δ A ≤ M ∧ w ∈ finiteBallGood (gaussianDirectionSliceMeasure ν A δ) r T}

theorem gaussianPointGood_measurable_joint (μ : Measure (Space d)) [SFinite μ]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) :
    MeasurableSet {p : ((Fin h → Space d) × Space h) × Space d |
      p.2 ∈ gaussianPointGood μ δ r T p.1} := by
  change MeasurableSet {p : ((Fin h → Space d) × Space h) × Space d |
    ∀ i, gaussianPointSliceMeasure μ p.1.1 p.1.2 δ (ball p.2 (2*r i)) ≤ T i}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le
    (gaussian_point_ball_mass_measurable μ δ (2*r i)) measurable_const)

theorem gaussianDirectionGood_measurable_joint (ν : Measure (Sphere d)) [SFinite ν]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (M : ℝ≥0∞) :
    MeasurableSet {p : (Fin h → Space d) × Sphere d | p.2 ∈ gaussianDirectionGood ν δ r T M p.1} := by
  change MeasurableSet {p : (Fin h → Space d) × Sphere d |
    gaussianDirectionMass ν δ p.1 ≤ M ∧
    ∀ i, gaussianDirectionSliceMeasure ν p.1 δ (ball p.2 (2*r i)) ≤ T i}
  simp only [ofPred_and,ofPred_forall]
  apply MeasurableSet.inter
  · exact measurableSet_le ((gaussianDirectionMass_measurable ν δ).comp measurable_fst) measurable_const
  · exact MeasurableSet.iInter (fun i => measurableSet_le
      (gaussian_direction_ball_mass_measurable ν δ (2*r i)) measurable_const)

omit [Fintype ι] in
theorem gaussianPointGood_ball (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (p : (Fin h → Space d) × Space h) (i : ι) (a : Space d) :
    ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r T p))
      (ball a (r i)) ≤ T i := finiteBallGood_ball_bound _ r T i a

omit [Fintype ι] in
theorem gaussianDirectionGood_ball (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (A : Fin h → Space d) (i : ι) (a : Sphere d) :
    ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r T M A))
      (ball a (r i)) ≤ T i := by
  calc
    _ ≤ ((gaussianDirectionSliceMeasure ν A δ).restrict
        (finiteBallGood (gaussianDirectionSliceMeasure ν A δ) r T)) (ball a (r i)) :=
      Measure.restrict_mono_set _ (s := gaussianDirectionGood ν δ r T M A)
        (t := finiteBallGood (gaussianDirectionSliceMeasure ν A δ) r T) (fun _ hw => hw.2) _
    _ ≤ _ := finiteBallGood_ball_bound _ r T i a

omit [Fintype ι] in
theorem gaussianDirectionGood_mass (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (M : ℝ≥0∞) (A : Fin h → Space d) :
    ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r T M A)) univ ≤ M := by
  by_cases hm : gaussianDirectionMass ν δ A ≤ M
  · calc
      _ ≤ gaussianDirectionSliceMeasure ν A δ univ := Measure.restrict_le_self _
      _ = gaussianDirectionMass ν δ A := by
        simp [gaussianDirectionSliceMeasure,gaussianDirectionMass,Measure.smul_apply]
      _ ≤ _ := hm
  · have he : gaussianDirectionGood ν δ r T M A = ∅ := by ext w; simp [gaussianDirectionGood,hm]
    simp only [he,Measure.restrict_empty,Measure.coe_zero,Pi.zero_apply]
    exact zero_le

end Falconer

end OAI

end ExtensionScope14

/- Source: OAI.MeasureTheory.Falconer.Measures.ProductRestrictionLoss. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope15



namespace OAI

/-! # Incidence mass lost when either original marginal is restricted -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem product_restriction_incidence_loss (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (E : Set (X × Y)) (hE : MeasurableSet E)
    (P : Set X) (Q : Set Y) :
    (μ.prod ν) E ≤ (μ.restrict P).prod (ν.restrict Q) E +
      μ Pᶜ*ν univ + μ univ*ν Qᶜ := by
  have hs : E ⊆ (E ∩ (P ×ˢ Q)) ∪ (Pᶜ ×ˢ univ) ∪ (univ ×ˢ Qᶜ) := by
    intro z hz
    by_cases hp : z.1 ∈ P
    · by_cases hq : z.2 ∈ Q
      · exact Or.inl (Or.inl ⟨hz,hp,hq⟩)
      · exact Or.inr ⟨mem_univ _,hq⟩
    · exact Or.inl (Or.inr ⟨hp,mem_univ _⟩)
  rw [Measure.prod_restrict,Measure.restrict_apply hE]
  calc
    _ ≤ (μ.prod ν) ((E ∩ (P ×ˢ Q)) ∪ (Pᶜ ×ˢ univ) ∪ (univ ×ˢ Qᶜ)) := measure_mono hs
    _ ≤ (μ.prod ν) ((E ∩ (P ×ˢ Q)) ∪ (Pᶜ ×ˢ univ)) + (μ.prod ν) (univ ×ˢ Qᶜ) :=
      measure_union_le _ _
    _ ≤ ((μ.prod ν) (E ∩ (P ×ˢ Q)) + (μ.prod ν) (Pᶜ ×ˢ univ)) +
        (μ.prod ν) (univ ×ˢ Qᶜ) := add_le_add_left (measure_union_le _ _) _
    _ = _ := by rw [Measure.prod_prod,Measure.prod_prod]

theorem product_incidence_relation_loss (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (E F : Set (X × Y)) :
    (μ.prod ν) E ≤ (μ.prod ν) (E ∩ F) + (μ.prod ν) Fᶜ := by
  apply (measure_mono (show E ⊆ (E ∩ F) ∪ Fᶜ from ?_)).trans (measure_union_le _ _)
  intro z hz
  by_cases hf : z ∈ F
  · exact Or.inl ⟨hz,hf⟩
  · exact Or.inr hf

end Falconer

end OAI

end ExtensionScope15

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedIncidence. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope16



namespace OAI

/-! # Incidence on the original labels after the marginal slice restrictions -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

noncomputable def gaussianPrunedIncidence
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) (δ : ℝ)
    (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (p : (Fin h → Space d) × Space h) : ℝ≥0∞ :=
  ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)).prod
    ((gaussianDirectionSliceMeasure ν p.1 δ).restrict (gaussianDirectionGood ν δ r TD M p.1)) E

theorem gaussianPrunedIncidence_measurable
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E) :
    Measurable (gaussianPrunedIncidence (h := h) μ ν δ r TP TD M E) := by
  let G : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)) :=
    {q | q.2 ∈ E ∧ q.2.1 ∈ gaussianPointGood μ δ r TP q.1 ∧
      q.2.2 ∈ gaussianDirectionGood ν δ r TD M q.1.1}
  have hG : MeasurableSet G := by
    have hp := (gaussianPointGood_measurable_joint (h := h) μ δ r TP).preimage
      (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
        (q.1,q.2.1)) from by fun_prop)
    have hd := (gaussianDirectionGood_measurable_joint (h := h) ν δ r TD M).preimage
      (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
        (q.1.1,q.2.2)) from by fun_prop)
    exact (hE.preimage measurable_snd).inter (hp.inter hd)
  convert gaussian_pair_restriction_mass_measurable μ ν δ G hG using 1
  ext p
  rw [gaussianPrunedIncidence,Measure.prod_restrict,Measure.restrict_apply hE]
  congr 1

omit [Fintype ι] in
theorem gaussian_pruning_pointwise_loss
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (p : (Fin h → Space d) × Space h) :
    (gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianDirectionSliceMeasure ν p.1 δ) E ≤
      gaussianPrunedIncidence μ ν δ r TP TD M E p +
      gaussianPointSliceMeasure μ p.1 p.2 δ (gaussianPointGood μ δ r TP p)ᶜ*M +
      gaussianPointMass μ δ p*gaussianDirectionSliceMeasure ν p.1 δ
        (finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r TD)ᶜ +
      (if M < gaussianDirectionMass ν δ p.1 then
        gaussianPointMass μ δ p*gaussianDirectionMass ν δ p.1 else 0) := by
  have hm : gaussianDirectionSliceMeasure ν p.1 δ univ = gaussianDirectionMass ν δ p.1 := by
    simp [gaussianDirectionSliceMeasure,gaussianDirectionMass,Measure.smul_apply]
  by_cases hM : gaussianDirectionMass ν δ p.1 ≤ M
  · have hd : gaussianDirectionGood ν δ r TD M p.1 =
        finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r TD := by
      ext w
      simp only [gaussianDirectionGood,mem_ofPred_eq,hM,true_and]
    have hl := product_restriction_incidence_loss (gaussianPointSliceMeasure μ p.1 p.2 δ)
      (gaussianDirectionSliceMeasure ν p.1 δ) E hE (gaussianPointGood μ δ r TP p)
      (finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r TD)
    rw [gaussianPointSliceMeasure_univ,hm] at hl
    simp only [not_lt_of_ge hM,ite_false,add_zero,gaussianPrunedIncidence,hd]
    exact hl.trans (add_le_add (add_le_add le_rfl (mul_le_mul_right hM _)) le_rfl)
  · have hl : (gaussianPointSliceMeasure μ p.1 p.2 δ).prod
        (gaussianDirectionSliceMeasure ν p.1 δ) E ≤
        gaussianPointMass μ δ p*gaussianDirectionMass ν δ p.1 := by
      calc
        _ ≤ (gaussianPointSliceMeasure μ p.1 p.2 δ).prod
            (gaussianDirectionSliceMeasure ν p.1 δ) univ := measure_mono (subset_univ _)
        _ = _ := by rw [← univ_prod_univ,Measure.prod_prod,gaussianPointSliceMeasure_univ,hm]
    simp only [lt_of_not_ge hM,ite_true]
    exact hl.trans (show _ ≤ _ + _ from by
      exact (zero_add _).symm.le.trans (add_le_add bot_le le_rfl))

end Falconer

end OAI

end ExtensionScope16

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianIncidenceAverage. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope17



namespace OAI

/-! # Incidence averaging for the original point and direction labels -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_band_label_average
    (ξ : Measure (Space d × Sphere d)) [SFinite ξ]
    (A : Fin h → Space d) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ z : Space h, ξ {t | t.1 ∈ gaussianPointBand A z r}) =
      ENNReal.ofReal ((2*r)^h)*ξ univ := by
  let S : Set (Space h × (Space d × Sphere d)) := {p | p.2.1 ∈ gaussianPointBand A p.1 r}
  have hS : MeasurableSet S := by
    change MeasurableSet {p : Space h × (Space d × Sphere d) |
      ∀ i, |inner ℝ p.2.1 (A i)-p.1 i| ≤ r}
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  calc
    _ = ((volume : Measure (Space h)).prod ξ) S := (Measure.prod_apply hS).symm
    _ = ∫⁻ t : Space d × Sphere d, (volume : Measure (Space h))
        {z | t.1 ∈ gaussianPointBand A z r} ∂ξ := Measure.prod_apply_symm hS
    _ = ∫⁻ _ : Space d × Sphere d, ENNReal.ofReal ((2*r)^h) ∂ξ := by
      apply lintegral_congr
      intro t
      exact gaussianPointBand_parameter_measure A t.1 hr
    _ = _ := lintegral_const _

theorem gaussian_incidence_raw_point_average
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space d × Sphere d)) (_hE : MeasurableSet E)
    (A : Fin h → Space d) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ z : Space h, (μ.prod ν) (E ∩ ((gaussianPointBand A z r) ×ˢ (gaussianDirectionBand A r)))) =
      ENNReal.ofReal ((2*r)^h)*(μ.prod ν) (E ∩ (univ ×ˢ (gaussianDirectionBand A r))) := by
  let F := E ∩ (univ ×ˢ (gaussianDirectionBand A r))
  have hh := gaussian_point_band_label_average ((μ.prod ν).restrict F) A hr
  have he (z : Space h) : ((μ.prod ν).restrict F) {t | t.1 ∈ gaussianPointBand A z r} =
      (μ.prod ν) (E ∩ ((gaussianPointBand A z r) ×ˢ (gaussianDirectionBand A r))) := by
    rw [Measure.restrict_apply (show MeasurableSet {t : Space d × Sphere d |
      t.1 ∈ gaussianPointBand A z r} from
        (gaussianPointBand_measurable A z r).preimage measurable_fst)]
    congr 1
    ext t
    simp only [F,mem_inter_iff,mem_prod,mem_univ,mem_ofPred_eq,true_and]
    tauto
  simpa only [he,Measure.restrict_apply_univ,F] using hh

theorem gaussian_slice_incidence_point_average
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (A : Fin h → Space d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ z : Space h, (gaussianPointSliceMeasure μ A z r).prod
      (gaussianDirectionSliceMeasure ν A r) E) =
      ENNReal.ofReal ((2:ℝ)^h)*
        gaussianDirectionMass (((μ.prod ν).restrict E).map Prod.snd) r A := by
  have he (z : Space h) : (gaussianPointSliceMeasure μ A z r).prod
      (gaussianDirectionSliceMeasure ν A r) E =
      (ENNReal.ofReal (r^(-(h:ℝ))))^2*
        (μ.prod ν) (E ∩ ((gaussianPointBand A z r) ×ˢ (gaussianDirectionBand A r))) := by
    simp only [gaussianPointSliceMeasure,gaussianDirectionSliceMeasure,Measure.prod_smul_left,
      Measure.prod_smul_right,Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,
      Measure.restrict_apply hE,pow_two,mul_assoc]
  simp_rw [he]
  rw [lintegral_const_mul' _ _ (by
    rw [pow_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    gaussian_incidence_raw_point_average μ ν E hE A hr.le]
  have hmap : (((μ.prod ν).restrict E).map Prod.snd) (gaussianDirectionBand A r) =
      (μ.prod ν) (E ∩ (univ ×ˢ (gaussianDirectionBand A r))) := by
    rw [Measure.map_apply measurable_snd (gaussianDirectionBand_measurable A r),
      Measure.restrict_apply ((gaussianDirectionBand_measurable A r).preimage measurable_snd)]
    congr 1
    ext t
    simp only [mem_inter_iff,mem_preimage,mem_prod,mem_univ,true_and]
    tauto
  rw [gaussianDirectionMass,hmap,pow_two]
  calc
    _ = (ENNReal.ofReal (r^(-(h:ℝ)))*ENNReal.ofReal ((2*r)^h))*
        (ENNReal.ofReal (r^(-(h:ℝ)))*(μ.prod ν) (E ∩ (univ ×ˢ gaussianDirectionBand A r))) := by ac_rfl
    _ = _ := by rw [gaussian_band_normalization hr (by norm_num : (0:ℝ) ≤ 2)]

theorem gaussian_slice_incidence_mean_lower
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianBandLowerConstant^h)*(μ.prod ν) E ≤
      ∫⁻ A : Fin h → Space d, (∫⁻ z : Space h,
        (gaussianPointSliceMeasure μ A z r).prod (gaussianDirectionSliceMeasure ν A r) E) ∂gaussianRows d h := by
  simp_rw [gaussian_slice_incidence_point_average μ ν E hE _ hr]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hh := gaussian_direction_mass_mean_lower (h := h) (((μ.prod ν).restrict E).map Prod.snd) hr hr1
  rw [Measure.map_apply measurable_snd MeasurableSet.univ,preimage_univ,Measure.restrict_apply_univ] at hh
  simpa only [mul_assoc] using mul_le_mul_right hh (ENNReal.ofReal ((2:ℝ)^h))

end Falconer

end OAI

end ExtensionScope17

/- Source: OAI.MeasureTheory.Falconer.Measures.DensityTruncation. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope18




namespace OAI

/-!
# Truncation of radial densities

The integer-cap step `prep:integer-caps` deletes pairs on which either
radial density exceeds a threshold. These lemmas estimate the deleted
original product mass by the Lp moments and bound every remaining fiber
by the threshold times the angular reference measure.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

private theorem ennreal_le_threshold_tail {t T : ℝ≥0∞} {p : ℝ}
    (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) (ht : T ≤ t) :
    t ≤ T ^ (1 - p) * t ^ p := by
  have hpow := ENNReal.rpow_le_rpow ht (by linarith : 0 ≤ p - 1)
  have hprod : T ^ (p - 1) * t ≤ t ^ p := by
    calc
      T ^ (p - 1) * t ≤ t ^ (p - 1) * t := mul_le_mul_left hpow t
      _ = t ^ ((p - 1) + 1) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
      _ = t ^ p := by congr 1; ring
  have hcancel : T ^ (1 - p) * T ^ (p - 1) = 1 := by
    rw [← ENNReal.rpow_add _ _ hT.ne' hTtop]
    convert (ENNReal.rpow_zero : T ^ (0 : ℝ) = 1) using 1
    congr 1
    ring
  calc
    t = (T ^ (1 - p) * T ^ (p - 1)) * t := by rw [hcancel, one_mul]
    _ = T ^ (1 - p) * (T ^ (p - 1) * t) := mul_assoc _ _ _
    _ ≤ T ^ (1 - p) * t ^ p := mul_le_mul_right hprod _

/-- The density mass above `T` is bounded by `T^(1-p)` times its pth moment. -/
theorem density_tail_mass {A : Type*} [MeasurableSpace A]
    (σ : Measure A) (f : A → ℝ≥0∞) (hf : Measurable f)
    {T : ℝ≥0∞} {p : ℝ} (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) :
    (σ.withDensity f) {a | T < f a} ≤ T ^ (1 - p) * ∫⁻ a, f a ^ p ∂σ := by
  have hS : MeasurableSet {a | T < f a} := measurableSet_lt measurable_const hf
  rw [withDensity_apply _ hS]
  calc
    (∫⁻ a in {a | T < f a}, f a ∂σ) ≤
        ∫⁻ a in {a | T < f a}, T ^ (1 - p) * f a ^ p ∂σ := by
      apply setLIntegral_mono' hS
      intro a ha
      exact ennreal_le_threshold_tail hT hTtop hp ha.le
    _ = T ^ (1 - p) * ∫⁻ a in {a | T < f a}, f a ^ p ∂σ :=
      lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hT.ne' hTtop)
    _ ≤ T ^ (1 - p) * ∫⁻ a, f a ^ p ∂σ :=
      mul_le_mul_right (setLIntegral_le_lintegral _ _) _

/-- Truncation leaves a density bounded by the threshold on every cap. -/
theorem truncated_density_mass {A : Type*} [MeasurableSpace A]
    (σ : Measure A) (f : A → ℝ≥0∞) (hf : Measurable f)
    (T : ℝ≥0∞) (S : Set A) (hS : MeasurableSet S) :
    (σ.withDensity f) (S ∩ {a | f a ≤ T}) ≤ T * σ S := by
  have hlow : MeasurableSet {a | f a ≤ T} := measurableSet_le hf measurable_const
  rw [withDensity_apply _ (hS.inter hlow)]
  calc
    (∫⁻ a in S ∩ {a | f a ≤ T}, f a ∂σ) ≤
        ∫⁻ _ in S ∩ {a | f a ≤ T}, T ∂σ := by
      apply setLIntegral_mono' (hS.inter hlow)
      intro a ha
      exact ha.2
    _ = T * σ (S ∩ {a | f a ≤ T}) := by simp
    _ ≤ T * σ S := mul_le_mul_right (measure_mono inter_subset_left) T

/-- The bad pairs for one orientation of a radial kernel. -/
def densityFailure {X Y A : Type*} (f : X × A → ℝ≥0∞)
    (r : X × Y → A) (T : ℝ≥0∞) : Set (X × Y) :=
  {z | T < f (z.1, r z)}

theorem measurableSet_densityFailure {X Y A : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    {f : X × A → ℝ≥0∞} {r : X × Y → A} (hf : Measurable f) (hr : Measurable r)
    (T : ℝ≥0∞) : MeasurableSet (densityFailure f r T) :=
  measurableSet_lt measurable_const (hf.comp (measurable_fst.prodMk hr))

/-- Fubini measures failure using the original source marginal and the
original pin marginal. There is no normalization of individual fibers. -/
theorem density_failure_product_mass {X Y A : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    (μ : Measure X) (ν : Measure Y) [SFinite ν] (σ : Measure A)
    (f : X × A → ℝ≥0∞) (r : X × Y → A) (hf : Measurable f) (hr : Measurable r)
    (hdensity : ∀ᵐ x ∂μ, ν.map (fun y => r (x, y)) = σ.withDensity (fun a => f (x, a)))
    {T : ℝ≥0∞} {p : ℝ} (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) :
    (μ.prod ν) (densityFailure f r T) ≤
      T ^ (1 - p) * ∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂μ := by
  rw [Measure.prod_apply (measurableSet_densityFailure hf hr T)]
  calc
    (∫⁻ x, ν (Prod.mk x ⁻¹' densityFailure f r T) ∂μ) ≤
        ∫⁻ x, T ^ (1 - p) * ∫⁻ a, f (x, a) ^ p ∂σ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hdensity] with x hx
      have hfx : Measurable (fun a => f (x, a)) := hf.comp (measurable_const.prodMk measurable_id)
      have hrx : Measurable (fun y => r (x, y)) := hr.comp (measurable_const.prodMk measurable_id)
      change ν ((fun y => r (x, y)) ⁻¹' {a | T < f (x, a)}) ≤ _
      rw [← Measure.map_apply hrx (measurableSet_lt measurable_const hfx), hx]
      exact density_tail_mass σ _ hfx hT hTtop hp
    _ = _ := lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hT.ne' hTtop)

/-- Any additional pair restriction preserves the truncated fiber bound. -/
theorem truncated_radial_fiber {Y A : Type*} [MeasurableSpace Y] [MeasurableSpace A]
    (ν : Measure Y) (σ : Measure A) (f : A → ℝ≥0∞) (r : Y → A)
    (hf : Measurable f) (hr : Measurable r) (hdensity : ν.map r = σ.withDensity f)
    (T : ℝ≥0∞) (H : Set Y) (hH : ∀ y ∈ H, f (r y) ≤ T)
    (S : Set A) (hS : MeasurableSet S) :
    ν (H ∩ r ⁻¹' S) ≤ T * σ S := by
  have hset : H ∩ r ⁻¹' S ⊆ r ⁻¹' (S ∩ {a | f a ≤ T}) := by
    rintro y ⟨hy, hSy⟩
    exact ⟨hSy, hH y hy⟩
  calc
    ν (H ∩ r ⁻¹' S) ≤ ν (r ⁻¹' (S ∩ {a | f a ≤ T})) := measure_mono hset
    _ = (σ.withDensity f) (S ∩ {a | f a ≤ T}) := by
      rw [← hdensity, Measure.map_apply hr (hS.inter (measurableSet_le hf measurable_const))]
    _ ≤ T * σ S := truncated_density_mass σ f hf T S hS

/-- Deleting the failures in both orientations costs the sum of the two
integrated radial pth moments. -/
theorem bilateral_density_failure_mass {X Y A : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (σ : Measure A)
    (f : X × A → ℝ≥0∞) (r : X × Y → A) (g : Y × A → ℝ≥0∞) (s : Y × X → A)
    (hf : Measurable f) (hr : Measurable r) (hg : Measurable g) (hs : Measurable s)
    (hfdensity : ∀ᵐ x ∂μ, ν.map (fun y => r (x, y)) = σ.withDensity (fun a => f (x, a)))
    (hgdensity : ∀ᵐ y ∂ν, μ.map (fun x => s (y, x)) = σ.withDensity (fun a => g (y, a)))
    {T : ℝ≥0∞} {p : ℝ} (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) :
    (μ.prod ν) (densityFailure f r T ∪ Prod.swap ⁻¹' densityFailure g s T) ≤
      T ^ (1 - p) * ((∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂μ) +
        ∫⁻ y, ∫⁻ a, g (y, a) ^ p ∂σ ∂ν) := by
  have hswap : (μ.prod ν) (Prod.swap ⁻¹' densityFailure g s T) =
      (ν.prod μ) (densityFailure g s T) := by
    rw [← Measure.map_apply measurable_swap (measurableSet_densityFailure hg hs T), Measure.prod_swap]
  calc
    _ ≤ (μ.prod ν) (densityFailure f r T) + (μ.prod ν) (Prod.swap ⁻¹' densityFailure g s T) :=
      measure_union_le _ _
    _ = (μ.prod ν) (densityFailure f r T) + (ν.prod μ) (densityFailure g s T) := by rw [hswap]
    _ ≤ T ^ (1 - p) * (∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂μ) +
        T ^ (1 - p) * ∫⁻ y, ∫⁻ a, g (y, a) ^ p ∂σ ∂ν :=
      add_le_add (density_failure_product_mass μ ν σ f r hf hr hfdensity hT hTtop hp)
        (density_failure_product_mass ν μ σ g s hg hs hgdensity hT hTtop hp)
    _ = _ := (mul_add _ _ _).symm

/-- The threshold `R^(e/2)` gives a positive power saving in deleted mass
for every `p > 1`; its exponent is exactly `e * (p - 1) / 2`. -/
theorem exists_density_tail_power_bound (M : ℝ≥0∞) (hM : M ≠ ∞)
    {e p : ℝ} (he : 0 < e) (hp : 1 < p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ R : ℝ, 0 < R →
      (ENNReal.ofReal (R ^ (e / 2))) ^ (1 - p) * M ≤
        ENNReal.ofReal (C * R ^ (-c)) := by
  refine ⟨e * (p - 1) / 2, M.toReal + 1, by positivity, by positivity, ?_⟩
  intro R hR
  have hpow : (e / 2) * (1 - p) = -(e * (p - 1) / 2) := by ring
  calc
    (ENNReal.ofReal (R ^ (e / 2))) ^ (1 - p) * M =
        ENNReal.ofReal (M.toReal * R ^ (-(e * (p - 1) / 2))) := by
      rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hR _),
        ← Real.rpow_mul hR.le, hpow]
      conv_lhs => rw [← ENNReal.ofReal_toReal hM]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal ((M.toReal + 1) * R ^ (-(e * (p - 1) / 2))) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hR.le _)

@[fun_prop] theorem measurable_radialDirection_joint {d : ℕ} :
    Measurable (fun z : Space d × Space d => radialDirection z.1 z.2) := by
  unfold radialDirection
  fun_prop

end Falconer

end OAI

end ExtensionScope18

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianSliceTail. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope19



namespace OAI

/-! # Direction-slice mass deletion using the proved second moment -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_direction_mass_tail (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {r : ℝ} {T B : ℝ≥0∞} (hT : 0 < T) (hTtop : T ≠ ∞)
    (hmoment : (∫⁻ A : Fin h → Space d, (gaussianDirectionMass ν r A)^2
      ∂gaussianRows d h) ≤ B) :
    (∫⁻ A in {A : Fin h → Space d | T < gaussianDirectionMass ν r A},
      gaussianDirectionMass ν r A ∂gaussianRows d h) ≤ T⁻¹*B := by
  have hm := gaussianDirectionMass_measurable (h := h) ν r
  have hh := density_tail_mass (gaussianRows d h) (gaussianDirectionMass ν r) hm
    (p := 2) hT hTtop (by norm_num)
  rw [withDensity_apply _ (measurableSet_lt measurable_const hm)] at hh
  norm_num only [show (1-(2:ℝ)) = -1 by norm_num,ENNReal.rpow_neg_one,ENNReal.rpow_two] at hh
  exact hh.trans (mul_le_mul_right hmoment _)

end Falconer

end OAI

end ExtensionScope19

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianIncidenceTail. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope20



namespace OAI

/-! # Incidence cost of deleting rows with excessive direction mass -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_slice_incidence_per_row_upper
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space d × Sphere d)) (A : Fin h → Space d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ z : Space h, (gaussianPointSliceMeasure μ A z r).prod
      (gaussianDirectionSliceMeasure ν A r) E) ≤
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*gaussianDirectionMass ν r A := by
  have he : gaussianDirectionSliceMeasure ν A r univ = gaussianDirectionMass ν r A := by
    simp [gaussianDirectionSliceMeasure,gaussianDirectionMass,Measure.smul_apply]
  calc
    _ ≤ ∫⁻ z : Space h, (gaussianPointSliceMeasure μ A z r).prod
        (gaussianDirectionSliceMeasure ν A r) univ := lintegral_mono (fun _ => measure_mono (subset_univ _))
    _ = ∫⁻ z : Space h, gaussianPointMass μ r (A,z)*gaussianDirectionMass ν r A := by
      rw [← univ_prod_univ]
      simp only [Measure.prod_prod,gaussianPointSliceMeasure_univ,he]
    _ = (∫⁻ z : Space h, gaussianPointMass μ r (A,z))*gaussianDirectionMass ν r A := by
      apply lintegral_mul_const'
      rw [← he]
      exact (measure_lt_top _ _).ne
    _ = _ := by rw [gaussianPointMass_integrated μ A hr]

theorem gaussian_slice_incidence_mass_tail
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space d × Sphere d)) {r : ℝ} (hr : 0 < r)
    {T B : ℝ≥0∞} (hT : 0 < T) (hTtop : T ≠ ∞)
    (hmoment : (∫⁻ A : Fin h → Space d, (gaussianDirectionMass ν r A)^2 ∂gaussianRows d h) ≤ B) :
    (∫⁻ A in {A : Fin h → Space d | T < gaussianDirectionMass ν r A},
      (∫⁻ z : Space h, (gaussianPointSliceMeasure μ A z r).prod
        (gaussianDirectionSliceMeasure ν A r) E) ∂gaussianRows d h) ≤
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(T⁻¹*B) := by
  calc
    _ ≤ ∫⁻ A in {A : Fin h → Space d | T < gaussianDirectionMass ν r A},
        (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*gaussianDirectionMass ν r A ∂gaussianRows d h :=
      lintegral_mono (fun A => gaussian_slice_incidence_per_row_upper μ ν E A hr)
    _ = (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*
        ∫⁻ A in {A : Fin h → Space d | T < gaussianDirectionMass ν r A},
          gaussianDirectionMass ν r A ∂gaussianRows d h :=
      lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_lt_top _ _).ne)
    _ ≤ _ := mul_le_mul_right (gaussian_direction_mass_tail ν hT hTtop hmoment) _

end Falconer

end OAI

end ExtensionScope20

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianLabelCost. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope21



namespace OAI

/-! # Integrating direction-label deletion costs against the point slices -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_point_weighted_label_integral
    (μ : Measure (Space d)) [SFinite μ] {δ : ℝ} (hδ : 0 < δ)
    (f : (Fin h → Space d) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p : (Fin h → Space d) × Space h, gaussianPointMass μ δ p*f p.1
      ∂(gaussianRows d h).prod volume) =
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*∫⁻ A, f A ∂gaussianRows d h := by
  rw [lintegral_prod (fun p : (Fin h → Space d) × Space h => gaussianPointMass μ δ p*f p.1)
    (show AEMeasurable (fun p : (Fin h → Space d) × Space h => gaussianPointMass μ δ p*f p.1)
      ((gaussianRows d h).prod volume) from
        ((gaussianPointMass_measurable μ δ).mul (hf.comp measurable_fst)).aemeasurable)]
  have hi (A : Fin h → Space d) :
      (∫⁻ z : Space h, gaussianPointMass μ δ (A,z)*f A) =
        (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*f A := by
    rw [lintegral_mul_const (f A) (show Measurable (fun z : Space h => gaussianPointMass μ δ (A,z)) from
      (gaussianPointMass_measurable μ δ).comp
        (show Measurable (fun z : Space h => (A,z)) from by fun_prop)),gaussianPointMass_integrated μ A hδ]
  simp_rw [hi]
  exact lintegral_const_mul _ hf

theorem gaussian_direction_good_compl_mass_measurable
    (ν : Measure (Sphere d)) [SFinite ν] (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) :
    Measurable (fun A : Fin h → Space d => gaussianDirectionSliceMeasure ν A δ
      (finiteBallGood (gaussianDirectionSliceMeasure ν A δ) r T)ᶜ) := by
  have hg : MeasurableSet {p : (Fin h → Space d) × Sphere d |
      p.2 ∈ finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r T} := by
    change MeasurableSet {p : (Fin h → Space d) × Sphere d |
      ∀ i, gaussianDirectionSliceMeasure ν p.1 δ (Metric.ball p.2 (2*r i)) ≤ T i}
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le
      (gaussian_direction_ball_mass_measurable ν δ (2*r i)) measurable_const)
  exact gaussian_direction_restriction_mass_measurable ν δ _ hg.compl

theorem gaussian_point_good_compl_mass_measurable
    (μ : Measure (Space d)) [SFinite μ] (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) :
    Measurable (fun p : (Fin h → Space d) × Space h => gaussianPointSliceMeasure μ p.1 p.2 δ
      (gaussianPointGood μ δ r T p)ᶜ) :=
  gaussian_point_restriction_mass_measurable μ δ _
    (gaussianPointGood_measurable_joint μ δ r T).compl

end Falconer

end OAI

end ExtensionScope21

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPruningCosts. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope22


namespace OAI

/-! # All three marginal-pruning costs under the original joint slice law -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_point_pruning_incidence_cost
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (δ : ℝ)
    (r : ι → ℝ) (T C : ι → ℝ≥0∞) (hT : ∀ i, 0 < T i) (M : ℝ≥0∞)
    (hp : ∀ i, (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows d h).prod volume) ≤ C i) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      gaussianPointSliceMeasure μ p.1 p.2 δ (gaussianPointGood μ δ r T p)ᶜ*M
        ∂(gaussianRows d h).prod volume) ≤ (∑ i, (T i)⁻¹*C i)*M := by
  rw [lintegral_mul_const _ (gaussian_point_good_compl_mass_measurable μ δ r T)]
  exact mul_le_mul_left (gaussian_point_finite_ball_deletion μ δ r T C hT hp) M

theorem gaussian_direction_pruning_incidence_cost
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {δ : ℝ} (hδ : 0 < δ) (r : ι → ℝ) (T C : ι → ℝ≥0∞) (hT : ∀ i, 0 < T i)
    (hp : ∀ i, (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows d h) ≤ C i) :
    (∫⁻ p : (Fin h → Space d) × Space h, gaussianPointMass μ δ p*
      gaussianDirectionSliceMeasure ν p.1 δ
        (finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r T)ᶜ
        ∂(gaussianRows d h).prod volume) ≤
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (T i)⁻¹*C i) := by
  rw [gaussian_point_weighted_label_integral μ hδ _
    (gaussian_direction_good_compl_mass_measurable ν δ r T)]
  exact mul_le_mul_right (gaussian_direction_finite_ball_deletion ν δ r T C hT hp) _

theorem gaussian_mass_pruning_incidence_cost
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {δ : ℝ} (hδ : 0 < δ) {M B : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hp : (∫⁻ A : Fin h → Space d, (gaussianDirectionMass ν δ A)^2 ∂gaussianRows d h) ≤ B) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      gaussianPointMass μ δ p*(if M < gaussianDirectionMass ν δ p.1 then
        gaussianDirectionMass ν δ p.1 else 0) ∂(gaussianRows d h).prod volume) ≤
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*B) := by
  let S : Set (Fin h → Space d) := {A | M < gaussianDirectionMass ν δ A}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (gaussianDirectionMass_measurable ν δ)
  have hf : Measurable (S.indicator (gaussianDirectionMass ν δ)) :=
    (gaussianDirectionMass_measurable ν δ).indicator hS
  have he (A : Fin h → Space d) :
      (if M < gaussianDirectionMass ν δ A then gaussianDirectionMass ν δ A else 0) =
        S.indicator (gaussianDirectionMass ν δ) A := by
    simp only [Set.indicator_apply,S,mem_ofPred_eq]
  simp_rw [he]
  rw [gaussian_point_weighted_label_integral μ hδ _ hf,lintegral_indicator hS]
  exact mul_le_mul_right (gaussian_direction_mass_tail ν hM hMtop hp) _

end Falconer

end OAI

end ExtensionScope22

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPruningLedger. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope23



namespace OAI

/-! # The combined incidence ledger for the three marginal slice deletions -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_pruning_integral_loss
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ξ : Measure ((Fin h → Space d) × Space h)) (hξ : ξ ≤ (gaussianRows d h).prod volume)
    {δ : ℝ} (hδ : 0 < δ) (r : ι → ℝ) (TP TD CP CD : ι → ℝ≥0∞)
    (hTP : ∀ i, 0 < TP i) (hTD : ∀ i, 0 < TD i)
    {M B : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hpoint : ∀ i, (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows d h).prod volume) ≤ CP i)
    (hdir : ∀ i, (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows d h) ≤ CD i)
    (hmoment : (∫⁻ A : Fin h → Space d, (gaussianDirectionMass ν δ A)^2 ∂gaussianRows d h) ≤ B)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      (gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianDirectionSliceMeasure ν p.1 δ) E ∂ξ) ≤
      (∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p ∂ξ) +
      (∑ i, (TP i)⁻¹*CP i)*M +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (TD i)⁻¹*CD i) +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*B) := by
  let f := gaussianPrunedIncidence (h := h) μ ν δ r TP TD M E
  let a := fun p : (Fin h → Space d) × Space h =>
    gaussianPointSliceMeasure μ p.1 p.2 δ (gaussianPointGood μ δ r TP p)ᶜ*M
  let b := fun p : (Fin h → Space d) × Space h => gaussianPointMass μ δ p*
    gaussianDirectionSliceMeasure ν p.1 δ (finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r TD)ᶜ
  let c := fun p : (Fin h → Space d) × Space h =>
    if M < gaussianDirectionMass ν δ p.1 then gaussianPointMass μ δ p*gaussianDirectionMass ν δ p.1 else 0
  have hf : Measurable f := gaussianPrunedIncidence_measurable μ ν δ r TP TD M E hE
  have ha : Measurable a := (gaussian_point_good_compl_mass_measurable μ δ r TP).mul_const M
  have hb : Measurable b := (gaussianPointMass_measurable μ δ).mul
    ((gaussian_direction_good_compl_mass_measurable ν δ r TD).comp measurable_fst)
  have hia : (∫⁻ p, a p ∂ξ) ≤ (∑ i, (TP i)⁻¹*CP i)*M :=
    (lintegral_mono' hξ le_rfl).trans (gaussian_point_pruning_incidence_cost μ δ r TP CP hTP M hpoint)
  have hib : (∫⁻ p, b p ∂ξ) ≤ (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (TD i)⁻¹*CD i) :=
    (lintegral_mono' hξ le_rfl).trans (gaussian_direction_pruning_incidence_cost μ ν hδ r TD CD hTD hdir)
  have hic : (∫⁻ p, c p ∂ξ) ≤ (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*B) := by
    apply (lintegral_mono' hξ le_rfl).trans
    simpa only [c,mul_ite,mul_zero] using gaussian_mass_pruning_incidence_cost μ ν hδ hM hMtop hmoment
  calc
    _ ≤ ∫⁻ p, f p+a p+b p+c p ∂ξ :=
      lintegral_mono (fun p => gaussian_pruning_pointwise_loss μ ν δ r TP TD M E hE p)
    _ = ((∫⁻ p, f p ∂ξ)+(∫⁻ p, a p ∂ξ))+(∫⁻ p, b p ∂ξ)+(∫⁻ p, c p ∂ξ) := by
      rw [lintegral_add_left (show Measurable (fun p => f p+a p+b p) from (hf.add ha).add hb),
        lintegral_add_left (show Measurable (fun p => f p+a p) from hf.add ha),lintegral_add_left hf]
    _ ≤ _ := add_le_add (add_le_add (add_le_add le_rfl hia) hib) hic

end Falconer

end OAI

end ExtensionScope23

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianSlabBox. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope24



namespace OAI

/-! # Positive Gaussian mass in a bounded coordinate slab -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ}

theorem gaussian_lower_volume_bounded (S : Set (Space n)) (hS : MeasurableSet S)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x ∈ S, ‖x‖ ≤ B) :
    ENNReal.ofReal (gaussianVolumeNormalization n*Real.exp (-(1/2:ℝ)*B^2))*volume S ≤
      stdGaussian (Space n) S := by
  rw [← normalizedGaussianLebesgue_eq_standard,normalizedGaussianLebesgue,
    Measure.smul_apply,smul_eq_mul,gaussianLebesgue,withDensity_apply _ hS,
    ENNReal.ofReal_mul (by unfold gaussianVolumeNormalization; positivity)]
  rw [mul_assoc]
  apply mul_le_mul_right
  rw [← setLIntegral_const]
  apply setLIntegral_mono' hS
  intro x hx
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hh := hbound x hx
  nlinarith [norm_nonneg x]

def coordinateSlabBox (c : Space (n+1)) (r ρ : ℝ) : Set (Space (n+1)) :=
  {x | |x 0| ≤ r ∧ ∀ i : Fin n, |x i.succ-c i.succ| ≤ ρ}

theorem coordinateSlabBox_measurable (c : Space (n+1)) (r ρ : ℝ) :
    MeasurableSet (coordinateSlabBox c r ρ) := by
  simp only [coordinateSlabBox,ofPred_and,ofPred_forall]
  exact (measurableSet_le (by fun_prop) measurable_const).inter
    (MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const))

theorem coordinateSlabBox_volume (c : Space (n+1)) {r ρ : ℝ}
    (hr : 0 ≤ r) (hρ : 0 ≤ ρ) :
    volume (coordinateSlabBox c r ρ) = ENNReal.ofReal ((2*r)*(2*ρ)^n) := by
  rw [← (PiLp.volume_preserving_toLp (Fin (n+1))).measure_preimage
    (coordinateSlabBox_measurable c r ρ).nullMeasurableSet]
  have he : (@WithLp.toLp 2 (Fin (n+1) → ℝ)) ⁻¹' coordinateSlabBox c r ρ =
      Set.pi univ (Fin.cases (Icc (-r) r)
        (fun i : Fin n => Icc (c i.succ-ρ) (c i.succ+ρ))) := by
    ext x
    simp only [mem_preimage,coordinateSlabBox,mem_ofPred_eq,mem_pi,mem_univ,true_implies,
      Fin.forall_fin_succ,Fin.cases_zero,Fin.cases_succ,mem_Icc,abs_le]
    constructor
    · rintro ⟨hx,ht⟩
      exact ⟨hx,fun i => by have hh := ht i; constructor <;> linarith [hh.1,hh.2]⟩
    · rintro ⟨hx,ht⟩
      exact ⟨hx,fun i => by have hh := ht i; constructor <;> linarith [hh.1,hh.2]⟩
  rw [he,volume_pi_pi,Fin.prod_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Real.volume_Icc,sub_neg_eq_add,
    ← two_mul,show ∀ a : ℝ, a+ρ-(a-ρ) = 2*ρ by intro a; ring,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*ρ),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*r)]

theorem coordinateSlabBox_distance (c : Space (n+1)) {r ρ : ℝ}
    (hrρ : r ≤ ρ) (hc : |c 0| ≤ ρ) {x : Space (n+1)}
    (hx : x ∈ coordinateSlabBox c r ρ) : ‖x-c‖ ≤ (n+1:ℝ)*(2*ρ) := by
  rw [show (n+1:ℝ) = ((n+1:ℕ):ℝ) by norm_cast]
  apply coordinate_norm_le_card_mul
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change |x 0-c 0| ≤ 2*ρ
    calc
      _ ≤ |x 0|+|c 0| := abs_sub _ _
      _ ≤ 2*ρ := by linarith [hx.1]
  · change |x j.succ-c j.succ| ≤ 2*ρ
    have hnonneg : 0 ≤ ρ := (abs_nonneg _).trans hc
    exact (hx.2 j).trans (by linarith)

end Falconer

end OAI

end ExtensionScope24

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianLocalBand. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope25



namespace OAI

/-! # Band mass inside a fixed neighborhood of a transverse row -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ}

noncomputable def gaussianLocalBandConstant (n : ℕ) (ρ : ℝ) : ℝ :=
  gaussianVolumeNormalization (n+1)*
    Real.exp (-(1/2:ℝ)*(1+(n+1:ℝ)*(2*ρ))^2)*2*(2*ρ)^n

theorem gaussianLocalBandConstant_pos {ρ : ℝ} (hρ : 0 < ρ) :
    0 < gaussianLocalBandConstant n ρ := by
  unfold gaussianLocalBandConstant gaussianVolumeNormalization
  positivity

theorem gaussian_local_band_lower {w b : Space (n+1)}
    (hw : ‖w‖ = 1) (hb : ‖b‖ ≤ 1) {r ρ : ℝ}
    (hr : 0 ≤ r) (hrρ : r ≤ ρ) (hρ : 0 ≤ ρ)
    (hwb : |inner ℝ w b| ≤ ρ) :
    ENNReal.ofReal (gaussianLocalBandConstant n ρ*r) ≤
      stdGaussian (Space (n+1))
        {x | ‖x-b‖ ≤ (n+1:ℝ)*(2*ρ) ∧ |inner ℝ w x| ≤ r} := by
  let u : Space (n+1) := EuclideanSpace.basisFun (Fin (n+1)) ℝ 0
  let e : Space (n+1) ≃ₗᵢ[ℝ] Space (n+1) := (ℝ ∙ (u-w))ᗮ.reflection
  have he : e u = w := Submodule.reflection_sub
    (((EuclideanSpace.basisFun (Fin (n+1)) ℝ).norm_eq_one 0).trans hw.symm)
  let c := e.symm b
  have hc : |c 0| ≤ ρ := by
    have hi : c 0 = inner ℝ w b := by
      rw [← he,← e.apply_symm_apply b,e.inner_map_map]
      exact (EuclideanSpace.basisFun_inner (Fin (n+1)) ℝ _ 0).symm
    rwa [hi]
  have hn (x : Space (n+1)) (hx : x ∈ coordinateSlabBox c r ρ) :
      ‖x‖ ≤ 1+(n+1:ℝ)*(2*ρ) := by
    calc
      _ ≤ ‖x-c‖+‖c‖ := by simpa only [sub_add_cancel] using norm_add_le (x-c) c
      _ ≤ (n+1:ℝ)*(2*ρ)+1 := add_le_add (coordinateSlabBox_distance c hrρ hc hx)
        (by simpa only [c,e.symm.norm_map] using hb)
      _ = _ := by ring
  have hl := gaussian_lower_volume_bounded (coordinateSlabBox c r ρ)
    (coordinateSlabBox_measurable c r ρ) (by positivity) hn
  rw [coordinateSlabBox_volume c hr hρ,← ENNReal.ofReal_mul
    (by unfold gaussianVolumeNormalization; positivity)] at hl
  have hl' : ENNReal.ofReal (gaussianLocalBandConstant n ρ*r) ≤
      stdGaussian (Space (n+1)) (coordinateSlabBox c r ρ) := by
    convert hl using 1
    unfold gaussianLocalBandConstant
    congr 1
    ring
  let T : Set (Space (n+1)) :=
    {x | ‖x-b‖ ≤ (n+1:ℝ)*(2*ρ) ∧ |inner ℝ w x| ≤ r}
  have hT : MeasurableSet T := by
    simp only [T,ofPred_and]
    apply MeasurableSet.inter
    · exact measurableSet_le (by fun_prop) measurable_const
    · exact measurableSet_le (by fun_prop) measurable_const
  have hs : coordinateSlabBox c r ρ ⊆ e ⁻¹' T := by
    intro x hx
    constructor
    · rw [← e.apply_symm_apply b,← e.map_sub,e.norm_map]
      exact coordinateSlabBox_distance c hrρ hc hx
    · rw [← he,e.inner_map_map]
      simpa only [u,EuclideanSpace.basisFun_inner] using hx.1
  calc
    _ ≤ stdGaussian (Space (n+1)) (coordinateSlabBox c r ρ) := hl'
    _ ≤ stdGaussian (Space (n+1)) (e ⁻¹' T) := measure_mono hs
    _ = stdGaussian (Space (n+1)) T := by
      rw [← Measure.map_apply e.continuous.measurable hT,stdGaussian_map]

end Falconer

end OAI

end ExtensionScope25

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianKernelGeometry. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope26



namespace OAI

/-! # Passing from Gaussian row bands to their actual kernel planes -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem linearMap_orthogonal_kernel_projection (L : Space d →L[ℝ] Space h) (x : Space d) :
    L (L.kerᗮ.starProjection x) = L x := by
  rw [Submodule.starProjection_orthogonal_val,map_sub]
  have hz : L (L.ker.starProjection x) = 0 := (L.ker.orthogonalProjectionOnto x).property
  rw [hz,sub_zero]

theorem linearMap_kernel_projection_bound (L : Space d →L[ℝ] Space h) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : Space d, ‖L.kerᗮ.starProjection x‖ ≤ K*‖L x‖ := by
  let F : L.kerᗮ →L[ℝ] Space h := L.comp L.kerᗮ.subtypeL
  have hf : LinearMap.ker F.toLinearMap = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hmem : (x:Space d) ∈ L.ker := hx
    have hz : (x:Space d) = 0 := inner_self_eq_zero.mp
      (L.ker.inner_right_of_mem_orthogonal hmem x.property)
    exact Subtype.ext hz
  obtain ⟨K,hK,hLip⟩ := F.toLinearMap.exists_antilipschitzWith hf
  refine ⟨K,by exact_mod_cast hK,?_⟩
  intro x
  have hh := (antilipschitzWith_iff_le_mul_dist.mp hLip) (L.kerᗮ.orthogonalProjectionOnto x) 0
  change dist (L.kerᗮ.orthogonalProjectionOnto x) 0 ≤
    (K:ℝ)*dist (L (L.kerᗮ.starProjection x)) (L 0) at hh
  simp only [dist_zero_right,map_zero] at hh
  change ‖L.kerᗮ.starProjection x‖ ≤ (K:ℝ)*‖L (L.kerᗮ.starProjection x)‖ at hh
  rwa [linearMap_orthogonal_kernel_projection] at hh

theorem gaussian_direction_band_kernel_distance (A : Fin h → Space d)
    {K r : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    {w : Sphere d} (hw : w ∈ gaussianDirectionBand A r) :
    ‖(gaussianRowMap A).kerᗮ.starProjection (w:Space d)‖ ≤ K*((h:ℝ)*r) := by
  exact (hbound w).trans (mul_le_mul_of_nonneg_left (gaussianRowMap_norm_le_of_bands A w hw) hK)

theorem gaussian_point_band_kernel_difference (A : Fin h → Space d) (z : Space h)
    {K r : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    {x y : Space d} (hx : x ∈ gaussianPointBand A z r) (hy : y ∈ gaussianPointBand A z r) :
    ‖(gaussianRowMap A).kerᗮ.starProjection (x-y)‖ ≤ K*((h:ℝ)*(2*r)) :=
  (hbound (x-y)).trans (mul_le_mul_of_nonneg_left
    (gaussianRowMap_norm_le_of_bands A (x-y) (gaussianPointBand_pair_difference A z hx hy)) hK)

end Falconer

end OAI

end ExtensionScope26

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianRowStability. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope27


namespace OAI

/-! # Quantitative kernel geometry near a fixed orthonormal row frame -/

namespace Falconer
open Set MeasureTheory
variable {d h : ℕ}

theorem gaussianRowMap_adjoint_apply (A : Fin h → Space d) (a : Space h) :
    (gaussianRowMap A).adjoint a = ∑ i, a i • A i := by
  calc
    _ = (gaussianRowMap A).adjoint
        (∑ i, a i • EuclideanSpace.basisFun (Fin h) ℝ i) := by
      congr 1
      exact (EuclideanSpace.basisFun (Fin h) ℝ).sum_repr a |>.symm
    _ = _ := by simp only [map_sum,map_smul,gaussianRowMap_adjoint_basis]

theorem row_adjoint_near_isometry (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (a : Space h) :
    ‖(gaussianRowMap A).adjoint a-e a‖ ≤ (h:ℝ)*ε*‖a‖ := by
  have he : e a = ∑ i, a i • e (EuclideanSpace.basisFun (Fin h) ℝ i) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin h) ℝ).sum_repr a]
    simp only [map_sum,map_smul]
    rfl
  rw [gaussianRowMap_adjoint_apply,he,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin h, ‖a i • A i-a i • e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : Fin h, ‖a‖*ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [← smul_sub,norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le a i) (hA i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem row_adjoint_lower_near_isometry (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hε : (h:ℝ)*ε ≤ 1/2) (a : Space h) :
    ‖a‖ ≤ 2*‖(gaussianRowMap A).adjoint a‖ := by
  have h1 := row_adjoint_near_isometry A e hA a
  have h2 := norm_sub_norm_le (e a) ((gaussianRowMap A).adjoint a)
  rw [e.norm_map,norm_sub_rev] at h2
  have h3 := mul_le_mul_of_nonneg_right hε (norm_nonneg a)
  nlinarith

theorem kernel_projection_bound_of_adjoint_lower (L : Space d →L[ℝ] Space h)
    {K : ℝ} (hK : 0 ≤ K) (hL : ∀ a : Space h, ‖a‖ ≤ K*‖L.adjoint a‖)
    (x : Space d) : ‖L.kerᗮ.starProjection x‖ ≤ K*‖L x‖ := by
  let y := L.kerᗮ.starProjection x
  have hy : y ∈ L.kerᗮ := L.kerᗮ.starProjection_apply_mem x
  have hr : y ∈ L.adjoint.range := by
    rw [← ContinuousLinearMap.adjoint_toLinearMap,← LinearMap.orthogonal_ker]
    exact hy
  obtain ⟨a,ha⟩ := hr
  change L.adjoint a = y at ha
  have hnorm : ‖y‖^2 ≤ ‖a‖*‖L x‖ := by
    calc
      _ = inner ℝ y y := (real_inner_self_eq_norm_sq y).symm
      _ = inner ℝ (L.adjoint a) y := by rw [ha]
      _ = inner ℝ a (L y) := ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = inner ℝ a (L x) := congrArg (inner ℝ a)
        (linearMap_orthogonal_kernel_projection L x)
      _ ≤ _ := real_inner_le_norm _ _
  have hla := hL a
  rw [ha] at hla
  have hh := mul_le_mul_of_nonneg_right hla (norm_nonneg (L x))
  by_cases hz : ‖y‖ = 0
  · change ‖y‖ ≤ _
    rw [hz]
    exact mul_nonneg hK (norm_nonneg _)
  · have hp : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖y‖ ≤ _
    nlinarith

theorem row_kernel_projection_bound (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hε : (h:ℝ)*ε ≤ 1/2) (x : Space d) :
    ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖ :=
  kernel_projection_bound_of_adjoint_lower _ (by norm_num)
    (row_adjoint_lower_near_isometry A e hA hε) x

end Falconer

end OAI

end ExtensionScope27

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianRowDimension. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope28


namespace OAI

/-! # The dimension of kernel slices in the controlled row chart -/

namespace Falconer
variable {d h : ℕ}

theorem adjoint_injective_of_lower (L : Space d →L[ℝ] Space h)
    {K : ℝ} (hL : ∀ a : Space h, ‖a‖ ≤ K*‖L.adjoint a‖) :
    Function.Injective L.adjoint := by
  apply LinearMap.ker_eq_bot.mp
  apply (LinearMap.ker_eq_bot').mpr
  intro a ha
  change L.adjoint a = 0 at ha
  have hn := hL a
  rw [ha,norm_zero,mul_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

theorem kernel_finrank_of_adjoint_lower (L : Space d →L[ℝ] Space h)
    {K : ℝ} (hL : ∀ a : Space h, ‖a‖ ≤ K*‖L.adjoint a‖) :
    Module.finrank ℝ L.ker = d-h := by
  have hr := LinearMap.finrank_range_of_inj (adjoint_injective_of_lower L hL)
  have ha := LinearMap.finrank_range_adjoint L.toLinearMap
  rw [ContinuousLinearMap.adjoint_toLinearMap] at ha
  have hn := L.toLinearMap.finrank_range_add_finrank_ker
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hr hn
  omega

theorem row_kernel_finrank (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hε : (h:ℝ)*ε ≤ 1/2) :
    Module.finrank ℝ (gaussianRowMap A).ker = d-h :=
  kernel_finrank_of_adjoint_lower _ (row_adjoint_lower_near_isometry A e hA hε)

end Falconer

end OAI

end ExtensionScope28

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianControlledRows. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope29




namespace OAI

/-! # Positive band mass on uniformly controlled Gaussian row parameters -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

def gaussianRowNeighborhood (B : Fin h → Space (n+1)) (ε : ℝ) :
    Set (Fin h → Space (n+1)) := {A | ∀ i, ‖A i-B i‖ ≤ ε}

theorem gaussianRowNeighborhood_measurable (B : Fin h → Space (n+1)) (ε : ℝ) :
    MeasurableSet (gaussianRowNeighborhood B ε) := by
  simp only [gaussianRowNeighborhood,ofPred_forall]
  exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)

theorem gaussianRows_controlled_band_lower (B : Fin h → Space (n+1))
    (hB : ∀ i, ‖B i‖ ≤ 1) {w : Space (n+1)} (hw : ‖w‖ = 1)
    {r ρ : ℝ} (hr : 0 ≤ r) (hrρ : r ≤ ρ) (hρ : 0 ≤ ρ)
    (hwB : ∀ i, |inner ℝ w (B i)| ≤ ρ) :
    ENNReal.ofReal ((gaussianLocalBandConstant n ρ*r)^h) ≤
      gaussianRows (n+1) h ({A | ∀ i, |inner ℝ w (A i)| ≤ r} ∩
        gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))) := by
  have he : {A : Fin h → Space (n+1) | ∀ i, |inner ℝ w (A i)| ≤ r} ∩
      gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)) =
      Set.pi univ (fun i => {x | ‖x-B i‖ ≤ (n+1:ℝ)*(2*ρ) ∧ |inner ℝ w x| ≤ r}) := by
    ext A
    simp only [mem_inter_iff,mem_ofPred_eq,gaussianRowNeighborhood,mem_pi,mem_univ,true_implies]
    constructor
    · rintro ⟨ha,hb⟩ i
      exact ⟨hb i,ha i⟩
    · intro ha
      exact ⟨fun i => (ha i).2,fun i => (ha i).1⟩
  rw [he,gaussianRows,Measure.pi_pi]
  calc
    _ = ∏ _ : Fin h, ENNReal.ofReal (gaussianLocalBandConstant n ρ*r) := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow]
      unfold gaussianLocalBandConstant gaussianVolumeNormalization
      positivity
    _ ≤ _ := Finset.prod_le_prod (fun i _ => gaussian_local_band_lower hw (hB i) hr hrρ hρ (hwB i))

theorem direction_band_first_moment {d : ℕ}
    (γ : Measure (Fin h → Space d)) [SFinite γ]
    (ν : Measure (Sphere d)) [SFinite ν] (r : ℝ) :
    (∫⁻ A : Fin h → Space d, ν (gaussianDirectionBand A r) ∂γ) =
      ∫⁻ w : Sphere d, γ {A | ∀ i, |inner ℝ (w:Space d) (A i)| ≤ r} ∂ν := by
  let S : Set ((Fin h → Space d) × Sphere d) :=
    {p | ∀ i, |inner ℝ (p.2:Space d) (p.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall]
    exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  exact (Measure.prod_apply hS).symm.trans (Measure.prod_apply_symm hS)

theorem gaussian_controlled_direction_mean_lower (B : Fin h → Space (n+1))
    (hB : ∀ i, ‖B i‖ ≤ 1) (ν : Measure (Sphere (n+1))) [SFinite ν]
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρ : 0 ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ) :
    ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*ν univ ≤
      ∫⁻ A : Fin h → Space (n+1), gaussianDirectionMass ν r A
        ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))) := by
  simp only [gaussianDirectionMass]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,direction_band_first_moment]
  have hl : ENNReal.ofReal ((gaussianLocalBandConstant n ρ*r)^h)*ν univ ≤
      ∫⁻ w : Sphere (n+1), ((gaussianRows (n+1) h).restrict
        (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))))
        {A | ∀ i, |inner ℝ (w:Space (n+1)) (A i)| ≤ r} ∂ν := by
    rw [← lintegral_const]
    apply lintegral_mono_ae
    filter_upwards [hwB] with w hw
    rw [Measure.restrict_apply]
    · exact gaussianRows_controlled_band_lower B hB (sphere_norm w) hr.le hrρ hρ hw
    · simp only [ofPred_forall]
      exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  calc
    _ = ENNReal.ofReal (r^(-(h:ℝ)))*
        (ENNReal.ofReal ((gaussianLocalBandConstant n ρ*r)^h)*ν univ) := by
      rw [← mul_assoc,gaussian_band_normalization hr]
      unfold gaussianLocalBandConstant gaussianVolumeNormalization
      positivity
    _ ≤ _ := mul_le_mul_right hl _

end Falconer

end OAI

end ExtensionScope29

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianControlledIncidence. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope30



namespace OAI

/-! # Original-label incidence on the uniformly controlled row chart -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem incidence_direction_ae (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space (n+1) × Sphere (n+1))) {P : Sphere (n+1) → Prop}
    (hP : ∀ᵐ w ∂ν, P w) :
    ∀ᵐ w ∂(((μ.prod ν).restrict E).map Prod.snd), P w := by
  have hd : ((μ.prod ν).restrict E).map Prod.snd ≤ (μ univ) • ν := by
    calc
      _ ≤ (μ.prod ν).map Prod.snd := Measure.map_mono Measure.restrict_le_self measurable_snd
      _ = _ := Measure.map_snd_prod
  exact (Measure.absolutelyContinuous_of_le hd).ae_le (Measure.ae_smul_measure hP _)

theorem gaussian_controlled_incidence_mean_lower (B : Fin h → Space (n+1))
    (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρ : 0 ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ) :
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E ≤
      ∫⁻ A : Fin h → Space (n+1), (∫⁻ z : Space h,
        (gaussianPointSliceMeasure μ A z r).prod (gaussianDirectionSliceMeasure ν A r) E)
        ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))) := by
  simp_rw [gaussian_slice_incidence_point_average μ ν E hE _ hr]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hh := gaussian_controlled_direction_mean_lower B hB
    (((μ.prod ν).restrict E).map Prod.snd) hr hrρ hρ (incidence_direction_ae μ ν E hwB)
  rw [Measure.map_apply measurable_snd MeasurableSet.univ,preimage_univ,
    Measure.restrict_apply_univ] at hh
  simpa only [mul_assoc] using mul_le_mul_right hh (ENNReal.ofReal ((2:ℝ)^h))

theorem controlled_row_kernel_geometry (e : Space h →ₗᵢ[ℝ] Space (n+1))
    {A : Fin h → Space (n+1)} {ρ : ℝ}
    (hρ : (h:ℝ)*((n+1:ℝ)*(2*ρ)) ≤ 1/2)
    (hA : A ∈ gaussianRowNeighborhood (fun i => e (EuclideanSpace.basisFun (Fin h) ℝ i))
      ((n+1:ℝ)*(2*ρ))) :
    Module.finrank ℝ (gaussianRowMap A).ker = n+1-h ∧
      ∀ x : Space (n+1), ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖ :=
  ⟨row_kernel_finrank A e hA hρ, row_kernel_projection_bound A e hA hρ⟩

end Falconer

end OAI

end ExtensionScope30

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianControlledLedger. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope31



namespace OAI

/-! # Original incidence survives controlled-row marginal pruning -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_controlled_pruning_ledger
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ)
    (r : ι → ℝ) (TP TD CP CD : ι → ℝ≥0∞)
    (hTP : ∀ i, 0 < TP i) (hTD : ∀ i, 0 < TD i)
    {M Q : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hpoint : ∀ i, (∫⁻ p : (Fin h → Space (n+1)) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows (n+1) h).prod volume) ≤ CP i)
    (hdir : ∀ i, (∫⁻ A : Fin h → Space (n+1),
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows (n+1) h) ≤ CD i)
    (hmoment : (∫⁻ A : Fin h → Space (n+1), (gaussianDirectionMass ν δ A)^2
      ∂gaussianRows (n+1) h) ≤ Q)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E) :
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E ≤
      (∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p
        ∂((gaussianRows (n+1) h).restrict
          (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)))).prod volume) +
      (∑ i, (TP i)⁻¹*CP i)*M +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (TD i)⁻¹*CD i) +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*Q) := by
  let G := gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))
  let ξ := ((gaussianRows (n+1) h).restrict G).prod (volume : Measure (Space h))
  have hlo := gaussian_controlled_incidence_mean_lower B hB μ ν E hE hδ hδρ
    (hδ.le.trans hδρ) hwB
  have hraw : Measurable (fun p : (Fin h → Space (n+1)) × Space h =>
      (gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianDirectionSliceMeasure ν p.1 δ) E) :=
    gaussian_pair_restriction_mass_measurable μ ν δ (Prod.snd ⁻¹' E) (hE.preimage measurable_snd)
  rw [← lintegral_prod _ (show AEMeasurable
    (fun p : (Fin h → Space (n+1)) × Space h =>
      (gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianDirectionSliceMeasure ν p.1 δ) E) ξ
      from hraw.aemeasurable)] at hlo
  exact hlo.trans (gaussian_pruning_integral_loss μ ν ξ
    (Measure.prod_mono Measure.restrict_le_self le_rfl) hδ r TP TD CP CD hTP hTD hM hMtop
    hpoint hdir hmoment E hE)

end Falconer

end OAI

end ExtensionScope31

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianParameterSupport. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope32




namespace OAI

/-! # A bounded point-parameter region for bounded original source laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianRowNeighborhood_norm {n : ℕ} (B : Fin h → Space (n+1))
    (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} {A : Fin h → Space (n+1)}
    (hA : A ∈ gaussianRowNeighborhood B ε) (i : Fin h) : ‖A i‖ ≤ ε+1 := by
  calc
    _ ≤ ‖A i-B i‖+‖B i‖ := by simpa only [sub_add_cancel] using norm_add_le (A i-B i) (B i)
    _ ≤ _ := add_le_add (hA i) (hB i)

theorem gaussianPointBand_parameter_bound (A : Fin h → Space d)
    {M D r : ℝ} (_hM : 0 ≤ M) (hA : ∀ i, ‖A i‖ ≤ M)
    {x : Space d} (hx : ‖x‖ ≤ D) {z : Space h} (hz : x ∈ gaussianPointBand A z r) :
    z ∈ coordinateBox h (D*M+r) := by
  intro i
  calc
    |z i| ≤ |inner ℝ x (A i)|+|inner ℝ x (A i)-z i| := by
      calc
        _ = |inner ℝ x (A i)-(inner ℝ x (A i)-z i)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    _ ≤ ‖x‖*‖A i‖+r := add_le_add (abs_real_inner_le_norm _ _) (hz i)
    _ ≤ D*M+r := add_le_add
      (mul_le_mul hx (hA i) (norm_nonneg _) ((norm_nonneg x).trans hx)) le_rfl

theorem gaussian_point_mass_zero_outside_box
    (μ : Measure (Space d)) (A : Fin h → Space d)
    {M D r : ℝ} (hM : 0 ≤ M) (hA : ∀ i, ‖A i‖ ≤ M)
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) {z : Space h} (hz : z ∉ coordinateBox h (D*M+r)) :
    gaussianPointMass μ r (A,z) = 0 := by
  have hs : gaussianPointBand A z r ⊆ {x | ¬‖x‖ ≤ D} := by
    intro x hx hnorm
    exact hz (gaussianPointBand_parameter_bound A hM hA hnorm hx)
  have he : μ (gaussianPointBand A z r) = 0 := measure_mono_null hs (ae_iff.mp hμ)
  simp only [gaussianPointMass,he,mul_zero]

end Falconer

end OAI

end ExtensionScope32

/- Source: OAI.MeasureTheory.Falconer.Slicing.SliceSelectionMean. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope33


namespace OAI

/-! # Selecting a retained slice from its quantitative mean -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem exists_large_slice_of_mean (μ : Measure X) (S : Set X) (hS : MeasurableSet S)
    (f : X → ℝ≥0∞) (hsupport : ∀ᵐ x ∂μ, x ∉ S → f x = 0) {a : ℝ≥0∞}
    (hmean : a*μ S < ∫⁻ x, f x ∂μ) :
    ∃ x ∈ S, a < f x := by
  by_contra! hn
  have hle : f ≤ᵐ[μ] S.indicator (fun _ => a) := by
    filter_upwards [hsupport] with x hx
    by_cases hxs : x ∈ S
    · simpa only [indicator_of_mem hxs] using hn x hxs
    · simp only [hx hxs,indicator_of_notMem hxs,le_refl]
  have hi := lintegral_mono_ae hle
  rw [lintegral_indicator_const hS] at hi
  exact (not_le_of_gt hmean) hi

end Falconer

end OAI

end ExtensionScope33

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianSelectPruned. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope34




namespace OAI

/-! # Quantitative selection of a retained slice in the controlled row chart -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ} {ι : Type*}

theorem gaussian_pruned_incidence_zero_of_point_mass
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space (n+1) × Sphere (n+1)))
    (p : (Fin h → Space (n+1)) × Space h) (hp : gaussianPointMass μ δ p = 0) :
    gaussianPrunedIncidence μ ν δ r TP TD M E p = 0 := by
  have hz : gaussianPointSliceMeasure μ p.1 p.2 δ = 0 :=
    Measure.measure_univ_eq_zero.mp (by rw [gaussianPointSliceMeasure_univ]; exact hp)
  simp only [gaussianPrunedIncidence,hz,Measure.restrict_zero,Measure.zero_prod,Measure.coe_zero,Pi.zero_apply]

theorem gaussian_pruned_parameter_support
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space (n+1) × Sphere (n+1))) :
    ∀ᵐ p ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume,
      p ∉ (gaussianRowNeighborhood B ε) ×ˢ (coordinateBox h (D*(ε+1)+δ)) →
      gaussianPrunedIncidence μ ν δ r TP TD M E p = 0 := by
  have ha : ∀ᵐ p : (Fin h → Space (n+1)) × Space h
      ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume,
      p.1 ∈ gaussianRowNeighborhood B ε :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (gaussianRowNeighborhood_measurable B ε))
  filter_upwards [ha] with p hp hnot
  have hz : p.2 ∉ coordinateBox h (D*(ε+1)+δ) := fun hz => hnot ⟨hp,hz⟩
  apply gaussian_pruned_incidence_zero_of_point_mass μ ν δ r TP TD M E p
  exact gaussian_point_mass_zero_outside_box μ p.1 (by linarith)
    (gaussianRowNeighborhood_norm B hB hp) hμ hz

theorem gaussian_select_pruned_slice
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space (n+1) × Sphere (n+1))) {a : ℝ≥0∞}
    (hmean : a*volume (coordinateBox h (D*(ε+1)+δ)) <
      ∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p
        ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume) :
    ∃ A ∈ gaussianRowNeighborhood B ε, ∃ z ∈ coordinateBox h (D*(ε+1)+δ),
      a < gaussianPrunedIncidence μ ν δ r TP TD M E (A,z) := by
  let G := gaussianRowNeighborhood B ε
  let Z := coordinateBox h (D*(ε+1)+δ)
  let ξ := ((gaussianRows (n+1) h).restrict G).prod (volume : Measure (Space h))
  have hmass : ξ (G ×ˢ Z) ≤ volume Z := by
    rw [Measure.prod_prod]
    have hg : ((gaussianRows (n+1) h).restrict G) G ≤ 1 := by
      calc
        _ ≤ gaussianRows (n+1) h G := Measure.restrict_le_self _
        _ ≤ gaussianRows (n+1) h univ := measure_mono (subset_univ _)
        _ = 1 := measure_univ
    simpa only [one_mul] using mul_le_mul_left hg (volume Z)
  have hgt : a*ξ (G ×ˢ Z) < ∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p ∂ξ :=
    (mul_le_mul_right hmass a).trans_lt hmean
  obtain ⟨⟨A,z⟩,hAz,hi⟩ := exists_large_slice_of_mean ξ (G ×ˢ Z)
    ((gaussianRowNeighborhood_measurable B ε).prod (coordinateBox_measurable _)) _
    (gaussian_pruned_parameter_support B hB hε μ ν hμ δ r TP TD M E) hgt
  exact ⟨A,hAz.1,z,hAz.2,hi⟩

end Falconer

end OAI

end ExtensionScope34

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedPair. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope35


namespace OAI

/-! # Measurable parameter-dependent incidence on the retained original laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

noncomputable def gaussianPrunedPairMass
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) (δ : ℝ)
    (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (G : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)))
    (p : (Fin h → Space d) × Space h) : ℝ≥0∞ :=
  gaussianPrunedIncidence μ ν δ r TP TD M {t | (p,t) ∈ G} p

theorem gaussianPrunedPairMass_measurable
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (G : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d))) (hG : MeasurableSet G) :
    Measurable (gaussianPrunedPairMass μ ν δ r TP TD M G) := by
  let F : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)) :=
    {q | q ∈ G ∧ q.2.1 ∈ gaussianPointGood μ δ r TP q.1 ∧
      q.2.2 ∈ gaussianDirectionGood ν δ r TD M q.1.1}
  have hF : MeasurableSet F := by
    have hp := (gaussianPointGood_measurable_joint (h := h) μ δ r TP).preimage
      (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
        (q.1,q.2.1)) from by fun_prop)
    have hd := (gaussianDirectionGood_measurable_joint (h := h) ν δ r TD M).preimage
      (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
        (q.1.1,q.2.2)) from by fun_prop)
    exact hG.inter (hp.inter hd)
  convert gaussian_pair_restriction_mass_measurable μ ν δ F hF using 1
  ext p
  rw [gaussianPrunedPairMass,gaussianPrunedIncidence,Measure.prod_restrict,
    Measure.restrict_apply (show MeasurableSet {t | (p,t) ∈ G} from
      hG.preimage measurable_prodMk_left)]
  congr 1

omit [Fintype ι] in
theorem gaussianPrunedPairMass_parameter_support {n : ℕ}
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (G : Set (((Fin h → Space (n+1)) × Space h) × (Space (n+1) × Sphere (n+1)))) :
    ∀ᵐ p ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume,
      p ∉ (gaussianRowNeighborhood B ε) ×ˢ (coordinateBox h (D*(ε+1)+δ)) →
      gaussianPrunedPairMass μ ν δ r TP TD M G p = 0 := by
  have ha : ∀ᵐ p : (Fin h → Space (n+1)) × Space h
      ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume,
      p.1 ∈ gaussianRowNeighborhood B ε :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (gaussianRowNeighborhood_measurable B ε))
  filter_upwards [ha] with p hp hnot
  apply gaussian_pruned_incidence_zero_of_point_mass μ ν δ r TP TD M _ p
  apply gaussian_point_mass_zero_outside_box μ p.1 (by linarith)
    (gaussianRowNeighborhood_norm B hB hp) hμ
  exact fun hz => hnot ⟨hp,hz⟩

omit [Fintype ι] in
theorem gaussian_select_pruned_pair {n : ℕ}
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (G : Set (((Fin h → Space (n+1)) × Space h) × (Space (n+1) × Sphere (n+1))))
    {a : ℝ≥0∞}
    (hmean : a*volume (coordinateBox h (D*(ε+1)+δ)) <
      ∫⁻ p, gaussianPrunedPairMass μ ν δ r TP TD M G p
        ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume) :
    ∃ A ∈ gaussianRowNeighborhood B ε, ∃ z ∈ coordinateBox h (D*(ε+1)+δ),
      a < gaussianPrunedPairMass μ ν δ r TP TD M G (A,z) := by
  let U := gaussianRowNeighborhood B ε
  let Z := coordinateBox h (D*(ε+1)+δ)
  let ξ := ((gaussianRows (n+1) h).restrict U).prod (volume : Measure (Space h))
  have hmass : ξ (U ×ˢ Z) ≤ volume Z := by
    rw [Measure.prod_prod]
    have hg : ((gaussianRows (n+1) h).restrict U) U ≤ 1 := by
      calc
        _ ≤ gaussianRows (n+1) h U := Measure.restrict_le_self _
        _ ≤ gaussianRows (n+1) h univ := measure_mono (subset_univ _)
        _ = 1 := measure_univ
    simpa only [one_mul] using mul_le_mul_left hg (volume Z)
  have hgt : a*ξ (U ×ˢ Z) < ∫⁻ p, gaussianPrunedPairMass μ ν δ r TP TD M G p ∂ξ :=
    (mul_le_mul_right hmass a).trans_lt hmean
  obtain ⟨⟨A,z⟩,hAz,hi⟩ := exists_large_slice_of_mean ξ (U ×ˢ Z)
    ((gaussianRowNeighborhood_measurable B ε).prod (coordinateBox_measurable _)) _
    (gaussianPrunedPairMass_parameter_support B hB hε μ ν hμ δ r TP TD M G) hgt
  exact ⟨A,hAz.1,z,hAz.2,hi⟩

end Falconer

end OAI

end ExtensionScope35

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianActiveCount. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope36



namespace OAI

/-! # Active original tube-anchor counts in the Gaussian point parameter -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

noncomputable def gaussianActiveAnchorCount (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) (r : ℝ) (z : Space h) : ℕ := by
  classical
  exact (S.filter (fun i => a i ∈ gaussianPointBand A z r)).card

theorem gaussianActiveAnchorCount_eq_sum (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) (r : ℝ) (z : Space h) :
    (gaussianActiveAnchorCount A S a r z : ℝ≥0∞) =
      ∑ i ∈ S, {v : Space h | a i ∈ gaussianPointBand A v r}.indicator (fun _ => (1:ℝ≥0∞)) z := by
  classical
  simp only [gaussianActiveAnchorCount,Finset.natCast_card_filter,Set.indicator_apply,mem_ofPred_eq]

theorem measurable_gaussianActiveAnchorCount (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) (r : ℝ) :
    Measurable (fun z : Space h => (gaussianActiveAnchorCount A S a r z : ℝ≥0∞)) := by
  simp_rw [gaussianActiveAnchorCount_eq_sum]
  apply Finset.measurable_sum
  intro i _
  apply measurable_const.indicator
  change MeasurableSet {v : Space h | ∀ j, |inner ℝ (a i) (A j)-v j| ≤ r}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)

theorem gaussianActiveAnchorCount_integral (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ z : Space h, (gaussianActiveAnchorCount A S a r z : ℝ≥0∞)) =
      (S.card:ℝ≥0∞)*ENNReal.ofReal ((2*r)^h) := by
  simp_rw [gaussianActiveAnchorCount_eq_sum]
  have hm (i : ι) : MeasurableSet {v : Space h | a i ∈ gaussianPointBand A v r} := by
    change MeasurableSet {v : Space h | ∀ j, |inner ℝ (a i) (A j)-v j| ≤ r}
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  rw [lintegral_finsetSum S (fun i _ => measurable_const.indicator (hm i))]
  simp only [lintegral_indicator_const (hm _),one_mul,gaussianPointBand_parameter_measure A _ hr,
    Finset.sum_const,nsmul_eq_mul]

theorem gaussianActiveAnchorCount_exceptional (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) {r : ℝ} (hr : 0 ≤ r)
    {T : ℝ≥0∞} (hT : T ≠ 0) (hTfin : T ≠ ∞) :
    volume {z : Space h | T < (gaussianActiveAnchorCount A S a r z : ℝ≥0∞)} ≤
      ((S.card:ℝ≥0∞)*ENNReal.ofReal ((2*r)^h))/T := by
  apply (measure_mono (show {z : Space h | T < (gaussianActiveAnchorCount A S a r z : ℝ≥0∞)} ⊆
      {z : Space h | T ≤ (gaussianActiveAnchorCount A S a r z : ℝ≥0∞)} from
    fun _ hz => (show T < _ from hz).le)).trans
  rw [← gaussianActiveAnchorCount_integral A S a hr]
  exact meas_ge_le_lintegral_div (measurable_gaussianActiveAnchorCount A S a r).aemeasurable hT hTfin

end Falconer

end OAI

end ExtensionScope36

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianActiveFamily. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope37


namespace OAI

/-! # Active counts for measurable original-label tube lists -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gaussianActiveFamily_measurable (J : Sphere d → Finset ι)
    (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : ι → Space d) (r : ℝ) :
    Measurable (fun p : ((Fin h → Space d) × Space h) × Sphere d =>
      (gaussianActiveAnchorCount p.1.1 (J p.2) a r p.1.2 : ℝ≥0∞)) := by
  classical
  have he (p : ((Fin h → Space d) × Space h) × Sphere d) :
      (gaussianActiveAnchorCount p.1.1 (J p.2) a r p.1.2 : ℝ≥0∞) =
      ∑ i : ι, {q : ((Fin h → Space d) × Space h) × Sphere d |
        i ∈ J q.2 ∧ a i ∈ gaussianPointBand q.1.1 q.1.2 r}.indicator (fun _ => (1:ℝ≥0∞)) p := by
    rw [gaussianActiveAnchorCount_eq_sum]
    simp only [Set.indicator_apply,mem_ofPred_eq]
    calc
      _ = ∑ i ∈ J p.2, (if i ∈ J p.2 ∧ a i ∈ gaussianPointBand p.1.1 p.1.2 r then
          (1:ℝ≥0∞) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [hi,true_and]
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
        simp only [hi,false_and,ite_false])
  simp_rw [he]
  apply Finset.measurable_sum
  intro i _
  apply measurable_const.indicator
  apply ((hJ i).preimage measurable_snd).inter
  change MeasurableSet {q : ((Fin h → Space d) × Space h) × Sphere d |
    ∀ j, |inner ℝ (a i) (q.1.1 j)-q.1.2 j| ≤ r}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)

omit [Fintype ι] [DecidableEq ι] in
theorem gaussianActiveFamily_exceptional_bound
    (A : Fin h → Space d) (J : Sphere d → Finset ι) (a : ι → Space d)
    {r : ℝ} (hr : 0 ≤ r) {N T : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞) (w : Sphere d) :
    (volume : Measure (Space h)) {z | T < (gaussianActiveAnchorCount A (J w) a r z : ℝ≥0∞)} ≤
      N*ENNReal.ofReal ((2*r)^h)/T := by
  apply (gaussianActiveAnchorCount_exceptional A (J w) a hr hT hTfin).trans
  simp only [div_eq_mul_inv]
  exact mul_le_mul_left (mul_le_mul_left (hN w) _) _

theorem gaussianActiveFamily_slice_count_measurable
    (A : Fin h → Space d) (J : Sphere d → Finset ι)
    (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : ι → Space d) (R : ℝ) :
    Measurable (fun p : Space h × Sphere d =>
      (gaussianActiveAnchorCount A (J p.2) a R p.1 : ℝ≥0∞)) := by
  classical
  have he (p : Space h × Sphere d) :
      (gaussianActiveAnchorCount A (J p.2) a R p.1 : ℝ≥0∞) =
      ∑ i : ι, {q : Space h × Sphere d | i ∈ J q.2 ∧ a i ∈ gaussianPointBand A q.1 R}.indicator
        (fun _ => (1:ℝ≥0∞)) p := by
    rw [gaussianActiveAnchorCount_eq_sum]
    simp only [Set.indicator_apply,mem_ofPred_eq]
    calc
      _ = ∑ i ∈ J p.2, (if i ∈ J p.2 ∧ a i ∈ gaussianPointBand A p.1 R then
          (1:ℝ≥0∞) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [hi,true_and]
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
        simp only [hi,false_and,ite_false])
  simp_rw [he]
  apply Finset.measurable_sum
  intro i _
  apply measurable_const.indicator
  apply ((hJ i).preimage measurable_snd).inter
  change MeasurableSet {q : Space h × Sphere d |
    ∀ j, |inner ℝ (a i) (A j)-q.1 j| ≤ R}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)

theorem gaussianActiveFamily_slice_measurable
    (A : Fin h → Space d) (J : Sphere d → Finset ι)
    (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : ι → Space d) (R : ℝ) (T : ℝ≥0∞) :
    MeasurableSet {p : Space h × Sphere d |
      T < (gaussianActiveAnchorCount A (J p.2) a R p.1 : ℝ≥0∞)} :=
  measurableSet_lt measurable_const (gaussianActiveFamily_slice_count_measurable A J hJ a R)

end Falconer

end OAI

end ExtensionScope37

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedMass. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope38


namespace OAI

/-! # Uniform masses and support of the pruned original slice laws -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussianPointSliceMeasure_ae_of_ae
    (μ : Measure (Space d)) (A : Fin h → Space d) (z : Space h) (δ : ℝ)
    {P : Space d → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂gaussianPointSliceMeasure μ A z δ, P x := by
  exact Measure.ae_smul_measure (ae_restrict_of_ae hP) _

theorem gaussianPointGood_mass
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞)
    (p : (Fin h → Space d) × Space h) {D : ℝ}
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (i : ι) (hi : D < r i) :
    ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r T p)) univ ≤ T i := by
  let α := (gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r T p)
  have ha : ∀ᵐ x ∂α, x ∈ ball 0 (r i) := by
    filter_upwards [ae_restrict_of_ae (gaussianPointSliceMeasure_ae_of_ae μ p.1 p.2 δ hμ)] with x hx
    simpa only [mem_ball,dist_zero_right] using hx.trans_lt hi
  have he : α (ball 0 (r i)) = α univ := measure_congr (by
    filter_upwards [ha] with x hx
    exact propext ⟨fun _ => mem_univ x,fun _ => hx⟩)
  rw [← he]
  exact gaussianPointGood_ball μ δ r T p i 0

theorem gaussian_pruned_incidence_le_masses
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (p : (Fin h → Space d) × Space h) :
    gaussianPrunedIncidence μ ν δ r TP TD M E p ≤
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)) univ *
      ((gaussianDirectionSliceMeasure ν p.1 δ).restrict (gaussianDirectionGood ν δ r TD M p.1)) univ := by
  let α := (gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)
  let β := (gaussianDirectionSliceMeasure ν p.1 δ).restrict (gaussianDirectionGood ν δ r TD M p.1)
  change (α.prod β) E ≤ α univ*β univ
  calc
    _ ≤ (α.prod β) univ := measure_mono (subset_univ _)
    _ = _ := by rw [← univ_prod_univ,Measure.prod_prod]

end Falconer

end OAI

end ExtensionScope38

/- Source: OAI.MeasureTheory.Falconer.Slicing.SliceDirectionDeletion. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope39



namespace OAI

/-! # Incidence cost of direction-dependent exceptional slice parameters -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {Z X W : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace W]

theorem slice_direction_deletion_cost
    (ζ : Measure Z) (α : Z → Measure X) (β : Measure W)
    [SFinite ζ] [SFinite β] [∀ z, SFinite (α z)]
    (D : Set (Z × W)) (hD : MeasurableSet D) (E : Set (X × W))
    {P C : ℝ≥0∞} (hP : ∀ z, α z univ ≤ P)
    (hC : ∀ w, ζ {z | (z,w) ∈ D} ≤ C) :
    (∫⁻ z, ((α z).prod β) (E ∩ (univ ×ˢ {w | (z,w) ∈ D})) ∂ζ) ≤ P*C*β univ := by
  have hm : Measurable (fun z => β {w | (z,w) ∈ D}) := measurable_measure_prodMk_left hD
  calc
    _ ≤ ∫⁻ z, P*β {w | (z,w) ∈ D} ∂ζ := by
      apply lintegral_mono
      intro z
      calc
        _ ≤ ((α z).prod β) (univ ×ˢ {w | (z,w) ∈ D}) := measure_mono inter_subset_right
        _ = α z univ*β {w | (z,w) ∈ D} := by rw [Measure.prod_prod]
        _ ≤ _ := mul_le_mul_left (hP z) _
    _ = P*(ζ.prod β) D := by
      rw [lintegral_const_mul _ hm]
      exact congrArg (fun t => P*t) (Measure.prod_apply hD).symm
    _ ≤ P*(C*β univ) := by
      apply mul_le_mul_right
      rw [Measure.prod_apply_symm hD]
      exact (lintegral_mono hC).trans_eq (lintegral_const _)
    _ = _ := (mul_assoc _ _ _).symm

end Falconer

end OAI

end ExtensionScope39

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianActiveLoss. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope40




namespace OAI

/-! # Cost of deleting excessive active original tube lists -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι κ : Type*} [Fintype κ] [DecidableEq κ]

theorem gaussian_active_loss_in_row
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (A : Fin h → Space d) (E : Set (Space d × Sphere d))
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : κ → Space d)
    {R : ℝ} (hR : 0 ≤ R) {N T P : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (hP : ∀ z, ((gaussianPointSliceMeasure μ A z δ).restrict
      (gaussianPointGood μ δ r TP (A,z))) univ ≤ P) :
    (∫⁻ z : Space h, gaussianPrunedIncidence μ ν δ r TP TD M
      (E ∩ (univ ×ˢ {w | T < (gaussianActiveAnchorCount A (J w) a R z : ℝ≥0∞)})) (A,z)) ≤
      P*(N*ENNReal.ofReal ((2*R)^h)/T)*M := by
  let β := (gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A)
  let α := fun z : Space h => (gaussianPointSliceMeasure μ A z δ).restrict
    (gaussianPointGood μ δ r TP (A,z))
  have : IsFiniteMeasure β := by change IsFiniteMeasure (Measure.restrict _ _); infer_instance
  have : ∀ z, SFinite (α z) := fun z => by change SFinite (Measure.restrict _ _); infer_instance
  let D : Set (Space h × Sphere d) :=
    {p | T < (gaussianActiveAnchorCount A (J p.2) a R p.1 : ℝ≥0∞)}
  have hD : MeasurableSet D := gaussianActiveFamily_slice_measurable A J hJ a R T
  have hc : ∀ w, (volume : Measure (Space h)) {z | (z,w) ∈ D} ≤
      N*ENNReal.ofReal ((2*R)^h)/T :=
    gaussianActiveFamily_exceptional_bound A J a hR hN hT hTfin
  change (∫⁻ z : Space h, ((α z).prod β) (E ∩ (univ ×ˢ {w | (z,w) ∈ D}))) ≤ _
  have hl := slice_direction_deletion_cost (Z := Space h) (X := Space d) (W := Sphere d)
    (volume : Measure (Space h)) α β D hD E hP hc
  exact hl.trans (mul_le_mul_right (gaussianDirectionGood_mass ν δ r TD M A) _)

end Falconer

end OAI

end ExtensionScope40

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianActiveRelation. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope41



namespace OAI

/-! # Original-pair incidence after the active-cover deletion -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

def gaussianActiveRelation (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ)
    (a : κ → Space d) (R : ℝ) (T : ℝ≥0∞) (good : Bool) :
    Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)) :=
  {q | q.2 ∈ E ∧ if good then
      (gaussianActiveAnchorCount q.1.1 (J q.2.2) a R q.1.2 : ℝ≥0∞) ≤ T
    else T < (gaussianActiveAnchorCount q.1.1 (J q.2.2) a R q.1.2 : ℝ≥0∞)}

omit [Fintype ι] in
theorem gaussianActiveRelation_measurable (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space d) (R : ℝ) (T : ℝ≥0∞) (good : Bool) :
    MeasurableSet (gaussianActiveRelation (h := h) E J a R T good) := by
  have hm := (gaussianActiveFamily_measurable (h := h) J hJ a R).comp
    (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
      (q.1,q.2.2)) from by fun_prop)
  cases good
  · exact (hE.preimage measurable_snd).inter (measurableSet_lt measurable_const hm)
  · exact (hE.preimage measurable_snd).inter (measurableSet_le hm measurable_const)

theorem gaussian_active_bad_integral
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : κ → Space d)
    {R : ℝ} (hR : 0 ≤ R) {N T P : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (hP : ∀ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)) univ ≤ P) :
    (∫⁻ p, gaussianPrunedPairMass μ ν δ r TP TD M
      (gaussianActiveRelation E J a R T false) p ∂(gaussianRows d h).prod volume) ≤
      P*(N*ENNReal.ofReal ((2*R)^h)/T)*M := by
  rw [lintegral_prod _ (show AEMeasurable
    (gaussianPrunedPairMass μ ν δ r TP TD M (gaussianActiveRelation E J a R T false))
    ((gaussianRows d h).prod volume) from
    (gaussianPrunedPairMass_measurable μ ν δ r TP TD M _
      (gaussianActiveRelation_measurable E hE J hJ a R T false)).aemeasurable)]
  calc
    _ ≤ ∫⁻ _ : Fin h → Space d, P*(N*ENNReal.ofReal ((2*R)^h)/T)*M ∂gaussianRows d h := by
      apply lintegral_mono
      intro A
      have he (z : Space h) : {t | ((A,z),t) ∈ gaussianActiveRelation E J a R T false} =
          E ∩ (univ ×ˢ {w | T < (gaussianActiveAnchorCount A (J w) a R z : ℝ≥0∞)}) := by
        ext t
        simp [gaussianActiveRelation]
      simp only [gaussianPrunedPairMass,he]
      exact gaussian_active_loss_in_row μ ν δ r TP TD M A E J hJ a hR hN hT hTfin
        (fun z => hP (A,z))
    _ = _ := by rw [lintegral_const,measure_univ,mul_one]

theorem gaussian_active_pruning_loss
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ξ : Measure ((Fin h → Space d) × Space h)) (hξ : ξ ≤ (gaussianRows d h).prod volume)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : κ → Space d)
    {R : ℝ} (hR : 0 ≤ R) {N T P : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (hP : ∀ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)) univ ≤ P) :
    (∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p ∂ξ) ≤
      (∫⁻ p, gaussianPrunedPairMass μ ν δ r TP TD M (gaussianActiveRelation E J a R T true) p ∂ξ) +
      P*(N*ENNReal.ofReal ((2*R)^h)/T)*M := by
  let f := gaussianPrunedPairMass (h := h) μ ν δ r TP TD M (gaussianActiveRelation E J a R T true)
  let g := gaussianPrunedPairMass (h := h) μ ν δ r TP TD M (gaussianActiveRelation E J a R T false)
  have hf : Measurable f := gaussianPrunedPairMass_measurable μ ν δ r TP TD M _
    (gaussianActiveRelation_measurable E hE J hJ a R T true)
  have hg : (∫⁻ p, g p ∂ξ) ≤ P*(N*ENNReal.ofReal ((2*R)^h)/T)*M :=
    (lintegral_mono' hξ le_rfl).trans
      (gaussian_active_bad_integral μ ν δ r TP TD M E hE J hJ a hR hN hT hTfin hP)
  calc
    _ ≤ ∫⁻ p, f p+g p ∂ξ := by
      apply lintegral_mono
      intro p
      apply (measure_mono (show E ⊆
        {t | (p,t) ∈ gaussianActiveRelation E J a R T true} ∪
        {t | (p,t) ∈ gaussianActiveRelation E J a R T false} from ?_)).trans (measure_union_le _ _)
      intro t ht
      rcases le_or_gt (gaussianActiveAnchorCount p.1 (J t.2) a R p.2 : ℝ≥0∞) T with hle | hgt
      · exact Or.inl ⟨ht,hle⟩
      · exact Or.inr ⟨ht,hgt⟩
    _ = (∫⁻ p, f p ∂ξ)+(∫⁻ p, g p ∂ξ) := lintegral_add_left hf _
    _ ≤ _ := add_le_add le_rfl hg

end Falconer

end OAI

end ExtensionScope41

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianSelectActive. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope42


namespace OAI

/-! # Choosing a quantitatively nonempty slice with its original active tube covers -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem gaussian_select_active_slice
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : κ → Space (n+1))
    {R : ℝ} (hR : 0 ≤ R) {N T P b : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (hP : ∀ p : (Fin h → Space (n+1)) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)) univ ≤ P)
    (hmean : b*volume (coordinateBox h (D*(ε+1)+δ)) + P*(N*ENNReal.ofReal ((2*R)^h)/T)*M <
      ∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p
        ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume) :
    ∃ A ∈ gaussianRowNeighborhood B ε, ∃ z ∈ coordinateBox h (D*(ε+1)+δ),
      b < gaussianPrunedPairMass μ ν δ r TP TD M (gaussianActiveRelation E J a R T true) (A,z) := by
  have hξ : ((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod
      (volume : Measure (Space h)) ≤ (gaussianRows (n+1) h).prod volume :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have hl := gaussian_active_pruning_loss μ ν _ hξ δ r TP TD M E hE J hJ a hR hN hT hTfin hP
  apply gaussian_select_pruned_pair B hB hε μ ν hμ δ r TP TD M _
  exact lt_of_add_lt_add_right (hmean.trans_le hl)

end Falconer

end OAI

end ExtensionScope42

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianOriginalSlice. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope43



namespace OAI

/-! # A retained original-label slice from the explicit four-cost budget -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem gaussian_select_original_slice
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {D δ ρ : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ)
    (r : ι → ℝ) (TP TD CP CD : ι → ℝ≥0∞)
    (hTP : ∀ i, 0 < TP i) (hTD : ∀ i, 0 < TD i)
    (i₀ : ι) (hi₀ : D < r i₀)
    {M Q : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hpoint : ∀ i, (∫⁻ p : (Fin h → Space (n+1)) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows (n+1) h).prod volume) ≤ CP i)
    (hdir : ∀ i, (∫⁻ A : Fin h → Space (n+1),
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows (n+1) h) ≤ CD i)
    (hmoment : (∫⁻ A : Fin h → Space (n+1), (gaussianDirectionMass ν δ A)^2
      ∂gaussianRows (n+1) h) ≤ Q)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : κ → Space (n+1))
    {R : ℝ} (hR : 0 ≤ R) {N T b : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (hbudget : (b*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ)) +
      TP i₀*(N*ENNReal.ofReal ((2*R)^h)/T)*M) +
      (∑ i, (TP i)⁻¹*CP i)*M +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (TD i)⁻¹*CD i) +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*Q) <
      ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E) :
    ∃ A ∈ gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)),
      ∃ z ∈ coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ),
      b < gaussianPrunedPairMass μ ν δ r TP TD M (gaussianActiveRelation E J a R T true) (A,z) := by
  have hρ : 0 ≤ ρ := hδ.le.trans hδρ
  have hlo := gaussian_controlled_pruning_ledger B hB μ ν hδ hδρ hwB r TP TD CP CD
    hTP hTD hM hMtop hpoint hdir hmoment E hE
  have hlt := hbudget.trans_le hlo
  have hmean := lt_of_add_lt_add_right (lt_of_add_lt_add_right (lt_of_add_lt_add_right hlt))
  apply gaussian_select_active_slice B hB (by positivity) μ ν hμ δ r TP TD M E hE J hJ a
    hR hN hT hTfin (fun p => gaussianPointGood_mass μ δ r TP p hμ i₀ hi₀)
  exact hmean

end Falconer

end OAI

end ExtensionScope43

/- Source: OAI.MeasureTheory.Falconer.Slicing.SlicePruningRatios. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope44


namespace OAI

/-! # Cancellation of the dyadic weights in the simultaneous pruning costs -/

namespace Falconer
open scoped ENNReal
variable {ι : Type*} [Fintype ι]

theorem pruning_weight_cancel {H C w : ℝ≥0∞}
    (hH : H ≠ 0) (hw : w ≠ 0) (hwtop : w ≠ ∞) :
    (H*w)⁻¹*(C*w) = H⁻¹*C := by
  rw [ENNReal.mul_inv (Or.inl hH) (Or.inr hw)]
  calc
    H⁻¹*w⁻¹*(C*w) = (H⁻¹*C)*(w⁻¹*w) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hw hwtop,mul_one]

theorem pruning_weighted_sum {H C : ℝ≥0∞} (hH : H ≠ 0)
    (w : ι → ℝ≥0∞) (hw : ∀ i, w i ≠ 0) (hwtop : ∀ i, w i ≠ ∞) :
    (∑ i, (H*w i)⁻¹*(C*w i)) = (Fintype.card ι : ℝ≥0∞)*(H⁻¹*C) := by
  simp_rw [pruning_weight_cancel hH (hw _) (hwtop _)]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

theorem pruning_weighted_sum_le {H C : ℝ≥0∞} (hH : H ≠ 0)
    (w B : ι → ℝ≥0∞) (hw : ∀ i, w i ≠ 0) (hwtop : ∀ i, w i ≠ ∞)
    (hB : ∀ i, B i ≤ C*w i) :
    (∑ i, (H*w i)⁻¹*B i) ≤ (Fintype.card ι : ℝ≥0∞)*(H⁻¹*C) := by
  apply (Finset.sum_le_sum (fun i _ => mul_le_mul_right (hB i) _)).trans_eq
  exact pruning_weighted_sum hH w hw hwtop

theorem pruning_real_weighted_sum {H C : ℝ} (hH : 0 < H)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (B : ι → ℝ≥0∞)
    (hB : ∀ i, B i ≤ ENNReal.ofReal (C*w i)) :
    (∑ i, (ENNReal.ofReal (H*w i))⁻¹*B i) ≤
      ENNReal.ofReal ((Fintype.card ι:ℝ)*C/H) := by
  have hi (i : ι) : (ENNReal.ofReal (H*w i))⁻¹*B i ≤ ENNReal.ofReal (C/H) := by
    apply (mul_le_mul_right (hB i) _).trans_eq
    rw [mul_comm]
    change ENNReal.ofReal (C*w i) / ENNReal.ofReal (H*w i) = _
    rw [← ENNReal.ofReal_div_of_pos (mul_pos hH (hw i))]
    congr 1
    field_simp [(hw i).ne']
  calc
    _ ≤ ∑ _i : ι, ENNReal.ofReal (C/H) := Finset.sum_le_sum (fun i _ => hi i)
    _ = (Fintype.card ι:ℝ≥0∞)*ENNReal.ofReal (C/H) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ = _ := by
      rw [show (Fintype.card ι:ℝ≥0∞) = ENNReal.ofReal (Fintype.card ι:ℝ) by simp,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end Falconer

end OAI

end ExtensionScope44

/- Source: OAI.MeasureTheory.Falconer.Slicing.SliceBudget. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope45


namespace OAI

/-! # The four deletion costs fit inside the original incidence budget -/

namespace Falconer
open scoped ENNReal

theorem slice_four_cost_budget_real {K B A : ℝ} (hK : 0 < K)
    (hlarge : 4*(1+2*B+A) ≤ K) :
    1/(4*K)+1/K^2+B/K^2+B/K^2+A/K^2 < 1/K := by
  have he : 1/(4*K)+1/K^2+B/K^2+B/K^2+A/K^2 =
      (K/4+(1+2*B+A))/K^2 := by field_simp; ring
  rw [he]
  apply (div_lt_div_iff₀ (sq_pos_of_pos hK) hK).mpr
  have hh := mul_le_mul_of_nonneg_right hlarge hK.le
  nlinarith

theorem slice_four_cost_budget {K B A : ℝ} (hK : 0 < K) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hlarge : 4*(1+2*B+A) ≤ K)
    {base point direction mass active : ℝ≥0∞}
    (hb : base ≤ ENNReal.ofReal (1/(4*K))) (hp : point ≤ ENNReal.ofReal (1/K^2))
    (hd : direction ≤ ENNReal.ofReal (B/K^2)) (hm : mass ≤ ENNReal.ofReal (B/K^2))
    (ha : active ≤ ENNReal.ofReal (A/K^2)) :
    base+point+direction+mass+active < ENNReal.ofReal (1/K) := by
  calc
    _ ≤ ENNReal.ofReal (1/(4*K))+ENNReal.ofReal (1/K^2)+ENNReal.ofReal (B/K^2)+
        ENNReal.ofReal (B/K^2)+ENNReal.ofReal (A/K^2) :=
      add_le_add (add_le_add (add_le_add (add_le_add hb hp) hd) hm) ha
    _ = ENNReal.ofReal (1/(4*K)+1/K^2+B/K^2+B/K^2+A/K^2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (slice_four_cost_budget_real hK hlarge)

end Falconer

end OAI

end ExtensionScope45

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianScaleBudget. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope46


namespace OAI

/-! # The concrete polynomial thresholds in Gaussian slice selection -/

namespace Falconer
open scoped ENNReal
variable {ι : Type*} [Fintype ι]

theorem slice_cube_ratio_le {K X : ℝ} (hK : 0 < K) (hX : X ≤ K) :
    X/K^3 ≤ 1/K^2 := by
  apply (div_le_iff₀ (pow_pos hK 3)).mpr
  calc
    X ≤ K := hX
    _ = (1/K^2)*K^3 := by field_simp

theorem gaussian_point_scale_cost {K C : ℝ} (hK : 0 < K)
    (hcard : (Fintype.card ι:ℝ)*C ≤ K)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (B : ι → ℝ≥0∞)
    (hB : ∀ i, B i ≤ ENNReal.ofReal (C*w i)) :
    (∑ i, (ENNReal.ofReal (K^6*w i))⁻¹*B i)*ENNReal.ofReal (K^3) ≤
      ENNReal.ofReal (1/K^2) := by
  have hs := pruning_real_weighted_sum (pow_pos hK 6) w hw B hB
  have he : ((Fintype.card ι:ℝ)*C/K^6)*K^3 = (Fintype.card ι:ℝ)*C/K^3 := by
    field_simp
  calc
    _ ≤ ENNReal.ofReal ((Fintype.card ι:ℝ)*C/K^6)*ENNReal.ofReal (K^3) := mul_le_mul' hs le_rfl
    _ = ENNReal.ofReal (((Fintype.card ι:ℝ)*C/K^6)*K^3) := by
      rw [← ENNReal.ofReal_mul' (by positivity : 0 ≤ K^3)]
    _ ≤ _ := by rw [he]; exact ENNReal.ofReal_le_ofReal (slice_cube_ratio_le hK hcard)

theorem gaussian_direction_scale_cost {K C S : ℝ} (hK : 0 < K) (hS : 0 ≤ S)
    (hcard : (Fintype.card ι:ℝ)*C ≤ K)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (B : ι → ℝ≥0∞)
    (hB : ∀ i, B i ≤ ENNReal.ofReal (C*w i)) :
    ENNReal.ofReal S*(∑ i, (ENNReal.ofReal (K^3*w i))⁻¹*B i) ≤
      ENNReal.ofReal (S/K^2) := by
  have hs := (pruning_real_weighted_sum (pow_pos hK 3) w hw B hB).trans
    (ENNReal.ofReal_le_ofReal (slice_cube_ratio_le hK hcard))
  calc
    _ ≤ ENNReal.ofReal S*ENNReal.ofReal (1/K^2) := mul_le_mul' le_rfl hs
    _ = _ := by rw [← ENNReal.ofReal_mul hS]; congr 1; ring

theorem gaussian_mass_scale_cost {K C S : ℝ} (hK : 0 < K) (hS : 0 ≤ S)
    (hC : C ≤ K) {Q : ℝ≥0∞} (hQ : Q ≤ ENNReal.ofReal C) :
    ENNReal.ofReal S*((ENNReal.ofReal (K^3))⁻¹*Q) ≤ ENNReal.ofReal (S/K^2) := by
  have hs : (ENNReal.ofReal (K^3))⁻¹*Q ≤ ENNReal.ofReal (1/K^2) := by
    calc
      _ ≤ (ENNReal.ofReal (K^3))⁻¹*ENNReal.ofReal C := mul_le_mul' le_rfl hQ
      _ = ENNReal.ofReal (C/K^3) := by
        rw [mul_comm]
        change ENNReal.ofReal C / ENNReal.ofReal (K^3) = _
        rw [← ENNReal.ofReal_div_of_pos (pow_pos hK 3)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (slice_cube_ratio_le hK hC)
  calc
    _ ≤ ENNReal.ofReal S*ENNReal.ofReal (1/K^2) := mul_le_mul' le_rfl hs
    _ = _ := by rw [← ENNReal.ofReal_mul hS]; congr 1; ring

theorem gaussian_active_scale_cost {K w N R : ℝ} (hK : 0 < K) (hw : 0 < w)
    (hN : 0 < N) (hR : 0 < R) (h : ℕ) :
    ENNReal.ofReal (K^6*w)*
      (ENNReal.ofReal N*ENNReal.ofReal ((2*R)^h)/
        ENNReal.ofReal (K^11*(w*(N*(2*R)^h))))*ENNReal.ofReal (K^3) =
      ENNReal.ofReal (1/K^2) := by
  have hp : 0 < (2*R)^h := pow_pos (by positivity) h
  have hd : 0 < K^11*(w*(N*(2*R)^h)) := by positivity
  rw [← ENNReal.ofReal_mul hN.le,← ENNReal.ofReal_div_of_pos hd,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ K^6*w),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (K^6*w)*((N*(2*R)^h)/(K^11*(w*(N*(2*R)^h)))))]
  congr 1
  field_simp [hK.ne',hw.ne',hN.ne',hp.ne']

theorem gaussian_four_polynomial_costs {K C S w₀ N R : ℝ}
    (hK : 0 < K) (hS : 0 ≤ S) (hw₀ : 0 < w₀) (hN : 0 < N) (hR : 0 < R)
    (hcard : (Fintype.card ι:ℝ)*C ≤ K) (hC : C ≤ K)
    (hlarge : 4*(1+2*S+1) ≤ K)
    (w v : ι → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (CP CD : ι → ℝ≥0∞) (hCP : ∀ i, CP i ≤ ENNReal.ofReal (C*w i))
    (hCD : ∀ i, CD i ≤ ENNReal.ofReal (C*v i))
    (h : ℕ) {base Q : ℝ≥0∞}
    (hbase : base ≤ ENNReal.ofReal (1/(4*K))) (hQ : Q ≤ ENNReal.ofReal C) :
    base + (∑ i, (ENNReal.ofReal (K^6*w i))⁻¹*CP i)*ENNReal.ofReal (K^3) +
      ENNReal.ofReal S*(∑ i, (ENNReal.ofReal (K^3*v i))⁻¹*CD i) +
      ENNReal.ofReal S*((ENNReal.ofReal (K^3))⁻¹*Q) +
      ENNReal.ofReal (K^6*w₀)*
        (ENNReal.ofReal N*ENNReal.ofReal ((2*R)^h)/
          ENNReal.ofReal (K^11*(w₀*(N*(2*R)^h))))*ENNReal.ofReal (K^3) <
      ENNReal.ofReal (1/K) := by
  apply slice_four_cost_budget hK hS (show (0:ℝ) ≤ 1 by norm_num) hlarge hbase
    (gaussian_point_scale_cost hK hcard w hw CP hCP)
    (gaussian_direction_scale_cost hK hS hcard v hv CD hCD)
    (gaussian_mass_scale_cost hK hS hC hQ)
  exact (gaussian_active_scale_cost hK hw₀ hN hR h).le

end Falconer

end OAI

end ExtensionScope46

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPolynomialSlice. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope47



namespace OAI

/-! # A retained original slice with the explicit polynomial pruning thresholds -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

private theorem original_cost_order (a b c d e : ℝ≥0∞) :
    (a+e)+b+c+d = a+b+c+d+e := by ac_rfl

theorem gaussian_select_polynomial_slice
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {D δ ρ : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ)
    (r w v : ι → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (CP CD : ι → ℝ≥0∞) (Q : ℝ≥0∞)
    {K C S N R : ℝ} (hK : 0 < K) (hS : 0 ≤ S) (hN : 0 < N) (hR : 0 < R)
    (hcard : (Fintype.card ι:ℝ)*C ≤ K) (hC : C ≤ K) (hlarge : 4*(1+2*S+1) ≤ K)
    (hCP : ∀ i, CP i ≤ ENNReal.ofReal (C*w i))
    (hCD : ∀ i, CD i ≤ ENNReal.ofReal (C*v i)) (hQ : Q ≤ ENNReal.ofReal C)
    (hfactor : ENNReal.ofReal ((2:ℝ)^h)*μ univ ≤ ENNReal.ofReal S)
    (i₀ : ι) (hi₀ : D < r i₀)
    (hpoint : ∀ i, (∫⁻ p : (Fin h → Space (n+1)) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows (n+1) h).prod volume) ≤ CP i)
    (hdir : ∀ i, (∫⁻ A : Fin h → Space (n+1),
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows (n+1) h) ≤ CD i)
    (hmoment : (∫⁻ A : Fin h → Space (n+1), (gaussianDirectionMass ν δ A)^2
      ∂gaussianRows (n+1) h) ≤ Q)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {u | i ∈ J u})
    (a : κ → Space (n+1)) (hJN : ∀ u, ((J u).card : ℝ≥0∞) ≤ ENNReal.ofReal N)
    (hmean : ENNReal.ofReal (1/K) ≤ ENNReal.ofReal ((2:ℝ)^h)*
      ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E)
    {b : ℝ≥0∞}
    (hbase : b*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ)) ≤
      ENNReal.ofReal (1/(4*K))) :
    ∃ A ∈ gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)),
      ∃ z ∈ coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ),
      b < gaussianPrunedPairMass μ ν δ r
        (fun i => ENNReal.ofReal (K^6*w i)) (fun i => ENNReal.ofReal (K^3*v i))
        (ENNReal.ofReal (K^3))
        (gaussianActiveRelation E J a R
          (ENNReal.ofReal (K^11*(w i₀*(N*(2*R)^h)))) true) (A,z) := by
  have hw₀ := hw i₀
  apply gaussian_select_original_slice B hB μ ν hμ hδ hδρ hwB r
    (fun i => ENNReal.ofReal (K^6*w i)) (fun i => ENNReal.ofReal (K^3*v i)) CP CD
    (fun i => ENNReal.ofReal_pos.mpr (mul_pos (pow_pos hK 6) (hw i)))
    (fun i => ENNReal.ofReal_pos.mpr (mul_pos (pow_pos hK 3) (hv i))) i₀ hi₀
    (ENNReal.ofReal_pos.mpr (pow_pos hK 3)) ENNReal.ofReal_ne_top
    hpoint hdir hmoment E hE J hJ a hR.le hJN
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))) ENNReal.ofReal_ne_top
  have hc := gaussian_four_polynomial_costs hK hS (hw i₀) hN hR hcard hC hlarge
    w v hw hv CP CD hCP hCD h hbase hQ
  apply lt_of_le_of_lt _ (hc.trans_le hmean)
  calc
    _ = b*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ)) +
        (∑ i, (ENNReal.ofReal (K^6*w i))⁻¹*CP i)*ENNReal.ofReal (K^3) +
        (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (ENNReal.ofReal (K^3*v i))⁻¹*CD i) +
        (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*((ENNReal.ofReal (K^3))⁻¹*Q) +
        ENNReal.ofReal (K^6*w i₀)*(ENNReal.ofReal N*ENNReal.ofReal ((2*R)^h)/
          ENNReal.ofReal (K^11*(w i₀*(N*(2*R)^h))))*ENNReal.ofReal (K^3) :=
      original_cost_order _ _ _ _ _
    _ ≤ _ := add_le_add
      (add_le_add (add_le_add le_rfl (mul_le_mul' hfactor le_rfl))
        (mul_le_mul' hfactor le_rfl)) le_rfl

end Falconer

end OAI

end ExtensionScope47

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianMomentWeights. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope48




namespace OAI

/-! # The dyadic weights of the actual point and direction pair moments -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianFrostmanFactor (h : ℕ) (s : ℝ) : ℝ :=
  1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-s))

theorem gaussian_point_moment_weight
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {Kt t C : ℝ} (hKt : 0 ≤ Kt) (ht : (h:ℝ) < t) (g N : ℕ) (hg : g ≤ N)
    (hmass : μ univ ≤ 1)
    (hball : ∀ x : Space d, ∀ j : ℕ, j ≤ N →
      μ (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Kt*(1/(2:ℝ)^j)^t))
    (hC : (4*gaussianVectorBandConstant)^h*Kt*gaussianFrostmanFactor h t ≤ C) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 (1/(2:ℝ)^N)).prod
        (gaussianPointSliceMeasure μ p.1 p.2 (1/(2:ℝ)^N)))
        {z | dist z.1 z.2 < 2*((1/(2:ℝ)^g)/2)} ∂(gaussianRows d h).prod volume) ≤
      ENNReal.ofReal (C*((2:ℝ)^g)^((h:ℝ)-t)) := by
  have hVC := gaussianVectorBandConstant_pos
  have hr : (2:ℝ)*((1/(2:ℝ)^g)/2) = 1/(2:ℝ)^g := by ring
  rw [hr]
  apply (gaussian_point_slice_close_frostman μ hKt ht g N hg hmass hball).trans
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (4*gaussianVectorBandConstant)^h)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = ((4*gaussianVectorBandConstant)^h*Kt*gaussianFrostmanFactor h t)*
      ((2:ℝ)^g)^((h:ℝ)-t) := by unfold gaussianFrostmanFactor; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (by positivity) _)

theorem gaussian_direction_moment_weight
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {Kq q C : ℝ} (hKq : 0 ≤ Kq) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : ν univ ≤ 1)
    (hball : ∀ x : Sphere d, ∀ j : ℕ, j ≤ N →
      ν (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Kq*(1/(2:ℝ)^j)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d))
    (hC : (2*gaussianPairBandConstant)^h*Kq*gaussianFrostmanFactor h q ≤ C) :
    (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).prod
        (gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)))
        {z | dist z.1 z.2 < 2*((1/(2:ℝ)^g)/2)} ∂gaussianRows d h) ≤
      ENNReal.ofReal (C*((2:ℝ)^g)^((h:ℝ)-q)) := by
  have hPC := gaussianPairBandConstant_pos
  have hr : (2:ℝ)*((1/(2:ℝ)^g)/2) = 1/(2:ℝ)^g := by ring
  rw [hr]
  apply (gaussian_direction_slice_close_frostman ν hKq hq g N hg hmass hball hchart).trans
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2*gaussianPairBandConstant)^h)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = ((2*gaussianPairBandConstant)^h*Kq*gaussianFrostmanFactor h q)*
      ((2:ℝ)^g)^((h:ℝ)-q) := by unfold gaussianFrostmanFactor; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (by positivity) _)

theorem gaussian_direction_total_moment_bound
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {Kq q C : ℝ} (hKq : 0 ≤ Kq) (hq : (h:ℝ) < q) (N : ℕ)
    (hmass : ν univ ≤ 1)
    (hball : ∀ x : Sphere d, ∀ j : ℕ, j ≤ N →
      ν (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Kq*(1/(2:ℝ)^j)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d))
    (hC : (2*gaussianPairBandConstant)^h*(|Kq*gaussianFrostmanFactor h q|+1) ≤ C) :
    (∫⁻ A : Fin h → Space d, (gaussianDirectionMass ν (1/(2:ℝ)^N) A)^2
      ∂gaussianRows d h) ≤ ENNReal.ofReal C := by
  have hPC := gaussianPairBandConstant_pos
  apply (gaussian_direction_mass_second_moment ν hKq hq N hmass hball hchart).trans
  have hb : ENNReal.ofReal (Kq*gaussianFrostmanFactor h q)+1 ≤
      ENNReal.ofReal (|Kq*gaussianFrostmanFactor h q|+1) := by
    rw [ENNReal.ofReal_add (abs_nonneg _) zero_le_one,ENNReal.ofReal_one]
    exact add_le_add (ENNReal.ofReal_le_ofReal (le_abs_self _)) le_rfl
  apply (mul_le_mul' le_rfl hb).trans
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2*gaussianPairBandConstant)^h)]
  exact ENNReal.ofReal_le_ofReal hC

end Falconer

end OAI

end ExtensionScope48

/- Source: OAI.MeasureTheory.Falconer.Slicing.DyadicSliceSelection. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope49



namespace OAI

/-! # Selecting a slice directly from the two original finite-scale ball bounds -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def gaussianPruningRadius {N : ℕ} (g : Fin (N+1)) : ℝ :=
  (1/(2:ℝ)^g.val)/2

noncomputable def gaussianPruningWeight (h : ℕ) (s : ℝ) {N : ℕ} (g : Fin (N+1)) : ℝ :=
  ((2:ℝ)^g.val)^((h:ℝ)-s)

theorem gaussianPruningWeight_eq (h : ℕ) (s : ℝ) {N : ℕ} (g : Fin (N+1)) :
    gaussianPruningWeight h s g = (1/(2:ℝ)^g.val)^(s-(h:ℝ)) := by
  unfold gaussianPruningWeight
  rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity)]
  congr 1
  ring

theorem dyadic_original_slice_selection
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (N : ℕ)
    {D ρ Lt Lq t q : ℝ} (hD : D < 1/2) (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (hδρ : 1/(2:ℝ)^N ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ)
    (hLt : 0 ≤ Lt) (hLq : 0 ≤ Lq) (ht : (h:ℝ) < t) (hq : (h:ℝ) < q)
    (hμmass : μ univ ≤ 1) (hνmass : ν univ ≤ 1)
    (hμball : ∀ x : Space (n+1), ∀ j : ℕ, j ≤ N →
      μ (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lt*(1/(2:ℝ)^j)^t))
    (hνball : ∀ x : Sphere (n+1), ∀ j : ℕ, j ≤ N →
      ν (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lq*(1/(2:ℝ)^j)^q))
    (hchart : ∀ᵐ z : Sphere (n+1) × Sphere (n+1) ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space (n+1)) (z.2:Space (n+1)))
    {K C S Nc R : ℝ} (hK : 0 < K) (hS : 0 ≤ S) (hNc : 0 < Nc) (hR : 0 < R)
    (hCpoint : (4*gaussianVectorBandConstant)^h*Lt*gaussianFrostmanFactor h t ≤ C)
    (hCdir : (2*gaussianPairBandConstant)^h*Lq*gaussianFrostmanFactor h q ≤ C)
    (hCmass : (2*gaussianPairBandConstant)^h*(|Lq*gaussianFrostmanFactor h q|+1) ≤ C)
    (hcard : ((N+1:ℕ):ℝ)*C ≤ K) (hC : C ≤ K) (hlarge : 4*(1+2*S+1) ≤ K)
    (hfactor : ENNReal.ofReal ((2:ℝ)^h)*μ univ ≤ ENNReal.ofReal S)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space (n+1)) (hJN : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc)
    (hmean : ENNReal.ofReal (1/K) ≤ ENNReal.ofReal ((2:ℝ)^h)*
      ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E)
    {b : ℝ≥0∞}
    (hbase : b*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N)) ≤
      ENNReal.ofReal (1/(4*K))) :
    ∃ A ∈ gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)),
      ∃ z ∈ coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N),
      b < gaussianPrunedPairMass μ ν (1/(2:ℝ)^N) (gaussianPruningRadius (N := N))
        (fun i => ENNReal.ofReal (K^6*gaussianPruningWeight h t i))
        (fun i => ENNReal.ofReal (K^3*gaussianPruningWeight h q i)) (ENNReal.ofReal (K^3))
        (gaussianActiveRelation E J a R (ENNReal.ofReal (K^11*(Nc*(2*R)^h))) true) (A,z) := by
  let r : Fin (N+1) → ℝ := gaussianPruningRadius
  let w : Fin (N+1) → ℝ := gaussianPruningWeight h t
  let v : Fin (N+1) → ℝ := gaussianPruningWeight h q
  let CP : Fin (N+1) → ℝ≥0∞ := fun i => ENNReal.ofReal (C*w i)
  let CD : Fin (N+1) → ℝ≥0∞ := fun i => ENNReal.ofReal (C*v i)
  have hp (i : Fin (N+1)) := gaussian_point_moment_weight μ hLt ht i.val N
    (Nat.le_of_lt_succ i.isLt) hμmass hμball hCpoint
  have hd (i : Fin (N+1)) := gaussian_direction_moment_weight ν hLq hq i.val N
    (Nat.le_of_lt_succ i.isLt) hνmass hνball hchart hCdir
  have hm := gaussian_direction_total_moment_bound ν hLq hq N hνmass hνball hchart hCmass
  have hi₀ : D < r 0 := by simpa only [r,gaussianPruningRadius,Fin.val_zero,pow_zero,div_one] using hD
  have hh := gaussian_select_polynomial_slice B hB μ ν hμ (by positivity) hδρ hwB r w v
    (fun i => by dsimp [w,gaussianPruningWeight]; positivity)
    (fun i => by dsimp [v,gaussianPruningWeight]; positivity)
    CP CD (ENNReal.ofReal C) hK hS hNc hR
    (by simpa only [Fintype.card_fin] using hcard) hC hlarge
    (fun _ => le_rfl) (fun _ => le_rfl) le_rfl hfactor 0 hi₀ hp hd hm
    E hE J hJ a hJN hmean hbase
  simpa only [w,v,r,gaussianPruningWeight,Fin.val_zero,pow_zero,Real.one_rpow,one_mul] using hh

end Falconer

end OAI

end ExtensionScope49

/- Source: OAI.MeasureTheory.Falconer.Slicing.SliceCoordinates. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope50



namespace OAI

/-! # Isometric Euclidean coordinates on the actual finite-dimensional slice -/

namespace Falconer
open NormedSpace
variable {d m : ℕ}

noncomputable def sliceCoordinates (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) : V ≃ₗᵢ[ℝ] Space m :=
  ((stdOrthonormalBasis ℝ V).reindex (finCongr hm)).repr

noncomputable def slicePointCoordinates (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (x : Space d) : Space m :=
  sliceCoordinates V hm (V.orthogonalProjectionOnto x)

theorem slicePointCoordinates_continuous (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) : Continuous (slicePointCoordinates V hm) :=
  (sliceCoordinates V hm).continuous.comp V.orthogonalProjectionOnto.continuous

theorem slicePointCoordinates_norm (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (x : Space d) :
    ‖slicePointCoordinates V hm x‖ = ‖V.starProjection x‖ := by
  rw [slicePointCoordinates,(sliceCoordinates V hm).norm_map]
  rfl

theorem slicePointCoordinates_sub (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (x y : Space d) :
    slicePointCoordinates V hm (x-y) = slicePointCoordinates V hm x-slicePointCoordinates V hm y := by
  simp only [slicePointCoordinates,map_sub]

theorem slicePointCoordinates_dist (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (x y : Space d) :
    dist (slicePointCoordinates V hm x) (slicePointCoordinates V hm y) =
      dist (V.starProjection x) (V.starProjection y) := by
  rw [dist_eq_norm,← slicePointCoordinates_sub,slicePointCoordinates_norm,map_sub,dist_eq_norm]

theorem sliceCoordinates_normalize (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (x : V) :
    sliceCoordinates V hm (normalize x) = normalize (sliceCoordinates V hm x) := by
  simp only [NormedSpace.normalize,map_smul,(sliceCoordinates V hm).norm_map]

theorem sliceCoordinates_perpendicularPart (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (w x : V) :
    sliceCoordinates V hm (perpendicularPart w x) =
      perpendicularPart (sliceCoordinates V hm w) (sliceCoordinates V hm x) := by
  simp only [perpendicularPart,map_sub,map_smul,(sliceCoordinates V hm).inner_map_map]

end Falconer

end OAI

end ExtensionScope50

/- Source: OAI.MeasureTheory.Falconer.Geometry.FrameEmbedding. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope51


namespace OAI

/-! # The linear isometry associated with a finite orthonormal frame -/

namespace Falconer
variable {d h : ℕ}

noncomputable def frameLinearMap (v : Fin h → Space d) : Space h →ₗ[ℝ] Space d :=
  (EuclideanSpace.basisFun (Fin h) ℝ).toBasis.constr ℝ v

@[simp] theorem frameLinearMap_basis (v : Fin h → Space d) (i : Fin h) :
    frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ i) = v i :=
  (EuclideanSpace.basisFun (Fin h) ℝ).toBasis.constr_basis ℝ v i

theorem frameLinearMap_orthonormal {v : Fin h → Space d} (hv : Orthonormal ℝ v) :
    Orthonormal ℝ (frameLinearMap v ∘ (EuclideanSpace.basisFun (Fin h) ℝ).toBasis) := by
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  change inner ℝ (frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ i))
    (frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ j)) = _
  simpa only [frameLinearMap_basis] using hv i j

theorem orthonormal_frame_embedding {v : Fin h → Space d} (hv : Orthonormal ℝ v) :
    ∃ e : Space h →ₗᵢ[ℝ] Space d,
      ∀ i, e (EuclideanSpace.basisFun (Fin h) ℝ i) = v i := by
  let e : Space h →ₗᵢ[ℝ] Space d := (frameLinearMap v).isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (Fin h) ℝ).toBasis)
    (EuclideanSpace.basisFun (Fin h) ℝ).orthonormal (frameLinearMap_orthonormal hv)
  refine ⟨e,?_⟩
  intro i
  change frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ i) = v i
  exact frameLinearMap_basis v i

end Falconer

end OAI

end ExtensionScope51

/- Source: OAI.MeasureTheory.Falconer.Slicing.TransverseFrame. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope52



namespace OAI

/-! # A uniformly transverse row frame for each fixed spherical chart -/

namespace Falconer
variable {n h : ℕ}

theorem exists_transverse_row_frame (hhn : h ≤ n) {w : Space (n+1)} (hw : ‖w‖ = 1) :
    ∃ e : Space h →ₗᵢ[ℝ] Space (n+1),
      ∀ i, inner ℝ w (e (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0 := by
  let u := EuclideanSpace.basisFun (Fin (n+1)) ℝ 0
  let R : Space (n+1) ≃ₗᵢ[ℝ] Space (n+1) := (ℝ ∙ (u-w))ᗮ.reflection
  have hR : R u = w := Submodule.reflection_sub
    (((EuclideanSpace.basisFun (Fin (n+1)) ℝ).norm_eq_one 0).trans hw.symm)
  let f : Fin h → Fin (n+1) := fun i => ⟨i.val+1,by omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have he := congrArg Fin.val hij
    dsimp [f] at he
    omega
  let v : Fin h → Space (n+1) := fun i => R (EuclideanSpace.basisFun (Fin (n+1)) ℝ (f i))
  have hv : Orthonormal ℝ v := by
    exact ((EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal.comp f hf).comp_linearIsometryEquiv R
  obtain ⟨e,he⟩ := orthonormal_frame_embedding hv
  refine ⟨e,fun i => ?_⟩
  rw [he,← hR]
  change inner ℝ (R u) (R (EuclideanSpace.basisFun (Fin (n+1)) ℝ (f i))) = 0
  rw [R.inner_map_map]
  exact (EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal.2 (by
    intro heq
    have hz := congrArg Fin.val heq
    dsimp [f] at hz
    omega)

theorem transverse_frame_chart_bound (e : Space h →ₗᵢ[ℝ] Space (n+1))
    (w₀ : Space (n+1))
    (he : ∀ i, inner ℝ w₀ (e (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0)
    {w : Space (n+1)} {ρ : ℝ} (hw : dist w w₀ ≤ ρ) (i : Fin h) :
    |inner ℝ w (e (EuclideanSpace.basisFun (Fin h) ℝ i))| ≤ ρ := by
  let b := e (EuclideanSpace.basisFun (Fin h) ℝ i)
  have hi : inner ℝ w b = inner ℝ (w-w₀) b := by rw [inner_sub_left,he i,sub_zero]
  rw [hi]
  calc
    _ ≤ ‖w-w₀‖*‖b‖ := abs_real_inner_le_norm _ _
    _ = dist w w₀ := by
      rw [show ‖b‖ = 1 from (e.norm_map _).trans
        ((EuclideanSpace.basisFun (Fin h) ℝ).norm_eq_one i),mul_one,dist_eq_norm]
    _ ≤ _ := hw

end Falconer

end OAI

end ExtensionScope52

/- Source: OAI.MeasureTheory.Falconer.Slicing.PlanarSliceGeometry. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope53



namespace OAI

/-! # Oriented planar coordinates and the strip equations of sliced tubes -/

namespace Falconer
open NormedSpace

theorem exists_unit_axis_isometry {m : ℕ} (hm : 0 < m)
    {v : Space m} (hv : ‖v‖ = 1) :
    ∃ R : Space m ≃ₗᵢ[ℝ] Space m,
      R v = EuclideanSpace.basisFun (Fin m) ℝ ⟨0,hm⟩ := by
  let u := EuclideanSpace.basisFun (Fin m) ℝ ⟨0,hm⟩
  let S : Space m ≃ₗᵢ[ℝ] Space m := (ℝ ∙ (u-v))ᗮ.reflection
  have he : S u = v := Submodule.reflection_sub
    (((EuclideanSpace.basisFun (Fin m) ℝ).norm_eq_one ⟨0,hm⟩).trans hv.symm)
  exact ⟨S.symm,by rw [← he,S.symm_apply_apply]⟩

noncomputable def planarSlope (w : Space 2) : ℝ := w 1 / w 0

noncomputable def planarIntercept (w x : Space 2) : ℝ := x 1-planarSlope w*x 0

theorem planarSlope_small_of_axis_close {w : Space 2}
    (hw : dist w (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) :
    0 < w 0 ∧ |planarSlope w| ≤ 1/2 := by
  have hzero := (PiLp.dist_apply_le w (EuclideanSpace.basisFun (Fin 2) ℝ 0) 0).trans hw
  have hone := (PiLp.dist_apply_le w (EuclideanSpace.basisFun (Fin 2) ℝ 0) 1).trans hw
  have hz : |w 0-1| ≤ 1/4 := by simpa [Real.dist_eq] using hzero
  have ho : |w 1| ≤ 1/4 := by simpa [Real.dist_eq] using hone
  have hpos : 0 < w 0 := by have := (abs_le.mp hz).1; linarith
  refine ⟨hpos,?_⟩
  rw [planarSlope,abs_div,abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  have := (abs_le.mp hz).1
  linarith

theorem planarIntercept_sub (w x a : Space 2) :
    planarIntercept w (x-a) = planarIntercept w x-planarIntercept w a := by
  simp only [planarIntercept,PiLp.sub_apply]
  ring

theorem planarIntercept_perpendicular {w : Space 2} (hw : w 0 ≠ 0) (x : Space 2) :
    planarIntercept w (perpendicularPart w x) = planarIntercept w x := by
  simp only [planarIntercept,planarSlope,perpendicularPart,PiLp.sub_apply,PiLp.smul_apply,
    smul_eq_mul]
  field_simp
  ring

theorem planarIntercept_norm_bound (w x : Space 2) :
    |planarIntercept w x| ≤ (1+|planarSlope w|)*‖x‖ := by
  calc
    _ ≤ |x 1|+|planarSlope w*x 0| := abs_sub _ _
    _ = |x 1|+|planarSlope w| * |x 0| := by rw [abs_mul]
    _ ≤ ‖x‖+|planarSlope w| * ‖x‖ :=
      add_le_add (PiLp.norm_apply_le x 1)
        (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x 0) (abs_nonneg _))
    _ = _ := by ring

theorem planar_tube_strip {w x a : Space 2} {ε : ℝ}
    (hw : w 0 ≠ 0) (hslope : |planarSlope w| ≤ 1/2)
    (htube : ‖perpendicularPart w (x-a)‖ ≤ ε) :
    |x 1-planarSlope w*x 0-planarIntercept w a| ≤ (3/2)*ε := by
  change |planarIntercept w x-planarIntercept w a| ≤ _
  rw [← planarIntercept_sub,← planarIntercept_perpendicular hw]
  exact (planarIntercept_norm_bound w _).trans
    (mul_le_mul (by linarith) htube (norm_nonneg _) (by norm_num))

end Falconer

end OAI

end ExtensionScope53

/- Source: OAI.MeasureTheory.Falconer.Geometry.PlanarSlopeBalls. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope54


namespace OAI

/-! # Direction-ball control transfers to the slope coordinate -/

namespace Falconer
open Set MeasureTheory NormedSpace

theorem normalize_dist_le_twice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {x y : E} (hx : 1 ≤ ‖x‖) (hy : y ≠ 0) :
    dist (normalize x) (normalize y) ≤ 2*dist x y := by
  have he : ‖x‖ • (normalize x-normalize y) =
      x-y+(‖y‖-‖x‖) • normalize y := by
    rw [smul_sub,norm_smul_normalize,sub_smul,norm_smul_normalize]
    abel
  have hb := norm_add_le (x-y) ((‖y‖-‖x‖) • normalize y)
  rw [← he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    norm_smul,Real.norm_eq_abs,norm_normalize hy,mul_one] at hb
  have hn := abs_norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hn
  rw [dist_eq_norm,dist_eq_norm]
  nlinarith [norm_nonneg (normalize x-normalize y)]

noncomputable def slopeVector (m : ℝ) : Space 2 := WithLp.toLp 2 ![1,m]

@[simp] theorem slopeVector_zero (m : ℝ) : slopeVector m 0 = 1 := rfl
@[simp] theorem slopeVector_one (m : ℝ) : slopeVector m 1 = m := rfl

theorem slopeVector_norm_lower (m : ℝ) : 1 ≤ ‖slopeVector m‖ := by
  simpa only [slopeVector_zero,Real.norm_eq_abs,abs_one] using
    PiLp.norm_apply_le (slopeVector m) 0

theorem slopeVector_dist (m t : ℝ) : dist (slopeVector m) (slopeVector t) = |m-t| := by
  have hh := EuclideanSpace.dist_sq_eq (slopeVector m) (slopeVector t)
  simp only [Fin.sum_univ_two,slopeVector_zero,slopeVector_one,Real.dist_eq,sq_abs,sub_self,
    zero_pow (by omega : 2 ≠ 0),zero_add] at hh
  nlinarith [dist_nonneg (x := slopeVector m) (y := slopeVector t),abs_nonneg (m-t),sq_abs (m-t)]

theorem slopeDirection_dist (m t : ℝ) :
    dist (normalize (slopeVector m)) (normalize (slopeVector t)) ≤ 2*|m-t| := by
  have ht : slopeVector t ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (slopeVector_norm_lower t))
  simpa only [slopeVector_dist] using normalize_dist_le_twice (slopeVector_norm_lower m) ht

theorem planar_unit_eq_slopeDirection {w : Space 2} (hw : ‖w‖ = 1) (hpos : 0 < w 0) :
    w = normalize (slopeVector (planarSlope w)) := by
  have he : w = w 0 • slopeVector (planarSlope w) := by
    apply PiLp.ext
    intro i
    fin_cases i
    · change w 0 = w 0 * 1
      ring
    · change w 1 = w 0 * (w 1 / w 0)
      field_simp
  have hn := normalize_eq_self_of_norm_eq_one hw
  rw [he,normalize_smul_of_pos hpos] at hn
  exact he.trans hn.symm

theorem planar_slope_ball_subset {W : Type*} (q : W → Space 2)
    (hunit : ∀ w, ‖q w‖ = 1) (hpos : ∀ w, 0 < q w 0) (a r : ℝ) :
    {w | |planarSlope (q w)-a| ≤ r} ⊆
      {w | dist (q w) (normalize (slopeVector a)) ≤ 2*r} := by
  intro w hw
  change dist (q w) (normalize (slopeVector a)) ≤ 2*r
  rw [planar_unit_eq_slopeDirection (hunit w) (hpos w)]
  exact (slopeDirection_dist _ a).trans (mul_le_mul_of_nonneg_left hw (by norm_num))

theorem planar_slope_ball_measure {W : Type*} [MeasurableSpace W]
    (ν : Measure W) (q : W → Space 2)
    (hunit : ∀ w, ‖q w‖ = 1) (hpos : ∀ w, 0 < q w 0) (a r : ℝ) :
    ν {w | |planarSlope (q w)-a| ≤ r} ≤
      ν {w | dist (q w) (normalize (slopeVector a)) ≤ 2*r} :=
  measure_mono (planar_slope_ball_subset q hunit hpos a r)

end Falconer

end OAI

end ExtensionScope54

/- Source: OAI.MeasureTheory.Falconer.Estimates.PlanarGainNumerics. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope55


namespace OAI

/-!
# Absorbing the explicit losses in the planar measure obstruction

Only fixed constants, logarithms and ceilings are absorbed here. The
underlying incidence estimate has already been proved from the cited
published input.
-/

namespace Falconer
open Real Filter
open scoped Topology

theorem samplingBallLoss_le {δ η B s : ℝ} (hB : B ≤ δ^(-η)) :
    samplingBallLoss (δ^(-η)) B s ≤ (exp 1 * 8^s) * δ^(-η) := by
  unfold samplingBallLoss
  have hh : (exp 1-1)*δ^(-η)+B ≤ exp 1*δ^(-η) := by linarith
  calc
    _ ≤ (exp 1*δ^(-η))*8^s := mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by ring

theorem rpow_absorb_constant {δ t u C : ℝ} (hδ : 0 < δ)
    (hC : C ≤ δ^(-(u-t))) : C * δ^(-t) ≤ δ^(-u) := by
  calc
    _ ≤ δ^(-(u-t)) * δ^(-t) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring

theorem sampling_point_loss_le {δ η Tf C : ℝ} (hδ : 0 < δ)
    (hTf : 0 ≤ Tf) (hT : Tf ≤ C*δ^(-η)) :
    2*(8*Tf/δ^η)^2 ≤ (128*C^2)*δ^(-4*η) := by
  have hh : 0 ≤ 8*Tf/δ^η := by positivity
  have hq : 8*Tf/δ^η ≤ 8*(C*δ^(-η))/δ^η := by gcongr
  have he : (δ^(-η)/δ^η)^2 = δ^(-4*η) := by
    rw [← Real.rpow_sub hδ, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    ring
  calc
    _ ≤ 2*(8*(C*δ^(-η))/δ^η)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh hq 2) (by norm_num)
    _ = (128*C^2)*(δ^(-η)/δ^η)^2 := by ring
    _ = _ := by rw [he]

theorem sampling_direction_loss_le {δ η Tb C b : ℝ} (hδ : 0 < δ)
    (hTb : 0 ≤ Tb) (hT : Tb ≤ C*δ^(-η)) :
    8*2^b*Tb^2/δ^η ≤ (8*2^b*C^2)*δ^(-3*η) := by
  have he : (δ^(-η))^2/δ^η = δ^(-3*η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_sub hδ]
    congr 1
    ring
  calc
    _ ≤ 8*2^b*(C*δ^(-η))^2/δ^η := by gcongr
    _ = (8*2^b*C^2)*((δ^(-η))^2/δ^η) := by ring
    _ = _ := by rw [he]

structure PlanarSamplingReady (δ b f η ε : ℝ) (J : ℕ) : Prop where
  scale_pos : 0 < δ
  scale_small : δ ≤ 1/4
  budget : 1 ≤ -10*log δ
  point_loss : 2*(8*samplingBallLoss (δ^(-η)) (-10*log δ) f/δ^η)^2 ≤ δ^(-ε)
  direction_loss : 8*2^b*(samplingBallLoss (δ^(-η)) (-10*log δ) b)^2/δ^η ≤ δ^(-ε)
  count : (Nat.ceil (δ^(-b)) : ℝ) ≤ δ^(-b-ε/4)
  cover : (δ^(-b-η)) * (2*J+1) ≤ δ^(-b-ε/4)
  tail : (((2 * Nat.ceil (δ⁻¹+1)+1)^2 * Nat.ceil δ⁻¹ : ℕ) : ℝ) *
    exp (-(-10*log δ)) ≤ δ^η/16

theorem eventually_planarSamplingReady {b f η ε : ℝ} (hb : 0 < b)
    (hη : 0 < η) (hη1 : η ≤ 1) (hmargin : 4*η < ε)
    (J : ℕ) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), PlanarSamplingReady δ b f η ε J := by
  let Cf := exp 1 * (8 : ℝ)^f
  let Cb := exp 1 * (8 : ℝ)^b
  have hp := (tendsto_rpow_neg_nhdsGT_zero (show -(ε-4*η) < 0 by linarith)).eventually
    (eventually_ge_atTop (128*Cf^2))
  have ht := (tendsto_rpow_neg_nhdsGT_zero (show -(ε-3*η) < 0 by linarith)).eventually
    (eventually_ge_atTop (8*2^b*Cb^2))
  have hn := (tendsto_rpow_neg_nhdsGT_zero (show -(ε/4) < 0 by linarith)).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hc := (tendsto_rpow_neg_nhdsGT_zero (show -(ε/4-η) < 0 by linarith)).eventually
    (eventually_ge_atTop (2*J+1 : ℝ))
  filter_upwards [sampling_log_budget hη, hp, ht, hn, hc,
    Ioc_mem_nhdsGT (show (0 : ℝ) < 1/4 by norm_num),
    Ioc_mem_nhdsGT (exp_pos (-1 : ℝ))] with δ hlog hp ht hn hc hδsmall hδexp
  have hδ : 0 < δ := hδsmall.1
  have hδ1 : δ ≤ 1 := hδsmall.2.trans (by norm_num)
  have hB : 1 ≤ -10*log δ := by
    have hh := Real.log_le_log hδ hδexp.2
    rw [Real.log_exp] at hh
    linarith
  have hT (s : ℝ) : 0 < samplingBallLoss (δ^(-η)) (-10*log δ) s :=
    samplingBallLoss_pos (by positivity) hB
  refine ⟨hδ, hδsmall.2, hB, ?_, ?_, ?_, ?_, ?_⟩
  · apply (sampling_point_loss_le hδ (hT f).le (samplingBallLoss_le hlog)).trans
    simpa only [Cf, neg_mul] using rpow_absorb_constant hδ hp
  · apply (sampling_direction_loss_le hδ (hT b).le (samplingBallLoss_le hlog)).trans
    simpa only [Cb, neg_mul] using rpow_absorb_constant hδ ht
  · have hsize := (sampling_ceil_size hδ hδ1 hb.le).2.2
    have hN : (Nat.ceil (δ^(-b)) : ℝ) ≤ 2*δ^(-b) := by
      have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hδ b)).mpr hsize
      simpa only [Real.rpow_neg hδ.le, div_eq_mul_inv] using hh
    apply hN.trans
    have hh := rpow_absorb_constant (t := b) (u := b+ε/4) hδ
      (by simpa only [add_sub_cancel_left] using hn)
    convert hh using 1; ring_nf
  · have hh := rpow_absorb_constant (t := b+η) (u := b+ε/4) hδ
      (by convert hc using 1; ring_nf)
    convert hh using 1 <;> ring_nf
  · apply (sampling_failure_bound hδ hδsmall.2).trans
    apply div_le_div_of_nonneg_right _ (by norm_num)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη1

end Falconer

end OAI

end ExtensionScope55

/- Source: OAI.MeasureTheory.Falconer.Estimates.PlanarGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope56


namespace OAI

/-!
# Planar measure projection gain from the published Furstenberg input

This gives a fixed positive power bound for incidence with small parallel
strip covers. Both coordinate maps may identify original labels. The
conclusion is proved from the cited finite Furstenberg theorem through the
two-stage sampling argument.
-/

namespace Falconer
open Set MeasureTheory
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem planar_measure_projection_gain
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (X W : Type) [MeasurableSpace X] [MeasurableSpace W]
      (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
      (p : X → Space 2) (m : W → ℝ) (E : X → W → Prop),
      Measurable p → Measurable m → MeasurableSet {z : X × W | E z.1 z.2} →
      (∀ x, |p x 0| ≤ 1/4 ∧ |p x 1| ≤ 1/4) → (∀ w, |m w| ≤ 1/2) →
      (∀ c r, δ ≤ r → (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ δ^(-η)*r^f) →
      (∀ a r, δ ≤ r → (ν : Measure W).real {w | |m w-a| ≤ r} ≤ δ^(-η)*r^b) →
    ∀ A : W → Finset ℝ,
      (∀ w, ((A w).card : ℝ) ≤ δ^(-b-η)) →
      (∀ x w, E x w → ∃ a ∈ A w, |p x 1-m w*p x 0-a| ≤ C*δ) →
      (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) ≤ δ^η := by
  obtain ⟨ε, δF, hε, hδF, _, hObs⟩ :=
    planar_measure_incidence_obstruction hpublished hb hb' hbf hf
  obtain ⟨J, hJ⟩ := exists_nat_ge (C+2)
  let η := min (ε/100) (1/2)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hηε : η ≤ ε/100 := min_le_left _ _
  have hmargin : 4*η < ε := by linarith
  have hready := eventually_planarSamplingReady (f := f) hb hη hη1 hmargin J
  obtain ⟨δ₁, hδ₁, hδready⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0 : ℝ) < 1 by norm_num)).mp hready
  refine ⟨η, min δF δ₁, hη, lt_min hδF hδ₁, ?_⟩
  intro δ hδ hδsmall X W _ _ μ ν p m E hp hm hE hpchart hmchart hpball hmball A hA hcover
  have hr : PlanarSamplingReady δ b f η ε J := hδready ⟨hδ, hδsmall.trans_le (min_le_right _ _)⟩
  have hδ1 : δ ≤ 1 := hr.scale_small.trans (by norm_num)
  obtain ⟨hn, hnsize, hnsize'⟩ := sampling_ceil_size hδ hδ1 hb.le
  obtain ⟨hl, hlsize, hlsize'⟩ := sampling_ceil_size hδ hδ1 (hb.trans hbf).le
  by_contra hnot
  have hmean : δ^η ≤ (∫ w, ∫ x, if E x w then (1 : ℝ) else 0
      ∂(μ : Measure X) ∂(ν : Measure W)) := (lt_of_not_ge hnot).le
  apply hObs δ hδ (hδsmall.trans_le (min_le_left _ _)) X W μ ν p m E hp hm hE hpchart hmchart
    (δ^(-η)) (-10*Real.log δ) (δ^η) (Nat.ceil (δ^(-b))) (Nat.ceil (δ^(-f)))
    (Nat.ceil (δ⁻¹+1)) (Nat.ceil δ⁻¹) J A
    (Real.rpow_nonneg hδ.le _) hr.budget (Real.rpow_pos_of_pos hδ _) hn hl
    (Nat.le_ceil _) (Nat.le_ceil _) hnsize hnsize' hlsize hlsize' hpball hmball
    hmean hr.tail hr.point_loss hr.direction_loss hr.count
  · intro w
    calc
      (((A w).card * (2*J+1) : ℕ) : ℝ) = ((A w).card : ℝ)*(2*J+1) := by norm_cast
      _ ≤ δ^(-b-η)*(2*J+1) := mul_le_mul_of_nonneg_right (hA w) (by positivity)
      _ ≤ δ^(-b-ε/4) := hr.cover
  · intro x w hx
    obtain ⟨a, ha, he⟩ := hcover x w hx
    refine ⟨a, ha, he.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith : C ≤ (J : ℝ)-2) hδ.le

end Falconer

end OAI

end ExtensionScope56

/- Source: OAI.MeasureTheory.Falconer.Radial.PlanarUnitTubeGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope57



namespace OAI

/-! # The planar Furstenberg consequence for unit-direction tube covers -/

namespace Falconer
open Set MeasureTheory
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem planar_unit_tube_gain
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (X W : Type) [MeasurableSpace X] [MeasurableSpace W]
      (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
      (p : X → Space 2) (q : W → Space 2) (E : X → W → Prop),
      Measurable p → Measurable q → MeasurableSet {z : X × W | E z.1 z.2} →
      (∀ x, ‖p x‖ ≤ 1/4) → (∀ w, ‖q w‖ = 1) →
      (∀ w, dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
      (∀ c r, δ ≤ r → (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ δ^(-η)*r^f) →
      (∀ c r, δ ≤ r → (ν : Measure W).real {w | dist (q w) c ≤ 2*r} ≤ δ^(-η)*r^b) →
    ∀ (κ : Type) (J : W → Finset κ) (a : κ → Space 2),
      (∀ w, ((J w).card : ℝ) ≤ δ^(-b-η)) →
      (∀ x w, E x w → ∃ i ∈ J w, ‖perpendicularPart (q w) (p x-a i)‖ ≤ C*δ) →
      (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) ≤ δ^η := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := planar_measure_projection_gain hpublished hb hb' hbf hf ((3/2)*C)
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro δ hδ hδsmall X W _ _ μ ν p q E hp hq hE hpbound hqunit hqchart hpball hqball κ J a hJ hcover
  have hpos (w : W) : 0 < q w 0 := (planarSlope_small_of_axis_close (hqchart w)).1
  have hslope (w : W) : |planarSlope (q w)| ≤ 1/2 :=
    (planarSlope_small_of_axis_close (hqchart w)).2
  let A : W → Finset ℝ := fun w => (J w).image (fun i => planarIntercept (q w) (a i))
  refine hgain δ hδ hδsmall X W μ ν p (fun w => planarSlope (q w)) E hp
    (by unfold planarSlope; fun_prop) hE
    (fun x => ⟨(PiLp.norm_apply_le (p x) 0).trans (hpbound x),
      (PiLp.norm_apply_le (p x) 1).trans (hpbound x)⟩) hslope hpball ?_ A ?_ ?_
  · intro c r hr
    exact (measureReal_mono (μ := (ν : Measure W))
      (planar_slope_ball_subset q hqunit hpos c r)).trans (hqball _ r hr)
  · intro w
    exact (Nat.cast_le.mpr (Finset.card_image_le)).trans (hJ w)
  · intro x w hx
    obtain ⟨i,hi,ht⟩ := hcover x w hx
    refine ⟨planarIntercept (q w) (a i),Finset.mem_image.mpr ⟨i,hi,rfl⟩,?_⟩
    simpa only [mul_assoc] using planar_tube_strip (hpos w).ne' (hslope w) ht

end Falconer

end OAI

end ExtensionScope57

/- Source: OAI.MeasureTheory.Falconer.Geometry.PlanarChartRepair. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope58


namespace OAI

/-! # Choosing bounded representatives of almost-everywhere planar chart maps -/

namespace Falconer
open Set MeasureTheory

noncomputable def boundedPlanarPoint (x : Space 2) : Space 2 :=
  if ‖x‖ ≤ 1/4 then x else 0

noncomputable def chartedPlanarDirection (w : Space 2) : Space 2 :=
  if ‖w‖ = 1 ∧ dist w (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 then w
  else EuclideanSpace.basisFun (Fin 2) ℝ 0

theorem boundedPlanarPoint_measurable : Measurable boundedPlanarPoint := by
  apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_id measurable_const

theorem chartedPlanarDirection_measurable : Measurable chartedPlanarDirection := by
  have hn : Measurable (fun w : Space 2 => ‖w‖) := continuous_norm.measurable
  have hd : Measurable (fun w : Space 2 => dist w (EuclideanSpace.basisFun (Fin 2) ℝ 0)) :=
    (continuous_id.dist continuous_const).measurable
  have hQ : MeasurableSet {w : Space 2 | ‖w‖ = 1 ∧
      dist w (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4} :=
    (measurableSet_eq_fun hn measurable_const).inter
      (measurableSet_le hd measurable_const)
  exact Measurable.ite hQ measurable_id measurable_const

theorem boundedPlanarPoint_norm (x : Space 2) : ‖boundedPlanarPoint x‖ ≤ 1/4 := by
  unfold boundedPlanarPoint
  split_ifs with hx
  · exact hx
  · simp

theorem chartedPlanarDirection_unit (w : Space 2) : ‖chartedPlanarDirection w‖ = 1 := by
  unfold chartedPlanarDirection
  split_ifs with hw
  · exact hw.1
  · exact (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one 0

theorem chartedPlanarDirection_chart (w : Space 2) :
    dist (chartedPlanarDirection w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 := by
  unfold chartedPlanarDirection
  split_ifs with hw
  · exact hw.2
  · simp

theorem boundedPlanarPoint_eq {x : Space 2} (hx : ‖x‖ ≤ 1/4) : boundedPlanarPoint x = x :=
  ite_eq_left hx

theorem chartedPlanarDirection_eq {w : Space 2}
    (hw : ‖w‖ = 1 ∧ dist w (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) :
    chartedPlanarDirection w = w := ite_eq_left hw

end Falconer

end OAI

end ExtensionScope58

/- Source: OAI.MeasureTheory.Falconer.Radial.PlanarAETubeGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope59



namespace OAI

/-! # The planar tube gain on the actual supports of the two laws -/

namespace Falconer
open Set MeasureTheory
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem planar_ae_tube_gain
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (X W : Type) [MeasurableSpace X] [MeasurableSpace W]
      (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
      (p : X → Space 2) (q : W → Space 2) (E : X → W → Prop),
      Measurable p → Measurable q → MeasurableSet {z : X × W | E z.1 z.2} →
      (∀ᵐ x ∂(μ : Measure X), ‖p x‖ ≤ 1/4) →
      (∀ᵐ w ∂(ν : Measure W), ‖q w‖ = 1 ∧
        dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
      (∀ c r, δ ≤ r → (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ δ^(-η)*r^f) →
      (∀ c r, δ ≤ r → (ν : Measure W).real {w | dist (q w) c ≤ 2*r} ≤ δ^(-η)*r^b) →
    ∀ (κ : Type) (J : W → Finset κ) (a : κ → Space 2),
      (∀ w, ((J w).card : ℝ) ≤ δ^(-b-η)) →
      (∀ x w, E x w → ∃ i ∈ J w, ‖perpendicularPart (q w) (p x-a i)‖ ≤ C*δ) →
      (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) ≤ δ^η := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := planar_unit_tube_gain hpublished hb hb' hbf hf C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro δ hδ hδsmall X W _ _ μ ν p q E hp hq hE hpb hqb hpball hqball κ J a hJ hcover
  let F : X → W → Prop := fun x w => E x w ∧ ‖p x‖ ≤ 1/4 ∧
    (‖q w‖ = 1 ∧ dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4)
  have hP : MeasurableSet {x | ‖p x‖ ≤ 1/4} := measurableSet_le hp.norm measurable_const
  have hQ : MeasurableSet {w | ‖q w‖ = 1 ∧
      dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4} :=
    (measurableSet_eq_fun hq.norm measurable_const).inter
      (measurableSet_le (hq.dist measurable_const) measurable_const)
  have hF : MeasurableSet {z : X × W | F z.1 z.2} :=
    hE.inter ((hP.preimage measurable_fst).inter (hQ.preimage measurable_snd))
  have hpb' (c : Space 2) (r : ℝ) (hr : δ ≤ r) :
      (μ : Measure X).real {x | dist (boundedPlanarPoint (p x)) c ≤ r} ≤ δ^(-η)*r^f := by
    have he : {x | dist (boundedPlanarPoint (p x)) c ≤ r} =ᵐ[(μ : Measure X)]
        {x | dist (p x) c ≤ r} := by
      filter_upwards [hpb] with x hx
      simp only [boundedPlanarPoint_eq hx]
    rw [measureReal_congr he]
    exact hpball c r hr
  have hqb' (c : Space 2) (r : ℝ) (hr : δ ≤ r) :
      (ν : Measure W).real {w | dist (chartedPlanarDirection (q w)) c ≤ 2*r} ≤ δ^(-η)*r^b := by
    have he : {w | dist (chartedPlanarDirection (q w)) c ≤ 2*r} =ᵐ[(ν : Measure W)]
        {w | dist (q w) c ≤ 2*r} := by
      filter_upwards [hqb] with w hw
      simp only [chartedPlanarDirection_eq hw]
    rw [measureReal_congr he]
    exact hqball c r hr
  have hsmall : (∫ w, ∫ x, @ite ℝ (F x w) (Classical.propDecidable (F x w)) 1 0
      ∂(μ : Measure X) ∂(ν : Measure W)) ≤ δ^η := by
    apply hgain δ hδ hδsmall X W μ ν (fun x => boundedPlanarPoint (p x))
      (fun w => chartedPlanarDirection (q w)) F
      (boundedPlanarPoint_measurable.comp hp) (chartedPlanarDirection_measurable.comp hq) hF
      (fun x => boundedPlanarPoint_norm (p x)) (fun w => chartedPlanarDirection_unit (q w))
      (fun w => chartedPlanarDirection_chart (q w)) hpb' hqb' κ J a hJ
    intro x w hx
    obtain ⟨i,hi,ht⟩ := hcover x w hx.1
    refine ⟨i,hi,?_⟩
    rw [boundedPlanarPoint_eq hx.2.1,chartedPlanarDirection_eq hx.2.2]
    exact ht
  have he : (∫ w, ∫ x, @ite ℝ (F x w) (Classical.propDecidable (F x w)) 1 0
      ∂(μ : Measure X) ∂(ν : Measure W)) =
      (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) := by
    apply integral_congr_ae
    filter_upwards [hqb] with w hw
    apply integral_congr_ae
    filter_upwards [hpb] with x hx
    simp only [F,hx,hw,and_true]
  rw [he] at hsmall
  exact hsmall

end Falconer

end OAI

end ExtensionScope59

/- Source: OAI.MeasureTheory.Falconer.Slicing.SliceBallTransfer. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope60


namespace OAI

/-! # Ball estimates for the actual point and direction slice coordinates -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem pointSlice_projection_ball_bound (V : Submodule ℝ (Space d))
    (μ : Measure (Space d)) (z : Space d) {δ K s : ℝ} (hδ : 0 ≤ δ)
    (hsupport : ∀ᵐ x ∂μ, x ∈ pointSliceBand V z δ)
    (hball : ∀ x : Space d, ∀ r : ℝ, δ ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s))
    (a : Space d) {r : ℝ} (hr : δ ≤ r) :
    (Measure.map V.starProjection μ) (ball a r) ≤ ENNReal.ofReal (K*(2*r)^s) := by
  rw [Measure.map_apply V.starProjection.continuous.measurable measurableSet_ball]
  apply (measure_mono_ae ?_).trans (hball (a+z) (2*r) (by linarith))
  filter_upwards [hsupport] with x hx
  intro hxa
  have ha : ‖V.starProjection x-a‖ < r := by
    simpa only [mem_preimage,mem_ball,dist_eq_norm] using hxa
  have he : x-(a+z) = (V.starProjection x-a)+(Vᗮ.starProjection x-z) := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  change ‖x-(a+z)‖ < 2*r
  rw [he]
  have hb : ‖Vᗮ.starProjection x-z‖ ≤ δ := hx
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem normalizedSlice_projection_ball_bound (V : Submodule ℝ (Space d))
    (ν : Measure (Sphere d)) {δ K s : ℝ} (hδ : δ < 1)
    (hsupport : ∀ᵐ w ∂ν, w ∈ directionSliceBand V δ)
    (hball : ∀ a : Space d, ∀ r : ℝ, δ ≤ r →
      ν {w : Sphere d | dist (w:Space d) a < r} ≤ ENNReal.ofReal (K*r^s))
    (a : Space d) {r : ℝ} (hr : δ ≤ r) (hr₀ : 0 ≤ r) :
    (Measure.map (fun w : Sphere d => normalize (V.starProjection (w:Space d))) ν) (ball a r) ≤
      ENNReal.ofReal (K*(3*r)^s) := by
  have hm : Measurable (fun w : Sphere d => normalize (V.starProjection (w:Space d))) := by
    unfold NormedSpace.normalize
    fun_prop
  rw [Measure.map_apply hm measurableSet_ball]
  apply (measure_mono_ae ?_).trans (hball a (3*r) (by linarith))
  filter_upwards [hsupport] with w hw
  intro hwa
  have hh := directionSliceBand_normalize_error V hδ hw
  have ha : ‖normalize (V.starProjection (w:Space d))-a‖ < r := by
    simpa only [mem_preimage,mem_ball,dist_eq_norm] using hwa
  change ‖(w:Space d)-a‖ < 3*r
  have he := norm_sub_le_norm_sub_add_norm_sub (w:Space d)
    (normalize (V.starProjection (w:Space d))) a
  have hh' : ‖(w:Space d)-normalize (V.starProjection (w:Space d))‖ ≤ 2*δ := by
    simpa only [norm_sub_rev] using hh
  linarith

end Falconer

end OAI

end ExtensionScope60

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianKernelCoordinates. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope61



namespace OAI

/-! # Metric control in the kernel coordinates of a Gaussian slice -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d h : ℕ}

theorem gaussian_point_kernel_pair_distance (A : Fin h → Space d) (z : Space h)
    {K r s : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    {x y : Space d} (hx : x ∈ gaussianPointBand A z r) (hy : y ∈ gaussianPointBand A z r)
    (hxy : ‖(gaussianRowMap A).ker.starProjection x-
      (gaussianRowMap A).ker.starProjection y‖ ≤ s) :
    ‖x-y‖ ≤ s+K*((h:ℝ)*(2*r)) := by
  have he : x-y = (gaussianRowMap A).ker.starProjection (x-y)+
      (gaussianRowMap A).kerᗮ.starProjection (x-y) := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  calc
    _ ≤ ‖(gaussianRowMap A).ker.starProjection (x-y)‖+
        ‖(gaussianRowMap A).kerᗮ.starProjection (x-y)‖ := by
      conv_lhs => rw [he]
      exact norm_add_le _ _
    _ ≤ _ := add_le_add (by simpa only [map_sub] using hxy)
      (gaussian_point_band_kernel_difference A z hK hbound hx hy)

theorem gaussian_direction_kernel_normalize_error (A : Fin h → Space d)
    {K r : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hr : K*((h:ℝ)*r) < 1) {w : Sphere d} (hw : w ∈ gaussianDirectionBand A r) :
    ‖normalize ((gaussianRowMap A).ker.starProjection (w:Space d))-(w:Space d)‖ ≤
      2*(K*((h:ℝ)*r)) :=
  directionSliceBand_normalize_error _ hr (gaussian_direction_band_kernel_distance A hK hbound hw)

theorem gaussian_direction_kernel_nonzero (A : Fin h → Space d)
    {K r : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hr : K*((h:ℝ)*r) < 1) {w : Sphere d} (hw : w ∈ gaussianDirectionBand A r) :
    (gaussianRowMap A).ker.starProjection (w:Space d) ≠ 0 := by
  apply norm_pos_iff.mp
  exact (sub_pos.mpr hr).trans_le (directionSliceBand_projection_lower _
    (gaussian_direction_band_kernel_distance A hK hbound hw))

end Falconer

end OAI

end ExtensionScope61

/- Source: OAI.MeasureTheory.Falconer.Slicing.SliceTubeGeometry. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope62



namespace OAI

/-! # Original tube anchors and projected tube widths in an orthogonal slice -/

namespace Falconer
open NormedSpace
variable {d : ℕ}

theorem slice_active_anchor (V : Submodule ℝ (Space d)) {w : Sphere d}
    {x a z : Space d} {δ ε L : ℝ} (_hδ : 0 ≤ δ)
    (hw : w ∈ directionSliceBand V δ) (hx : x ∈ pointSliceBand V z δ)
    (htube : ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε)
    (hlength : |inner ℝ (w:Space d) (x-a)| ≤ L) :
    ‖Vᗮ.starProjection a-z‖ ≤ δ+L*δ+ε := by
  let t := inner ℝ (w:Space d) (x-a)
  let e := perpendicularPart (w:Space d) (x-a)
  have he : a = x-t • (w:Space d)-e := by dsimp [t,e,perpendicularPart]; module
  have he' : Vᗮ.starProjection a-z = (Vᗮ.starProjection x-z)-
      t • Vᗮ.starProjection (w:Space d)-Vᗮ.starProjection e := by
    rw [he,map_sub,map_sub,map_smul]
    abel
  have ht : ‖t • Vᗮ.starProjection (w:Space d)‖ ≤ L*δ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hlength hw (norm_nonneg _) ((abs_nonneg _).trans hlength)
  have heps : ‖Vᗮ.starProjection e‖ ≤ ε :=
    (Vᗮ.norm_starProjection_apply_le e).trans htube
  rw [he']
  calc
    _ ≤ (‖Vᗮ.starProjection x-z‖+‖t • Vᗮ.starProjection (w:Space d)‖)+
        ‖Vᗮ.starProjection e‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add hx ht) heps

theorem slice_projected_tube_width (V : Submodule ℝ (Space d)) {w : Sphere d}
    {δ : ℝ} (hδ : δ < 1) (hw : w ∈ directionSliceBand V δ) (x a : Space d) :
    ‖perpendicularPart (normalize (V.starProjection (w:Space d)))
      (V.starProjection x-V.starProjection a)‖ ≤ ‖perpendicularPart (w:Space d) (x-a)‖ := by
  let v := V.starProjection (w:Space d)
  let u := normalize v
  let t := inner ℝ (w:Space d) (x-a)
  let e := perpendicularPart (w:Space d) (x-a)
  have hv : v ≠ 0 := norm_pos_iff.mp
    ((sub_pos.mpr hδ).trans_le (directionSliceBand_projection_lower V hw))
  have hu : ‖u‖ = 1 := norm_normalize hv
  have hperp : perpendicularPart u v = 0 := by
    have hv' : v = ‖v‖ • u := (norm_smul_normalize v).symm
    rw [hv',perpendicularPart_smul]
    simp [perpendicularPart,hu]
  have hsplit : V.starProjection x-V.starProjection a = t • v+V.starProjection e := by
    dsimp [v,t,e,perpendicularPart]
    simp only [map_sub,map_smul]
    module
  change ‖perpendicularPart u (V.starProjection x-V.starProjection a)‖ ≤ ‖e‖
  rw [hsplit]
  have he : perpendicularPart u (t • v+V.starProjection e) = perpendicularPart u (V.starProjection e) := by
    calc
      _ = t • perpendicularPart u v+perpendicularPart u (V.starProjection e) := by
        simp only [perpendicularPart,inner_add_right,inner_smul_right,add_smul]
        module
      _ = _ := by rw [hperp,smul_zero,zero_add]
  rw [he]
  exact (norm_perpendicularPart_le hu _).trans (V.norm_starProjection_apply_le e)

end Falconer

end OAI

end ExtensionScope62

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianTubeGeometry. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope63



namespace OAI

/-! # Original tube labels and active anchors for Gaussian row slices -/

namespace Falconer
variable {d h : ℕ}

theorem gaussian_active_anchor (A : Fin h → Space d) (z : Space h)
    {w : Sphere d} {x a : Space d} {δ ε L M : ℝ} (_hM : 0 ≤ M)
    (hA : ∀ i, ‖A i‖ ≤ M) (hw : w ∈ gaussianDirectionBand A δ)
    (hx : x ∈ gaussianPointBand A z δ)
    (htube : ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε)
    (hlength : |inner ℝ (w:Space d) (x-a)| ≤ L) :
    a ∈ gaussianPointBand A z (δ+L*δ+ε*M) := by
  let t := inner ℝ (w:Space d) (x-a)
  let e := perpendicularPart (w:Space d) (x-a)
  have he : a = x-t • (w:Space d)-e := by dsimp [t,e,perpendicularPart]; module
  intro i
  have hi : inner ℝ a (A i)-z i =
      (inner ℝ x (A i)-z i)-t*inner ℝ (w:Space d) (A i)-inner ℝ e (A i) := by
    rw [he,inner_sub_left,inner_sub_left,real_inner_smul_left]
    ring
  have ht : |t*inner ℝ (w:Space d) (A i)| ≤ L*δ := by
    rw [abs_mul]
    exact mul_le_mul hlength (hw i) (abs_nonneg _) ((abs_nonneg _).trans hlength)
  have hp : |inner ℝ e (A i)| ≤ ε*M :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul htube (hA i) (norm_nonneg _)
      ((norm_nonneg _).trans htube))
  rw [hi]
  exact ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
    (add_le_add (add_le_add (hx i) ht) hp)

theorem gaussian_projected_tube_width (A : Fin h → Space d)
    {w : Sphere d} {δ K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hδ : K*((h:ℝ)*δ) < 1) (hw : w ∈ gaussianDirectionBand A δ) (x a : Space d) :
    ‖perpendicularPart (NormedSpace.normalize ((gaussianRowMap A).ker.starProjection (w:Space d)))
      ((gaussianRowMap A).ker.starProjection x-(gaussianRowMap A).ker.starProjection a)‖ ≤
      ‖perpendicularPart (w:Space d) (x-a)‖ :=
  slice_projected_tube_width _ hδ (gaussian_direction_band_kernel_distance A hK hbound hw) x a

end Falconer

end OAI

end ExtensionScope63

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianActiveCover. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope64



namespace OAI

/-! # The projected fiber cover keeps the original direction label -/

namespace Falconer
open Set NormedSpace
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

noncomputable def gaussianActiveAnchors (A : Fin h → Space d) (z : Space h)
    (J : Finset ι) (a : ι → Space d) (R : ℝ) : Finset ι := by
  classical
  exact J.filter (fun i => a i ∈ gaussianPointBand A z R)

theorem gaussianActiveAnchors_card (A : Fin h → Space d) (z : Space h)
    (J : Finset ι) (a : ι → Space d) (R : ℝ) :
    (gaussianActiveAnchors A z J a R).card = gaussianActiveAnchorCount A J a R z := rfl

theorem gaussian_active_fiber_cover (A : Fin h → Space d) (z : Space h)
    (J : Finset ι) (a : ι → Space d) (E : Set (Space d)) (w : Sphere d)
    {δ ε L M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hA : ∀ i, ‖A i‖ ≤ M)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1) (hw : w ∈ gaussianDirectionBand A δ)
    (hcover : ∀ x ∈ E, ∃ i ∈ J,
      ‖perpendicularPart (w:Space d) (x-a i)‖ ≤ ε ∧ |inner ℝ (w:Space d) (x-a i)| ≤ L) :
    ∀ x ∈ E ∩ gaussianPointBand A z δ,
      ∃ i ∈ gaussianActiveAnchors A z J a (δ+L*δ+ε*M),
        ‖perpendicularPart (normalize ((gaussianRowMap A).ker.starProjection (w:Space d)))
          ((gaussianRowMap A).ker.starProjection x-(gaussianRowMap A).ker.starProjection (a i))‖ ≤ ε := by
  classical
  intro x hx
  obtain ⟨i,hi,hperp,hlength⟩ := hcover x hx.1
  refine ⟨i,?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨hi,gaussian_active_anchor A z hM hA hw hx.2 hperp hlength⟩
  · exact (gaussian_projected_tube_width A hK hbound hsmall hw x (a i)).trans hperp

end Falconer

end OAI

end ExtensionScope64

/- Source: OAI.MeasureTheory.Falconer.Slicing.OrientedSlice. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope65



namespace OAI

/-! # Isometric slice coordinates aligned with the center of a direction chart -/

namespace Falconer
open NormedSpace
variable {d m : ℕ}

theorem slice_isometry_normalize (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (x : V) : e (normalize x) = normalize (e x) := by
  simp only [NormedSpace.normalize,map_smul,e.norm_map]

theorem slice_isometry_perpendicular (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (w x : V) :
    e (perpendicularPart w x) = perpendicularPart (e w) (e x) := by
  simp only [perpendicularPart,map_sub,map_smul,e.inner_map_map]

theorem exists_oriented_slice_coordinates (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (hmpos : 0 < m) (w₀ : Space d)
    (hw₀ : V.starProjection w₀ ≠ 0) :
    ∃ e : V ≃ₗᵢ[ℝ] Space m,
      normalize (e (V.orthogonalProjectionOnto w₀)) =
        EuclideanSpace.basisFun (Fin m) ℝ ⟨0,hmpos⟩ := by
  let e₀ := sliceCoordinates V hm
  have hv : e₀ (V.orthogonalProjectionOnto w₀) ≠ 0 := by
    intro hzero
    have hp : V.orthogonalProjectionOnto w₀ = 0 := e₀.injective (by simpa using hzero)
    exact hw₀ (congrArg Subtype.val hp)
  obtain ⟨R,hR⟩ := exists_unit_axis_isometry hmpos (norm_normalize hv)
  refine ⟨e₀.trans R,?_⟩
  change normalize (R (e₀ (V.orthogonalProjectionOnto w₀))) = _
  have hRN (v : Space m) : R (normalize v) = normalize (R v) := by
    simp only [NormedSpace.normalize,map_smul,R.norm_map]
  rw [← hRN]
  exact hR

theorem oriented_slice_direction_distance (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) {w w₀ : Sphere d} {δ δ₀ ρ : ℝ}
    (hδ : δ < 1) (hδ₀ : δ₀ < 1)
    (hw : w ∈ directionSliceBand V δ) (hw₀ : w₀ ∈ directionSliceBand V δ₀)
    (hclose : dist (w:Space d) (w₀:Space d) ≤ ρ) :
    dist (normalize (e (V.orthogonalProjectionOnto (w:Space d))))
      (normalize (e (V.orthogonalProjectionOnto (w₀:Space d)))) ≤ 2*δ+ρ+2*δ₀ := by
  rw [← slice_isometry_normalize V e,← slice_isometry_normalize V e,e.dist_map,dist_eq_norm]
  change ‖normalize (V.starProjection (w:Space d))-
    normalize (V.starProjection (w₀:Space d))‖ ≤ _
  calc
    _ ≤ ‖normalize (V.starProjection (w:Space d))-(w:Space d)‖+
        ‖(w:Space d)-normalize (V.starProjection (w₀:Space d))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2*δ+(‖(w:Space d)-(w₀:Space d)‖+
        ‖(w₀:Space d)-normalize (V.starProjection (w₀:Space d))‖) :=
      add_le_add (directionSliceBand_normalize_error V hδ hw)
        (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ 2*δ+(ρ+2*δ₀) := add_le_add le_rfl
      (add_le_add hclose (by simpa only [norm_sub_rev] using
        directionSliceBand_normalize_error V hδ₀ hw₀))
    _ = _ := by ring

theorem oriented_slice_tube_width (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) {w : Sphere d} {δ : ℝ}
    (hδ : δ < 1) (hw : w ∈ directionSliceBand V δ) (x a : Space d) :
    ‖perpendicularPart (normalize (e (V.orthogonalProjectionOnto (w:Space d))))
      (e (V.orthogonalProjectionOnto x)-e (V.orthogonalProjectionOnto a))‖ ≤
      ‖perpendicularPart (w:Space d) (x-a)‖ := by
  rw [← slice_isometry_normalize V e,← map_sub,← slice_isometry_perpendicular V e,e.norm_map]
  exact slice_projected_tube_width V hδ hw x a

end Falconer

end OAI

end ExtensionScope65

/- Source: OAI.MeasureTheory.Falconer.Geometry.TubeAnchorNet. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope66




namespace OAI

/-! # Finite bounded anchor nets for the original direction-wise tube covers -/

namespace Falconer
open Set Metric
variable {d : ℕ}

theorem exists_bounded_anchor_net (D : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset (Space d), (∀ a ∈ S, ‖a‖ ≤ D) ∧
      ∀ x : Space d, ‖x‖ ≤ D → ∃ a ∈ S, ‖x-a‖ ≤ δ := by
  classical
  obtain ⟨T,hT,hfin,hcover⟩ := (isCompact_closedBall (0 : Space d) D).finite_cover_balls hδ
  refine ⟨hfin.toFinset,?_,?_⟩
  · intro a ha
    simpa only [mem_closedBall,dist_zero_right] using hT (hfin.mem_toFinset.mp ha)
  · intro x hx
    have hxc : x ∈ closedBall (0 : Space d) D := by simpa only [mem_closedBall,dist_zero_right] using hx
    obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (hcover hxc)
    refine ⟨a,hfin.mem_toFinset.mpr ha,?_⟩
    simpa only [mem_ball,dist_eq_norm] using hxa.le

theorem perpendicular_anchor_rounding {w x a y b : Space d} (hw : ‖w‖ = 1)
    {ε δ : ℝ} (hx : ‖perpendicularPart w (x-a)‖ ≤ ε)
    (hy : ‖perpendicularPart w (y-a)‖ ≤ ε) (hb : ‖y-b‖ ≤ δ) :
    ‖perpendicularPart w (x-b)‖ ≤ 2*ε+δ := by
  have he : perpendicularPart w (x-b) =
      (perpendicularPart w (x-a)-perpendicularPart w (y-a))+perpendicularPart w (y-b) := by
    simp only [perpendicularPart,inner_sub_right]
    module
  rw [he]
  exact (norm_add_le _ _).trans
    (((add_le_add (norm_sub_le _ _) (norm_perpendicularPart_le hw _)).trans
      (add_le_add (add_le_add hx hy) hb)).trans_eq (by ring))

theorem bounded_anchor_longitudinal (w : Sphere d) {x a : Space d} {D : ℝ}
    (hx : ‖x‖ ≤ D) (ha : ‖a‖ ≤ D) : |inner ℝ (w:Space d) (x-a)| ≤ 2*D := by
  calc
    _ ≤ ‖(w:Space d)‖*‖x-a‖ := abs_real_inner_le_norm _ _
    _ = ‖x-a‖ := by rw [sphere_norm,one_mul]
    _ ≤ ‖x‖+‖a‖ := norm_sub_le _ _
    _ ≤ 2*D := by linarith

theorem rounded_tube_cover (w : Sphere d) (E : Set (Space d))
    (S G : Finset (Space d)) {ε δ : ℝ}
    (hnet : ∀ x ∈ E, ∃ b ∈ G, ‖x-b‖ ≤ δ)
    (hcover : ∀ x ∈ E, ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ J : Finset (Space d), J ⊆ G ∧ J.card ≤ S.card ∧
      ∀ x ∈ E, ∃ b ∈ J, ‖perpendicularPart (w:Space d) (x-b)‖ ≤ 2*ε+δ := by
  classical
  let P := fun a : Space d => ∃ y ∈ E, ‖perpendicularPart (w:Space d) (y-a)‖ ≤ ε
  have hround (a : Space d) (ha : P a) :
      ∃ b ∈ G, ∀ x ∈ E, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε →
        ‖perpendicularPart (w:Space d) (x-b)‖ ≤ 2*ε+δ := by
    obtain ⟨y,hy,hya⟩ := ha
    obtain ⟨b,hb,hyb⟩ := hnet y hy
    exact ⟨b,hb,fun _ _ hx => perpendicular_anchor_rounding (sphere_norm w) hx hya hyb⟩
  let b : Space d → Space d := fun a => if ha : P a then (hround a ha).choose else 0
  let J := (S.filter P).image b
  refine ⟨J,?_,(Finset.card_image_le.trans (Finset.card_filter_le _ _)),?_⟩
  · intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    have hp := (Finset.mem_filter.mp ha).2
    simpa only [b,dite_eq_left hp] using (hround a hp).choose_spec.1
  · intro x hx
    obtain ⟨a,ha,hxa⟩ := hcover x hx
    have hp : P a := ⟨x,hx,hxa⟩
    refine ⟨b a,Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hp⟩,rfl⟩,?_⟩
    simpa only [b,dite_eq_left hp] using (hround a hp).choose_spec.2 x hx hxa

end Falconer

end OAI

end ExtensionScope66

/- Source: OAI.MeasureTheory.Falconer.Angular.CappedActiveCover. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope67




namespace OAI

/-! # Bounded anchor lists for every original direction label -/

namespace Falconer
open Set NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {κ : Type*}

noncomputable def cappedActiveAnchors (A : Fin h → Space d) (z : Space h)
    (J : Finset κ) (a : κ → Space d) (R t : ℝ) : Finset κ :=
  if ((gaussianActiveAnchors A z J a R).card : ℝ) ≤ t then
    gaussianActiveAnchors A z J a R else ∅

theorem cappedActiveAnchors_card (A : Fin h → Space d) (z : Space h)
    (J : Finset κ) (a : κ → Space d) (R : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ((cappedActiveAnchors A z J a R t).card : ℝ) ≤ t := by
  unfold cappedActiveAnchors
  split_ifs with hc
  · exact hc
  · simpa only [Finset.card_empty,Nat.cast_zero] using ht

theorem cappedActiveAnchors_eq (A : Fin h → Space d) (z : Space h)
    (J : Finset κ) (a : κ → Space d) (R : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hc : (gaussianActiveAnchorCount A J a R z : ℝ≥0∞) ≤ ENNReal.ofReal t) :
    cappedActiveAnchors A z J a R t = gaussianActiveAnchors A z J a R := by
  apply ite_eq_left
  apply (ENNReal.ofReal_le_ofReal_iff ht).mp
  simpa only [ENNReal.ofReal_natCast,gaussianActiveAnchors_card] using hc

theorem gaussian_capped_coordinate_cover
    (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ) (a : κ → Space d)
    {δ ε D M K t : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hA : ∀ i, ‖A i‖ ≤ M)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1)
    (hbounded : ∀ u ∈ E, ‖u.1‖ ≤ D)
    (hanchor : ∀ w, ∀ i ∈ J w, ‖a i‖ ≤ D)
    (hcover : ∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-a i)‖ ≤ ε)
    {x : Space d} {w : Sphere d}
    (hx : x ∈ gaussianPointBand A z δ) (hw : w ∈ gaussianDirectionBand A δ)
    (hE : ((A,z),(x,w)) ∈ gaussianActiveRelation E J a (δ+(2*D)*δ+ε*M) (ENNReal.ofReal t) true) :
    ∃ i ∈ cappedActiveAnchors A z (J w) a (δ+(2*D)*δ+ε*M) t,
      ‖perpendicularPart (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)-
          e ((gaussianRowMap A).ker.orthogonalProjectionOnto (a i)))‖ ≤ ε := by
  classical
  obtain ⟨i,hi,hperp⟩ := hcover (x,w) hE.1
  have hlength := bounded_anchor_longitudinal (w := w) (hbounded (x,w) hE.1) (hanchor w i hi)
  have hactive : i ∈ gaussianActiveAnchors A z (J w) a (δ+(2*D)*δ+ε*M) :=
    Finset.mem_filter.mpr ⟨hi,gaussian_active_anchor A z hM hA hw hx hperp hlength⟩
  refine ⟨i,?_,?_⟩
  · rw [cappedActiveAnchors_eq A z (J w) a _ ht hE.2]
    exact hactive
  · exact (oriented_slice_tube_width (gaussianRowMap A).ker e hsmall
      (gaussian_direction_band_kernel_distance A hK hbound hw) x (a i)).trans hperp

end Falconer

end OAI

end ExtensionScope67

/- Source: OAI.MeasureTheory.Falconer.Slicing.SliceIncidence. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope68



namespace OAI

/-! # The real incidence integral of the normalized original slice laws -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem slice_iterated_incidence (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (E : Set (X × Y)) (hE : MeasurableSet E) :
    (∫ y, ∫ x, if (x,y) ∈ E then (1 : ℝ) else 0 ∂μ ∂ν) = (μ.prod ν).real E := by
  have hi : Integrable (E.indicator (fun _ : X × Y => (1 : ℝ))) (μ.prod ν) :=
    (integrable_const 1).indicator hE
  have he := integral_prod_symm (E.indicator (fun _ : X × Y => (1 : ℝ))) hi
  rw [integral_indicator_const (1 : ℝ) hE,smul_eq_mul,mul_one] at he
  exact he.symm

theorem normalized_slice_iterated_incidence (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ univ ≠ 0) (hν : ν univ ≠ 0)
    (E : Set (X × Y)) (hE : MeasurableSet E) :
    (∫ y, ∫ x, if (x,y) ∈ E then (1 : ℝ) else 0
      ∂(normalizedSliceLaw μ hμ : Measure X) ∂(normalizedSliceLaw ν hν : Measure Y)) =
      ((μ univ*ν univ)⁻¹*(μ.prod ν) E).toReal := by
  rw [slice_iterated_incidence _ _ E hE,Measure.real,normalizedSliceLaw_incidence]

end Falconer

end OAI

end ExtensionScope68

/- Source: OAI.MeasureTheory.Falconer.Estimates.PlanarSelectedGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope69




namespace OAI

/-! # Applying the published planar consequence to a selected original-label slice -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal Topology
variable {d h : ℕ} {κ : Type*}

def selectedActiveRelation (A : Fin h → Space d) (z : Space h) (δ : ℝ)
    (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ) (a : κ → Space d)
    (R T : ℝ) : Set (Space d × Sphere d) :=
  {u | ((A,z),u) ∈ gaussianActiveRelation E J a R (ENNReal.ofReal T) true} ∩
    (gaussianPointBand A z δ ×ˢ gaussianDirectionBand A δ)

theorem selectedActiveRelation_measurable [Fintype κ] [DecidableEq κ]
    (A : Fin h → Space d) (z : Space h) (δ : ℝ)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space d) (R T : ℝ) :
    MeasurableSet (selectedActiveRelation A z δ E J a R T) := by
  have hs := (gaussianActiveRelation_measurable E hE J hJ a R (ENNReal.ofReal T) true).preimage
    (show Measurable (fun u : Space d × Sphere d => ((A,z),u)) from by fun_prop)
  exact hs.inter ((gaussianPointBand_measurable A z δ).prod (gaussianDirectionBand_measurable A δ))

theorem planar_selected_slice_gain
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (d h : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (A : Fin h → Space d) (z : Space h) (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 2)
      (α : ProbabilityMeasure (Space d)) (β : ProbabilityMeasure (Sphere d))
      (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ) (a : κ → Space d)
      (M K T : ℝ),
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    0 ≤ M → 0 ≤ K → 0 ≤ T → T ≤ δ^(-b-η) →
    (∀ i, ‖A i‖ ≤ M) →
    (∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖) →
    K*((h:ℝ)*δ) < 1 →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-a i)‖ ≤ C*δ) →
    (∀ᵐ x ∂(α : Measure (Space d)), ‖x‖ ≤ 1/4) →
    (∀ᵐ w : Sphere d ∂(β : Measure (Sphere d)),
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
    (∀ c r, δ ≤ r → (α : Measure (Space d)).real
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ r} ≤ δ^(-η)*r^f) →
    (∀ c r, δ ≤ r → (β : Measure (Sphere d)).real
      {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ 2*r}
        ≤ δ^(-η)*r^b) →
    ((α : Measure (Space d)).prod (β : Measure (Sphere d))).real
      (selectedActiveRelation A z δ E J a (δ+(2*(1/4))*δ+(C*δ)*M) T) ≤ δ^η := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := planar_ae_tube_gain hpublished hb hb' hbf hf C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro δ hδ hδsmall d h κ _ _ A z e α β E J a M K T hE hJ hM hK hT hTbound
    hA hbound hsmall hbounded hanchors hcover hα hβ hpball hqball
  let R := δ+(2*(1/4))*δ+(C*δ)*M
  let F := selectedActiveRelation A z δ E J a R T
  have hF : MeasurableSet F := selectedActiveRelation_measurable A z δ E hE J hJ a R T
  rw [← slice_iterated_incidence (α : Measure (Space d)) (β : Measure (Sphere d)) F hF]
  refine hgain δ hδ hδsmall (Space d) (Sphere d) α β
    (fun x => e ((gaussianRowMap A).ker.orthogonalProjectionOnto x))
    (fun w : Sphere d => normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
    (fun x w => (x,w) ∈ F) (by fun_prop)
    (by unfold NormedSpace.normalize; fun_prop) hF ?_ hβ hpball hqball κ
    (fun w => cappedActiveAnchors A z (J w) a R T)
    (fun i => e ((gaussianRowMap A).ker.orthogonalProjectionOnto (a i))) ?_ ?_
  · filter_upwards [hα] with x hx
    rw [e.norm_map]
    exact ((gaussianRowMap A).ker.norm_starProjection_apply_le x).trans hx
  · intro w
    exact (cappedActiveAnchors_card A z (J w) a R hT).trans hTbound
  · intro x w hx
    exact gaussian_capped_coordinate_cover A z e E J a hM hK hT hA hbound hsmall
      hbounded hanchors hcover hx.2.1 hx.2.2 hx.1

end Falconer

end OAI

end ExtensionScope69

/- Source: OAI.MeasureTheory.Falconer.Slicing.SliceMapBalls. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope70




namespace OAI

/-! # Ball transport by pairwise metric control on a full-measure support -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

omit [BorelSpace X] in
theorem map_ball_bound_of_pair_control (μ : Measure X) (f : X → Y) (hf : Measurable f)
    (S : Set X) (hS : ∀ᵐ x ∂μ, x ∈ S) {r R : ℝ} {C : ℝ≥0∞}
    (hpair : ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) < 2*r → dist x y < R)
    (hball : ∀ x, μ (ball x R) ≤ C) (a : Y) :
    (Measure.map f μ) (ball a r) ≤ C := by
  rw [Measure.map_apply hf measurableSet_ball]
  by_cases he : (S ∩ f ⁻¹' ball a r).Nonempty
  · obtain ⟨x,hxS,hxa⟩ := he
    apply (measure_mono_ae ?_).trans (hball x)
    filter_upwards [hS] with y hy hya
    exact hpair y hy x hxS ((dist_triangle (f y) a (f x)).trans_lt
      (by linarith [show dist (f y) a < r from hya,show dist (f x) a < r from hxa,
        dist_comm a (f x)]))
  · have hz : μ (f ⁻¹' ball a r) = 0 := by
      apply measure_mono_null (t := Sᶜ)
      · intro x hx hxS
        exact he ⟨x,hxS,hx⟩
      · exact ae_iff.mp hS
    rw [hz]
    exact zero_le

end Falconer

end OAI

end ExtensionScope70

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianMapBalls. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope71




namespace OAI

/-! # Finite-scale ball bounds on the actual kernel-coordinate pushforwards -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_kernel_ball_bound (A : Fin h → Space d) (z : Space h)
    (μ : Measure (Space d)) {δ K s R : ℝ} {C : ℝ≥0∞} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hμ : ∀ᵐ x ∂μ, x ∈ gaussianPointBand A z δ)
    (hball : ∀ x, μ (ball x R) ≤ C) (hR : 2*s+K*((h:ℝ)*(2*δ)) ≤ R) (a : Space d) :
    (Measure.map (gaussianRowMap A).ker.starProjection μ) (ball a s) ≤ C := by
  apply map_ball_bound_of_pair_control μ _
    (gaussianRowMap A).ker.starProjection.continuous.measurable _ hμ _ hball a
  intro x hx y hy hxy
  have hp := gaussian_point_kernel_pair_distance A z hK hbound hx hy
    (le_refl ‖(gaussianRowMap A).ker.starProjection x-(gaussianRowMap A).ker.starProjection y‖)
  rw [dist_eq_norm] at hxy ⊢
  exact hp.trans_lt (by linarith)

theorem gaussian_direction_kernel_ball_bound (A : Fin h → Space d)
    (ν : Measure (Sphere d)) {δ K s R : ℝ} {C : ℝ≥0∞} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1)
    (hν : ∀ᵐ w ∂ν, w ∈ gaussianDirectionBand A δ)
    (hball : ∀ w, ν (ball w R) ≤ C) (hR : 2*s+4*(K*((h:ℝ)*δ)) ≤ R) (a : Space d) :
    (Measure.map (fun w : Sphere d => normalize ((gaussianRowMap A).ker.starProjection (w:Space d))) ν)
      (ball a s) ≤ C := by
  apply map_ball_bound_of_pair_control ν _ (by unfold NormedSpace.normalize; fun_prop) _ hν _ hball a
  intro w hw v hv hdist
  have hwe := gaussian_direction_kernel_normalize_error A hK hbound hsmall hw
  have hve := gaussian_direction_kernel_normalize_error A hK hbound hsmall hv
  change ‖(w:Space d)-(v:Space d)‖ < R
  rw [dist_eq_norm] at hdist
  have htriangle : ‖(w:Space d)-(v:Space d)‖ ≤
      ‖(w:Space d)-normalize ((gaussianRowMap A).ker.starProjection (w:Space d))‖ +
      ‖normalize ((gaussianRowMap A).ker.starProjection (w:Space d))-
        normalize ((gaussianRowMap A).ker.starProjection (v:Space d))‖ +
      ‖normalize ((gaussianRowMap A).ker.starProjection (v:Space d))-(v:Space d)‖ := by
    calc
      _ ≤ ‖(w:Space d)-normalize ((gaussianRowMap A).ker.starProjection (w:Space d))‖ +
          ‖normalize ((gaussianRowMap A).ker.starProjection (w:Space d))-(v:Space d)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by
        have ht := norm_sub_le_norm_sub_add_norm_sub
          (normalize ((gaussianRowMap A).ker.starProjection (w:Space d)))
          (normalize ((gaussianRowMap A).ker.starProjection (v:Space d))) (v:Space d)
        exact (add_le_add le_rfl ht).trans_eq (add_assoc _ _ _).symm
  have hwe' : ‖(w:Space d)-normalize ((gaussianRowMap A).ker.starProjection (w:Space d))‖ ≤
      2*(K*((h:ℝ)*δ)) := (norm_sub_rev _ _).le.trans hwe
  linarith

end Falconer

end OAI

end ExtensionScope71

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedBalls. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope72



namespace OAI

/-! # Coordinate ball estimates for the actual retained slice laws -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {ι : Type*}

theorem gaussian_pruned_point_kernel_ball
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (δ : ℝ) (r : ι → ℝ) (TP : ι → ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hs : 2*s+K*((h:ℝ)*(2*δ)) ≤ r i) (a : Space d) :
    (Measure.map (gaussianRowMap A).ker.starProjection
      ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z))))
        (ball a s) ≤ TP i := by
  apply gaussian_point_kernel_ball_bound A z _ hK hbound _ (fun x => gaussianPointGood_ball μ δ r TP (A,z) i x) hs a
  exact ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianPointBand_measurable _ _ _)) _)

theorem gaussian_pruned_direction_kernel_ball
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (A : Fin h → Space d)
    (δ : ℝ) (r : ι → ℝ) (TD : ι → ℝ≥0∞) (M : ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1) (hs : 2*s+4*(K*((h:ℝ)*δ)) ≤ r i) (a : Space d) :
    (Measure.map (fun w : Sphere d => normalize ((gaussianRowMap A).ker.starProjection (w:Space d)))
      ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A)))
        (ball a s) ≤ TD i := by
  apply gaussian_direction_kernel_ball_bound A _ hK hbound hsmall _
    (fun w => gaussianDirectionGood_ball ν δ r TD M A i w) hs a
  exact ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianDirectionBand_measurable _ _)) _)

theorem slicePointCoordinates_map_ball (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (μ : Measure (Space d)) (a : Space m) (r : ℝ) :
    (Measure.map (slicePointCoordinates V hm) μ) (ball a r) =
      (Measure.map V.starProjection μ) (ball ((sliceCoordinates V hm).symm a : Space d) r) := by
  rw [Measure.map_apply (slicePointCoordinates_continuous V hm).measurable measurableSet_ball,
    Measure.map_apply V.starProjection.continuous.measurable measurableSet_ball]
  congr 1
  ext x
  change dist (sliceCoordinates V hm (V.orthogonalProjectionOnto x)) a < r ↔ _
  have hd : dist (sliceCoordinates V hm (V.orthogonalProjectionOnto x)) a =
      dist (V.orthogonalProjectionOnto x) ((sliceCoordinates V hm).symm a) := by
    rw [← (sliceCoordinates V hm).dist_map, (sliceCoordinates V hm).apply_symm_apply]
  rw [hd]
  rfl

theorem gaussian_pruned_point_coordinate_ball
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (hm : Module.finrank ℝ (gaussianRowMap A).ker = m)
    (δ : ℝ) (r : ι → ℝ) (TP : ι → ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hs : 2*s+K*((h:ℝ)*(2*δ)) ≤ r i) (a : Space m) :
    (Measure.map (slicePointCoordinates (gaussianRowMap A).ker hm)
      ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z))))
        (ball a s) ≤ TP i := by
  rw [slicePointCoordinates_map_ball]
  exact gaussian_pruned_point_kernel_ball μ A z δ r TP i hK hbound hs _

theorem sliceDirectionCoordinates_map_ball (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (ν : Measure (Sphere d)) (a : Space m) (r : ℝ) :
    (Measure.map (fun w : Sphere d => normalize (slicePointCoordinates V hm (w:Space d))) ν) (ball a r) =
      (Measure.map (fun w : Sphere d => normalize (V.starProjection (w:Space d))) ν)
        (ball ((sliceCoordinates V hm).symm a : Space d) r) := by
  have hf : Measurable (fun w : Sphere d => slicePointCoordinates V hm (w:Space d)) :=
    (slicePointCoordinates_continuous V hm).measurable.comp measurable_subtype_coe
  have hg : Measurable (fun w : Sphere d => normalize (slicePointCoordinates V hm (w:Space d))) := by
    unfold NormedSpace.normalize
    exact (hf.norm.inv).smul hf
  rw [Measure.map_apply hg measurableSet_ball,
    Measure.map_apply (show Measurable (fun w : Sphere d => normalize (V.starProjection (w:Space d))) from
      by unfold NormedSpace.normalize; fun_prop) measurableSet_ball]
  congr 1
  ext w
  change dist (normalize (sliceCoordinates V hm (V.orthogonalProjectionOnto (w:Space d)))) a < r ↔ _
  rw [← sliceCoordinates_normalize]
  have hd : dist (sliceCoordinates V hm (normalize (V.orthogonalProjectionOnto (w:Space d)))) a =
      dist (normalize (V.orthogonalProjectionOnto (w:Space d))) ((sliceCoordinates V hm).symm a) := by
    rw [← (sliceCoordinates V hm).dist_map,(sliceCoordinates V hm).apply_symm_apply]
  rw [hd]
  rfl

theorem gaussian_pruned_direction_coordinate_ball
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (A : Fin h → Space d)
    (hm : Module.finrank ℝ (gaussianRowMap A).ker = m)
    (δ : ℝ) (r : ι → ℝ) (TD : ι → ℝ≥0∞) (M : ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1) (hs : 2*s+4*(K*((h:ℝ)*δ)) ≤ r i) (a : Space m) :
    (Measure.map (fun w : Sphere d => normalize (slicePointCoordinates (gaussianRowMap A).ker hm (w:Space d)))
      ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A)))
        (ball a s) ≤ TD i := by
  rw [sliceDirectionCoordinates_map_ball]
  exact gaussian_pruned_direction_kernel_ball ν A δ r TD M i hK hbound hsmall hs _

end Falconer

end OAI

end ExtensionScope72

/- Source: OAI.MeasureTheory.Falconer.Slicing.OrientedSliceBalls. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope73



namespace OAI

/-! # Closed-ball bounds in the oriented coordinates of the actual slice -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {ι : Type*}

theorem oriented_point_ball_eq (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (μ : Measure (Space d)) (c : Space m) (r : ℝ) :
    μ {x | dist (e (V.orthogonalProjectionOnto x)) c < r} =
      (Measure.map V.starProjection μ) (ball (e.symm c : Space d) r) := by
  rw [Measure.map_apply V.starProjection.continuous.measurable measurableSet_ball]
  congr 1
  ext x
  change dist (e (V.orthogonalProjectionOnto x)) c < r ↔
    dist (V.orthogonalProjectionOnto x) (e.symm c) < r
  rw [← e.dist_map (V.orthogonalProjectionOnto x) (e.symm c),e.apply_symm_apply]

theorem oriented_direction_ball_eq (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (ν : Measure (Sphere d)) (c : Space m) (r : ℝ) :
    ν {w | dist (normalize (e (V.orthogonalProjectionOnto (w:Space d)))) c < r} =
      (Measure.map (fun w : Sphere d => normalize (V.starProjection (w:Space d))) ν)
        (ball (e.symm c : Space d) r) := by
  rw [Measure.map_apply (show Measurable
    (fun w : Sphere d => normalize (V.starProjection (w:Space d))) from
      by unfold NormedSpace.normalize; fun_prop) measurableSet_ball]
  congr 1
  ext w
  change dist (normalize (e (V.orthogonalProjectionOnto (w:Space d)))) c < r ↔
    dist (normalize (V.orthogonalProjectionOnto (w:Space d))) (e.symm c) < r
  rw [← slice_isometry_normalize V e]
  rw [← e.dist_map (normalize (V.orthogonalProjectionOnto (w:Space d))) (e.symm c),e.apply_symm_apply]

theorem gaussian_pruned_oriented_point_closed_ball
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (δ : ℝ) (r : ι → ℝ) (TP : ι → ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K) (hspos : 0 < s)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hs : 4*s+K*((h:ℝ)*(2*δ)) ≤ r i) (c : Space m) :
    ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z)))
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s} ≤ TP i := by
  have hss : s < 2*s := by linarith
  calc
    _ ≤ ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z)))
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c < 2*s} :=
      measure_mono (show {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s} ⊆
        {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c < 2*s} from
          fun x hx => lt_of_le_of_lt hx hss)
    _ = _ := oriented_point_ball_eq (gaussianRowMap A).ker e _ c (2*s)
    _ ≤ _ := gaussian_pruned_point_kernel_ball μ A z δ r TP i hK hbound (by linarith) _

theorem gaussian_pruned_oriented_direction_closed_ball
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (A : Fin h → Space d)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (δ : ℝ) (r : ι → ℝ) (TD : ι → ℝ≥0∞) (M : ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K) (hspos : 0 < s)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1) (hs : 4*s+4*(K*((h:ℝ)*δ)) ≤ r i) (c : Space m) :
    ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A))
      {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ s} ≤ TD i := by
  have hss : s < 2*s := by linarith
  calc
    _ ≤ ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A))
      {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c < 2*s} :=
      measure_mono (show {w : Sphere d | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ s} ⊆
        {w : Sphere d | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c < 2*s} from
          fun w hw => lt_of_le_of_lt hw hss)
    _ = _ := oriented_direction_ball_eq (gaussianRowMap A).ker e _ c (2*s)
    _ ≤ _ := gaussian_pruned_direction_kernel_ball ν A δ r TD M i hK hbound hsmall (by linarith) _

end Falconer

end OAI

end ExtensionScope73

/- Source: OAI.MeasureTheory.Falconer.Slicing.SliceScaling. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope74


namespace OAI

/-! # The fixed spatial rescaling of a selected planar slice -/

namespace Falconer
open NormedSpace
variable {m : ℕ}

theorem slice_scaled_distance {L : ℝ} (hL : 0 < L) (x c : Space m) :
    dist (L⁻¹ • x) c = L⁻¹*dist x (L • c) := by
  have he : L⁻¹ • x-c = L⁻¹ • (x-L • c) := by
    rw [smul_sub,smul_smul,inv_mul_cancel₀ hL.ne',one_smul]
  rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hL),dist_eq_norm]

theorem slice_scaled_tube_width {L ε : ℝ} (hL : 0 < L) (w x a : Space m)
    (htube : ‖perpendicularPart w (x-a)‖ ≤ ε) :
    ‖perpendicularPart w (L⁻¹ • x-L⁻¹ • a)‖ ≤ L⁻¹*ε := by
  rw [← smul_sub,perpendicularPart_smul,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hL)]
  exact mul_le_mul_of_nonneg_left htube (inv_nonneg.mpr hL.le)

end Falconer

end OAI

end ExtensionScope74

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianDyadicGeometry. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope75



namespace OAI

/-! # The dyadic tests controlling scaled point and normalized direction balls -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {ι : Type*}

theorem gaussian_scaled_point_test
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (δ : ℝ) (r : ι → ℝ) (TP : ι → ℝ≥0∞) (i : ι)
    {K L a u : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (ha : 0 < a) (hu : 0 < u)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (haK : 4*L+2*K*(h:ℝ) ≤ a) (hδ : δ ≤ u/(2*a)) (hr : r i = u/2) (c : Space m) :
    ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z)))
      {x | dist (L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ u/(2*a)} ≤ TP i := by
  have hs : 0 < u/(2*a) := by positivity
  have he : a*(u/(2*a)) = u/2 := by field_simp
  have h₁ := mul_le_mul_of_nonneg_right haK hs.le
  have h₂ := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 2*K*(h:ℝ))
  have hrad : 4*(L*(u/(2*a)))+K*((h:ℝ)*(2*δ)) ≤ r i := by
    rw [hr]
    nlinarith
  apply (measure_mono (show
    {x | dist (L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ u/(2*a)} ⊆
    {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) (L • c) ≤ L*(u/(2*a))} from ?_)).trans
      (gaussian_pruned_oriented_point_closed_ball μ A z e δ r TP i hK (mul_pos hL hs) hbound hrad _)
  intro x hx
  change dist (L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ u/(2*a) at hx
  rw [slice_scaled_distance hL,mul_comm,← div_eq_mul_inv] at hx
  change dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) (L • c) ≤ L*(u/(2*a))
  simpa only [mul_comm] using (div_le_iff₀ hL).mp hx

theorem gaussian_normalized_direction_test
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (A : Fin h → Space d)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (δ : ℝ) (r : ι → ℝ) (TD : ι → ℝ≥0∞) (M : ℝ≥0∞) (i : ι)
    {K a u : ℝ} (hK : 0 ≤ K) (ha : 0 < a) (hu : 0 < u)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1) (haK : 4+4*K*(h:ℝ) ≤ a)
    (hδ : δ ≤ u/(2*a)) (hr : r i = u/2) (c : Space m) :
    ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A))
      {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ u/(2*a)} ≤ TD i := by
  have hs : 0 < u/(2*a) := by positivity
  have he : a*(u/(2*a)) = u/2 := by field_simp
  have h₁ := mul_le_mul_of_nonneg_right haK hs.le
  have h₂ := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 4*K*(h:ℝ))
  have hrad : 4*(u/(2*a))+4*(K*((h:ℝ)*δ)) ≤ r i := by
    rw [hr]
    nlinarith
  exact gaussian_pruned_oriented_direction_closed_ball ν A e δ r TD M i hK hs hbound hsmall hrad c

end Falconer

end OAI

end ExtensionScope75

/- Source: OAI.MeasureTheory.Falconer.Geometry.TruncatedDyadicBalls. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope76


namespace OAI

/-! # Only the dyadic ball tests above the slice thickness are needed -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] {m : ℕ}

theorem truncated_dyadic_ball_bound
    (μ : Measure X) (p : X → Space m) (N : ℕ) {a H s : ℝ}
    (ha : 1 ≤ a) (hH : 1 ≤ H) (hs : 0 ≤ s) (hmass : μ univ ≤ 1)
    (hdyadic : ∀ g ≤ N, 2*a*(1/(2:ℝ)^N) ≤ 1/(2:ℝ)^g → ∀ c : Space m,
      μ {x | dist (p x) c ≤ (1/(2:ℝ)^g)/(2*a)} ≤
        ENNReal.ofReal (H*(1/(2:ℝ)^g)^s)) :
    ∀ (c : Space m) (r : ℝ), 1/(2:ℝ)^N ≤ r →
      μ {x | dist (p x) c ≤ r} ≤ ENNReal.ofReal (H*(4*a*r)^s) := by
  intro c r hr
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hrp : 0 < r := (by positivity : 0 < 1/(2:ℝ)^N).trans_le hr
  by_cases hsmall : 2*a*r ≤ 1
  · have hmin : 1/(2:ℝ)^N ≤ 2*a*r := hr.trans (by nlinarith)
    obtain ⟨g,hg,hgr,hrg⟩ := Regularization.dyadic_radius_bracket hmin hsmall
    have hcut : 2*a*(1/(2:ℝ)^N) ≤ 1/(2:ℝ)^g :=
      (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2*a)).trans hgr
    have hrad : r ≤ (1/(2:ℝ)^g)/(2*a) := (le_div_iff₀ (by positivity)).mpr (by
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hgr)
    calc
      _ ≤ μ {x | dist (p x) c ≤ (1/(2:ℝ)^g)/(2*a)} := measure_mono (fun x hx => hx.trans hrad)
      _ ≤ ENNReal.ofReal (H*(1/(2:ℝ)^g)^s) := hdyadic g hg hcut c
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by nlinarith [hrg]) hs) (by linarith))
  · apply (measure_mono (subset_univ _) |>.trans hmass).trans
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hpow : 1 ≤ (4*a*r)^s := Real.one_le_rpow (by linarith) hs
    nlinarith

end Falconer

end OAI

end ExtensionScope76

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianFrostmanTransfer. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope77




namespace OAI

/-! # Frostman bounds for the actual normalized and oriented slice laws -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ}

theorem gaussian_point_normalized_frostman
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m) (N : ℕ)
    (r : Fin (N+1) → ℝ) (TP : Fin (N+1) → ℝ≥0∞)
    (hr : ∀ g, r g = (1/(2:ℝ)^g.val)/2)
    {K L a H P f : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (ha : 1 ≤ a) (hH : 1 ≤ H)
    (hP : 0 ≤ P) (hf : 0 ≤ f)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (haK : 4*L+2*K*(h:ℝ) ≤ a)
    (hTP : ∀ g, TP g ≤ ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^f))
    (hα : ((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
      (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z))) univ ≠ 0)
    (hratio : ENNReal.ofReal P /
      (((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
        (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z))) univ) ≤ ENNReal.ofReal H) :
    ∀ (c : Space m) (s : ℝ), 1/(2:ℝ)^N ≤ s →
      (normalizedSliceLaw ((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
        (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z))) hα : Measure (Space d))
        {x | dist (L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s} ≤
      ENNReal.ofReal (H*(4*a*s)^f) := by
  let α := (gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
    (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z))
  apply truncated_dyadic_ball_bound (normalizedSliceLaw α hα : Measure (Space d))
    (fun x => L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) N ha hH hf (by simp)
  intro g hg hcut c
  let j : Fin (N+1) := ⟨g,by omega⟩
  have hδ : 1/(2:ℝ)^N ≤ (1/(2:ℝ)^g)/(2*a) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm,mul_left_comm,mul_assoc] using hcut)
  have hball := gaussian_scaled_point_test μ A z e (1/(2:ℝ)^N) r TP j hK hL
    (by linarith) (by positivity) hbound haK hδ (hr j) c
  rw [normalizedSliceLaw_apply]
  calc
    _ ≤ (α univ)⁻¹*ENNReal.ofReal (P*(1/(2:ℝ)^g)^f) :=
      mul_le_mul' le_rfl (hball.trans (hTP j))
    _ = (ENNReal.ofReal P / α univ)*ENNReal.ofReal ((1/(2:ℝ)^g)^f) := by
      rw [ENNReal.ofReal_mul hP]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ ENNReal.ofReal H*ENNReal.ofReal ((1/(2:ℝ)^g)^f) := mul_le_mul' hratio le_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ H)]

theorem gaussian_direction_normalized_frostman
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (A : Fin h → Space d)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m) (N : ℕ)
    (r : Fin (N+1) → ℝ) (TD : Fin (N+1) → ℝ≥0∞) (M : ℝ≥0∞)
    (hr : ∀ g, r g = (1/(2:ℝ)^g.val)/2)
    {K a H P b : ℝ} (hK : 0 ≤ K) (ha : 1 ≤ a) (hH : 1 ≤ H) (hP : 0 ≤ P) (hb : 0 ≤ b)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*(1/(2:ℝ)^N)) < 1) (haK : 4+4*K*(h:ℝ) ≤ a)
    (hTD : ∀ g, TD g ≤ ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^b))
    (hβ : ((gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).restrict
      (gaussianDirectionGood ν (1/(2:ℝ)^N) r TD M A)) univ ≠ 0)
    (hratio : ENNReal.ofReal P /
      (((gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).restrict
        (gaussianDirectionGood ν (1/(2:ℝ)^N) r TD M A)) univ) ≤ ENNReal.ofReal H) :
    ∀ (c : Space m) (s : ℝ), 1/(2:ℝ)^N ≤ s →
      (normalizedSliceLaw ((gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).restrict
        (gaussianDirectionGood ν (1/(2:ℝ)^N) r TD M A)) hβ : Measure (Sphere d))
        {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ s} ≤
      ENNReal.ofReal (H*(4*a*s)^b) := by
  let β := (gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).restrict
    (gaussianDirectionGood ν (1/(2:ℝ)^N) r TD M A)
  apply truncated_dyadic_ball_bound (normalizedSliceLaw β hβ : Measure (Sphere d))
    (fun w : Sphere d => normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
    N ha hH hb (by simp)
  intro g hg hcut c
  let j : Fin (N+1) := ⟨g,by omega⟩
  have hδ : 1/(2:ℝ)^N ≤ (1/(2:ℝ)^g)/(2*a) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm,mul_left_comm,mul_assoc] using hcut)
  have hball := gaussian_normalized_direction_test ν A e (1/(2:ℝ)^N) r TD M j hK
    (by linarith) (by positivity) hbound hsmall haK hδ (hr j) c
  rw [normalizedSliceLaw_apply]
  calc
    _ ≤ (β univ)⁻¹*ENNReal.ofReal (P*(1/(2:ℝ)^g)^b) :=
      mul_le_mul' le_rfl (hball.trans (hTD j))
    _ = (ENNReal.ofReal P / β univ)*ENNReal.ofReal ((1/(2:ℝ)^g)^b) := by
      rw [ENNReal.ofReal_mul hP]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ ENNReal.ofReal H*ENNReal.ofReal ((1/(2:ℝ)^g)^b) := mul_le_mul' hratio le_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ H)]

end Falconer

end OAI

end ExtensionScope77

/- Source: OAI.MeasureTheory.Falconer.Geometry.PolynomialNormalization. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope78


namespace OAI

/-! # One common polynomial loss for both normalized slice laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem polynomial_slice_normalization
    (α : Measure X) (β : Measure Y) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (E : Set (X × Y)) {K V : ℝ} (hK : 0 < K) (hV : 0 < V)
    (hα : α univ ≤ ENNReal.ofReal (K^6)) (hβ : β univ ≤ ENNReal.ofReal (K^3))
    (hI : ENNReal.ofReal (1/(4*K*V)) ≤ (α.prod β) E) :
    ∃ ha : α univ ≠ 0, ∃ hb : β univ ≠ 0,
      ENNReal.ofReal (K^6) / α univ ≤ ENNReal.ofReal (4*K^10*V) ∧
      ENNReal.ofReal (K^3) / β univ ≤ ENNReal.ofReal (4*K^10*V) ∧
      (∀ (S : Set X) (w : ℝ), α S ≤ ENNReal.ofReal (K^6*w) →
        (normalizedSliceLaw α ha : Measure X) S ≤ ENNReal.ofReal (4*K^10*V*w)) ∧
      (∀ (S : Set Y) (w : ℝ), β S ≤ ENNReal.ofReal (K^3*w) →
        (normalizedSliceLaw β hb : Measure Y) S ≤ ENNReal.ofReal (4*K^10*V*w)) ∧
      ENNReal.ofReal (1/(4*K^10*V)) ≤
        ((normalizedSliceLaw α ha : Measure X).prod (normalizedSliceLaw β hb : Measure Y)) E := by
  have hIp : 0 < ENNReal.ofReal (1/(4*K*V)) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨ha,hb⟩ := positive_incidence_marginals α β E (hIp.trans_le hI)
  have hlo := incidence_marginal_lower_bounds α β E hα hβ
    (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hK 6))) ENNReal.ofReal_ne_top
    (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hK 3))) ENNReal.ofReal_ne_top hI
  have hla : ENNReal.ofReal (1/(4*K^4*V)) ≤ α univ := by
    convert hlo.1 using 1
    rw [← ENNReal.ofReal_div_of_pos (pow_pos hK 3)]
    congr 1
    field_simp
  have hlb : ENNReal.ofReal (1/(4*K^7*V)) ≤ β univ := by
    convert hlo.2 using 1
    rw [← ENNReal.ofReal_div_of_pos (pow_pos hK 6)]
    congr 1
    field_simp
  have hra : ENNReal.ofReal (K^6) / α univ ≤ ENNReal.ofReal (4*K^10*V) := by
    apply (mul_le_mul' le_rfl (ENNReal.inv_le_inv.mpr hla)).trans_eq
    change ENNReal.ofReal (K^6) / ENNReal.ofReal (1/(4*K^4*V)) = _
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  have hrb : ENNReal.ofReal (K^3) / β univ ≤ ENNReal.ofReal (4*K^10*V) := by
    apply (mul_le_mul' le_rfl (ENNReal.inv_le_inv.mpr hlb)).trans_eq
    change ENNReal.ofReal (K^3) / ENNReal.ofReal (1/(4*K^7*V)) = _
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  refine ⟨ha,hb,hra,hrb,?_,?_,?_⟩
  · intro S w hS
    apply (normalizedSliceLaw_bound α ha S hla hS).trans_eq
    rw [mul_comm]
    change ENNReal.ofReal (K^6*w) / ENNReal.ofReal (1/(4*K^4*V)) = _
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  · intro S w hS
    apply (normalizedSliceLaw_bound β hb S hlb hS).trans_eq
    rw [mul_comm]
    change ENNReal.ofReal (K^3*w) / ENNReal.ofReal (1/(4*K^7*V)) = _
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  · have hi := normalizedSliceLaw_incidence_lower α β ha hb E hα hβ hI
    convert hi using 1
    symm
    rw [mul_comm,← ENNReal.ofReal_mul (by positivity : 0 ≤ K^6)]
    change ENNReal.ofReal (1/(4*K*V)) / ENNReal.ofReal (K^6*K^3) = _
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp

end Falconer

end OAI

end ExtensionScope78

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianBandRestriction. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope79


namespace OAI

/-! # Making the two slice bands explicit in the original-label relation -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussian_pruned_incidence_inter_bands
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (p : (Fin h → Space d) × Space h) :
    gaussianPrunedIncidence μ ν δ r TP TD M
      (E ∩ (gaussianPointBand p.1 p.2 δ ×ˢ gaussianDirectionBand p.1 δ)) p =
      gaussianPrunedIncidence μ ν δ r TP TD M E p := by
  let α := (gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)
  let β := (gaussianDirectionSliceMeasure ν p.1 δ).restrict (gaussianDirectionGood ν δ r TD M p.1)
  have hp : ∀ᵐ x ∂α, x ∈ gaussianPointBand p.1 p.2 δ :=
    ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianPointBand_measurable _ _ _)) _)
  have hw : ∀ᵐ w ∂β, w ∈ gaussianDirectionBand p.1 δ :=
    ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianDirectionBand_measurable _ _)) _)
  change (α.prod β) _ = (α.prod β) E
  apply measure_congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hp,Measure.quasiMeasurePreserving_snd.ae hw] with t ht hu
  exact propext ⟨fun h => h.1,fun h => ⟨h,ht,hu⟩⟩

end Falconer

end OAI

end ExtensionScope79

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPlanarExclusion. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope80






namespace OAI

/-! # Excluding a large actual Gaussian slice using the published planar input -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem gaussian_planar_slice_exclusion
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ (N d h : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (A : Fin h → Space d) (z : Space h) (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 2)
      (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ) (a : κ → Space d)
      (K V M T a₀ : ℝ),
    1/(2:ℝ)^N < δ₀ → 0 < K → 0 < V → 0 ≤ M → 0 ≤ T →
    T ≤ (1/(2:ℝ)^N)^(-b-η) →
    1 ≤ a₀ → 1 ≤ 4*K^10*V → 4+8*(h:ℝ) ≤ a₀ →
    (4*K^10*V)*(4*a₀)^f ≤ (1/(2:ℝ)^N)^(-η) →
    (4*K^10*V)*(8*a₀)^b ≤ (1/(2:ℝ)^N)^(-η) →
    (1/(2:ℝ)^N)^η < 1/(4*K^10*V) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ i, ‖A i‖ ≤ M) →
    (∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖) →
    2*((h:ℝ)*(1/(2:ℝ)^N)) < 1 →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) →
    (∀ᵐ w : Sphere d ∂ν, w ∈ gaussianDirectionBand A (1/(2:ℝ)^N) →
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
    gaussianPrunedPairMass μ ν (1/(2:ℝ)^N)
      (fun g : Fin (N+1) => (1/(2:ℝ)^g.val)/2)
      (fun g => ENNReal.ofReal (K^6*(1/(2:ℝ)^g.val)^f))
      (fun g => ENNReal.ofReal (K^3*(1/(2:ℝ)^g.val)^b)) (ENNReal.ofReal (K^3))
      (gaussianActiveRelation E J a
        ((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+(C*(1/(2:ℝ)^N))*M)
        (ENNReal.ofReal T) true) (A,z) ≤ ENNReal.ofReal (1/(4*K*V)) := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := planar_selected_slice_gain hpublished hb hb' hbf hf C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro N d h κ _ _ A z e μ ν _ _ E J a K V M T a₀ hδsmall hK hV hM hT hTbound
    ha₀ hH haK hpcoef hqcoef hlow hE hJ hA hbound hsmall hEb hanchors hcover hμ hν
  let δ : ℝ := 1/(2:ℝ)^N
  let r : Fin (N+1) → ℝ := fun g => (1/(2:ℝ)^g.val)/2
  let TP : Fin (N+1) → ℝ≥0∞ := fun g => ENNReal.ofReal (K^6*(1/(2:ℝ)^g.val)^f)
  let TD : Fin (N+1) → ℝ≥0∞ := fun g => ENNReal.ofReal (K^3*(1/(2:ℝ)^g.val)^b)
  let α := (gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z))
  let β := (gaussianDirectionSliceMeasure ν A δ).restrict
    (gaussianDirectionGood ν δ r TD (ENNReal.ofReal (K^3)) A)
  let R := δ+(2*(1/4))*δ+(C*δ)*M
  let F := selectedActiveRelation A z δ E J a R T
  have hδ : 0 < δ := by dsimp [δ]; positivity
  by_contra hnot
  have hmass : ENNReal.ofReal (1/(4*K*V)) ≤ (α.prod β) F := by
    have hi := (lt_of_not_ge hnot).le
    change _ ≤ gaussianPrunedIncidence μ ν δ r TP TD (ENNReal.ofReal (K^3)) F (A,z)
    rw [show F = {u | ((A,z),u) ∈ gaussianActiveRelation E J a R (ENNReal.ofReal T) true} ∩
      (gaussianPointBand A z δ ×ˢ gaussianDirectionBand A δ) from rfl,
      gaussian_pruned_incidence_inter_bands μ ν δ r TP TD (ENNReal.ofReal (K^3))
        {u | ((A,z),u) ∈ gaussianActiveRelation E J a R (ENNReal.ofReal T) true} (A,z)]
    exact hi
  have hαmass : α univ ≤ ENNReal.ofReal (K^6) := by
    have hm := gaussianPointGood_mass μ δ r TP (A,z) hμ 0 (by norm_num [r])
    simpa only [TP,Fin.val_zero,pow_zero,div_one,Real.one_rpow,mul_one] using hm
  have hβmass : β univ ≤ ENNReal.ofReal (K^3) := gaussianDirectionGood_mass ν δ r TD _ A
  obtain ⟨hα,hβ,hαratio,hβratio,_,_,hinc⟩ :=
    polynomial_slice_normalization α β F hK hV hαmass hβmass hmass
  let α' := normalizedSliceLaw α hα
  let β' := normalizedSliceLaw β hβ
  have hpball (c : Space 2) (s : ℝ) (hs : δ ≤ s) :
      (α' : Measure (Space d)).real {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s}
        ≤ δ^(-η)*s^f := by
    have hh := gaussian_point_normalized_frostman μ A z e N r TP (fun _ => rfl)
      (by norm_num) (by norm_num : (0:ℝ) < 1) ha₀ hH (pow_nonneg hK.le 6)
      (hb.le.trans hbf.le) hbound (by linarith) (fun _ => le_rfl) hα hαratio c s hs
    simp only [inv_one,one_smul] at hh
    have hs0 : 0 ≤ s := hδ.le.trans hs
    have hc : (4*K^10*V)*(4*a₀*s)^f ≤ δ^(-η)*s^f := by
      rw [Real.mul_rpow (by positivity) hs0]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hpcoef (Real.rpow_nonneg hs0 f)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans (by
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (4*K^10*V)*(4*a₀*s)^f)] using hc)
  have hqball (c : Space 2) (s : ℝ) (hs : δ ≤ s) :
      (β' : Measure (Sphere d)).real
        {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ 2*s}
        ≤ δ^(-η)*s^b := by
    have hs0 : 0 ≤ s := hδ.le.trans hs
    have hh := gaussian_direction_normalized_frostman ν A e N r TD (ENNReal.ofReal (K^3))
      (fun _ => rfl) (by norm_num) ha₀ hH (pow_nonneg hK.le 3) hb.le hbound hsmall
      (by linarith) (fun _ => le_rfl) hβ hβratio c (2*s) (by linarith)
    have hc : (4*K^10*V)*(4*a₀*(2*s))^b ≤ δ^(-η)*s^b := by
      rw [show 4*a₀*(2*s) = (8*a₀)*s by ring,Real.mul_rpow (by positivity) hs0]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hqcoef (Real.rpow_nonneg hs0 b)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans (by
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (4*K^10*V)*(4*a₀*(2*s))^b)] using hc)
  have hαsupport : ∀ᵐ x ∂(α' : Measure (Space d)), ‖x‖ ≤ 1/4 :=
    normalizedSliceLaw_ae α hα (ae_restrict_of_ae (gaussianPointSliceMeasure_ae_of_ae μ A z δ hμ))
  have hβsupport : ∀ᵐ (w : Sphere d) ∂(β' : Measure (Sphere d)),
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 := by
    apply normalizedSliceLaw_ae β hβ
    have hc : ∀ᵐ (w : Sphere d) ∂β, w ∈ gaussianDirectionBand A δ →
        ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
        dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
          (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 :=
      ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_of_ae hν) _)
    have hbnd : ∀ᵐ (w : Sphere d) ∂β, w ∈ gaussianDirectionBand A δ :=
      ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianDirectionBand_measurable A δ)) _)
    filter_upwards [hc,hbnd] with w hw hbnd
    exact hw hbnd
  have hu := hgain δ hδ hδsmall d h κ A z e α' β' E J a M 2 T hE hJ hM (by norm_num)
    hT hTbound hA hbound hsmall hEb hanchors hcover hαsupport hβsupport hpball hqball
  have hl : 1/(4*K^10*V) ≤ ((α' : Measure (Space d)).prod (β' : Measure (Sphere d))).real F := by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) hinc
    simpa only [α',β',Measure.real,ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(4*K^10*V))] using hh
  exact (not_lt_of_ge (hl.trans hu)) hlow

end Falconer

end OAI

end ExtensionScope80

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianPlanarChart. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope81




namespace OAI

/-! # Every selected codimension-h slice in dimension h+2 has a controlled planar chart -/

namespace Falconer
open NormedSpace
variable {h : ℕ}

theorem gaussian_two_dimensional_slice_chart
    (B : Space h →ₗᵢ[ℝ] Space (h+2)) (A : Fin h → Space (h+2)) (w₀ : Sphere (h+2))
    {ε δ ρ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (hB : ∀ i, inner ℝ (w₀:Space (h+2)) (B (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0)
    (hA : ∀ i, ‖A i-B (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hstable : (h:ℝ)*ε ≤ 1/2)
    (hchart : 4*(h:ℝ)*δ+ρ+4*(h:ℝ)*ε ≤ 1/4) :
    ∃ e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 2,
      normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w₀:Space (h+2)))) =
        EuclideanSpace.basisFun (Fin 2) ℝ 0 ∧
      ∀ w : Sphere (h+2), w ∈ gaussianDirectionBand A δ → dist w w₀ ≤ ρ →
        ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2))))‖ = 1 ∧
        dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2)))))
          (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 := by
  have hpδ : 0 ≤ (h:ℝ)*δ := by positivity
  have hpε : 0 ≤ (h:ℝ)*ε := by positivity
  have hsδ : 2*((h:ℝ)*δ) < 1 := by nlinarith
  have hsε : 2*((h:ℝ)*ε) < 1 := by nlinarith
  have hbound := row_kernel_projection_bound A B hA hstable
  have hw₀ : w₀ ∈ gaussianDirectionBand A ε := by
    intro i
    have he : inner ℝ (w₀:Space (h+2)) (A i) =
        inner ℝ (w₀:Space (h+2)) (A i-B (EuclideanSpace.basisFun (Fin h) ℝ i)) := by
      rw [inner_sub_right,hB i,sub_zero]
    rw [he]
    exact (abs_real_inner_le_norm _ _).trans (by simpa only [sphere_norm,one_mul] using hA i)
  have hdim : Module.finrank ℝ (gaussianRowMap A).ker = 2 := by
    simpa only [Nat.add_sub_cancel_left] using row_kernel_finrank A B hA hstable
  obtain ⟨e,he⟩ := exists_oriented_slice_coordinates (gaussianRowMap A).ker hdim (by norm_num)
    (w₀:Space (h+2)) (gaussian_direction_kernel_nonzero A (by norm_num) hbound hsε hw₀)
  refine ⟨e,he,?_⟩
  intro w hw hclose
  have hn := gaussian_direction_kernel_nonzero A (by norm_num) hbound hsδ hw
  have hv : (gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2)) ≠ 0 :=
    fun hz => hn (congrArg Subtype.val hz)
  have hev : e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2))) ≠ 0 :=
    fun hz => hv (e.injective (by simpa only [map_zero] using hz))
  refine ⟨norm_normalize hev,?_⟩
  have hd := oriented_slice_direction_distance (gaussianRowMap A).ker e hsδ hsε
    (gaussian_direction_band_kernel_distance A (by norm_num) hbound hw)
    (gaussian_direction_band_kernel_distance A (by norm_num) hbound hw₀) hclose
  rw [he] at hd
  exact hd.trans (by nlinarith)

end Falconer

end OAI

end ExtensionScope81

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianThreshold. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope82


namespace OAI

/-! # A uniform positive incidence threshold on the bounded parameter box -/

namespace Falconer
open MeasureTheory
open scoped ENNReal

noncomputable def gaussianSelectionThreshold (h : ℕ) (K Z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1/(4*K*(2*Z)^h))

theorem gaussianSelectionThreshold_pos (h : ℕ) {K Z : ℝ} (hK : 0 < K) (hZ : 0 < Z) :
    0 < gaussianSelectionThreshold h K Z := by
  apply ENNReal.ofReal_pos.mpr
  positivity

theorem gaussianSelectionThreshold_budget (h : ℕ) {K Z : ℝ} (hK : 0 < K) (hZ : 0 < Z) :
    gaussianSelectionThreshold h K Z * volume (coordinateBox h Z) =
      ENNReal.ofReal (1/(4*K)) := by
  rw [gaussianSelectionThreshold,coordinateBox_volume hZ.le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem gaussianSelectionThreshold_uniform (h : ℕ) {K Z Z₀ : ℝ}
    (hK : 0 < K) (hZ₀ : 0 < Z₀) (hZZ : Z ≤ Z₀) :
    gaussianSelectionThreshold h K Z₀ * volume (coordinateBox h Z) ≤
      ENNReal.ofReal (1/(4*K)) := by
  have hsub : coordinateBox h Z ⊆ coordinateBox h Z₀ := fun x hx i => (hx i).trans hZZ
  exact (mul_le_mul' le_rfl (measure_mono hsub)).trans_eq (gaussianSelectionThreshold_budget h hK hZ₀)

end Falconer

end OAI

end ExtensionScope82

/- Source: OAI.MeasureTheory.Falconer.Angular.ControlledAngularGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope83






namespace OAI

/-! # A finite-scale angular gain on each controlled original direction chart -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem controlled_dyadic_angular_gain
    (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (w₀ : Sphere (h+2)) (B : Space h →ₗᵢ[ℝ] Space (h+2))
      (E : Set (Space (h+2) × Sphere (h+2)))
      (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2))
      (ρ Lt Lq K C₀ Nc Z a₀ : ℝ),
    1/(2:ℝ)^N < δ₀ → 0 ≤ ρ → 1/(2:ℝ)^N ≤ ρ →
    (∀ i, inner ℝ (w₀:Space (h+2)) (B (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0) →
    (∀ᵐ w ∂ν, dist w w₀ ≤ ρ) →
    (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2 →
    4*(h:ℝ)*(1/(2:ℝ)^N)+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 →
    (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    0 ≤ Lt → 0 ≤ Lq →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lt*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lq*(1/(2:ℝ)^j)^q)) →
    (∀ᵐ u : Sphere (h+2) × Sphere (h+2) ∂ν.prod ν,
      0 ≤ inner ℝ (u.1:Space (h+2)) (u.2:Space (h+2))) →
    0 < K → 0 < Nc → 0 < Z →
    (4*gaussianVectorBandConstant)^h*Lt*gaussianFrostmanFactor h t ≤ C₀ →
    (2*gaussianPairBandConstant)^h*Lq*gaussianFrostmanFactor h q ≤ C₀ →
    (2*gaussianPairBandConstant)^h*(|Lq*gaussianFrostmanFactor h q|+1) ≤ C₀ →
    ((N+1:ℕ):ℝ)*C₀ ≤ K → C₀ ≤ K → 4*(1+2*(2:ℝ)^h+1) ≤ K →
    (1/4)*((h+2:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N ≤ Z →
    1 ≤ a₀ → 1 ≤ 4*K^10*(2*Z)^h → 4+8*(h:ℝ) ≤ a₀ →
    (4*K^10*(2*Z)^h)*(4*a₀)^(t-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-η) →
    (4*K^10*(2*Z)^h)*(8*a₀)^(q-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-η) →
    (1/(2:ℝ)^N)^η < 1/(4*K^10*(2*Z)^h) →
    K^11*(Nc*(2*((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+
      (C*(1/(2:ℝ)^N))*((h+2:ℝ)*(2*ρ)+1)))^h) ≤ (1/(2:ℝ)^N)^(-(q-(h:ℝ))-η) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc) →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant (h+1) ρ^h)*
      (μ.prod ν) E < ENNReal.ofReal (1/K) := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := gaussian_planar_slice_exclusion hpublished
    (sub_pos.mpr hq) hq' (by linarith : q-(h:ℝ) < t-(h:ℝ)) ht C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro N κ _ _ μ ν _ _ w₀ B E J a ρ Lt Lq K C₀ Nc Z a₀ hδsmall hρ hδρ
    hB hν hstable hchart hμ hμmass hνmass hLt hLq hμball hνball hpair
    hK hNc hZ hCpoint hCdir hCmass hcard hC₀ hlarge hZbox ha₀ hH haK hpcoef hqcoef hlow
    hTbound hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  let ε : ℝ := (h+2:ℝ)*(2*ρ)
  let M : ℝ := ε+1
  let R : ℝ := δ+(2*(1/4))*δ+(C*δ)*M
  let T : ℝ := K^11*(Nc*(2*R)^h)
  let rows : Fin h → Space (h+2) := fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hrows (i : Fin h) : ‖rows i‖ ≤ 1 := by
    rw [show rows i = B (EuclideanSpace.basisFun (Fin h) ℝ i) from rfl,B.norm_map]
    exact ((EuclideanSpace.basisFun (Fin h) ℝ).norm_eq_one i).le
  have hwB : ∀ᵐ (w : Sphere (h+2)) ∂ν, ∀ i, |inner ℝ (w:Space (h+2)) (rows i)| ≤ ρ := by
    filter_upwards [hν] with w hw i
    exact transverse_frame_chart_bound B (w₀:Space (h+2)) hB hw i
  by_contra hnot
  have hmean := le_of_not_gt hnot
  have hfactor : ENNReal.ofReal ((2:ℝ)^h)*μ univ ≤ ENNReal.ofReal ((2:ℝ)^h) := by
    simpa only [mul_one] using mul_le_mul' le_rfl hμmass
  have hcast : ((h+1:ℕ):ℝ)+1 = (h+2:ℝ) := by push_cast; ring
  obtain ⟨A,hA,z,_,hbig⟩ := dyadic_original_slice_selection rows hrows μ ν N
    (by norm_num : (1/4:ℝ) < 1/2) hμ hδρ hwB hLt hLq (hq.trans hqt) hq hμmass hνmass
    hμball hνball hpair hK (by positivity : 0 ≤ (2:ℝ)^h) hNc hR hCpoint hCdir hCmass
    hcard hC₀ hlarge hfactor E hE J hJ a hJN hmean
    (by rw [hcast]; exact gaussianSelectionThreshold_uniform h hK hZ hZbox)
  rw [hcast] at hA
  obtain ⟨e,_,he⟩ := gaussian_two_dimensional_slice_chart B A w₀ hε hδ.le hρ hB hA hstable hchart
  have hbound := row_kernel_projection_bound A B hA hstable
  have hsmall : 2*((h:ℝ)*δ) < 1 := by
    have hpos : 0 ≤ 4*(h:ℝ)*ε := by positivity
    change 4*(h:ℝ)*δ+ρ+4*(h:ℝ)*ε ≤ 1/4 at hchart
    nlinarith
  have hchartAE : ∀ᵐ (w : Sphere (h+2)) ∂ν, w ∈ gaussianDirectionBand A δ →
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2))))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2)))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 := by
    filter_upwards [hν] with w hw hband
    exact he w hband hw
  have hupper := hgain N (h+2) h κ A z e μ ν E J a K ((2*Z)^h) M T a₀ hδsmall
    hK (by positivity) hM (by dsimp [T]; positivity) hTbound ha₀ hH haK hpcoef hqcoef hlow
    hE hJ (gaussianRowNeighborhood_norm rows hrows hA) hbound hsmall hEb hanchors hcover hμ hchartAE
  simp only [gaussianSelectionThreshold,gaussianPruningWeight_eq] at hbig
  exact (not_lt_of_ge hupper) hbig

end Falconer

end OAI

end ExtensionScope83

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianLossAbsorption. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope84


namespace OAI

/-! # Absorbing the concrete slice-selection losses into the planar gain -/

namespace Falconer
open Real Filter
open scoped Topology

theorem gaussian_scale_power {δ κ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    (δ^(-κ))^j = δ^(-((j:ℝ)*κ)) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
  congr 1
  ring

theorem eventually_gaussian_scale_losses {η : ℝ} (hη : 0 < η)
    (K₀ V A b : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      0 < δ ∧ K₀ ≤ δ^(-(η/100)) ∧
      4*V*(δ^(-(η/100)))^10 < δ^(-η) ∧
      A*(δ^(-(η/100)))^12*δ^(-b) ≤ δ^(-b-η) := by
  let κ := η/100
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hten : 0 < η-10*κ := by dsimp [κ]; linarith
  have htwelve : 0 < η-12*κ := by dsimp [κ]; linarith
  have hlarge := (tendsto_rpow_neg_nhdsGT_zero (show -κ < 0 by linarith)).eventually
    (eventually_ge_atTop K₀)
  have hnorm := (tendsto_rpow_neg_nhdsGT_zero (show -(η-10*κ) < 0 by linarith)).eventually
    (eventually_gt_atTop (4*V))
  have hcover := (tendsto_rpow_neg_nhdsGT_zero (show -(η-12*κ) < 0 by linarith)).eventually
    (eventually_ge_atTop A)
  filter_upwards [hlarge,hnorm,hcover,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)]
    with δ hlarge hnorm hcover hδone
  have hδ := hδone.1
  refine ⟨hδ,hlarge,?_,?_⟩
  · change 4*V*(δ^(-κ))^10 < δ^(-η)
    rw [gaussian_scale_power hδ]
    calc
      _ < δ^(-(η-10*κ))*δ^(-((10:ℝ)*κ)) :=
        mul_lt_mul_of_pos_right hnorm (Real.rpow_pos_of_pos hδ _)
      _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring
  · change A*(δ^(-κ))^12*δ^(-b) ≤ δ^(-b-η)
    rw [gaussian_scale_power hδ]
    calc
      _ = A*δ^(-(12*κ+b)) := by rw [mul_assoc,← Real.rpow_add hδ]; congr 2; ring
      _ ≤ δ^(-(b+η)) := rpow_absorb_constant hδ (by
        rw [show -((b+η)-(12*κ+b)) = -(η-12*κ) by ring]
        exact hcover)
      _ = _ := by congr 1; ring

end Falconer

end OAI

end ExtensionScope84

/- Source: OAI.MeasureTheory.Falconer.Estimates.PlanarLossBudget. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope85


namespace OAI

/-! # One scale choice supplies every scalar inequality in the planar slice application -/

namespace Falconer
open Real Filter
open scoped Topology

theorem inverse_power_gap {δ η H : ℝ} (hδ : 0 < δ) (hH : 0 < H)
    (hgap : H < δ^(-η)) : δ^η < 1/H := by
  apply (lt_div_iff₀ hH).mpr
  calc
    δ^η*H < δ^η*δ^(-η) := mul_lt_mul_of_pos_left hgap (Real.rpow_pos_of_pos hδ η)
    _ = 1 := by
      rw [Real.rpow_neg hδ.le]
      exact mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hδ η))

theorem eventually_gaussian_planar_loss_budget {η : ℝ} (hη : 0 < η)
    {V a : ℝ} (hV : 1 ≤ V) (ha : 1 ≤ a) (f b A K₀ : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      0 < δ ∧ K₀ ≤ δ^(-(η/100)) ∧
      1 ≤ 4*(δ^(-(η/100)))^10*V ∧
      (4*(δ^(-(η/100)))^10*V)*(4*a)^f ≤ δ^(-η) ∧
      (4*(δ^(-(η/100)))^10*V)*(8*a)^b ≤ δ^(-η) ∧
      δ^η < 1/(4*(δ^(-(η/100)))^10*V) ∧
      A*(δ^(-(η/100)))^12*δ^(-b) ≤ δ^(-b-η) := by
  let W : ℝ := V*((4*a)^f+(8*a)^b+1)
  have hVpos : 0 < V := by linarith
  have ha0 : 0 < a := by linarith
  have hfpos : 0 < (4*a)^f := Real.rpow_pos_of_pos (by positivity) _
  have hbpos : 0 < (8*a)^b := Real.rpow_pos_of_pos (by positivity) _
  have hVW : V < W := by dsimp [W]; nlinarith
  have hpf : V*(4*a)^f ≤ W := by dsimp [W]; nlinarith
  have hqb : V*(8*a)^b ≤ W := by dsimp [W]; nlinarith
  filter_upwards [eventually_gaussian_scale_losses hη (max K₀ 1) W A b]
    with δ hδ
  rcases hδ with ⟨hδ,hK,hgap,hcover⟩
  have hK₀ : K₀ ≤ δ^(-(η/100)) := (le_max_left _ _).trans hK
  have hK1 : 1 ≤ δ^(-(η/100)) := (le_max_right _ _).trans hK
  have hKpow : 1 ≤ (δ^(-(η/100)))^10 := one_le_pow₀ hK1
  have hH : 0 < 4*(δ^(-(η/100)))^10*V := by positivity
  have hHW : 4*(δ^(-(η/100)))^10*V < δ^(-η) := by
    apply lt_trans _ hgap
    nlinarith [Real.rpow_pos_of_pos hδ (-(η/100))]
  refine ⟨hδ,hK₀,?_,?_,?_,inverse_power_gap hδ hH hHW,hcover⟩
  · nlinarith
  · apply le_trans _ hgap.le
    nlinarith [pow_nonneg (Real.rpow_nonneg hδ.le (-(η/100))) 10]
  · apply le_trans _ hgap.le
    nlinarith [pow_nonneg (Real.rpow_nonneg hδ.le (-(η/100))) 10]

end Falconer

end OAI

end ExtensionScope85

/- Source: OAI.MeasureTheory.Falconer.Geometry.ActiveCoverScale. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope86


namespace OAI

/-! # The original tube count after codimension-h slicing -/

namespace Falconer

theorem gaussian_active_cover_scale {δ ε κ q Nc D : ℝ} (h : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hεκ : ε ≤ κ) (hD : 0 ≤ D)
    (hNc : Nc ≤ δ^(-q-ε)) :
    (δ^(-κ))^11*(Nc*(2*(D*δ))^h) ≤
      (2*D)^h*(δ^(-κ))^12*δ^(-(q-(h:ℝ))) := by
  have hε : δ^(-ε) ≤ δ^(-κ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hεκ)
  have hpower : δ^(-q-ε)*δ^h = δ^(-ε)*δ^(-(q-(h:ℝ))) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hδ,← Real.rpow_add hδ]
    congr 1
    ring
  calc
    _ ≤ (δ^(-κ))^11*(δ^(-q-ε)*(2*(D*δ))^h) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNc (by positivity)) (by positivity)
    _ = (2*D)^h*(δ^(-κ))^11*(δ^(-ε)*δ^(-(q-(h:ℝ)))) := by
      rw [show 2*(D*δ) = (2*D)*δ by ring,mul_pow]
      calc
        _ = (2*D)^h*(δ^(-κ))^11*(δ^(-q-ε)*δ^h) := by ring
        _ = _ := by rw [hpower]
    _ ≤ (2*D)^h*(δ^(-κ))^11*(δ^(-κ)*δ^(-(q-(h:ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hε (Real.rpow_nonneg hδ.le _)) (by positivity)
    _ = _ := by ring

end Falconer

end OAI

end ExtensionScope86

/- Source: OAI.MeasureTheory.Falconer.Slicing.GaussianMomentScale. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope87


namespace OAI

/-! # A common fixed coefficient for the original finite-scale moment bounds -/

namespace Falconer

theorem exists_gaussian_moment_coefficient (h : ℕ) (t q : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      (4*gaussianVectorBandConstant)^h*L*gaussianFrostmanFactor h t ≤ C*L ∧
      (2*gaussianPairBandConstant)^h*L*gaussianFrostmanFactor h q ≤ C*L ∧
      (2*gaussianPairBandConstant)^h*(|L*gaussianFrostmanFactor h q|+1) ≤ C*L := by
  let P := (4*gaussianVectorBandConstant)^h*gaussianFrostmanFactor h t
  let Q := (2*gaussianPairBandConstant)^h*gaussianFrostmanFactor h q
  let U := (2*gaussianPairBandConstant)^h*(|gaussianFrostmanFactor h q|+1)
  let C := |P|+|Q|+U+1
  have hG := gaussianPairBandConstant_pos
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hPC : P ≤ C := by dsimp [C]; linarith [le_abs_self P,abs_nonneg Q]
  have hQC : Q ≤ C := by dsimp [C]; linarith [le_abs_self Q,abs_nonneg P]
  have hUC : U ≤ C := by dsimp [C]; linarith [abs_nonneg P,abs_nonneg Q]
  refine ⟨C,hC,?_⟩
  intro L hL
  have hL0 : 0 ≤ L := by linarith
  refine ⟨?_,?_,?_⟩
  · simpa only [P,mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_right hPC hL0
  · simpa only [Q,mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_right hQC hL0
  · calc
      _ = (2*gaussianPairBandConstant)^h*(L*|gaussianFrostmanFactor h q|+1) := by
        rw [abs_mul,abs_of_nonneg hL0]
      _ ≤ (2*gaussianPairBandConstant)^h*(L*|gaussianFrostmanFactor h q|+L) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hL _) (by positivity)
      _ = U*L := by dsimp [U]; ring
      _ ≤ C*L := mul_le_mul_of_nonneg_right hUC hL0

end Falconer

end OAI

end ExtensionScope87

/- Source: OAI.MeasureTheory.Falconer.Estimates.DyadicLossAbsorption. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope88


namespace OAI

/-! # The logarithmic number of dyadic tests fits inside the chosen power loss -/

namespace Falconer
open Real Filter
open scoped Topology

theorem dyadic_log_depth (N : ℕ) :
    1-Real.log (1/(2:ℝ)^N)/Real.log 2 = (N:ℝ)+1 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [one_div,Real.log_inv,Real.log_pow]
  field_simp
  ring

theorem eventually_dyadic_loss_absorption {ε κ : ℝ} (hεκ : ε < κ) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      0 < δ ∧ C*(1-Real.log δ/Real.log 2)*δ^(-ε) ≤ δ^(-κ) := by
  have hr : 0 < κ-ε := sub_pos.mpr hεκ
  have hp : Tendsto (fun δ : ℝ => δ^(κ-ε)) (𝓝[>] 0) (𝓝 0) := by
    have hp₀ : Tendsto (fun δ : ℝ => δ^(κ-ε)) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
      simpa only [Real.zero_rpow hr.ne'] using (Real.continuous_rpow_const hr.le).tendsto (0:ℝ)
    exact hp₀.mono_left nhdsWithin_le_nhds
  have hl := tendsto_log_mul_rpow_nhdsGT_zero hr
  have ht : Tendsto (fun δ : ℝ => C*(δ^(κ-ε)-(Real.log δ*δ^(κ-ε))/Real.log 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_div,sub_zero,mul_zero] using (hp.sub (hl.div_const (Real.log 2))).const_mul C
  have hsmall := ht.eventually (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num))
  filter_upwards [hsmall,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hs hδone
  have hδ := hδone.1
  refine ⟨hδ,?_⟩
  calc
    _ = (C*(δ^(κ-ε)-(Real.log δ*δ^(κ-ε))/Real.log 2))*δ^(-κ) := by
      calc
        _ = C*(1-Real.log δ/Real.log 2)*δ^((κ-ε)+(-κ)) := by congr 2; ring
        _ = C*(1-Real.log δ/Real.log 2)*(δ^(κ-ε)*δ^(-κ)) := by rw [Real.rpow_add hδ]
        _ = _ := by ring
    _ ≤ 1*δ^(-κ) := mul_le_mul_of_nonneg_right hs.le (Real.rpow_nonneg hδ.le _)
    _ = _ := one_mul _

end Falconer

end OAI

end ExtensionScope88

/- Source: OAI.MeasureTheory.Falconer.Angular.CapNet. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope89



namespace OAI

/-!
# A separated finite cap net with uniform local multiplicity

The cardinality maximization takes place in the natural numbers. It needs
only the proved Euclidean packing bound, so no selection of infinitely many
centers or measurable choice is involved.
-/

namespace Falconer
open Set Metric

private theorem sphere_separated_card {d : ℕ} (S : Finset (Sphere d)) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 < dist x y) :
    (S.card : ℝ) ≤ (4/δ+1)^d := by
  have hinj : Function.Injective (fun x : Sphere d => (x : Space d)) := Subtype.val_injective
  have hh := separated_ball_card (S.image (fun x : Sphere d => (x : Space d))) (0 : Space d)
    (half_pos hδ) (show (0 : ℝ) ≤ 1 by norm_num) (by
      intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      exact (hsep a ha b hb (fun hab => hxy (congrArg Subtype.val hab))).le) (by
      intro x hx
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
      simpa only [dist_zero_right,sphere_norm] using (le_refl (1 : ℝ)))
  rw [Finset.card_image_of_injective S hinj] at hh
  have hr : 2*1/(δ/2)+1 = 4/δ+1 := by ring
  simpa only [hr] using hh

theorem finite_separated_cap_net (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset (Sphere d),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 < dist x y) ∧
      (∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) ∧
      (S.card : ℝ) ≤ (4/δ+1)^d ∧
      (∀ w : Sphere d, ((S.filter (fun c => dist w c ≤ δ)).card : ℝ) ≤ (5 : ℝ)^d) := by
  classical
  let P : Finset (Sphere d) → Prop := fun S =>
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 < dist x y
  let K : Set ℕ := {k | ∃ S : Finset (Sphere d), P S ∧ S.card = k}
  have hK : BddAbove K := by
    obtain ⟨N,hN⟩ := exists_nat_ge ((4/δ+1)^d)
    refine ⟨N,?_⟩
    intro k hk
    obtain ⟨S,hS,rfl⟩ := hk
    exact_mod_cast (sphere_separated_card S hδ hS).trans hN
  have hne : K.Nonempty := ⟨0,∅,(by simp [P]),rfl⟩
  obtain ⟨k,hk,hmax⟩ := hK.exists_isGreatest_of_nonempty hne
  obtain ⟨S,hS,hcard⟩ := hk
  refine ⟨S,hS,?_,sphere_separated_card S hδ hS,?_⟩
  · intro w
    by_contra hn
    have hfar : ∀ c ∈ S, δ/2 < dist w c := by
      simpa only [not_exists,not_and,not_le] using hn
    have hw : w ∉ S := by
      intro hw
      have hh := hfar w hw
      simp only [dist_self] at hh
      linarith
    have hS' : P (insert w S) := by
      intro x hx y hy hxy
      by_cases hxw : x = w
      · subst x
        have hyw : y ≠ w := fun h => hxy h.symm
        have hyS : y ∈ S := Finset.mem_of_mem_insert_of_ne hy hyw
        exact hfar y hyS
      · have hxS : x ∈ S := Finset.mem_of_mem_insert_of_ne hx hxw
        by_cases hyw : y = w
        · subst y
          simpa only [dist_comm] using hfar x hxS
        · exact hS x hxS y (Finset.mem_of_mem_insert_of_ne hy hyw) hxy
    have hbad := hmax (show (insert w S).card ∈ K from ⟨insert w S,hS',rfl⟩)
    rw [Finset.card_insert_of_notMem hw,← hcard] at hbad
    omega
  · intro w
    exact separated_sphere_overlap S hδ (fun x hx y hy hxy => (hS x hx y hy hxy).le) w

end Falconer

end OAI

end ExtensionScope89

/- Source: OAI.MeasureTheory.Falconer.Angular.OriginalDirectionChart. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope90



namespace OAI

/-! # Selecting a small direction chart on the original incidence labels -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem sphere_chart_pair_inner_nonnegative (w v c : Sphere d)
    (hw : dist w c ≤ 1/2) (hv : dist v c ≤ 1/2) :
    0 ≤ inner ℝ (w:Space d) (v:Space d) := by
  have hd : dist w v ≤ 1 := (dist_triangle w c v).trans (by rw [dist_comm c v]; linarith)
  have hn : ‖(w:Space d)-(v:Space d)‖ ≤ 1 := by simpa only [Subtype.dist_eq,dist_eq_norm] using hd
  have hsq := norm_sub_sq_real (w:Space d) (v:Space d)
  rw [sphere_norm,sphere_norm] at hsq
  nlinarith [norm_nonneg ((w:Space d)-(v:Space d))]

theorem direction_chart_pair_ae (ν : Measure (Sphere d)) [SFinite ν] (c : Sphere d)
    {ρ : ℝ} (hρ : ρ ≤ 1/2) :
    ∀ᵐ z : Sphere d × Sphere d ∂(ν.restrict (closedBall c ρ)).prod (ν.restrict (closedBall c ρ)),
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d) := by
  have ha : ∀ᵐ w ∂ν.restrict (closedBall c ρ), w ∈ closedBall c ρ := ae_restrict_mem measurableSet_closedBall
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ha,Measure.quasiMeasurePreserving_snd.ae ha]
    with z hz₁ hz₂
  exact sphere_chart_pair_inner_nonnegative z.1 z.2 c (hz₁.trans hρ) (hz₂.trans hρ)

theorem original_direction_chart_selection
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [SFinite μ] [SFinite ν]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {ρ : ℝ} (hρ : 0 < ρ) {a : ℝ≥0∞}
    (hmean : ENNReal.ofReal ((2/ρ+1)^d)*a < (μ.prod ν) E) :
    ∃ c : Sphere d, a < (μ.prod (ν.restrict (closedBall c ρ))) E := by
  classical
  obtain ⟨S,_,hcover,hcard,_⟩ := finite_separated_cap_net d (show 0 < 2*ρ by positivity)
  have hcover' (w : Sphere d) : ∃ c ∈ S, dist w c ≤ ρ := by
    have hr : (2*ρ)/2 = ρ := by ring
    simpa only [hr] using hcover w
  let F : Sphere d → Set (Space d × Sphere d) := fun c => E ∩ (univ ×ˢ closedBall c ρ)
  have hsub : E ⊆ ⋃ c ∈ S, F c := by
    intro z hz
    obtain ⟨c,hc,hd⟩ := hcover' z.2
    exact mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hc,hz,mem_univ _,hd⟩⟩
  have hmass : (μ.prod ν) E ≤ ∑ c ∈ S, (μ.prod ν) (F c) :=
    (measure_mono hsub).trans (measure_biUnion_finset_le S F)
  have he (c : Sphere d) : (μ.prod ν) (F c) = (μ.prod (ν.restrict (closedBall c ρ))) E := by
    have hprod : μ.prod (ν.restrict (closedBall c ρ)) =
        (μ.prod ν).restrict (univ ×ˢ closedBall c ρ) := by
      simpa only [Measure.restrict_univ] using
        Measure.prod_restrict (μ := μ) (ν := ν) univ (closedBall c ρ)
    rw [hprod,Measure.restrict_apply hE]
  by_contra! hn
  have hsum : (μ.prod ν) E ≤ (S.card:ℝ≥0∞)*a := hmass.trans (by
    calc
      _ ≤ ∑ _c ∈ S, a := Finset.sum_le_sum (fun c _ => by rw [he]; exact hn c)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul])
  have hcard' : (S.card:ℝ≥0∞) ≤ ENNReal.ofReal ((2/ρ+1)^d) := by
    have hh : (S.card:ℝ) ≤ (2/ρ+1)^d := by
      have hr : 4/(2*ρ)+1 = 2/ρ+1 := by field_simp; ring
      simpa only [hr] using hcard
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hh
  exact (not_le_of_gt hmean) (hsum.trans (mul_le_mul' hcard' le_rfl))

end Falconer

end OAI

end ExtensionScope90

/- Source: OAI.MeasureTheory.Falconer.Geometry.NonendpointChartGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope91







namespace OAI

/-! # Uniform nonendpoint angular decay on a fixed original direction chart -/

namespace Falconer
open Set MeasureTheory Real Filter
open scoped ENNReal Topology

theorem nonendpoint_chart_angular_gain
    (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q C ρ : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2)
    (hstable : (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2)
    (hchart : 4*(h:ℝ)*ρ+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4) :
    ∃ ε c δ₀ : ℝ, 0 < ε ∧ 0 < c ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (w₀ : Sphere (h+2)) (E : Set (Space (h+2) × Sphere (h+2)))
      (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2)),
    1/(2:ℝ)^N < δ₀ → (∀ᵐ w ∂ν, dist w w₀ ≤ ρ) →
    (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-q-ε)) →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    (μ.prod ν).real E ≤ (1/(2:ℝ)^N)^c := by
  classical
  obtain ⟨η,δF,hη,hδF,hgain⟩ := controlled_dyadic_angular_gain hpublished hq hq' hqt ht hC
  obtain ⟨Cm,hCm,hcoeff⟩ := exists_gaussian_moment_coefficient h t q
  let κ₀ := η/100
  let ε := κ₀/2
  let c := κ₀/2
  let M := (h+2:ℝ)*(2*ρ)+1
  let Z := M+1
  let V := (2*Z)^h
  let a₀ := 4+8*(h:ℝ)
  let D := 1+2*(1/4)+C*M
  let B₀ := (2:ℝ)^h*gaussianLocalBandConstant (h+1) ρ^h
  have hκ : 0 < κ₀ := by dsimp [κ₀]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hεκ : ε < κ₀ := by dsimp [ε]; linarith
  have hM : 0 < M := by dsimp [M]; positivity
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hV : 1 ≤ V := by
    apply one_le_pow₀
    change 1 ≤ 2*(M+1)
    linarith
  have ha₀ : 1 ≤ a₀ := by dsimp [a₀]; linarith [Nat.cast_nonneg (α := ℝ) h]
  have hD : 0 < D := by dsimp [D]; positivity
  have hB₀ : 0 < B₀ := by
    have hb := gaussianLocalBandConstant_pos (n := h+1) hρ
    dsimp [B₀]
    positivity
  have hplan := eventually_gaussian_planar_loss_budget hη hV ha₀ (t-(h:ℝ))
    (q-(h:ℝ)) ((2*D)^h) (4*(1+2*(2:ℝ)^h+1))
  have hdepth := eventually_dyadic_loss_absorption hεκ Cm
  have habs := (tendsto_rpow_neg_nhdsGT_zero (show -(κ₀-c) < 0 by dsimp [c]; linarith)).eventually
    (eventually_ge_atTop (1/B₀))
  obtain ⟨δ₁,hδ₁,hready⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0:ℝ) < 1 by norm_num)).mp
      (hplan.and (hdepth.and habs))
  refine ⟨ε,c,min δF (min δ₁ (min ρ 1)),hε,hc,
    lt_min hδF (lt_min hδ₁ (lt_min hρ (by norm_num))),?_⟩
  intro N κ _ _ μ ν _ _ w₀ E J a hδsmall hν hμ hμmass hνmass hμball hνball
    hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  let K : ℝ := δ^(-κ₀)
  let L : ℝ := δ^(-ε)
  let Nc : ℝ := δ^(-q-ε)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδρ : δ ≤ ρ := (hδsmall.trans_le (min_le_right _ _)).trans_le
    ((min_le_right _ _).trans (min_le_left _ _)) |>.le
  have hδ1 : δ ≤ 1 := (hδsmall.trans_le (min_le_right _ _)).trans_le
    ((min_le_right _ _).trans (min_le_right _ _)) |>.le
  obtain ⟨hp,⟨_,hd⟩,ha⟩ := hready ⟨hδ,hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
  rcases hp with ⟨_,hlarge,hH,hpcoef,hqcoef,hlow,hcoverScale⟩
  have hL : 1 ≤ L := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show -ε ≤ 0 by linarith)
  have hK : 0 < K := Real.rpow_pos_of_pos hδ _
  have hL0 : 0 ≤ L := by linarith
  have hCmL : 0 ≤ Cm*L := mul_nonneg hCm.le hL0
  have hcard : ((N+1:ℕ):ℝ)*(Cm*L) ≤ K := by
    rw [dyadic_log_depth N] at hd
    simpa only [Nat.cast_add,Nat.cast_one,mul_assoc,mul_comm,mul_left_comm] using hd
  have hCK : Cm*L ≤ K := by
    have hN : (1:ℝ) ≤ (N+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    exact (le_mul_of_one_le_left hCmL hN).trans hcard
  have hpair : ∀ᵐ u : Sphere (h+2) × Sphere (h+2) ∂ν.prod ν,
      0 ≤ inner ℝ (u.1:Space (h+2)) (u.2:Space (h+2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν,Measure.quasiMeasurePreserving_snd.ae hν]
      with u hu hv
    exact sphere_chart_pair_inner_nonnegative u.1 u.2 w₀ (hu.trans hρhalf) (hv.trans hρhalf)
  obtain ⟨B,hB⟩ := exists_transverse_row_frame (h := h) (n := h+1) (by omega) (sphere_norm w₀)
  have hchartδ : 4*(h:ℝ)*δ+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 := by
    nlinarith [mul_le_mul_of_nonneg_left hδρ (by positivity : 0 ≤ 4*(h:ℝ))]
  have hbox : (1/4)*((h+2:ℝ)*(2*ρ)+1)+δ ≤ Z := by
    change (1/4)*M+δ ≤ M+1
    nlinarith
  have hactive : K^11*(Nc*(2*(δ+(2*(1/4))*δ+(C*δ)*M))^h) ≤ δ^(-(q-(h:ℝ))-η) := by
    have hh := gaussian_active_cover_scale h hδ hδ1 hεκ.le hD.le (le_refl Nc)
    have hr : δ+(2*(1/4))*δ+(C*δ)*M = D*δ := by dsimp [D]; ring
    rw [hr]
    exact hh.trans hcoverScale
  have hNc : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc := by
    intro w
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hJN w)
  obtain ⟨hCP,hCD,hCM⟩ := hcoeff L hL
  have hg := hgain N κ μ ν w₀ B E J a ρ L L K (Cm*L) Nc Z a₀
    (hδsmall.trans_le (min_le_left _ _)) hρ.le hδρ hB hν hstable hchartδ hμ hμmass hνmass
    hL0 hL0 hμball hνball hpair hK (Real.rpow_pos_of_pos hδ _) hZ hCP hCD hCM
    hcard hCK hlarge hbox ha₀ hH (le_refl a₀) hpcoef hqcoef hlow hactive
    hE hJ hNc hEb hanchors hcover
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg.le
  have hlocal := gaussianLocalBandConstant_pos (n := h+1) hρ
  have hr' : B₀*(μ.prod ν).real E ≤ δ^κ₀ := by
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ (2:ℝ)^h),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ gaussianLocalBandConstant (h+1) ρ^h),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/K),B₀,Measure.real,one_div,
      K,Real.rpow_neg hδ.le,inv_inv,ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le κ₀),mul_assoc] using hr
  have habs' : (1/B₀)*δ^κ₀ ≤ δ^c := by
    have hh := rpow_absorb_constant (t := -κ₀) (u := -c) hδ (by
      convert ha using 1; ring_nf)
    simpa only [neg_neg] using hh
  have hI : (μ.prod ν).real E ≤ (1/B₀)*δ^κ₀ := by
    calc
      _ = (1/B₀)*(B₀*(μ.prod ν).real E) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hr' (by positivity)
  exact hI.trans habs'

end Falconer

end OAI

end ExtensionScope91

/- Source: OAI.MeasureTheory.Falconer.Slicing.SmallGaussianChart. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope92



namespace OAI

/-! # A fixed direction-chart radius for the controlled Gaussian slice geometry -/

namespace Falconer

theorem exists_small_gaussian_chart_radius (h : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/2 ∧
      (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2 ∧
      4*(h:ℝ)*ρ+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 := by
  let A : ℝ := 4*(h:ℝ)+1+8*(h:ℝ)*(h+2:ℝ)
  let ρ : ℝ := 1/(8*(A+1))
  have hh : 0 ≤ (h:ℝ) := Nat.cast_nonneg h
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have he : 8*(A+1)*ρ = 1 := by dsimp [ρ]; field_simp
  have hp : A*ρ ≤ 1/8 := by nlinarith
  have hcoef : (h:ℝ)*((h+2:ℝ)*2) ≤ A := by dsimp [A]; nlinarith
  refine ⟨ρ,hρ,?_,?_,?_⟩
  · nlinarith [mul_nonneg hA hρ.le]
  · have hb := mul_le_mul_of_nonneg_right hcoef hρ.le
    nlinarith
  · calc
      _ = A*ρ := by dsimp [A]; ring
      _ ≤ 1/8 := hp
      _ ≤ 1/4 := by norm_num

end Falconer

end OAI

end ExtensionScope92

/- Source: OAI.MeasureTheory.Falconer.Angular.NonendpointAngularGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope93



namespace OAI

/-! # The nonendpoint angular gain in every ambient dimension h+2 -/

namespace Falconer
open Set MeasureTheory Real Filter
open scoped ENNReal Topology

theorem nonendpoint_dyadic_angular_gain
    (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q C : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (hC : 0 ≤ C) :
    ∃ ε c δ₀ : ℝ, 0 < ε ∧ 0 < c ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (E : Set (Space (h+2) × Sphere (h+2)))
      (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2)),
    1/(2:ℝ)^N < δ₀ → (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-q-ε)) →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ρ,hρ,hρhalf,hstable,hchart⟩ := exists_small_gaussian_chart_radius h
  obtain ⟨ε,c₁,δ₁,hε,hc₁,hδ₁,hgain⟩ := nonendpoint_chart_angular_gain hpublished hq hq' hqt ht
    hC hρ hρhalf hstable hchart
  let H : ℝ := (2/ρ+1)^(h+2)
  let c := c₁/2
  have hc : 0 < c := by dsimp [c]; positivity
  have habs := (tendsto_rpow_neg_nhdsGT_zero (show -(c₁-c) < 0 by dsimp [c]; linarith)).eventually
    (eventually_ge_atTop H)
  obtain ⟨δ₂,hδ₂,hready⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0:ℝ) < 1 by norm_num)).mp habs
  refine ⟨ε,c,min δ₁ δ₂,hε,hc,lt_min hδ₁ hδ₂,?_⟩
  intro N κ _ _ μ ν _ _ E J a hδsmall hμ hμmass hνmass hμball hνball hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hH : H*δ^c₁ ≤ δ^c := by
    have ha : H ≤ δ^(-(c₁-c)) := hready ⟨hδ,hδsmall.trans_le (min_le_right _ _)⟩
    have hh := rpow_absorb_constant (t := -c₁) (u := -c) hδ (by
      convert ha using 1; ring_nf)
    simpa only [neg_neg] using hh
  by_contra hn
  have hlarge : ENNReal.ofReal H*ENNReal.ofReal (δ^c₁) < (μ.prod ν) E := by
    apply lt_of_le_of_lt _ (lt_of_not_ge hn)
    rw [← ENNReal.ofReal_mul (by dsimp [H]; positivity)]
    exact ENNReal.ofReal_le_ofReal hH
  obtain ⟨w₀,hw₀⟩ := original_direction_chart_selection μ ν E hE hρ hlarge
  let ν' := ν.restrict (Metric.closedBall w₀ ρ)
  have hνsupport : ∀ᵐ w ∂ν', dist w w₀ ≤ ρ := ae_restrict_mem measurableSet_closedBall
  have hν'mass : ν' univ ≤ 1 := (Measure.restrict_le_self _).trans hνmass
  have hν'ball (x : Sphere (h+2)) (j : ℕ) (hj : j ≤ N) :
      ν' (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (δ^(-ε)*(1/(2:ℝ)^j)^q) :=
    (Measure.restrict_le_self _).trans (hνball x j hj)
  have hg := hgain N κ μ ν' w₀ E J a (hδsmall.trans_le (min_le_left _ _))
    hνsupport hμ hμmass hν'mass hμball hν'ball hE hJ hJN hEb hanchors hcover
  have hgle : (μ.prod ν') E ≤ ENNReal.ofReal (δ^c₁) := by
    simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top (μ.prod ν') E)] using
      ENNReal.ofReal_le_ofReal hg
  exact (not_lt_of_ge hgle) hw₀

end Falconer

end OAI

end ExtensionScope93

/- Source: OAI.MeasureTheory.Falconer.Radial.TubeCoverChoice. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope94


namespace OAI

/-! # Measurable choice of countably listed original-label tube covers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W ι : Type*} [MeasurableSpace X] [MeasurableSpace W]

theorem tube_cover_uncovered_mass_measurable
    (μ : Measure X) [SFinite μ] (E : Set (X × W)) (hE : MeasurableSet E)
    (U : ι → W → Set X) (hU : ∀ i, MeasurableSet {p : W × X | p.2 ∈ U i p.1})
    (C : Finset ι) :
    Measurable (fun w => μ {x | (x,w) ∈ E ∧ ∀ i ∈ C, x ∉ U i w}) := by
  have hC : MeasurableSet {p : W × X | ∀ i ∈ C, p.2 ∉ U i p.1} := by
    simp only [ofPred_forall]
    exact C.measurableSet_biInter (fun i _ => (hU i).compl)
  exact measurable_measure_prodMk_left ((hE.preimage measurable_swap).inter hC)

theorem exists_measurable_tube_cover_choice
    (μ : Measure X) [SFinite μ] (E : Set (X × W)) (hE : MeasurableSet E)
    (U : ι → W → Set X) (hU : ∀ i, MeasurableSet {p : W × X | p.2 ∈ U i p.1})
    (C : ℕ → Finset ι)
    (hcover : ∀ w, ∃ n, μ {x | (x,w) ∈ E ∧ ∀ i ∈ C n, x ∉ U i w} = 0) :
    ∃ J : W → Finset ι, (∀ i, MeasurableSet {w | i ∈ J w}) ∧
      (∀ w, μ {x | (x,w) ∈ E ∧ ∀ i ∈ J w, x ∉ U i w} = 0) ∧
      ∀ w, ∃ n, J w = C n := by
  classical
  let j : W → ℕ := fun w => Nat.find (hcover w)
  have hj : Measurable j := measurable_find hcover (fun n =>
    measurableSet_eq_fun (tube_cover_uncovered_mass_measurable μ E hE U hU (C n)) measurable_const)
  refine ⟨fun w => C (j w),?_,?_,?_⟩
  · intro i
    exact hj ((Set.to_countable {n | i ∈ C n}).measurableSet)
  · intro w
    exact Nat.find_spec (hcover w)
  · intro w
    exact ⟨j w,rfl⟩

end Falconer

end OAI

end ExtensionScope94

/- Source: OAI.MeasureTheory.Falconer.Radial.TubeCoverEnumeration. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope95



namespace OAI

/-! # Enumerating the admissible finite lists from a bounded anchor net -/

namespace Falconer
open Set
variable {X : Type*}

theorem bounded_finset_enumeration (G : Finset X) (N : ℕ) :
    ∃ C : ℕ → Finset X, (∀ n, C n ⊆ G ∧ (C n).card ≤ N) ∧
      ∀ J : Finset X, J ⊆ G → J.card ≤ N → ∃ n, C n = J := by
  classical
  let S := G.powerset.filter (fun J => J.card ≤ N)
  have hs : (∅ : Finset X) ∈ S := by simp [S]
  have : Nonempty {J : Finset X // J ∈ S} := ⟨⟨∅,hs⟩⟩
  obtain ⟨f,hf⟩ := exists_surjective_nat {J : Finset X // J ∈ S}
  refine ⟨fun n => (f n).val,?_,?_⟩
  · intro n
    have hp := Finset.mem_filter.mp (f n).property
    exact ⟨Finset.mem_powerset.mp hp.1,hp.2⟩
  · intro J hJG hJN
    have hJS : J ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hJG,hJN⟩
    obtain ⟨n,hn⟩ := hf ⟨J,hJS⟩
    exact ⟨n,congrArg Subtype.val hn⟩

end Falconer

end OAI

end ExtensionScope95

/- Source: OAI.MeasureTheory.Falconer.Radial.MeasurableTubeCover. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope96


namespace OAI

/-! # Measurable bounded-grid covers of the original direction fibers -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem original_tube_cover_choice (μ : Measure (Space d)) [SFinite μ]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {D ε δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (hbounded : ∀ t ∈ E, ‖t.1‖ ≤ D)
    (hcover : ∀ w : Sphere d, ∃ S : Finset (Space d), S.card ≤ N ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ G : Finset (Space d), (∀ a ∈ G, ‖a‖ ≤ D) ∧
      ∃ J : Sphere d → Finset (Space d),
        (∀ a, MeasurableSet {w | a ∈ J w}) ∧ (∀ w, J w ⊆ G ∧ (J w).card ≤ N) ∧
        ∀ w, μ {x | (x,w) ∈ E ∧ ∀ a ∈ J w,
          ¬‖perpendicularPart (w:Space d) (x-a)‖ ≤ 2*ε+δ} = 0 := by
  classical
  obtain ⟨G,hGb,hGn⟩ := exists_bounded_anchor_net (d := d) D hδ
  obtain ⟨C,hC,hCs⟩ := bounded_finset_enumeration G N
  let U : Space d → Sphere d → Set (Space d) := fun a w =>
    {x | ‖perpendicularPart (w:Space d) (x-a)‖ ≤ 2*ε+δ}
  have hU (a : Space d) : MeasurableSet {p : Sphere d × Space d | p.2 ∈ U a p.1} := by
    dsimp [U,perpendicularPart]
    exact measurableSet_le (by fun_prop) measurable_const
  have hc : ∀ w : Sphere d, ∃ n, μ {x | (x,w) ∈ E ∧ ∀ a ∈ C n, x ∉ U a w} = 0 := by
    intro w
    obtain ⟨S,hSN,hS⟩ := hcover w
    obtain ⟨J,hJG,hJS,hJ⟩ := rounded_tube_cover w {x | (x,w) ∈ E} S G
      (fun x hx => hGn x (hbounded (x,w) hx)) hS
    obtain ⟨n,hn⟩ := hCs J hJG (hJS.trans hSN)
    refine ⟨n,?_⟩
    apply measure_mono_null (t := ∅) _ (measure_empty)
    intro x hx
    obtain ⟨a,ha,hxa⟩ := hJ x hx.1
    exact (hx.2 a (hn.symm ▸ ha) hxa).elim
  obtain ⟨J,hJ,hzero,hJC⟩ := exists_measurable_tube_cover_choice μ E hE U hU C hc
  refine ⟨G,hGb,J,hJ,?_,hzero⟩
  intro w
  obtain ⟨n,hn⟩ := hJC w
  simpa only [hn] using hC n

theorem finite_tube_cover_relation_measurable
    (G : Finset (Space d)) (J : Sphere d → Finset (Space d))
    (hJ : ∀ a, MeasurableSet {w | a ∈ J w}) (hJG : ∀ w, J w ⊆ G) (ε : ℝ) :
    MeasurableSet {t : Space d × Sphere d |
      ∃ a ∈ J t.2, ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε} := by
  have hm : MeasurableSet {t : Space d × Sphere d |
      ∃ a ∈ G, a ∈ J t.2 ∧ ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε} := by
    have hu : MeasurableSet (⋃ a ∈ G, {t : Space d × Sphere d |
        a ∈ J t.2 ∧ ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε}) := by
      apply G.measurableSet_biUnion
      intro a _
      have hp : MeasurableSet {t : Space d × Sphere d |
          ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε} := by
        dsimp [perpendicularPart]
        exact measurableSet_le (by fun_prop) measurable_const
      exact ((hJ a).preimage measurable_snd).inter hp
    convert hu using 1
    ext t
    simp only [mem_ofPred_eq,mem_iUnion,exists_prop]
  convert hm using 1
  ext t
  constructor
  · rintro ⟨a,ha,hp⟩
    exact ⟨a,hJG t.2 ha,ha,hp⟩
  · rintro ⟨a,_,ha,hp⟩
    exact ⟨a,ha,hp⟩

end Falconer

end OAI

end ExtensionScope96

/- Source: OAI.MeasureTheory.Falconer.Estimates.FiniteAnchorLabels. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope97


namespace OAI

/-! # Finite anchor labels for the measurable original tube lists -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

noncomputable def finiteAnchorLabels (G J : Finset (Space d)) : Finset {a // a ∈ G} := by
  classical
  exact J.subtype (fun a => a ∈ G)

theorem finiteAnchorLabels_mem (G J : Finset (Space d)) (a : {a // a ∈ G}) :
    a ∈ finiteAnchorLabels G J ↔ a.val ∈ J := by
  classical
  exact Finset.mem_subtype

theorem finiteAnchorLabels_card (G J : Finset (Space d)) (hJG : J ⊆ G) :
    (finiteAnchorLabels G J).card = J.card := by
  classical
  rw [finiteAnchorLabels,Finset.card_subtype]
  congr 1
  exact Finset.filter_eq_self.mpr (fun a ha => hJG ha)

theorem finiteAnchorLabels_measurable (G : Finset (Space d)) (J : Sphere d → Finset (Space d))
    (hJ : ∀ a, MeasurableSet {w | a ∈ J w}) (a : {a // a ∈ G}) :
    MeasurableSet {w | a ∈ finiteAnchorLabels G (J w)} := by
  simpa only [finiteAnchorLabels_mem] using hJ a.val

theorem finiteAnchorLabels_uncovered (G : Finset (Space d)) (J : Finset (Space d))
    (hJG : J ⊆ G) (w : Sphere d) (R : ℝ) (x : Space d) :
    (∀ a ∈ finiteAnchorLabels G J, ¬‖perpendicularPart (w:Space d) (x-a.val)‖ ≤ R) ↔
      ∀ a ∈ J, ¬‖perpendicularPart (w:Space d) (x-a)‖ ≤ R := by
  constructor
  · intro h a ha
    exact h ⟨a,hJG ha⟩ ((finiteAnchorLabels_mem G J _).mpr ha)
  · intro h a ha
    exact h a.val ((finiteAnchorLabels_mem G J _).mp ha)

theorem original_finite_label_cover_choice (μ : Measure (Space d)) [SFinite μ]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {D ε δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (hbounded : ∀ t ∈ E, ‖t.1‖ ≤ D)
    (hcover : ∀ w : Sphere d, ∃ S : Finset (Space d), S.card ≤ N ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ G : Finset (Space d), (∀ a ∈ G, ‖a‖ ≤ D) ∧
      ∃ J : Sphere d → Finset {a // a ∈ G},
        (∀ a, MeasurableSet {w | a ∈ J w}) ∧ (∀ w, (J w).card ≤ N) ∧
        ∀ w, μ {x | (x,w) ∈ E ∧ ∀ a ∈ J w,
          ¬‖perpendicularPart (w:Space d) (x-a.val)‖ ≤ 2*ε+δ} = 0 := by
  obtain ⟨G,hGb,J,hJ,hJG,hzero⟩ := original_tube_cover_choice μ E hE hδ N hbounded hcover
  refine ⟨G,hGb,(fun w => finiteAnchorLabels G (J w)),?_,?_,?_⟩
  · exact finiteAnchorLabels_measurable G J hJ
  · intro w
    rw [finiteAnchorLabels_card G (J w) (hJG w).1]
    exact (hJG w).2
  · intro w
    simpa only [finiteAnchorLabels_uncovered G (J w) (hJG w).1] using hzero w

end Falconer

end OAI

end ExtensionScope97

/- Source: OAI.MeasureTheory.Falconer.Measures.OriginalCoverRestriction. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope98


namespace OAI

/-! # Null original fiber losses stay null for every retained slice -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]

theorem product_inter_eq_of_null_original_fibers
    (μ α : Measure X) (β : Measure W) [SFinite α] [SFinite β] (hα : α ≪ μ)
    (E F : Set (X × W)) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hzero : ∀ w, μ {x | (x,w) ∈ E ∧ (x,w) ∉ F} = 0) :
    (α.prod β) (E ∩ F) = (α.prod β) E := by
  have hz : (α.prod β) (E \ F) = 0 := by
    rw [Measure.prod_apply_symm (hE.diff hF)]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact ae_of_all _ (fun w => hα (hzero w))
  apply measure_congr
  have hnot : ∀ᵐ t ∂α.prod β, t ∉ E \ F := measure_eq_zero_iff_ae_notMem.mp hz
  filter_upwards [hnot] with t ht
  simp only [mem_sdiff] at ht
  apply propext
  simp only [mem_inter_iff]
  tauto

theorem gaussian_pruned_inter_eq_of_null_original_fibers {d h : ℕ} {ι : Type*}
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E F : Set (Space d × Sphere d)) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hzero : ∀ w, μ {x | (x,w) ∈ E ∧ (x,w) ∉ F} = 0)
    (p : (Fin h → Space d) × Space h) :
    gaussianPrunedIncidence μ ν δ r TP TD M (E ∩ F) p =
      gaussianPrunedIncidence μ ν δ r TP TD M E p := by
  apply product_inter_eq_of_null_original_fibers μ _ _ _ E F hE hF hzero
  exact Measure.absolutelyContinuous_restrict.trans
    (Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict)

end Falconer

end OAI

end ExtensionScope98

/- Source: OAI.MeasureTheory.Falconer.Radial.PreparedTubeRelation. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope99



namespace OAI

/-! # Preparing a pointwise covered relation without losing original fiber mass -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem prepare_original_tube_relation (μ : Measure (Space d)) [SFinite μ]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {D ε δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (hbounded : ∀ t ∈ E, ‖t.1‖ ≤ D)
    (hcover : ∀ w : Sphere d, ∃ S : Finset (Space d), S.card ≤ N ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ G : Finset (Space d), (∀ a ∈ G, ‖a‖ ≤ D) ∧
      ∃ J : Sphere d → Finset {a // a ∈ G}, ∃ F : Set (Space d × Sphere d),
        MeasurableSet F ∧ F ⊆ E ∧
        (∀ a, MeasurableSet {w | a ∈ J w}) ∧ (∀ w, (J w).card ≤ N) ∧
        (∀ w, μ {x | (x,w) ∈ E ∧ (x,w) ∉ F} = 0) ∧
        ∀ t ∈ F, ∃ a ∈ J t.2, ‖perpendicularPart (t.2:Space d) (t.1-a.val)‖ ≤ 2*ε+δ := by
  classical
  obtain ⟨G,hGb,J,hJ,hJG,hzero⟩ := original_tube_cover_choice μ E hE hδ N hbounded hcover
  let C : Set (Space d × Sphere d) :=
    {t | ∃ a ∈ J t.2, ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ 2*ε+δ}
  have hC : MeasurableSet C := finite_tube_cover_relation_measurable G J hJ
    (fun w => (hJG w).1) _
  refine ⟨G,hGb,(fun w => finiteAnchorLabels G (J w)),E ∩ C,hE.inter hC,inter_subset_left,
    finiteAnchorLabels_measurable G J hJ,?_,?_,?_⟩
  · intro w
    rw [finiteAnchorLabels_card G (J w) (hJG w).1]
    exact (hJG w).2
  · intro w
    have he : {x | (x,w) ∈ E ∧ (x,w) ∉ E ∩ C} =
        {x | (x,w) ∈ E ∧ ∀ a ∈ J w, ¬‖perpendicularPart (w:Space d) (x-a)‖ ≤ 2*ε+δ} := by
      ext x
      constructor
      · rintro ⟨hx,hn⟩
        refine ⟨hx,fun a ha hp => hn ⟨hx,?_⟩⟩
        exact ⟨a,ha,hp⟩
      · rintro ⟨hx,hn⟩
        refine ⟨hx,fun ht => ?_⟩
        obtain ⟨a,ha,hp⟩ := ht.2
        exact hn a ha hp
    rw [he]
    exact hzero w
  · intro t ht
    obtain ⟨a,ha,hp⟩ := ht.2
    refine ⟨⟨a,(hJG t.2).1 ha⟩,?_,hp⟩
    exact (finiteAnchorLabels_mem G (J t.2) _).mpr ha

end Falconer

end OAI

end ExtensionScope99

/- Source: OAI.MeasureTheory.Falconer.Radial.NonendpointTubeGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope100



namespace OAI

/-! # Nonendpoint angular decay for arbitrary original finite fiber covers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem nonendpoint_dyadic_tube_gain
    (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q C : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (hC : 0 ≤ C) :
    ∃ ε c δ₀ : ℝ, 0 < ε ∧ 0 < c ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν] (E : Set (Space (h+2) × Sphere (h+2))),
    1/(2:ℝ)^N < δ₀ → (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
    MeasurableSet E → (∀ u ∈ E, ‖u.1‖ ≤ 1/4) →
    (∀ w : Sphere (h+2), ∃ S : Finset (Space (h+2)),
      (S.card : ℝ) ≤ (1/(2:ℝ)^N)^(-q-ε) ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S,
        ‖perpendicularPart (w:Space (h+2)) (x-a)‖ ≤ C*(1/(2:ℝ)^N)) →
    (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ε,c,δ₀,hε,hc,hδ₀,hgain⟩ := nonendpoint_dyadic_angular_gain hpublished hq hq' hqt ht
    (by linarith : 0 ≤ 2*C+1)
  refine ⟨ε,c,δ₀,hε,hc,hδ₀,?_⟩
  intro N μ ν _ _ E hδsmall hμ hμmass hνmass hμball hνball hE hEb hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨G,hG,J,F,hF,hFE,hJ,hcard,hzero,hcoverF⟩ :=
    prepare_original_tube_relation μ E hE hδ (Nat.floor (δ^(-q-ε))) hEb (by
      intro w
      obtain ⟨S,hS,hcoverS⟩ := hcover w
      exact ⟨S,Nat.le_floor hS,hcoverS⟩)
  have hmass : (μ.prod ν) F = (μ.prod ν) E := by
    have hh := product_inter_eq_of_null_original_fibers μ μ ν Measure.AbsolutelyContinuous.rfl
      E F hE hF hzero
    simpa only [inter_eq_right.mpr hFE] using hh
  rw [← hmass]
  refine hgain N {a // a ∈ G} μ ν F J (fun a => a.val) hδsmall hμ hμmass hνmass
    hμball hνball hF hJ ?_ (fun u hu => hEb u (hFE hu)) (fun _ i _ => hG i.val i.property) ?_
  · intro w
    have hh : ((J w).card : ℝ) ≤ (Nat.floor (δ^(-q-ε)) : ℝ) := by exact_mod_cast hcard w
    exact hh.trans (Nat.floor_le (Real.rpow_nonneg hδ.le _))
  · intro u hu
    obtain ⟨a,ha,hp⟩ := hcoverF u hu
    refine ⟨a,ha,?_⟩
    nlinarith

end Falconer

end OAI

end ExtensionScope100

/- Source: OAI.MeasureTheory.Falconer.Angular.BadDirectionEnvelope. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope101


namespace OAI

/-! # A Borel envelope for geometric bad directions

The finite anchor net and the envelope depend only on the point law and the
geometric test, before a direction measure is selected.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def boundedTubeUnion (D R : ℝ) (J : Finset (Space d))
    (w : Sphere d) : Set (Space d) :=
  {x | ‖x‖ ≤ D ∧ ∃ a ∈ J, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ R}

theorem boundedTubeUnion_joint_measurable (D R : ℝ) (J : Finset (Space d)) :
    MeasurableSet {p : Sphere d × Space d | p.2 ∈ boundedTubeUnion D R J p.1} := by
  have hU : MeasurableSet (⋃ a ∈ J, {p : Sphere d × Space d |
      ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R}) := by
    apply J.measurableSet_biUnion
    intro a _
    unfold perpendicularPart
    exact measurableSet_le (by fun_prop) measurable_const
  have he : {p : Sphere d × Space d | ∃ a ∈ J,
      ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R} =
      ⋃ a ∈ J, {p : Sphere d × Space d | ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R} := by
    ext p
    simp only [mem_iUnion,mem_ofPred_eq,exists_prop]
  have hb : MeasurableSet {p : Sphere d × Space d | ‖p.2‖ ≤ D} :=
    measurableSet_le (by fun_prop) measurable_const
  have hU' : MeasurableSet {p : Sphere d × Space d | ∃ a ∈ J,
      ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R} := by
    rw [he]
    exact hU
  change MeasurableSet ({p : Sphere d × Space d | ‖p.2‖ ≤ D} ∩ _)
  exact hb.inter hU'

theorem boundedTubeUnion_mass_measurable (μ : Measure (Space d)) [SFinite μ]
    (D R : ℝ) (J : Finset (Space d)) :
    Measurable (fun w : Sphere d => μ (boundedTubeUnion D R J w)) :=
  measurable_measure_prodMk_left (boundedTubeUnion_joint_measurable D R J)

noncomputable def finiteBadDirections (μ : Measure (Space d))
    (G : Finset (Space d)) (N : ℕ) (D R : ℝ) (a : ℝ≥0∞) : Set (Sphere d) :=
  {w | ∃ J ∈ G.powerset, J.card ≤ N ∧ a ≤ μ (boundedTubeUnion D R J w)}

theorem finiteBadDirections_measurable (μ : Measure (Space d)) [SFinite μ]
    (G : Finset (Space d)) (N : ℕ) (D R : ℝ) (a : ℝ≥0∞) :
    MeasurableSet (finiteBadDirections μ G N D R a) := by
  classical
  have hU : MeasurableSet (⋃ J ∈ G.powerset,
      {w : Sphere d | J.card ≤ N ∧ a ≤ μ (boundedTubeUnion D R J w)}) := by
    apply G.powerset.measurableSet_biUnion
    intro J _
    exact (MeasurableSet.const _).inter
      (measurableSet_le measurable_const (boundedTubeUnion_mass_measurable μ D R J))
  convert hU using 1
  ext w
  simp only [finiteBadDirections,mem_iUnion,mem_ofPred_eq,exists_prop]

theorem original_bad_direction_mem_envelope (μ : Measure (Space d)) [SFinite μ]
    {D R δ : ℝ} (G : Finset (Space d)) (N : ℕ) (a : ℝ≥0∞)
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (hnet : ∀ x : Space d, ‖x‖ ≤ D → ∃ b ∈ G, ‖x-b‖ ≤ δ)
    (w : Sphere d) (S : Finset (Space d)) (hS : S.card ≤ N)
    (hmass : a ≤ μ {x | ∃ b ∈ S, ‖perpendicularPart (w:Space d) (x-b)‖ ≤ R}) :
    w ∈ finiteBadDirections μ G N D (2*R+δ) a := by
  classical
  let E := boundedTubeUnion D R S w
  obtain ⟨J,hJG,hJS,hcover⟩ := rounded_tube_cover w E S G
    (fun x hx => hnet x hx.1) (fun _ hx => hx.2)
  refine ⟨J,Finset.mem_powerset.mpr hJG,hJS.trans hS,?_⟩
  have hrestrict : μ {x | ∃ b ∈ S, ‖perpendicularPart (w:Space d) (x-b)‖ ≤ R} ≤ μ E := by
    apply measure_mono_ae
    filter_upwards [hμ] with x hx hm
    exact ⟨hx,hm⟩
  apply (hmass.trans hrestrict).trans
  apply measure_mono
  intro x hx
  exact ⟨hx.1,hcover x hx⟩

end Falconer

end OAI

end ExtensionScope101

/- Source: OAI.MeasureTheory.Falconer.Angular.BadDirectionSelection. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope102


namespace OAI

/-! # A measurable incidence witnessing every direction in the finite envelope -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem exists_finite_bad_incidence (μ : Measure (Space d)) [SFinite μ]
    (G : Finset (Space d)) (N : ℕ) (D R : ℝ) (a : ℝ≥0∞) :
    ∃ J : Sphere d → Finset (Space d), ∃ F : Set (Space d × Sphere d),
      MeasurableSet F ∧ (∀ w, J w ⊆ G ∧ (J w).card ≤ N) ∧
      (∀ x, MeasurableSet {w | x ∈ J w}) ∧
      (∀ p ∈ F, ‖p.1‖ ≤ D) ∧
      (∀ p ∈ F, ∃ x ∈ J p.2, ‖perpendicularPart (p.2:Space d) (p.1-x)‖ ≤ R) ∧
      ∀ (ν : Measure (Sphere d)) [SFinite ν],
        a*ν (finiteBadDirections μ G N D R a) ≤ (μ.prod ν) F := by
  classical
  let B := finiteBadDirections μ G N D R a
  have hB : MeasurableSet B := finiteBadDirections_measurable μ G N D R a
  obtain ⟨C,hC,hCs⟩ := bounded_finset_enumeration G N
  have hfind : ∀ w : Sphere d, ∃ n : ℕ,
      w ∉ B ∨ a ≤ μ (boundedTubeUnion D R (C n) w) := by
    intro w
    by_cases hw : w ∈ B
    · obtain ⟨J,hJG,hJN,hm⟩ := hw
      obtain ⟨n,rfl⟩ := hCs J (Finset.mem_powerset.mp hJG) hJN
      exact ⟨n,Or.inr hm⟩
    · exact ⟨0,Or.inl hw⟩
  let j : Sphere d → ℕ := fun w => Nat.find (hfind w)
  have hj : Measurable j := measurable_find hfind (fun n => hB.compl.union
    (measurableSet_le measurable_const (boundedTubeUnion_mass_measurable μ D R (C n))))
  let J : Sphere d → Finset (Space d) := fun w => C (j w)
  have hJ (x : Space d) : MeasurableSet {w | x ∈ J w} :=
    hj ((Set.to_countable {n | x ∈ C n}).measurableSet)
  let F : Set (Space d × Sphere d) := {p | p.2 ∈ B ∧ p.1 ∈ boundedTubeUnion D R (J p.2) p.2}
  have hF : MeasurableSet F := by
    have ht := finite_tube_cover_relation_measurable G J hJ (fun w => (hC (j w)).1) R
    have hb : MeasurableSet {p : Space d × Sphere d | ‖p.1‖ ≤ D} :=
      measurableSet_le (by fun_prop) measurable_const
    exact (hB.preimage measurable_snd).inter (hb.inter ht)
  refine ⟨J,F,hF,(fun w => hC (j w)),hJ,(fun _ hp => hp.2.1),(fun _ hp => hp.2.2),?_⟩
  intro ν _
  have hbound (w : Sphere d) : B.indicator (fun _ => a) w ≤ μ {x | (x,w) ∈ F} := by
    by_cases hw : w ∈ B
    · rw [indicator_of_mem hw]
      have hm := (Nat.find_spec (hfind w)).resolve_left (not_not.mpr hw)
      have he : {x | (x,w) ∈ F} = boundedTubeUnion D R (J w) w := by
        ext x
        simp only [F,mem_ofPred_eq,hw,true_and]
      rw [he]
      exact hm
    · rw [indicator_of_notMem hw]
      exact bot_le
  rw [Measure.prod_apply_symm hF]
  calc
    _ = ∫⁻ w, B.indicator (fun _ => a) w ∂ν := by
      rw [lintegral_indicator hB,lintegral_const,Measure.restrict_apply_univ]
    _ ≤ _ := lintegral_mono hbound

end Falconer

end OAI

end ExtensionScope102

/- Source: OAI.MeasureTheory.Falconer.Incidence.PowerIncidenceMass. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope103



namespace OAI

/-! # Turning a power-small incidence into a power-small direction mass -/

namespace Falconer
open scoped ENNReal

theorem ennreal_mass_of_power_incidence {δ b c : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hbc : 2*b ≤ c) (M : ℝ≥0∞)
    (h : ENNReal.ofReal (δ^b)*M ≤ ENNReal.ofReal (δ^c)) : M ≤ ENNReal.ofReal (δ^b) := by
  have h0 : ENNReal.ofReal (δ^b) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ _))
  have hh := mul_le_mul' (le_refl ((ENNReal.ofReal (δ^b))⁻¹)) h
  rw [← mul_assoc,ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top,one_mul] at hh
  apply hh.trans
  rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hδ _),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.rpow_neg hδ.le,← Real.rpow_add hδ]
  exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

end Falconer

end OAI

end ExtensionScope103

/- Source: OAI.MeasureTheory.Falconer.Estimates.EndpointCountBudget. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope104


namespace OAI

/-! # The strict dimension gap absorbs all endpoint tube-counting losses -/

namespace Falconer
open Real Filter
open scoped Topology

theorem endpoint_count_power {δ : ℝ} (hδ : 0 < δ) (C a κ s : ℝ) :
    (δ^(-1-κ))^3*((6*C+35)/δ^a)^6*(δ^(-κ)*(6*δ)^s)^2 =
      ((6*C+35)^6*((6:ℝ)^s)^2)*δ^(2*s-3-6*a-5*κ) := by
  have hp (t : ℝ) (k : ℕ) : (δ^t)^k = δ^(t*(k:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
  rw [Real.mul_rpow (by norm_num) hδ.le,div_pow,mul_pow,mul_pow,
    hp (-1-κ) 3,hp a 6,hp (-κ) 2,hp s 2]
  calc
    _ = ((6*C+35)^6*((6:ℝ)^s)^2)*
        (δ^((-1-κ)*3)/δ^(a*6)*δ^(-κ*2)*δ^(s*2)) := by ring_nf
    _ = _ := by
      rw [← Real.rpow_sub hδ,← Real.rpow_add hδ,← Real.rpow_add hδ]
      congr 1
      ring_nf

theorem eventually_endpoint_count_budget {s a κ : ℝ}
    (hgap : 0 < 2*s-3-6*a-7*κ) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧
      (δ^(-1-κ))^3*((6*C+35)/δ^a)^6*(δ^(-κ)*(6*δ)^s)^2 < (δ^κ)^2 := by
  let K : ℝ := (6*C+35)^6*((6:ℝ)^s)^2
  have hh := (tendsto_rpow_neg_nhdsGT_zero (show -(2*s-3-6*a-7*κ) < 0 by linarith)).eventually
    (eventually_gt_atTop K)
  filter_upwards [hh,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hd hδ
  refine ⟨hδ.1,?_⟩
  rw [endpoint_count_power hδ.1]
  calc
    _ < δ^(-(2*s-3-6*a-7*κ))*δ^(2*s-3-6*a-5*κ) :=
      mul_lt_mul_of_pos_right hd (Real.rpow_pos_of_pos hδ.1 _)
    _ = (δ^κ)^2 := by
      rw [← Real.rpow_add hδ.1,← Real.rpow_natCast,← Real.rpow_mul hδ.1.le]
      congr 1
      ring_nf

end Falconer

end OAI

end ExtensionScope104

/- Source: OAI.MeasureTheory.Falconer.Estimates.EndpointPowerAbsorption. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope105


namespace OAI

/-! # Strict power gaps used in endpoint row and triple selection -/

namespace Falconer
open Real Filter
open scoped Topology

theorem eventually_const_mul_rpow_lt {p q : ℝ} (hpq : q < p) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧ C*δ^p < δ^q := by
  have hh := (tendsto_rpow_neg_nhdsGT_zero (show q-p < 0 by linarith)).eventually
    (eventually_gt_atTop C)
  filter_upwards [hh,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hd hδ
  refine ⟨hδ.1,?_⟩
  calc
    _ < δ^(q-p)*δ^p := mul_lt_mul_of_pos_right hd (Real.rpow_pos_of_pos hδ.1 _)
    _ = _ := by rw [← Real.rpow_add hδ.1]; congr 1; ring

theorem eventually_endpoint_selection_powers {u τ c₁ c₂ : ℝ}
    (hu : 0 < u) (hτ : 30*u < τ) (hc₁ : τ+10*u < c₁) (hc₂ : τ+10*u < c₂)
    (V C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧
      12*δ^(τ-6*u) < δ^(24*u) ∧
      2*δ^(40*u) < δ^(36*u) ∧
      C*δ^(-6*u) < δ^(-40*u) ∧
      V*δ^(2*u) < δ^u/4 ∧
      V*δ^(c₁-τ-9*u) < δ^u/4 ∧ V*δ^(c₂-τ-9*u) < δ^u/4 := by
  have hbad := eventually_const_mul_rpow_lt (show 24*u < τ-6*u by linarith) 12
  have hmass := eventually_const_mul_rpow_lt (show 36*u < 40*u by linarith) 2
  have hcoef := eventually_const_mul_rpow_lt (show -40*u < -6*u by linarith) C
  have hbase := eventually_const_mul_rpow_lt (show u < 2*u by linarith) (4*V)
  have hpair := eventually_const_mul_rpow_lt (show u < c₁-τ-9*u by linarith) (4*V)
  have htriple := eventually_const_mul_rpow_lt (show u < c₂-τ-9*u by linarith) (4*V)
  filter_upwards [hbad,hmass,hcoef,hbase,hpair,htriple] with δ hb hm hC hB hP hT
  exact ⟨hb.1,hb.2,hm.2,hC.2,by linarith [hB.2],by linarith [hP.2],by linarith [hT.2]⟩

end Falconer

end OAI

end ExtensionScope105

/- Source: OAI.MeasureTheory.Falconer.Estimates.EndpointDyadicScale. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope106


namespace OAI

/-! # Dyadic cutoff and power conversions for endpoint assembly -/

namespace Falconer
open Filter
open scoped Topology

theorem dyadic_inverse_tendsto :
    Tendsto (fun N : ℕ => 1/(2:ℝ)^N) atTop (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [one_div,inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹)
        (by norm_num : (2:ℝ)⁻¹ < 1))
  · filter_upwards [] with N
    change 0 < 1/(2:ℝ)^N
    positivity

theorem dyadic_depth_of_inverse_lt {N B : ℕ}
    (h : 1/(2:ℝ)^N < 1/(2:ℝ)^B) : B ≤ N := by
  by_contra hn
  have hp : (2:ℝ)^N ≤ (2:ℝ)^B := pow_le_pow_right₀ (by norm_num) (by omega)
  have hi : 1/(2:ℝ)^B ≤ 1/(2:ℝ)^N := one_div_le_one_div_of_le (by positivity) hp
  exact (not_lt_of_ge hi) h

theorem dyadic_inverse_rpow (N : ℕ) (c : ℝ) :
    ((2:ℝ)^N)^(-c) = (1/(2:ℝ)^N)^c := by
  rw [one_div,Real.inv_rpow (by positivity),Real.rpow_neg (by positivity)]

theorem dyadic_loss_conversion (N : ℕ) (c : ℝ) :
    ((2:ℝ)^N)^c = (1/(2:ℝ)^N)^(-c) := by
  simpa only [neg_neg] using dyadic_inverse_rpow N (-c)

end Falconer

end OAI

end ExtensionScope106

/- Source: OAI.MeasureTheory.Falconer.Angular.NonendpointBadDirections. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope107





namespace OAI

/-! # A universal Borel bad-direction envelope in the nonendpoint regime -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem nonendpoint_bad_direction_envelope (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {t q C : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
    (hqt : q < t) (ht : t-(h:ℝ) < 1) (hC : 0 ≤ C) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ : Measure (Space (h+2))) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      ∃ B : Set (Sphere (h+2)), MeasurableSet B ∧
        {w : Sphere (h+2) | ∃ S : Finset (Space (h+2)), (S.card:ℝ) ≤ (1/(2:ℝ)^N)^(-q-b) ∧
          ENNReal.ofReal ((1/(2:ℝ)^N)^b) ≤
            μ {x | ∃ v ∈ S, ‖perpendicularPart (w:Space (h+2)) (x-v)‖ ≤ C*(1/(2:ℝ)^N)}} ⊆ B ∧
        ∀ (ν : Measure (Sphere (h+2))) [IsFiniteMeasure ν], ν univ ≤ 1 →
          (∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
          ν B ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
  classical
  obtain ⟨ε₀,c,δ₀,hε₀,hc,hδ₀,hgain⟩ := nonendpoint_dyadic_tube_gain hpublished hq hq' hqt ht
    (by linarith : 0 ≤ 2*C+1)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    (dyadic_inverse_tendsto.eventually (Ioo_mem_nhdsGT hδ₀))
  let ε : ℝ := ε₀/2
  let b : ℝ := min ε (c/3)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hb : 0 < b := lt_min hε (by positivity)
  have hεle : ε ≤ ε₀ := by dsimp [ε]; linarith
  have hble : b ≤ ε₀ := (min_le_left _ _).trans hεle
  have hbc : 2*b ≤ c := by have hh := min_le_right ε (c/3); dsimp [b]; linarith
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ _ hμ hμball
  let δ : ℝ := 1/(2:ℝ)^N
  let count : ℕ := Nat.floor (δ^(-q-b))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) : (1:ℝ) ≤ (2:ℝ)^N)
  have hL : δ^(-ε) ≤ δ^(-ε₀) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hεle)
  obtain ⟨G,hG,hnet⟩ := exists_bounded_anchor_net (d := h+2) (1/4) hδ
  let B := finiteBadDirections μ G count (1/4) ((2*C+1)*δ) (ENNReal.ofReal (δ^b))
  refine ⟨B,finiteBadDirections_measurable μ G count _ _ _,?_,?_⟩
  · rintro w ⟨S,hS,hmass⟩
    have hh := original_bad_direction_mem_envelope μ G count (ENNReal.ofReal (δ^b))
      hμ hnet w S (Nat.le_floor hS) hmass
    have he : 2*(C*δ)+δ = (2*C+1)*δ := by ring
    change w ∈ finiteBadDirections μ G count (1/4) (2*(C*δ)+δ) (ENNReal.ofReal (δ^b)) at hh
    rw [he] at hh
    exact hh
  · intro ν _ hνmass hνball
    obtain ⟨J,F,hF,hJ,hJmeas,hFb,hcover,hlower⟩ :=
      exists_finite_bad_incidence μ G count (1/4) ((2*C+1)*δ) (ENNReal.ofReal (δ^b))
    have hcount : (count:ℝ) ≤ δ^(-q-ε₀) :=
      (Nat.floor_le (Real.rpow_nonneg hδ.le _)).trans
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
    have hupper := hgain N μ ν F (hN₀ N hN).2 hμ (by simp) hνmass
      (fun x j hj => (hμball x j hj).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) t))))
      (fun w j hj => (hνball w j hj).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) q))))
      hF hFb (by
          intro w
          refine ⟨J w,?_,?_⟩
          · exact (show ((J w).card:ℝ) ≤ count by exact_mod_cast (hJ w).2).trans hcount
          · intro x hx
            exact hcover (x,w) hx)
    exact ennreal_mass_of_power_incidence hδ hδ1 hbc (ν B) ((hlower ν).trans hupper)

end Falconer

end OAI

end ExtensionScope107

/- Source: OAI.MeasureTheory.Falconer.Radial.RadialBadWitness. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope108


namespace OAI

/-! # Deleting original pairs whose witness direction is exceptional -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def radialBadWitness (w₀ : Sphere d) (G : Set (Space d × Space d))
    (B : Set (Sphere d)) : Set (Space d × Space d) :=
  G ∩ {p | normalizeToSphere w₀ (p.2-p.1) ∈ B}

theorem radialBadWitness_measurable (w₀ : Sphere d) {G : Set (Space d × Space d)}
    (hG : MeasurableSet G) {B : Set (Sphere d)} (hB : MeasurableSet B) :
    MeasurableSet (radialBadWitness w₀ G B) :=
  hG.inter (hB.preimage ((normalizeToSphere_measurable w₀).comp
    (measurable_snd.sub measurable_fst)))

theorem radial_bad_witness_mass (w₀ : Sphere d) (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (B : Set (Sphere d)) (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hsmall : ∀ᵐ z ∂μ, originalRadialSphereLaw w₀ ν G z B ≤ c) :
    (μ.prod ν) (radialBadWitness w₀ G B) ≤ c*μ univ := by
  rw [Measure.prod_apply (radialBadWitness_measurable w₀ hG hB)]
  have he (z : Space d) : ν {x | (z,x) ∈ radialBadWitness w₀ G B} =
      originalRadialSphereLaw w₀ ν G z B := by
    rw [originalRadialSphereLaw_apply w₀ ν G z B hB]
    rfl
  change (∫⁻ z, ν {x | (z,x) ∈ radialBadWitness w₀ G B} ∂μ) ≤ c*μ univ
  simp_rw [he]
  exact (lintegral_mono_ae hsmall).trans_eq (lintegral_const c)

theorem direction_good_of_not_radialBadWitness (w₀ : Sphere d)
    (G : Set (Space d × Space d)) (B : Set (Sphere d)) {z x : Space d}
    (hgood : (z,x) ∈ G \ radialBadWitness w₀ G B) :
    normalizeToSphere w₀ (x-z) ∉ B := by
  intro hb
  exact hgood.2 ⟨hgood.1,hb⟩

end Falconer

end OAI

end ExtensionScope108

/- Source: OAI.MeasureTheory.Falconer.Radial.RadialSphereBounds. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope109


namespace OAI

/-! # The sphere law has exactly the original directional cap and plate bounds -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

theorem originalRadialSphereLaw_ball (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) (hdiag : ∀ x, (z,x) ∈ G → x ≠ z)
    (w : Sphere d) (r : ℝ) :
    originalRadialSphereLaw w₀ ν G z (Metric.ball w r) =
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space d) < r} := by
  rw [originalRadialSphereLaw_apply w₀ ν G z (Metric.ball w r) measurableSet_ball]
  congr 1
  ext x
  by_cases hx : (z,x) ∈ G
  · simp only [mem_ofPred_eq,hx,true_and,Metric.mem_ball,Subtype.dist_eq,
      normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr (hdiag x hx))]
  · simp only [mem_ofPred_eq,hx,false_and]

theorem originalRadialSphereLaw_slab (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) (hdiag : ∀ x, (z,x) ∈ G → x ≠ z)
    (w : Space d) (r : ℝ) :
    originalRadialSphereLaw w₀ ν G z {u : Sphere d | |inner ℝ w (u:Space d)| ≤ r} =
      ν {x | (z,x) ∈ G ∧ |inner ℝ w (normalize (x-z))| ≤ r} := by
  rw [originalRadialSphereLaw_apply w₀ ν G z _
    (measurableSet_le (by fun_prop) measurable_const)]
  congr 1
  ext x
  by_cases hx : (z,x) ∈ G
  · simp only [hx,true_and,mem_ofPred_eq,
      normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr (hdiag x hx))]
  · simp only [mem_ofPred_eq,hx,false_and]

end Falconer

end OAI

end ExtensionScope109

/- Source: OAI.MeasureTheory.Falconer.Radial.NonendpointRadialBadDirections. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope110




namespace OAI

/-! # Nonendpoint angular gain for the original radial witness pairs -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem nonendpoint_radial_bad_directions (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {t q C : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
    (hqt : q < t) (ht : t-(h:ℝ) < 1) (hC : 0 ≤ C) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+2)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (w₀ : Sphere (h+2)) (G : Set (Space (h+2) × Space (h+2))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ, ‖z‖ ≤ 1/4) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∃ B : Set (Sphere (h+2)), MeasurableSet B ∧
        {w : Sphere (h+2) | ∃ S : Finset (Space (h+2)),
          (S.card:ℝ) ≤ (1/(2:ℝ)^N)^(-q-b) ∧
          ENNReal.ofReal ((1/(2:ℝ)^N)^b) ≤
            μ {z | ∃ v ∈ S, ‖perpendicularPart (w:Space (h+2)) (z-v)‖ ≤ C*(1/(2:ℝ)^N)}} ⊆ B ∧
        (μ.prod ν) (radialBadWitness w₀ G B) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
  obtain ⟨ε,b,hε,hb,N₀,hN₀⟩ := nonendpoint_bad_direction_envelope hpublished hq hq' hqt ht hC
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ ν _ _ hν w₀ G hG hdiag hμ hμball hdata
  obtain ⟨B,hB,hcontains,hbound⟩ := hN₀ N hN μ hμ hμball
  refine ⟨B,hB,hcontains,?_⟩
  have hsmall : ∀ᵐ z ∂μ, originalRadialSphereLaw w₀ ν G z B ≤
      ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
    filter_upwards [hdata] with z hz
    apply hbound (originalRadialSphereLaw w₀ ν G z)
      ((originalRadialSphereLaw_mass_le w₀ ν G z).trans hν)
    intro w j hj
    rw [originalRadialSphereLaw_ball w₀ ν G z (hdiag z)]
    exact hz w j hj
  simpa only [measure_univ,mul_one] using radial_bad_witness_mass w₀ μ ν G hG B hB _ hsmall

end Falconer

end OAI

end ExtensionScope110

/- Source: OAI.MeasureTheory.Falconer.Geometry.IntegerRectangle. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope111



namespace OAI

/-! # Integer rectangles arising from projected tube covers -/

namespace Falconer

theorem integer_near_real_bounds (z : ℤ) (x r : ℝ) (L : ℕ)
    (hz : |(z:ℝ)-x| ≤ r) (hL : r+1/2 ≤ (L:ℝ)) :
    round x-(L:ℤ) ≤ z ∧ z ≤ round x+(L:ℤ) := by
  have hh : |(z:ℝ)-(round x:ℝ)| ≤ (L:ℝ) :=
    ((abs_sub_le (z:ℝ) x (round x:ℝ)).trans
      (add_le_add hz (abs_sub_round x))).trans hL
  have hi : |z-round x| ≤ (L:ℤ) := by exact_mod_cast hh
  have h := abs_le.mp hi
  constructor <;> omega

theorem integer_rectangle_card (T : Finset (ℤ × ℤ)) (x y r : ℝ) (L : ℕ)
    (hL : r+1/2 ≤ (L:ℝ))
    (hT : ∀ z ∈ T, |(z.1:ℝ)-x| ≤ r ∧ |(z.2:ℝ)-y| ≤ r) :
    T.card ≤ (2*L+1)^2 := by
  have hsub : T ⊆
      (Finset.Icc (round x-(L:ℤ)) (round x+(L:ℤ))).product
        (Finset.Icc (round y-(L:ℤ)) (round y+(L:ℤ))) := by
    intro z hz
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr (integer_near_real_bounds z.1 x r L (hT z hz).1 hL),
        Finset.mem_Icc.mpr (integer_near_real_bounds z.2 y r L (hT z hz).2 hL)⟩
  have hx : (Finset.Icc (round x-(L:ℤ)) (round x+(L:ℤ))).card = 2*L+1 := by
    rw [Int.card_Icc]
    omega
  have hy : (Finset.Icc (round y-(L:ℤ)) (round y+(L:ℤ))).card = 2*L+1 := by
    rw [Int.card_Icc]
    omega
  exact (Finset.card_le_card hsub).trans_eq (by
    rw [Finset.product_eq_sprod,Finset.card_product,hx,hy,pow_two])

theorem integer_rectangle_cover_card {ι : Type*} [DecidableEq ι]
    (T : Finset (ℤ × ℤ)) (A : Finset ι) (x y : ι → ℝ) (r : ℝ) (L : ℕ)
    (hL : r+1/2 ≤ (L:ℝ))
    (hcover : ∀ z ∈ T, ∃ a ∈ A, |(z.1:ℝ)-x a| ≤ r ∧ |(z.2:ℝ)-y a| ≤ r) :
    T.card ≤ A.card*(2*L+1)^2 := by
  classical
  let F : ι → Finset (ℤ × ℤ) := fun a =>
    T.filter (fun z => |(z.1:ℝ)-x a| ≤ r ∧ |(z.2:ℝ)-y a| ≤ r)
  have hsub : T ⊆ A.biUnion F := by
    intro z hz
    obtain ⟨a,ha,hza⟩ := hcover z hz
    exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_filter.mpr ⟨hz,hza⟩⟩
  calc
    _ ≤ (A.biUnion F).card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ A, (F a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, (2*L+1)^2 := Finset.sum_le_sum (fun a _ =>
      integer_rectangle_card (F a) (x a) (y a) r L hL
        (fun z hz => (Finset.mem_filter.mp hz).2))
    _ = _ := by simp

end Falconer

end OAI

end ExtensionScope111

/- Source: OAI.MeasureTheory.Falconer.Incidence.PublishedLoomisWhitney. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope112



namespace OAI

/-!
# The exact finite lattice projection input for general-dimensional tube counting

Loomis–Whitney, *An inequality related to the isoperimetric inequality*,
Bull. AMS 55 (1949), 961–962, DOI 10.1090/S0002-9904-1949-09320-5.
The finite lattice consequence is stated explicitly in Balister–Bollobás,
*Projections, entropy and sumsets*, Combinatorica 32 (2012), equation (7),
specialized here to the (n+1) coordinate-deletion projections, an n-uniform cover.
Author manuscript: https://www.memphis.edu/msci/people/pbalistr/projections.pdf
Only this counting specialization is an explicit conditional input.
-/

namespace Falconer
open scoped BigOperators

abbrev dropGridCoordinate {n : ℕ} (i : Fin (n+1)) (z : Fin (n+1) → ℤ) : Fin n → ℤ :=
  fun j => z (i.succAbove j)

def PublishedFiniteLoomisWhitney : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ S : Finset (Fin (n+1) → ℤ),
    S.card^n ≤ ∏ i : Fin (n+1), (S.image (dropGridCoordinate i)).card

end Falconer

end OAI

end ExtensionScope112

/- Source: OAI.MeasureTheory.Falconer.Geometry.IntegerBox. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope113


namespace OAI

/-! # Product grid boxes for the general-dimensional tube count -/

namespace Falconer
open scoped BigOperators
variable {n : ℕ}

theorem integer_box_card (T : Finset (Fin n → ℤ)) (x : Fin n → ℝ) (r : ℝ) (L : ℕ)
    (hL : r+1/2 ≤ (L:ℝ)) (hT : ∀ z ∈ T, ∀ j, |(z j:ℝ)-x j| ≤ r) :
    T.card ≤ (2*L+1)^n := by
  classical
  let B (j : Fin n) := Finset.Icc (round (x j)-(L:ℤ)) (round (x j)+(L:ℤ))
  have hsub : T ⊆ Fintype.piFinset B := by
    intro z hz
    apply Fintype.mem_piFinset.mpr
    intro j
    exact Finset.mem_Icc.mpr (integer_near_real_bounds (z j) (x j) r L (hT z hz j) hL)
  have hB (j : Fin n) : (B j).card = 2*L+1 := by
    dsimp [B]
    rw [Int.card_Icc]
    omega
  exact (Finset.card_le_card hsub).trans_eq (by simp only [Fintype.card_piFinset,hB,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin])

theorem integer_box_cover_card {ι : Type*} [DecidableEq ι]
    (T : Finset (Fin n → ℤ)) (A : Finset ι) (x : ι → Fin n → ℝ) (r : ℝ) (L : ℕ)
    (hL : r+1/2 ≤ (L:ℝ))
    (hcover : ∀ z ∈ T, ∃ a ∈ A, ∀ j, |(z j:ℝ)-x a j| ≤ r) :
    T.card ≤ A.card*(2*L+1)^n := by
  classical
  let F : ι → Finset (Fin n → ℤ) := fun a => T.filter (fun z => ∀ j, |(z j:ℝ)-x a j| ≤ r)
  have hs : T ⊆ A.biUnion F := by
    intro z hz
    obtain ⟨a,ha,hza⟩ := hcover z hz
    exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_filter.mpr ⟨hz,hza⟩⟩
  calc
    _ ≤ (A.biUnion F).card := Finset.card_le_card hs
    _ ≤ ∑ a ∈ A, (F a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, (2*L+1)^n := Finset.sum_le_sum (fun a _ =>
      integer_box_card (F a) (x a) r L hL (fun z hz => (Finset.mem_filter.mp hz).2))
    _ = _ := by simp

end Falconer

end OAI

end ExtensionScope113

/- Source: OAI.MeasureTheory.Falconer.Geometry.TransverseGridCoordinates. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope114



namespace OAI

/-! # Pulling physical tube tests back to transverse coordinates -/

namespace Falconer
variable {d : ℕ}

theorem inverse_coordinate_tube_bound (e : Space d ≃L[ℝ] Space d)
    (v x a : Space d) (j : Fin d) (hj : (e.symm v) j = 0) :
    |(e.symm x) j-(e.symm a) j| ≤
      ‖e.symm.toContinuousLinearMap‖*‖perpendicularPart v (x-a)‖ := by
  have he : (e.symm (perpendicularPart v (x-a))) j = (e.symm x) j-(e.symm a) j := by
    simp only [perpendicularPart,map_sub,map_smul,PiLp.sub_apply,PiLp.smul_apply,
      smul_eq_mul,hj,mul_zero,sub_zero]
  calc
    _ = ‖(e.symm (perpendicularPart v (x-a))) j‖ := by rw [he,Real.norm_eq_abs]
    _ ≤ ‖e.symm (perpendicularPart v (x-a))‖ := PiLp.norm_apply_le _ _
    _ ≤ _ := e.symm.toContinuousLinearMap.le_opNorm _

noncomputable def tripleGridPoint (δ : ℝ) (z : ℤ × ℤ × ℤ) : Space 3 :=
  WithLp.toLp 2 ![δ*(z.1:ℝ),δ*(z.2.1:ℝ),δ*(z.2.2:ℝ)]

@[simp] theorem tripleGridPoint_zero (δ : ℝ) (z : ℤ × ℤ × ℤ) :
    tripleGridPoint δ z 0 = δ*(z.1:ℝ) := rfl

@[simp] theorem tripleGridPoint_one (δ : ℝ) (z : ℤ × ℤ × ℤ) :
    tripleGridPoint δ z 1 = δ*(z.2.1:ℝ) := rfl

@[simp] theorem tripleGridPoint_two (δ : ℝ) (z : ℤ × ℤ × ℤ) :
    tripleGridPoint δ z 2 = δ*(z.2.2:ℝ) := rfl

theorem transverse_grid_coordinate (e : Space 3 ≃L[ℝ] Space 3)
    (v a : Space 3) (z : ℤ × ℤ × ℤ) (j : Fin 3)
    {δ C : ℝ} (hδ : 0 < δ) (hj : (e.symm v) j = 0)
    (htube : ‖perpendicularPart v (e (tripleGridPoint δ z)-a)‖ ≤ C*δ) :
    |tripleGridPoint δ z j/δ-(e.symm a) j/δ| ≤
      ‖e.symm.toContinuousLinearMap‖*C := by
  have hh := inverse_coordinate_tube_bound e v (e (tripleGridPoint δ z)) a j hj
  rw [e.symm_apply_apply] at hh
  have hb := hh.trans (mul_le_mul_of_nonneg_left htube (norm_nonneg _))
  rw [← sub_div,abs_div,abs_of_pos hδ]
  apply (div_le_iff₀ hδ).mpr
  nlinarith

end Falconer

end OAI

end ExtensionScope114

/- Source: OAI.MeasureTheory.Falconer.Geometry.GeneralTransverseGrid. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope115



namespace OAI

/-! # General-dimensional physical grid count from the precise published input -/

namespace Falconer
open scoped BigOperators
variable {n : ℕ}

noncomputable def euclideanIntegerGrid (δ : ℝ) (z : Fin (n+1) → ℤ) : Space (n+1) :=
  WithLp.toLp 2 (fun j => δ*(z j:ℝ))

theorem general_transverse_grid_count (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (e : Space (n+1) ≃L[ℝ] Space (n+1))
    (v : Fin (n+1) → Space (n+1)) (A : Fin (n+1) → Finset (Space (n+1)))
    (S : Finset (Fin (n+1) → ℤ)) {δ C : ℝ} (hδ : 0 < δ)
    (haxis : ∀ i j : Fin (n+1), j ≠ i → (e.symm (v i)) j = 0)
    (L : ℕ) (hL : ‖e.symm.toContinuousLinearMap‖*C+1/2 ≤ (L:ℝ))
    (hcover : ∀ i : Fin (n+1), ∀ z ∈ S, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (e (euclideanIntegerGrid δ z)-a)‖ ≤ C*δ) :
    S.card^n ≤ (∏ i : Fin (n+1), (A i).card)*(2*L+1)^(n*(n+1)) := by
  classical
  have hp (i : Fin (n+1)) : (S.image (dropGridCoordinate i)).card ≤ (A i).card*(2*L+1)^n := by
    apply integer_box_cover_card _ (A i) (fun a j => (e.symm a) (i.succAbove j)/δ)
      (‖e.symm.toContinuousLinearMap‖*C) L hL
    intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a,ha,ht⟩ := hcover i y hy
    refine ⟨a,ha,?_⟩
    intro j
    have hh := inverse_coordinate_tube_bound e (v i) (e (euclideanIntegerGrid δ y)) a
      (i.succAbove j) (haxis i (i.succAbove j) (Fin.succAbove_ne i j))
    rw [e.symm_apply_apply] at hh
    have hb := hh.trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
    change |(y (i.succAbove j):ℝ)-(e.symm a) (i.succAbove j)/δ| ≤ _
    change |δ*(y (i.succAbove j):ℝ)-(e.symm a) (i.succAbove j)| ≤ _ at hb
    have hd : |(δ*(y (i.succAbove j):ℝ)-(e.symm a) (i.succAbove j))/δ| ≤
        ‖e.symm.toContinuousLinearMap‖*C := by
      rw [abs_div,abs_of_pos hδ]
      apply (div_le_iff₀ hδ).mpr
      nlinarith
    have he : (δ*(y (i.succAbove j):ℝ)-(e.symm a) (i.succAbove j))/δ =
        (y (i.succAbove j):ℝ)-(e.symm a) (i.succAbove j)/δ := by field_simp
    rwa [he] at hd
  calc
    _ ≤ ∏ i : Fin (n+1), (S.image (dropGridCoordinate i)).card := hLW n hn S
    _ ≤ ∏ i : Fin (n+1), (A i).card*(2*L+1)^n := Finset.prod_le_prod (fun i _ => hp i)
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,← pow_mul]

end Falconer

end OAI

end ExtensionScope115

/- Source: OAI.MeasureTheory.Falconer.Geometry.TripleGridRounding. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope116




namespace OAI

/-! # Rounding bounded physical point sets in transverse coordinates -/

namespace Falconer
open Set Metric

noncomputable def tripleRound (δ : ℝ) (x : Space 3) : ℤ × ℤ × ℤ :=
  (round (x 0/δ),round (x 1/δ),round (x 2/δ))

theorem round_mesh_error {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |t-δ*(round (t/δ):ℝ)| ≤ δ/2 := by
  have he : t-δ*(round (t/δ):ℝ) = δ*(t/δ-(round (t/δ):ℝ)) := by field_simp
  rw [he,abs_mul,abs_of_pos hδ]
  have hh := mul_le_mul_of_nonneg_left (abs_sub_round (t/δ)) hδ.le
  nlinarith

theorem tripleRound_distance {δ : ℝ} (hδ : 0 < δ) (x : Space 3) :
    dist x (tripleGridPoint δ (tripleRound δ x)) ≤ 3*δ/2 := by
  rw [dist_eq_norm]
  have hh := coordinate_norm_le_card_mul (x-tripleGridPoint δ (tripleRound δ x))
    (r := δ/2) (by
      intro i
      fin_cases i <;> exact round_mesh_error hδ _)
  norm_num only [Nat.cast_ofNat] at hh
  linarith

noncomputable def tripleIntegerBox (L : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-(L:ℤ)) (L:ℤ)).product
    ((Finset.Icc (-(L:ℤ)) (L:ℤ)).product (Finset.Icc (-(L:ℤ)) (L:ℤ)))

theorem round_bound {δ R : ℝ} (hδ : 0 < δ) (L : ℕ) (hL : R/δ+1 ≤ (L:ℝ))
    (t : ℝ) (ht : |t| ≤ R) : -(L:ℤ) ≤ round (t/δ) ∧ round (t/δ) ≤ (L:ℤ) := by
  have hh : |(round (t/δ):ℝ)| ≤ (L:ℝ) := by
    have hs := abs_sub_round (t/δ)
    have htri := abs_sub_le (round (t/δ):ℝ) (t/δ) 0
    rw [sub_zero,sub_zero,abs_sub_comm (round (t/δ):ℝ)] at htri
    have hd : |t/δ| ≤ R/δ := by
      rw [abs_div,abs_of_pos hδ]
      exact div_le_div_of_nonneg_right ht hδ.le
    linarith
  have hi : |round (t/δ)| ≤ (L:ℤ) := by exact_mod_cast hh
  exact abs_le.mp hi

theorem tripleRound_mem_box {δ R : ℝ} (hδ : 0 < δ) (L : ℕ)
    (hL : R/δ+1 ≤ (L:ℝ)) (x : Space 3) (hx : ‖x‖ ≤ R) :
    tripleRound δ x ∈ tripleIntegerBox L := by
  have hb (i : Fin 3) : -(L:ℤ) ≤ round (x i/δ) ∧ round (x i/δ) ≤ (L:ℤ) :=
    round_bound hδ L hL (x i) ((PiLp.norm_apply_le x i).trans hx)
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hb 0),
    Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hb 1),Finset.mem_Icc.mpr (hb 2)⟩⟩

noncomputable def roundedTripleGrid (E : Set (Space 3)) (δ : ℝ) (L : ℕ) :
    Finset (ℤ × ℤ × ℤ) := by
  classical
  exact (tripleIntegerBox L).filter (fun z => ∃ x ∈ E, tripleRound δ x = z)

theorem roundedTripleGrid_mem {E : Set (Space 3)} {δ R : ℝ} (hδ : 0 < δ)
    (L : ℕ) (hL : R/δ+1 ≤ (L:ℝ)) (hE : ∀ x ∈ E, ‖x‖ ≤ R)
    {x : Space 3} (hx : x ∈ E) : tripleRound δ x ∈ roundedTripleGrid E δ L := by
  classical
  exact Finset.mem_filter.mpr ⟨tripleRound_mem_box hδ L hL x (hE x hx),x,hx,rfl⟩

theorem roundedTripleGrid_original {E : Set (Space 3)} {δ : ℝ} {L : ℕ}
    {z : ℤ × ℤ × ℤ} (hz : z ∈ roundedTripleGrid E δ L) :
    ∃ x ∈ E, tripleRound δ x = z := by
  classical
  exact (Finset.mem_filter.mp hz).2

end Falconer

end OAI

end ExtensionScope116

/- Source: OAI.MeasureTheory.Falconer.Geometry.GeneralGridRounding. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope117



namespace OAI

/-! # Bounded original point sets admit finite transverse lattice approximations -/

namespace Falconer
open Set Metric
variable {n : ℕ}

noncomputable def euclideanRound (δ : ℝ) (x : Space (n+1)) : Fin (n+1) → ℤ :=
  fun j => round (x j/δ)

theorem euclideanRound_distance {δ : ℝ} (hδ : 0 < δ) (x : Space (n+1)) :
    dist x (euclideanIntegerGrid δ (euclideanRound δ x)) ≤ ((n+1:ℕ):ℝ)*δ/2 := by
  rw [dist_eq_norm]
  have hh := coordinate_norm_le_card_mul (x-euclideanIntegerGrid δ (euclideanRound δ x))
    (r := δ/2) (fun i => round_mesh_error hδ (x i))
  nlinarith

noncomputable def integerGridBox (n L : ℕ) : Finset (Fin (n+1) → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(L:ℤ)) (L:ℤ))

theorem euclideanRound_mem_box {δ R : ℝ} (hδ : 0 < δ) (L : ℕ)
    (hL : R/δ+1 ≤ (L:ℝ)) (x : Space (n+1)) (hx : ‖x‖ ≤ R) :
    euclideanRound δ x ∈ integerGridBox n L := by
  apply Fintype.mem_piFinset.mpr
  intro i
  exact Finset.mem_Icc.mpr (round_bound hδ L hL (x i) ((PiLp.norm_apply_le x i).trans hx))

noncomputable def roundedEuclideanGrid (E : Set (Space (n+1))) (δ : ℝ) (L : ℕ) :
    Finset (Fin (n+1) → ℤ) := by
  classical
  exact (integerGridBox n L).filter (fun z => ∃ x ∈ E, euclideanRound δ x = z)

theorem roundedEuclideanGrid_mem {E : Set (Space (n+1))} {δ R : ℝ} (hδ : 0 < δ)
    (L : ℕ) (hL : R/δ+1 ≤ (L:ℝ)) (hE : ∀ x ∈ E, ‖x‖ ≤ R)
    {x : Space (n+1)} (hx : x ∈ E) : euclideanRound δ x ∈ roundedEuclideanGrid E δ L := by
  classical
  exact Finset.mem_filter.mpr ⟨euclideanRound_mem_box hδ L hL x (hE x hx),x,hx,rfl⟩

theorem roundedEuclideanGrid_original {E : Set (Space (n+1))} {δ : ℝ} {L : ℕ}
    {z : Fin (n+1) → ℤ} (hz : z ∈ roundedEuclideanGrid E δ L) :
    ∃ x ∈ E, euclideanRound δ x = z := by
  classical
  exact (Finset.mem_filter.mp hz).2

end Falconer

end OAI

end ExtensionScope117

/- Source: OAI.MeasureTheory.Falconer.Estimates.FiniteOverlap. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope118



namespace OAI

/-! # Counting heavy members of a finite family with bounded overlap -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {X ι : Type*} [MeasurableSpace X]
attribute [local instance] Classical.propDecidable

theorem finite_measure_sum_le_overlap (μ : Measure X) (I : Finset ι) (U : ι → Set X)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (L : ℕ)
    (hoverlap : ∀ x, (I.filter (fun i => x ∈ U i)).card ≤ L) :
    ∑ i ∈ I, μ (U i) ≤ (L:ℝ≥0∞)*μ univ := by
  classical
  have hp (x : X) : (∑ i ∈ I, (U i).indicator (fun _ => (1:ℝ≥0∞)) x) =
      ((I.filter (fun i => x ∈ U i)).card:ℝ≥0∞) := by
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter]
    simp
  calc
    _ = ∑ i ∈ I, ∫⁻ x, (U i).indicator (fun _ => (1:ℝ≥0∞)) x ∂μ :=
      Finset.sum_congr rfl (fun i hi => (lintegral_indicator_one (hU i hi)).symm)
    _ = ∫⁻ x, ∑ i ∈ I, (U i).indicator (fun _ => (1:ℝ≥0∞)) x ∂μ := by
      rw [lintegral_finsetSum' I (fun i hi => (measurable_const.indicator (hU i hi)).aemeasurable)]
    _ ≤ ∫⁻ _x, (L:ℝ≥0∞) ∂μ := lintegral_mono (fun x => by
      rw [hp]
      exact Nat.cast_le.mpr (hoverlap x))
    _ = _ := lintegral_const _

theorem heavy_family_card_bound (μ : Measure X) (I : Finset ι) (U : ι → Set X)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (L : ℕ)
    (hoverlap : ∀ x, (I.filter (fun i => x ∈ U i)).card ≤ L)
    (F : ℝ≥0∞) (hheavy : ∀ i ∈ I, F ≤ μ (U i)) :
    (I.card:ℝ≥0∞)*F ≤ (L:ℝ≥0∞)*μ univ := by
  calc
    _ = ∑ _i ∈ I, F := by simp
    _ ≤ ∑ i ∈ I, μ (U i) := Finset.sum_le_sum hheavy
    _ ≤ _ := finite_measure_sum_le_overlap μ I U hU L hoverlap

end Falconer

end OAI

end ExtensionScope118

/- Source: OAI.MeasureTheory.Falconer.Geometry.GridBallOverlap. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope119



namespace OAI

/-! # Uniform overlap of fixed-width lattice cells -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

theorem grid_ball_overlap (S : Finset (Fin (n+1) → ℤ)) {δ C : ℝ}
    (hδ : 0 < δ) (L : ℕ) (hL : C+1/2 ≤ (L:ℝ)) (x : Space (n+1)) :
    (S.filter (fun z => ‖x-euclideanIntegerGrid δ z‖ ≤ C*δ)).card ≤ (2*L+1)^(n+1) := by
  apply integer_box_card _ (fun j => x j/δ) C L hL
  intro z hz j
  have hb := (PiLp.norm_apply_le (x-euclideanIntegerGrid δ z) j).trans (Finset.mem_filter.mp hz).2
  change |x j-δ*(z j:ℝ)| ≤ C*δ at hb
  have hd : |(x j-δ*(z j:ℝ))/δ| ≤ C := by
    rw [abs_div,abs_of_pos hδ]
    exact (div_le_iff₀ hδ).mpr hb
  have he : (x j-δ*(z j:ℝ))/δ = x j/δ-(z j:ℝ) := by field_simp
  rw [he,abs_sub_comm] at hd
  exact hd

theorem grid_ball_heavy_card (μ : Measure (Space (n+1)))
    (f : Space (n+1) → Space (n+1)) (hf : Measurable f)
    (S : Finset (Fin (n+1) → ℤ)) {δ C : ℝ} (hδ : 0 < δ)
    (L : ℕ) (hL : C+1/2 ≤ (L:ℝ)) (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ S, F ≤ μ {x | ‖f x-euclideanIntegerGrid δ z‖ ≤ C*δ}) :
    (S.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  apply heavy_family_card_bound μ S
    (fun z => {x | ‖f x-euclideanIntegerGrid δ z‖ ≤ C*δ})
    (fun z _ => measurableSet_le (by fun_prop) measurable_const)
    ((2*L+1)^(n+1)) (fun x => grid_ball_overlap S hδ L hL (f x)) F hheavy

end Falconer

end OAI

end ExtensionScope119

/- Source: OAI.MeasureTheory.Falconer.Radial.HeavyProjectedCover. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope120


namespace OAI

/-! # A finite cover of sources whose full projected local mass is heavy -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem heavy_projected_grid_cover (μ : Measure (Space (n+1)))
    (f : Space (n+1) → Space (n+1)) (hf : Measurable f)
    (T : Set (Space (n+1))) {R δ C : ℝ} (hδ : 0 < δ)
    (hT : ∀ z ∈ T, ‖f z‖ ≤ R) (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ T, F ≤ μ {y | ‖f y-f z‖ ≤ C*δ})
    (L : ℕ) (hL : C+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) :
    ∃ P : Finset (Space (n+1)),
      (∀ z ∈ T, ∃ p ∈ P, ‖f z-p‖ ≤ ((n+1:ℕ):ℝ)*δ) ∧
      (P.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_ge (R/δ+1)
  let I := integerGridBox n N
  let U (q : Fin (n+1) → ℤ) : Set (Space (n+1)) :=
    {y | ‖f y-euclideanIntegerGrid δ q‖ ≤ (C+((n+1:ℕ):ℝ))*δ}
  let H := I.filter (fun q => F ≤ μ (U q))
  let P := H.image (euclideanIntegerGrid δ)
  have hm := grid_ball_heavy_card μ f hf H hδ L hL F
    (fun q hq => (Finset.mem_filter.mp hq).2)
  refine ⟨P,?_,?_⟩
  · intro z hz
    let q := euclideanRound δ (f z)
    have hqI : q ∈ I := euclideanRound_mem_box hδ N hN (f z) (hT z hz)
    have hclose : ‖f z-euclideanIntegerGrid δ q‖ ≤ ((n+1:ℕ):ℝ)*δ := by
      have he := euclideanRound_distance hδ (f z)
      rw [dist_eq_norm] at he
      have hd : 0 ≤ ((n+1:ℕ):ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
      exact he.trans (by linarith)
    have hsub : {y | ‖f y-f z‖ ≤ C*δ} ⊆ U q := by
      intro y hy
      change ‖f y-euclideanIntegerGrid δ q‖ ≤ _
      calc
        _ ≤ ‖f y-f z‖+‖f z-euclideanIntegerGrid δ q‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ C*δ+((n+1:ℕ):ℝ)*δ := add_le_add hy hclose
        _ = _ := by ring
    have hqH : q ∈ H := Finset.mem_filter.mpr ⟨hqI,(hheavy z hz).trans (measure_mono hsub)⟩
    exact ⟨_,Finset.mem_image.mpr ⟨q,hqH,rfl⟩,hclose⟩
  · have hc : (P.card:ℝ≥0∞) ≤ (H.card:ℝ≥0∞) := by exact_mod_cast Finset.card_image_le
    exact (mul_le_mul' hc le_rfl).trans hm

end Falconer

end OAI

end ExtensionScope120

/- Source: OAI.MeasureTheory.Falconer.Radial.RadialFreezing. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope121


namespace OAI

/-! # Freezing radial directions in a source cell away from its pin -/

namespace Falconer
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalize_distance_scaled {u v : E} {r : ℝ}
    (hu : r ≤ ‖u‖) (hv : v ≠ 0) :
    r*dist (normalize u) (normalize v) ≤ 2*dist u v := by
  have he : ‖u‖ • (normalize u-normalize v) =
      u-v+(‖v‖-‖u‖) • normalize v := by
    rw [smul_sub,norm_smul_normalize,sub_smul,norm_smul_normalize]
    abel
  have hb := norm_add_le (u-v) ((‖v‖-‖u‖) • normalize v)
  rw [← he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    norm_smul,Real.norm_eq_abs,norm_normalize hv,mul_one] at hb
  have hn := abs_norm_sub_norm_le v u
  rw [norm_sub_rev v u] at hn
  rw [dist_eq_norm,dist_eq_norm]
  have hh := mul_le_mul_of_nonneg_right hu (norm_nonneg (normalize u-normalize v))
  linarith

theorem perpendicular_normalize_self (v : E) : perpendicularPart (normalize v) v = 0 := by
  by_cases hv : v = 0
  · simp [hv,perpendicularPart,NormedSpace.normalize]
  · have he : v = ‖v‖ • normalize v := (norm_smul_normalize v).symm
    calc
      _ = perpendicularPart (normalize v) (‖v‖ • normalize v) := congrArg _ he
      _ = ‖v‖ • perpendicularPart (normalize v) (normalize v) := perpendicularPart_smul _ _ _
      _ = 0 := by simp [perpendicularPart,norm_normalize hv]

theorem frozen_radial_tube_error (x c z y : E) {r D W : ℝ}
    (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hzx : z ≠ x)
    (hzc : ‖z-c‖ ≤ D) (hyc : ‖y-c‖ ≤ D)
    (htube : ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ W) :
    ‖perpendicularPart (normalize (c-x)) (y-z)‖ ≤ W+8*D^2/r := by
  have hc0 : c-x ≠ 0 := norm_pos_iff.mp (hr.trans_le hcx)
  have hz0 : z-x ≠ 0 := sub_ne_zero.mpr hzx
  have hD : 0 ≤ D := (norm_nonneg _).trans hzc
  have hd : ‖normalize (c-x)-normalize (z-x)‖ ≤ 2*D/r := by
    apply (le_div_iff₀ hr).mpr
    have hh := normalize_distance_scaled hcx hz0
    have he : dist (c-x) (z-x) = ‖z-c‖ := by
      rw [dist_eq_norm,sub_sub_sub_cancel_right,norm_sub_rev]
    rw [he,dist_eq_norm] at hh
    nlinarith
  have hyz : ‖y-z‖ ≤ 2*D := by
    have hh := norm_sub_le_norm_sub_add_norm_sub y c z
    rw [norm_sub_rev c z] at hh
    linarith
  have hshift : perpendicularPart (normalize (z-x)) (y-z) =
      perpendicularPart (normalize (z-x)) (y-x) := by
    have he : y-z = (y-x)-(z-x) := by abel
    rw [he,perpendicularPart_sub,perpendicular_normalize_self,sub_zero]
  have herr := perpendicularPart_direction_error (norm_normalize hc0) (norm_normalize hz0) (y-z)
  have hu : ‖perpendicularPart (normalize (c-x)) (y-z) -
      perpendicularPart (normalize (z-x)) (y-z)‖ ≤ 8*D^2/r := by
    apply herr.trans
    calc
      _ ≤ 2*(2*D/r)*(2*D) := by gcongr
      _ = _ := by ring
  calc
    _ = ‖(perpendicularPart (normalize (c-x)) (y-z)-
        perpendicularPart (normalize (z-x)) (y-z))+
          perpendicularPart (normalize (z-x)) (y-z)‖ := by congr 1; abel
    _ ≤ ‖perpendicularPart (normalize (c-x)) (y-z)-
        perpendicularPart (normalize (z-x)) (y-z)‖+
          ‖perpendicularPart (normalize (z-x)) (y-z)‖ := norm_add_le _ _
    _ ≤ 8*D^2/r+W := add_le_add hu (by rw [hshift]; exact htube)
    _ = _ := add_comm _ _

end Falconer

end OAI

end ExtensionScope121

/- Source: OAI.MeasureTheory.Falconer.Incidence.FrozenHeavyCover. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope122



namespace OAI

/-! # Actual parallel tube covers of troublesome original source fibers -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem perpendicularPart_idempotent (v z : Space (n+1)) (hv : ‖v‖ = 1) :
    perpendicularPart v (perpendicularPart v z) = perpendicularPart v z := by
  simp [perpendicularPart,inner_sub_right,inner_smul_right,hv]

theorem frozen_heavy_tube_cover (μ : Measure (Space (n+1))) (x c : Space (n+1))
    {r D δ C B : ℝ} (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hδ : 0 < δ)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (T : Set (Space (n+1)))
    (hT : ∀ z ∈ T, z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B)
    (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ T, F ≤ μ {y |
      ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ C*δ})
    (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) :
    ∃ P : Finset (Space (n+1)),
      (∀ z ∈ T, ∃ p ∈ P,
        ‖perpendicularPart (normalize (c-x)) (z-p)‖ ≤ ((n+1:ℕ):ℝ)*δ) ∧
      (P.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  let v := normalize (c-x)
  have hv : ‖v‖ = 1 := norm_normalize (norm_pos_iff.mp (hr.trans_le hcx))
  let f : Space (n+1) → Space (n+1) := perpendicularPart v
  have hf : Measurable f := by unfold f perpendicularPart; fun_prop
  have hbd : ∀ z ∈ T, ‖f z‖ ≤ B := fun z hz =>
    (norm_perpendicularPart_le hv z).trans (hT z hz).2.2
  have hmass : ∀ z ∈ T, F ≤ μ {y | ‖f y-f z‖ ≤ (C+1)*δ} := by
    intro z hz
    apply (hheavy z hz).trans
    apply measure_mono_ae
    filter_upwards [hsource] with y hy
    intro ht
    have hh := frozen_radial_tube_error x c z y hr hcx (hT z hz).1 (hT z hz).2.1 hy ht
    change ‖perpendicularPart v y-perpendicularPart v z‖ ≤ _
    rw [← perpendicularPart_sub]
    exact hh.trans (by nlinarith)
  obtain ⟨P,hP,hcard⟩ := heavy_projected_grid_cover μ f hf T hδ hbd F hmass L hL
  refine ⟨P,?_,hcard⟩
  intro z hz
  obtain ⟨p,hp,hclose⟩ := hP z hz
  refine ⟨p,hp,?_⟩
  have he : perpendicularPart v (z-p) = perpendicularPart v (f z-p) := by
    rw [perpendicularPart_sub,perpendicularPart_sub]
    dsimp [f]
    rw [perpendicularPart_idempotent v z hv]
  rw [he]
  exact (norm_perpendicularPart_le hv _).trans hclose

end Falconer

end OAI

end ExtensionScope122

/- Source: OAI.MeasureTheory.Falconer.Incidence.BoundedFrozenHeavyCover. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope123



namespace OAI

/-! # Heavy radial fibers have bounded-anchor frozen tube covers -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem bounded_frozen_heavy_tube_cover (μ : Measure (Space (n+1))) (x c : Space (n+1))
    {r D δ C B : ℝ} (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hδ : 0 < δ)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (T : Set (Space (n+1)))
    (hT : ∀ z ∈ T, z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B)
    (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ T, F ≤ μ {y |
      ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ C*δ})
    (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) :
    ∃ J : Finset (Space (n+1)),
      (∀ a ∈ J, ‖a‖ ≤ B) ∧
      (∀ z ∈ T, ∃ a ∈ J, ‖perpendicularPart (normalize (c-x)) (z-a)‖ ≤
        (2*((n+1:ℕ):ℝ)+1)*δ) ∧
      (J.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  obtain ⟨P,hP,hcard⟩ := frozen_heavy_tube_cover μ x c hr hcx hδ hfreeze hsource T hT F hheavy L hL
  obtain ⟨K,hKb,hKn⟩ := exists_bounded_anchor_net (d := n+1) B hδ
  let w : Sphere (n+1) := ⟨normalize (c-x),by
    rw [Metric.mem_sphere,dist_zero_right]
    exact norm_normalize (norm_pos_iff.mp (hr.trans_le hcx))⟩
  obtain ⟨J,hJK,hJP,hJ⟩ := rounded_tube_cover w T P K
    (fun z hz => hKn z (hT z hz).2.2) hP
  refine ⟨J,fun a ha => hKb a (hJK ha),?_,?_⟩
  · intro z hz
    obtain ⟨a,ha,hza⟩ := hJ z hz
    refine ⟨a,ha,?_⟩
    change ‖perpendicularPart (normalize (c-x)) (z-a)‖ ≤ _ at hza
    convert hza using 1
    ring
  · have hc : (J.card:ℝ≥0∞) ≤ P.card := by exact_mod_cast hJP
    exact (mul_le_mul' hc le_rfl).trans hcard

end Falconer

end OAI

end ExtensionScope123

/- Source: OAI.MeasureTheory.Falconer.Geometry.NormalizedTripleGram. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope124


namespace OAI

/-! # Quantitative triple transversality in the bounded unit-direction chart -/

namespace Falconer
variable {n : ℕ}

theorem northLift_norm_le_two {p : Space n} (hp : ‖p‖ ≤ 1) : ‖northLift p‖ ≤ 2 := by
  have he := northLift_norm_sq p
  nlinarith [norm_nonneg p,norm_nonneg (northLift p)]

theorem gnomonic_tripleGram_lower {p q r : Space n}
    (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hr : ‖r‖ ≤ 1) :
    (1/64:ℝ)*(‖q-p‖^2*‖r-p‖^2-(inner ℝ (q-p) (r-p))^2) ≤
      tripleGram (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1))
        (gnomonicChart r : Space (n+1)) := by
  have hinv (x : Space n) (hx : ‖x‖ ≤ 1) : (1/2:ℝ) ≤ ‖northLift x‖⁻¹ := by
    rw [← one_div (‖northLift x‖)]
    apply (div_le_div_iff₀ (by norm_num) (norm_pos_iff.mpr (northLift_ne_zero x))).mpr
    simpa only [one_mul] using northLift_norm_le_two hx
  have hp' := hinv p hp
  have hq' := hinv q hq
  have hr' := hinv r hr
  have hprod : (1/8:ℝ) ≤ ‖northLift p‖⁻¹*‖northLift q‖⁻¹*‖northLift r‖⁻¹ := by
    calc
      _ = (1/2:ℝ)*(1/2)*(1/2) := by norm_num
      _ ≤ _ := by gcongr
  have hsq : (1/64:ℝ) ≤ (‖northLift p‖⁻¹*‖northLift q‖⁻¹*‖northLift r‖⁻¹)^2 := by
    calc
      _ = (1/8:ℝ)^2 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hprod 2
  have hw : 0 ≤ ‖q-p‖^2*‖r-p‖^2-(inner ℝ (q-p) (r-p))^2 := by
    have hc := pow_le_pow_left₀ (abs_nonneg (inner ℝ (q-p) (r-p)))
      (abs_real_inner_le_norm (q-p) (r-p)) 2
    rw [sq_abs,mul_pow] at hc
    exact sub_nonneg.mpr hc
  rw [gnomonic_tripleGram]
  exact mul_le_mul hsq (northLift_tripleGram_lower p q r) hw (sq_nonneg _)

end Falconer

end OAI

end ExtensionScope124

/- Source: OAI.MeasureTheory.Falconer.Angular.GnomonicPairGram. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope125



namespace OAI

/-! # Pair transversality retains the original affine separation -/

namespace Falconer
variable {n : ℕ}

noncomputable def pairGram {d : ℕ} (u v : Space d) : ℝ :=
  ‖u‖^2*‖v‖^2-(inner ℝ u v)^2

theorem pairGram_nonneg {d : ℕ} (u v : Space d) : 0 ≤ pairGram u v := by
  have hh := pow_le_pow_left₀ (abs_nonneg (inner ℝ u v))
    (abs_real_inner_le_norm u v) 2
  rw [sq_abs,mul_pow] at hh
  exact sub_nonneg.mpr hh

theorem pairGram_smul {d : ℕ} (u v : Space d) (a b : ℝ) :
    pairGram (a • u) (b • v) = (a*b)^2*pairGram u v := by
  simp only [pairGram,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    real_inner_smul_left,real_inner_smul_right]
  ring

theorem northLift_pairGram (p q : Space n) :
    pairGram (northLift p) (northLift q) = ‖q-p‖^2+pairGram p q := by
  rw [pairGram,northLift_norm_sq,northLift_norm_sq,northLift_inner,
    norm_sub_sq_real]
  simp only [pairGram]
  rw [real_inner_comm q p]
  ring

theorem gnomonic_pairGram (p q : Space n) :
    pairGram (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1)) =
      (‖northLift p‖⁻¹*‖northLift q‖⁻¹)^2*pairGram (northLift p) (northLift q) := by
  exact pairGram_smul _ _ _ _

theorem gnomonic_pairGram_lower {p q : Space n} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) :
    (1/16:ℝ)*‖q-p‖^2 ≤
      pairGram (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1)) := by
  have hinv (x : Space n) (hx : ‖x‖ ≤ 1) : (1/2:ℝ) ≤ ‖northLift x‖⁻¹ := by
    rw [← one_div (‖northLift x‖)]
    apply (div_le_div_iff₀ (by norm_num) (norm_pos_iff.mpr (northLift_ne_zero x))).mpr
    simpa only [one_mul] using northLift_norm_le_two hx
  have hprod : (1/4:ℝ) ≤ ‖northLift p‖⁻¹*‖northLift q‖⁻¹ := by
    calc
      _ = (1/2:ℝ)*(1/2) := by norm_num
      _ ≤ _ := mul_le_mul (hinv p hp) (hinv q hq) (by norm_num)
        (inv_nonneg.mpr (norm_nonneg _))
  have hsq : (1/16:ℝ) ≤ (‖northLift p‖⁻¹*‖northLift q‖⁻¹)^2 := by
    nlinarith
  rw [gnomonic_pairGram,northLift_pairGram]
  exact mul_le_mul hsq (le_add_of_nonneg_right (pairGram_nonneg p q))
    (sq_nonneg _) (sq_nonneg _)

theorem gnomonic_pair_separation {p q : Space n} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) :
    ‖q-p‖ ≤ 4*‖perpendicularPart (gnomonicChart p : Space (n+1))
      (gnomonicChart q : Space (n+1))‖ := by
  have hh := gnomonic_pairGram_lower hp hq
  have he := norm_perpendicularPart_sq (sphere_norm (gnomonicChart p))
    (gnomonicChart q : Space (n+1))
  simp only [pairGram,sphere_norm,one_pow,one_mul] at hh
  rw [sphere_norm] at he
  nlinarith [norm_nonneg (q-p),norm_nonneg
    (perpendicularPart (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1)))]

end Falconer

end OAI

end ExtensionScope125

/- Source: OAI.MeasureTheory.Falconer.Angular.GnomonicTripleAngle. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope126



namespace OAI

/-! # The affine displacement angle controls the spherical triple determinant -/

namespace Falconer
open NormedSpace
variable {n : ℕ}

noncomputable def displacementAngle (p q r : Space n) : ℝ :=
  ‖perpendicularPart (normalize (q-p)) (normalize (r-p))‖

theorem displacementAngle_nonneg (p q r : Space n) : 0 ≤ displacementAngle p q r :=
  norm_nonneg _

theorem displacement_pairGram (p q r : Space n) (hq : q ≠ p) (hr : r ≠ p) :
    pairGram (q-p) (r-p) = (‖q-p‖*‖r-p‖*displacementAngle p q r)^2 := by
  have hq0 : q-p ≠ 0 := sub_ne_zero.mpr hq
  have hr0 : r-p ≠ 0 := sub_ne_zero.mpr hr
  have hnq := norm_normalize hq0
  have hnr := norm_normalize hr0
  have hh := norm_perpendicularPart_sq hnq (normalize (r-p))
  rw [hnr] at hh
  have hg : pairGram (normalize (q-p)) (normalize (r-p)) =
      (displacementAngle p q r)^2 := by
    simp only [pairGram,hnq,hnr,one_pow,one_mul]
    simpa only [one_pow,displacementAngle] using hh.symm
  rw [NormedSpace.normalize,NormedSpace.normalize,pairGram_smul] at hg
  have hqn : ‖q-p‖ ≠ 0 := norm_ne_zero_iff.mpr hq0
  have hrn : ‖r-p‖ ≠ 0 := norm_ne_zero_iff.mpr hr0
  field_simp at hg
  nlinarith [sq_nonneg (displacementAngle p q r)]

theorem gnomonic_triple_sqrt_lower {p q r : Space n}
    (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hr : ‖r‖ ≤ 1)
    (hpq : q ≠ p) (hpr : r ≠ p) :
    ‖q-p‖*‖r-p‖*displacementAngle p q r/8 ≤
      Real.sqrt (tripleGram (gnomonicChart p : Space (n+1))
        (gnomonicChart q : Space (n+1)) (gnomonicChart r : Space (n+1))) := by
  have hh := gnomonic_tripleGram_lower hp hq hr
  change (1/64:ℝ)*pairGram (q-p) (r-p) ≤ _ at hh
  rw [displacement_pairGram p q r hpq hpr] at hh
  have hs := Real.sq_sqrt (tripleGram_nonnegative
    (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1))
    (gnomonicChart r : Space (n+1)))
  nlinarith [Real.sqrt_nonneg (tripleGram (gnomonicChart p : Space (n+1))
    (gnomonicChart q : Space (n+1)) (gnomonicChart r : Space (n+1))),
    mul_nonneg (mul_nonneg (norm_nonneg (q-p)) (norm_nonneg (r-p)))
      (displacementAngle_nonneg p q r)]

theorem displacementAngle_lt_of_tripleGram {p q r : Space n}
    (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hr : ‖r‖ ≤ 1)
    {b W : ℝ} (hb : 0 < b) (hpq : b ≤ ‖q-p‖) (hpr : b ≤ ‖r-p‖)
    (hsmall : Real.sqrt (tripleGram (gnomonicChart p : Space (n+1))
      (gnomonicChart q : Space (n+1)) (gnomonicChart r : Space (n+1))) < W) :
    displacementAngle p q r < 8*W/b^2 := by
  have hqne : q ≠ p := by
    intro he
    rw [he,sub_self,norm_zero] at hpq
    linarith
  have hrne : r ≠ p := by
    intro he
    rw [he,sub_self,norm_zero] at hpr
    linarith
  have hh := (gnomonic_triple_sqrt_lower hp hq hr hqne hrne).trans_lt hsmall
  have hm : b^2*displacementAngle p q r ≤ ‖q-p‖*‖r-p‖*displacementAngle p q r := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hpq hpr hb.le (norm_nonneg _))
      (displacementAngle_nonneg p q r)
  apply (lt_div_iff₀ (sq_pos_of_pos hb)).mpr
  nlinarith

end Falconer

end OAI

end ExtensionScope126

/- Source: OAI.MeasureTheory.Falconer.Radial.RadialAngleCaps. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope127


namespace OAI

/-! # Two radial caps control near-collinear affine triples -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem displacementAngle_measurable (p q : Space n) :
    Measurable (displacementAngle p q) := by
  unfold displacementAngle perpendicularPart NormedSpace.normalize
  fun_prop

theorem displacementAngle_two_caps (p q z : Space n) (hq : q ≠ p) (hz : z ≠ p)
    {r : ℝ} (hr : 0 < r) (ha : displacementAngle p q z ≤ r) :
    dist (normalize (z-p)) (normalize (q-p)) < 3*r ∨
      dist (normalize (z-p)) (-normalize (q-p)) < 3*r := by
  let u := normalize (q-p)
  let v := normalize (z-p)
  have hu : ‖u‖ = 1 := norm_normalize (sub_ne_zero.mpr hq)
  have hv : ‖v‖ = 1 := norm_normalize (sub_ne_zero.mpr hz)
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; norm_num)
  rcases perpendicular_direction_two_caps hu hv0 ha with hl | hr'
  · left
    have hh : ‖u-v‖ ≤ 2*r := by
      simpa only [hv,inv_one,one_smul,div_one] using hl
    change ‖v-u‖ < 3*r
    rw [norm_sub_rev]
    linarith
  · right
    have hh : ‖u+v‖ ≤ 2*r := by
      simpa only [hv,inv_one,neg_smul,one_smul,div_one,sub_neg_eq_add] using hr'
    change ‖v-(-u)‖ < 3*r
    rw [sub_neg_eq_add,add_comm]
    linarith

theorem radial_angle_sublevel (μ : Measure (Space n)) (G : Set (Space n × Space n))
    (p q : Space n) (hq : q ≠ p) (hdiag : ∀ z, (p,z) ∈ G → z ≠ p)
    {r K ℓ : ℝ} (hr : 0 < r)
    (hcap : ∀ u : Space n, ‖u‖ = 1 →
      μ {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*r} ≤
        ENNReal.ofReal (K*(3*r)^ℓ)) :
    μ {z | (p,z) ∈ G ∧ displacementAngle p q z ≤ r} ≤
      2*ENNReal.ofReal (K*(3*r)^ℓ) := by
  let u := normalize (q-p)
  have hu : ‖u‖ = 1 := norm_normalize (sub_ne_zero.mpr hq)
  have hsub : {z | (p,z) ∈ G ∧ displacementAngle p q z ≤ r} ⊆
      {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*r} ∪
      {z | (p,z) ∈ G ∧ dist (normalize (z-p)) (-u) < 3*r} := by
    rintro z ⟨hz,ha⟩
    rcases displacementAngle_two_caps p q z hq (hdiag z hz) hr ha with h | h
    · exact Or.inl ⟨hz,h⟩
    · exact Or.inr ⟨hz,h⟩
  have hh := (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add (hcap u hu) (hcap (-u) (by simpa only [norm_neg] using hu))))
  exact hh.trans_eq (by ring)

end Falconer

end OAI

end ExtensionScope127

/- Source: OAI.MeasureTheory.Falconer.Radial.ReverseRadialGeometry. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope128



namespace OAI

/-! # Reverse radial caps bound collisions of original source directions -/

namespace Falconer
open NormedSpace
variable {n : ℕ}

theorem unit_perpendicular_norm_symm {u v : Space n} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖perpendicularPart u v‖ = ‖perpendicularPart v u‖ := by
  have h₁ := norm_perpendicularPart_sq hu v
  have h₂ := norm_perpendicularPart_sq hv u
  rw [hu] at h₂
  rw [hv] at h₁
  rw [real_inner_comm u v] at h₂
  nlinarith [norm_nonneg (perpendicularPart u v),norm_nonneg (perpendicularPart v u)]

theorem perpendicularPart_neg_left (u v : Space n) :
    perpendicularPart (-u) v = perpendicularPart u v := by
  simp [perpendicularPart,neg_smul]

theorem reverse_radial_angle_identity (x z y : Space n) (hz : z ≠ x) (hy : y ≠ z) :
    ‖y-z‖*displacementAngle z y x =
      ‖perpendicularPart (normalize (z-x)) (y-z)‖ := by
  have hx : x-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hy0 : y-z ≠ 0 := sub_ne_zero.mpr hy
  have hsym := unit_perpendicular_norm_symm (norm_normalize hy0) (norm_normalize hx)
  have hneg : normalize (x-z) = -normalize (z-x) := by
    simp only [NormedSpace.normalize,norm_sub_rev x z]
    rw [show x-z = -(z-x) by abel,smul_neg]
  have he : perpendicularPart (normalize (z-x)) (y-z) =
      ‖y-z‖ • perpendicularPart (normalize (z-x)) (normalize (y-z)) := by
    rw [← perpendicularPart_smul,norm_smul_normalize]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  congr 1
  change ‖perpendicularPart (normalize (y-z)) (normalize (x-z))‖ = _
  rw [hsym,hneg,perpendicularPart_neg_left]

theorem reverse_radial_collision_angle (x z y : Space n) (hz : z ≠ x) (hy : y ≠ z)
    {D δ : ℝ} (hD : ‖y-x‖ ≤ D)
    (hclose : dist (normalize (y-x)) (normalize (z-x)) ≤ δ) :
    displacementAngle z y x ≤ D*δ/‖y-z‖ := by
  have hu : ‖normalize (z-x)‖ = 1 := norm_normalize (sub_ne_zero.mpr hz)
  have hperp : ‖perpendicularPart (normalize (z-x)) (normalize (y-x))‖ ≤ δ := by
    have hh := norm_perpendicularPart_le hu (normalize (y-x)-normalize (z-x))
    rw [perpendicularPart_sub] at hh
    have he : perpendicularPart (normalize (z-x)) (normalize (z-x)) = 0 := by
      simp [perpendicularPart,hu]
    rw [he,sub_zero] at hh
    exact hh.trans hclose
  have hraw : ‖perpendicularPart (normalize (z-x)) (y-z)‖ ≤ D*δ := by
    have he : y-z = (y-x)-(z-x) := by abel
    rw [he,perpendicularPart_sub,perpendicular_normalize_self,sub_zero]
    have he' : perpendicularPart (normalize (z-x)) (y-x) =
        ‖y-x‖ • perpendicularPart (normalize (z-x)) (normalize (y-x)) := by
      rw [← perpendicularPart_smul,norm_smul_normalize]
    rw [he',norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul hD hperp (norm_nonneg _) ((norm_nonneg _).trans hD)
  apply (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hy))).mpr
  rw [mul_comm,reverse_radial_angle_identity x z y hz hy]
  exact hraw

end Falconer

end OAI

end ExtensionScope128

/- Source: OAI.MeasureTheory.Falconer.Angular.TubeDirectionRobustness. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope129


namespace OAI

/-! # Robust tube covers under small unoriented changes of direction -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem tube_direction_point_bound {w v z : Space d} {η L r : ℝ}
    (hw : ‖w‖ = 1) (hv : ‖v‖ = 1) (hdir : ‖w-v‖ ≤ η)
    (hz : ‖z‖ ≤ L) (htube : ‖perpendicularPart w z‖ ≤ r) :
    ‖perpendicularPart v z‖ ≤ r+2*η*L := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hdir
  have he := perpendicularPart_direction_error hv hw z
  have htri := norm_sub_le_norm_sub_add_norm_sub (perpendicularPart v z) (perpendicularPart w z) 0
  simp only [sub_zero] at htri
  have hdir' : ‖v-w‖ ≤ η := by simpa only [norm_sub_rev] using hdir
  calc
    _ ≤ ‖perpendicularPart v z-perpendicularPart w z‖+‖perpendicularPart w z‖ := htri
    _ ≤ 2*‖v-w‖*‖z‖+r := add_le_add he htube
    _ ≤ 2*η*L+r := by gcongr
    _ = _ := by ring

theorem unoriented_tube_direction_point_bound {w v z : Space d} {η L r : ℝ}
    (hw : ‖w‖ = 1) (hv : ‖v‖ = 1)
    (hdir : ‖w-v‖ ≤ η ∨ ‖w+v‖ ≤ η)
    (hz : ‖z‖ ≤ L) (htube : ‖perpendicularPart w z‖ ≤ r) :
    ‖perpendicularPart v z‖ ≤ r+2*η*L := by
  rcases hdir with hdir | hdir
  · exact tube_direction_point_bound hw hv hdir hz htube
  · have hh := tube_direction_point_bound hw (show ‖-v‖ = 1 by simpa using hv)
      (show ‖w-(-v)‖ ≤ η by simpa only [sub_neg_eq_add] using hdir) hz htube
    simpa only [perpendicularPart_neg_left] using hh

theorem tube_cover_direction_transport (μ : Measure (Space d))
    {w v : Space d} {D B η r : ℝ} (hw : ‖w‖ = 1) (hv : ‖v‖ = 1)
    (hdir : ‖w-v‖ ≤ η ∨ ‖w+v‖ ≤ η)
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (S : Finset (Space d)) (hS : ∀ a ∈ S, ‖a‖ ≤ B) :
    μ {x | ∃ a ∈ S, ‖perpendicularPart w (x-a)‖ ≤ r} ≤
      μ {x | ∃ a ∈ S, ‖perpendicularPart v (x-a)‖ ≤ r+2*η*(D+B)} := by
  apply measure_mono_ae
  filter_upwards [hμ] with x hx
  rintro ⟨a,ha,htube⟩
  refine ⟨a,ha,unoriented_tube_direction_point_bound hw hv hdir ?_ htube⟩
  exact (norm_sub_le x a).trans (add_le_add hx (hS a ha))

end Falconer

end OAI

end ExtensionScope129

/- Source: OAI.MeasureTheory.Falconer.Angular.GoodDirectionMass. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope130


namespace OAI

/-! # One good witness direction rules out mass in a nearby heavy tube cover -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem mass_lt_of_good_direction_cover (μ : Measure (Space d))
    (Bad : Set (Sphere d)) (v : Sphere d) (hv : v ∉ Bad)
    (w : Space d) (hw : ‖w‖ = 1) {D B η r R : ℝ}
    (hdir : ‖w-(v:Space d)‖ ≤ η ∨ ‖w+(v:Space d)‖ ≤ η)
    (hwidth : r+2*η*(D+B) ≤ R) (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (J : Finset (Space d)) (hJ : ∀ a ∈ J, ‖a‖ ≤ B) (N : ℕ) (hcard : J.card ≤ N)
    (a : ℝ≥0∞)
    (henvelope : ∀ S : Finset (Space d), S.card ≤ N →
      a ≤ μ {x | ∃ b ∈ S, ‖perpendicularPart (v:Space d) (x-b)‖ ≤ R} → v ∈ Bad)
    (T : Set (Space d))
    (hcover : ∀ x ∈ T, ∃ b ∈ J, ‖perpendicularPart w (x-b)‖ ≤ r) : μ T < a := by
  by_contra hn
  have hlarge : a ≤ μ T := le_of_not_gt hn
  apply hv
  apply henvelope J hcard
  apply hlarge.trans
  apply (measure_mono hcover).trans
  apply (tube_cover_direction_transport μ hw (sphere_norm v) hdir hμ J hJ).trans
  apply measure_mono
  rintro x ⟨b,hb,hxb⟩
  exact ⟨b,hb,hxb.trans hwidth⟩

end Falconer

end OAI

end ExtensionScope130

/- Source: OAI.MeasureTheory.Falconer.Radial.MiddleHeavyRadialMass. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope131




namespace OAI

/-! # A good witness controls the full conditional heavy radial fiber -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem radial_collision_le_tube_mass (μ : Measure (Space (n+1)))
    (x z : Space (n+1)) (hz : z ≠ x) {H δ W : ℝ}
    (hsource : ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) (hwidth : H*δ ≤ W) :
    radialCollisionMass μ δ (z,x) ≤
      μ {y | ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ W} := by
  apply measure_mono_ae
  filter_upwards [hsource] with y hy
  intro hclose
  have hv : ‖normalize (z-x)‖ = 1 := norm_normalize (sub_ne_zero.mpr hz)
  have hperp : ‖perpendicularPart (normalize (z-x)) (normalize (y-x))‖ ≤ δ := by
    have hh := norm_perpendicularPart_le hv (normalize (y-x)-normalize (z-x))
    rw [perpendicularPart_sub] at hh
    have he : perpendicularPart (normalize (z-x)) (normalize (z-x)) = 0 := by
      simp [perpendicularPart,hv]
    rw [he,sub_zero] at hh
    exact hh.trans hclose
  have he : perpendicularPart (normalize (z-x)) (y-x) =
      ‖y-x‖ • perpendicularPart (normalize (z-x)) (normalize (y-x)) := by
    rw [← perpendicularPart_smul,norm_smul_normalize]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact (mul_le_mul hy hperp (norm_nonneg _) ((norm_nonneg _).trans hy)).trans hwidth

theorem middle_heavy_radial_mass_lt (μ : Measure (Space (n+1)))
    (x c : Space (n+1)) {r D δ θ C B H η R : ℝ}
    (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hδ : 0 < δ)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (hbounded : ∀ᵐ y ∂μ, ‖y‖ ≤ B) (hpin : ∀ᵐ y ∂μ, ‖y-x‖ ≤ H)
    (hwidth : H*θ ≤ C*δ)
    (Bad : Set (Sphere (n+1))) (v : Sphere (n+1)) (hv : v ∉ Bad)
    (hdir : ‖normalize (c-x)-(v:Space (n+1))‖ ≤ η ∨
      ‖normalize (c-x)+(v:Space (n+1))‖ ≤ η)
    (hrobust : (2*((n+1:ℕ):ℝ)+1)*δ+2*η*(B+B) ≤ R)
    (F a : ℝ≥0∞) (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ))
    (henvelope : ∀ S : Finset (Space (n+1)),
      (S.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ →
      a ≤ μ {z | ∃ b ∈ S, ‖perpendicularPart (v:Space (n+1)) (z-b)‖ ≤ R} → v ∈ Bad)
    (T : Set (Space (n+1)))
    (hT : ∀ z ∈ T, z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B ∧
      F < radialCollisionMass μ θ (z,x)) : μ T < a := by
  obtain ⟨J,hJ,hcover,hcard⟩ := bounded_frozen_heavy_tube_cover μ x c hr hcx hδ
    hfreeze hsource T (fun z hz => ⟨(hT z hz).1,(hT z hz).2.1,(hT z hz).2.2.1⟩)
    F (fun z hz => (hT z hz).2.2.2.le.trans
      (radial_collision_le_tube_mass μ x z (hT z hz).1 hpin hwidth)) L hL
  exact mass_lt_of_good_direction_cover μ Bad v hv _
    (norm_normalize (norm_pos_iff.mp (hr.trans_le hcx))) hdir hrobust hbounded J hJ
    J.card le_rfl a (fun S hS => henvelope S
      ((mul_le_mul' (by exact_mod_cast hS) le_rfl).trans hcard)) T hcover

end Falconer

end OAI

end ExtensionScope131

/- Source: OAI.MeasureTheory.Falconer.Radial.RadialCollisionDeletion. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope132




namespace OAI

/-! # Threshold deletion for the full conditional radial collision mass -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_collision_pair_integral (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G) (δ : ℝ) :
    (∫⁻ p in G, radialCollisionMass μ δ p ∂μ.prod ν) =
      ∫⁻ z, (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ δ (z,x) ∂ν) ∂μ := by
  rw [← lintegral_indicator hG,lintegral_prod _
    ((radialCollisionMass_measurable μ δ).indicator hG).aemeasurable]
  apply lintegral_congr
  intro z
  have hGz : MeasurableSet {x : Space d | (z,x) ∈ G} :=
    hG.preimage (measurable_const.prodMk measurable_id)
  rw [← lintegral_indicator hGz]
  rfl

theorem radial_collision_bad_mass (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (δ : ℝ) {F C : ℝ≥0∞} (hF : F ≠ 0) (hFtop : F ≠ ∞)
    (hmean : ∀ᵐ z ∂μ, (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ δ (z,x) ∂ν) ≤ C) :
    (μ.prod ν) (G ∩ {p | F < radialCollisionMass μ δ p}) ≤ C*μ univ/F := by
  have hmeas := radialCollisionMass_measurable μ δ
  have htotal : (∫⁻ p in G, radialCollisionMass μ δ p ∂μ.prod ν) ≤ C*μ univ := by
    rw [radial_collision_pair_integral μ ν G hG δ]
    exact (lintegral_mono_ae hmean).trans_eq (lintegral_const C)
  have hm : ((μ.prod ν).restrict G) {p | F ≤ radialCollisionMass μ δ p} ≤
      (∫⁻ p in G, radialCollisionMass μ δ p ∂μ.prod ν)/F :=
    meas_ge_le_lintegral_div hmeas.aemeasurable hF hFtop
  calc
    _ = ((μ.prod ν).restrict G) {p | F < radialCollisionMass μ δ p} := by
      rw [Measure.restrict_apply (measurableSet_lt measurable_const hmeas),inter_comm]
    _ ≤ ((μ.prod ν).restrict G) {p | F ≤ radialCollisionMass μ δ p} :=
      measure_mono (fun p hp => show F ≤ radialCollisionMass μ δ p from
        (show F < radialCollisionMass μ δ p from hp).le)
    _ ≤ (∫⁻ p in G, radialCollisionMass μ δ p ∂μ.prod ν)/F := hm
    _ ≤ _ := ENNReal.div_le_div_right htotal F

theorem radial_collision_pruning (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (δ : ℝ) {F C : ℝ≥0∞} (hF : F ≠ 0) (hFtop : F ≠ ∞)
    (hmean : ∀ᵐ z ∂μ, (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ δ (z,x) ∂ν) ≤ C) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ C*μ univ/F ∧ ∀ p ∈ H, radialCollisionMass μ δ p ≤ F := by
  let H := G ∩ {p | radialCollisionMass μ δ p ≤ F}
  refine ⟨H,hG.inter (measurableSet_le (radialCollisionMass_measurable μ δ) measurable_const),
    inter_subset_left,?_,fun _ hp => hp.2⟩
  have he : G \ H = G ∩ {p | F < radialCollisionMass μ δ p} := by
    ext p
    simp only [H,mem_sdiff,mem_inter_iff,mem_ofPred_eq,not_and,not_le]
    tauto
  rw [he]
  exact radial_collision_bad_mass μ ν G hG δ hF hFtop hmean

end Falconer

end OAI

end ExtensionScope132

/- Source: OAI.MeasureTheory.Falconer.Measures.RepresentedPruning. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope133


namespace OAI

/-! # Threshold deletion using one witness only on represented pin fibers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem represented_threshold_pruning (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (G : Set (X × Y)) (hG : MeasurableSet G)
    (K : X × Y → ℝ≥0∞) (hK : Measurable K) (F a : ℝ≥0∞)
    (hsmall : ∀ y, (∃ x, (x,y) ∈ G) → μ {x | (x,y) ∈ G ∧ F < K (x,y)} ≤ a) :
    ∃ H : Set (X × Y), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ a*ν univ ∧ ∀ p ∈ H, K p ≤ F := by
  let H := G ∩ {p | K p ≤ F}
  have hH : MeasurableSet H := hG.inter (measurableSet_le hK measurable_const)
  refine ⟨H,hH,inter_subset_left,?_,fun p hp => hp.2⟩
  rw [Measure.prod_apply_symm (hG.diff hH)]
  apply (lintegral_mono _).trans_eq (lintegral_const a)
  intro y
  change μ {x | (x,y) ∈ G \ H} ≤ a
  by_cases hy : ∃ x, (x,y) ∈ G
  · apply (measure_mono _).trans (hsmall y hy)
    rintro x ⟨hx,hnot⟩
    exact ⟨hx,lt_of_not_ge (fun hk => hnot (show (x,y) ∈ H from ⟨hx,hk⟩))⟩
  · have he : {x | (x,y) ∈ G \ H} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      exact fun x hx => hy ⟨x,hx.1⟩
    rw [he,measure_empty]
    exact zero_le

end Falconer

end OAI

end ExtensionScope133

/- Source: OAI.MeasureTheory.Falconer.Angular.WitnessDirection. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope134



namespace OAI

/-! # Unoriented closeness of a witness direction to the source-cell center -/

namespace Falconer
open NormedSpace
variable {d : ℕ}

theorem cell_center_witness_direction (w₀ : Sphere d) (x c z : Space d)
    {r D : ℝ} (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hzx : z ≠ x)
    (hzc : ‖z-c‖ ≤ D) :
    ‖normalize (c-x)+(normalizeToSphere w₀ (x-z):Space d)‖ ≤ 2*D/r := by
  rw [normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr hzx.symm)]
  have hn : normalize (x-z) = -normalize (z-x) := by
    rw [show x-z = -(z-x) by abel,normalize_neg]
  rw [hn,← sub_eq_add_neg]
  apply (le_div_iff₀ hr).mpr
  have hh := normalize_distance_scaled hcx (sub_ne_zero.mpr hzx)
  rw [dist_eq_norm,dist_eq_norm,sub_sub_sub_cancel_right,norm_sub_rev c z] at hh
  nlinarith

end Falconer

end OAI

end ExtensionScope134

/- Source: OAI.MeasureTheory.Falconer.Radial.MiddleRadialPruning. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope135





namespace OAI

/-! # Original-product middle-interval pruning with no choice of pin witnesses -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem middle_radial_pruning (μ ν : Measure (Space (n+1)))
    [SFinite μ] [SFinite ν] (w₀ : Sphere (n+1))
    (G : Set (Space (n+1) × Space (n+1))) (hG : MeasurableSet G)
    (Bad : Set (Sphere (n+1))) (hBad : MeasurableSet Bad)
    (c : Space (n+1)) {r D δ θ C B H R : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hfreeze : 8*D^2/r ≤ δ)
    (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D) (hbounded : ∀ᵐ y ∂μ, ‖y‖ ≤ B)
    (hgeom : ∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B)
    (hpin : ∀ x, (∃ z, (z,x) ∈ G) →
      r ≤ ‖c-x‖ ∧ ∀ᵐ y ∂μ, ‖y-x‖ ≤ H)
    (hwidth : H*θ ≤ C*δ)
    (hrobust : (2*((n+1:ℕ):ℝ)+1)*δ+2*(2*D/r)*(B+B) ≤ R)
    (F a e : ℝ≥0∞) (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ))
    (henvelope : ∀ v : Sphere (n+1), ∀ S : Finset (Space (n+1)),
      (S.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ →
      a ≤ μ {z | ∃ b ∈ S, ‖perpendicularPart (v:Space (n+1)) (z-b)‖ ≤ R} → v ∈ Bad)
    (hbadmass : (μ.prod ν) (radialBadWitness w₀ G Bad) ≤ e) :
    ∃ G' : Set (Space (n+1) × Space (n+1)), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ e+a*ν univ ∧
      ∀ p ∈ G', radialCollisionMass μ θ p ≤ F := by
  let G₁ := G \ radialBadWitness w₀ G Bad
  have hG₁ : MeasurableSet G₁ := hG.diff (radialBadWitness_measurable w₀ hG hBad)
  have hsub : G₁ ⊆ G := sdiff_subset
  have hsmall (x : Space (n+1)) (hx : ∃ z, (z,x) ∈ G₁) :
      μ {z | (z,x) ∈ G₁ ∧ F < radialCollisionMass μ θ (z,x)} ≤ a := by
    obtain ⟨z,hz⟩ := hx
    have hzx := hgeom z x (hsub hz)
    have hpx := hpin x ⟨z,hsub hz⟩
    let v := normalizeToSphere w₀ (x-z)
    have hv : v ∉ Bad := direction_good_of_not_radialBadWitness w₀ G Bad hz
    apply le_of_lt
    apply middle_heavy_radial_mass_lt μ x c hr hpx.1 hδ hfreeze hsource hbounded
      hpx.2 hwidth Bad v hv (Or.inr (cell_center_witness_direction w₀ x c z hr
        hpx.1 hzx.1 hzx.2.1)) hrobust F a L hL (henvelope v)
    intro y hy
    have hh := hgeom y x (hsub hy.1)
    exact ⟨hh.1,hh.2.1,hh.2.2,hy.2⟩
  obtain ⟨G',hG',hG'sub,hdeleted,hbound⟩ := represented_threshold_pruning μ ν G₁ hG₁
    (radialCollisionMass μ θ) (radialCollisionMass_measurable μ θ) F a hsmall
  refine ⟨G',hG',hG'sub.trans hsub,?_,hbound⟩
  have hcover : G \ G' ⊆ radialBadWitness w₀ G Bad ∪ (G₁ \ G') := by
    intro p hp
    by_cases hb : p ∈ radialBadWitness w₀ G Bad
    · exact Or.inl hb
    · exact Or.inr ⟨⟨hp.1,hb⟩,hp.2⟩
  exact (measure_mono hcover).trans ((measure_union_le _ _).trans (add_le_add hbadmass hdeleted))

end Falconer

end OAI

end ExtensionScope135

/- Source: OAI.MeasureTheory.Falconer.Radial.HeavyCoverCount. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope136


namespace OAI

/-! # Absorbing the fixed heavy-cover constant into the angular power margin -/

namespace Falconer
open Filter
open scoped ENNReal Topology

theorem heavy_cover_card_le {m : ℕ} {F K T : ℝ} (hF : 0 < F) (hK : 0 ≤ K)
    (h : (m:ℝ≥0∞)*ENNReal.ofReal F ≤ ENNReal.ofReal K) (hbudget : K ≤ T*F) :
    (m:ℝ) ≤ T := by
  have hm : ENNReal.ofReal ((m:ℝ)*F) ≤ ENNReal.ofReal K := by
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg m),ENNReal.ofReal_natCast] using h
  have hm' := (ENNReal.ofReal_le_ofReal_iff hK).mp hm
  nlinarith

theorem eventually_heavy_cover_card {q b K : ℝ} (hb : 0 < b) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ m : ℕ,
      (m:ℝ≥0∞)*ENNReal.ofReal ((1/(2:ℝ)^N)^(q+b/2)) ≤ ENNReal.ofReal K →
      (m:ℝ) ≤ (1/(2:ℝ)^N)^(-q-b) := by
  have he := eventually_const_mul_rpow_lt (show -b/2 < (0:ℝ) by linarith) K
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (dyadic_inverse_tendsto.eventually he)
  refine ⟨N₀,fun N hN m hm => ?_⟩
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  apply heavy_cover_card_le (Real.rpow_pos_of_pos hδ _) hK hm
  have hbound : K ≤ (1/(2:ℝ)^N)^(-b/2) := by
    have hh := (hN₀ N hN).2
    simpa only [Real.rpow_zero,mul_one] using hh.le
  apply hbound.trans_eq
  rw [← Real.rpow_add hδ]
  congr 1
  ring

end Falconer

end OAI

end ExtensionScope136

/- Source: OAI.MeasureTheory.Falconer.Radial.NonendpointMiddleRadial. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope137




namespace OAI

/-! # Quantitative middle-interval improvement from the published planar input -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem nonendpoint_middle_radial_pruning (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
    (hqt : q < t) (ht : t-(h:ℝ) < 1) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+2)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (_w₀ : Sphere (h+2)) (G : Set (Space (h+2) × Space (h+2))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z‖ ≤ 1/4) →
      (∀ᵐ z ∂μ, ‖z‖ ≤ 1/4) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/r ≤ 1/(2:ℝ)^N →
      H*θ ≤ 1/(2:ℝ)^N →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖(0:Space (h+2))-x‖ ∧
        ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^N)^b) ∧
        ∀ p ∈ G', radialCollisionMass μ θ p ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(q+b/2)) := by
  let C : ℝ := 2*((h+2:ℕ):ℝ)+2
  let L : ℕ := h+5
  let K : ℕ := (2*L+1)^(h+2)
  obtain ⟨ε,b,hε,hb,N₁,hN₁⟩ := nonendpoint_radial_bad_directions hpublished hq hq' hqt ht
    (show 0 ≤ C by dsimp [C]; positivity)
  obtain ⟨N₂,hN₂⟩ := eventually_heavy_cover_card (q := q) (K := (K:ℝ)) hb (by positivity)
  refine ⟨ε,b,hε,hb,max N₁ N₂,?_⟩
  intro N hN μ ν _ _ hν w₀ G hG hgeom hμ hballs hcaps r H θ hr hfreeze hwidth hpin
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Bad,hBad,hcontains,hbadmass⟩ := hN₁ N ((le_max_left _ _).trans hN) μ ν hν
    w₀ G hG (fun z x hx => (hgeom z x hx).1.symm) hμ hballs hcaps
  have hL : 1+1+((h+1+1:ℕ):ℝ)+1/2 ≤ (L:ℝ) := by dsimp [L]; push_cast; linarith
  have hrobust : (2*((h+1+1:ℕ):ℝ)+1)*δ+2*(2*(1/4)/r)*(1/4+1/4) ≤ C*δ := by
    have he : 2*(2*(1/4:ℝ)/r)*(1/4+1/4) = 8*(1/4:ℝ)^2/r := by ring
    rw [he]
    dsimp [C]
    change 8*(1/4:ℝ)^2/r ≤ δ at hfreeze
    nlinarith
  have henv (v : Sphere (h+2)) (S : Finset (Space (h+2)))
      (hc : (S.card:ℝ≥0∞)*ENNReal.ofReal (δ^(q+b/2)) ≤
        ((2*L+1)^(h+1+1):ℕ)*μ univ)
      (hm : ENNReal.ofReal (δ^b) ≤
        μ {z | ∃ a ∈ S, ‖perpendicularPart (v:Space (h+2)) (z-a)‖ ≤ C*δ}) : v ∈ Bad := by
    apply hcontains
    refine ⟨S,?_,hm⟩
    apply hN₂ N ((le_max_right _ _).trans hN) S.card
    simpa only [measure_univ,mul_one,ENNReal.ofReal_natCast] using hc
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := middle_radial_pruning (θ := θ) (n := h+1) μ ν w₀ G hG
    Bad hBad 0 hr hδ hfreeze (by simpa only [sub_zero] using hμ) hμ
    (fun z x hx => ⟨(hgeom z x hx).1,by simpa only [sub_zero] using (hgeom z x hx).2,
      (hgeom z x hx).2⟩) hpin (by simpa only [one_mul] using hwidth) hrobust (ENNReal.ofReal (δ^(q+b/2)))
    (ENNReal.ofReal (δ^b)) (ENNReal.ofReal (δ^b)) L hL henv hbadmass
  refine ⟨G',hG',hsub,hdel.trans ?_,hbound⟩
  calc
    _ ≤ ENNReal.ofReal (δ^b)+ENNReal.ofReal (δ^b)*1 :=
      add_le_add le_rfl (mul_le_mul' le_rfl hν)
    _ = 2*ENNReal.ofReal (δ^b) := by ring

end Falconer

end OAI

end ExtensionScope137

/- Source: OAI.MeasureTheory.Falconer.Incidence.RadialZoomFiniteBalls. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope138


namespace OAI

/-! # Finite-scale conditional balls and reverse caps after a fixed contraction -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_ae_iff (μ : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c : Space d) (P : Space d → Prop) :
    (∀ᵐ x ∂Measure.map (radialZoom a ha.ne' c) μ, P x) ↔
      ∀ᵐ x ∂μ, P (radialZoom a ha.ne' c x) := by
  have h := MeasurableEquiv.map_ae (radialZoom a ha.ne' c).toMeasurableEquiv μ
  change Filter.map (radialZoom a ha.ne' c) (ae μ) =
    ae (Measure.map (radialZoom a ha.ne' c) μ) at h
  rw [← h]
  rfl

theorem radialZoom_scaled_ball_bound (μ : Measure (Space d))
    {a δ K L s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hK : 1 ≤ K)
    (hL : 0 < L) (hs : 0 ≤ s) (hmass : μ univ ≤ 1) (c : Space d)
    (hball : ∀ x : Space d, ∀ r : ℝ, δ ≤ r → r ≤ 1/L →
      μ (Metric.ball x r) ≤ ENNReal.ofReal (K*(L*r)^s)) :
    ∀ x : Space d, ∀ r : ℝ, 0 < r → δ ≤ r →
      Measure.map (radialZoom a ha.ne' c) μ (Metric.ball x r) ≤
        ENNReal.ofReal (K*a^(-s)*(L*r)^s) := by
  intro x r hr hδ
  rw [radialZoom_ball_apply μ ha]
  have hrra : r ≤ r/a := (le_div_iff₀ ha).mpr (mul_le_of_le_one_right hr.le ha1)
  have he : K*(L*(r/a))^s = K*a^(-s)*(L*r)^s := by
    rw [show L*(r/a) = (L*r)/a by ring,
      Real.div_rpow (mul_pos hL hr).le ha.le,div_eq_mul_inv,← Real.rpow_neg ha.le]
    ring
  rw [← he]
  by_cases hsmall : r/a ≤ 1/L
  · exact hball _ _ (hδ.trans hrra) hsmall
  · have hscale : 1 ≤ L*(r/a) := by
      have hh := (lt_of_not_ge hsmall)
      have hh' := (div_lt_iff₀ hL).mp hh
      nlinarith
    have hp := Real.one_le_rpow hscale hs
    have hcoeff : 1 ≤ K*(L*(r/a))^s := by nlinarith
    exact ((measure_mono (subset_univ _)).trans hmass).trans
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hcoeff)

theorem norm_radialZoom_sub {a : ℝ} (ha : 0 < a) (c x y : Space d) :
    ‖radialZoom a ha.ne' c x-radialZoom a ha.ne' c y‖ = a*‖x-y‖ := by
  rw [radialZoom_sub,norm_smul,Real.norm_eq_abs,abs_of_pos ha]

theorem radialZoom_reverse_cap (ν : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c z u : Space d) (r : ℝ) (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    Measure.map (radialZoom a ha.ne' c) ν
      {x | (radialZoom a ha.ne' c z,x) ∈ zoomPairSet (radialZoom a ha.ne' c) G ∧
        dist (normalize (x-radialZoom a ha.ne' c z)) u < r} =
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} := by
  let e := radialZoom a ha.ne' c
  have hm : MeasurableSet {x | (e z,x) ∈ zoomPairSet e G ∧
      dist (normalize (x-e z)) u < r} :=
    ((zoomPairSet_measurable e hG).preimage (measurable_const.prodMk measurable_id)).inter
      (measurableSet_lt ((measurable_normalized_vector
        (measurable_id.sub measurable_const)).dist measurable_const) measurable_const)
  rw [Measure.map_apply e.measurable hm]
  congr 1
  ext x
  simp only [mem_preimage,mem_ofPred_eq,mem_zoomPairSet]
  dsimp only [e]
  rw [radialZoom_sub,normalize_smul_of_pos ha]

end Falconer

end OAI

end ExtensionScope138

/- Source: OAI.MeasureTheory.Falconer.Radial.MiddleRadialTransport. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope139


namespace OAI

/-! # Geometric data for middle-interval pruning after cell normalization -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_quarter_bound {a : ℝ} (ha : 0 < a) (c z : Space d)
    (hz : ‖z-c‖ ≤ 1/(4*a)) : ‖radialZoom a ha.ne' c z‖ ≤ 1/4 := by
  rw [radialZoom_norm ha]
  calc
    _ ≤ a*(1/(4*a)) := mul_le_mul_of_nonneg_left hz ha.le
    _ = _ := by field_simp

theorem radialZoom_pin_distance {a r : ℝ} (ha : 0 < a) (c x : Space d)
    (hx : r ≤ ‖c-x‖) : a*r ≤ ‖(0:Space d)-radialZoom a ha.ne' c x‖ := by
  rw [zero_sub,norm_neg,radialZoom_norm ha,norm_sub_rev x c]
  exact mul_le_mul_of_nonneg_left hx ha.le

theorem radialZoom_pair_ae_bound (μ : Measure (Space d)) {a H : ℝ}
    (ha : 0 < a) (c x : Space d) (h : ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) :
    ∀ᵐ y ∂Measure.map (radialZoom a ha.ne' c) μ,
      ‖y-radialZoom a ha.ne' c x‖ ≤ a*H := by
  rw [radialZoom_ae_iff μ ha]
  filter_upwards [h] with y hy
  rw [norm_radialZoom_sub ha]
  exact mul_le_mul_of_nonneg_left hy ha.le

theorem radialZoom_reverse_slab (ν : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c z u : Space d) (r : ℝ) (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    Measure.map (radialZoom a ha.ne' c) ν
      {x | (radialZoom a ha.ne' c z,x) ∈ zoomPairSet (radialZoom a ha.ne' c) G ∧
        |inner ℝ u (normalize (x-radialZoom a ha.ne' c z))| ≤ r} =
      ν {x | (z,x) ∈ G ∧ |inner ℝ u (normalize (x-z))| ≤ r} := by
  let e := radialZoom a ha.ne' c
  have hi : Measurable (fun x : Space d => inner ℝ u (normalize (x-e z))) :=
    measurable_const.inner (measurable_normalized_vector (measurable_id.sub measurable_const))
  have hm : MeasurableSet {x | (e z,x) ∈ zoomPairSet e G ∧
      |inner ℝ u (normalize (x-e z))| ≤ r} :=
    ((zoomPairSet_measurable e hG).preimage (measurable_const.prodMk measurable_id)).inter
      (measurableSet_le hi.abs measurable_const)
  rw [Measure.map_apply e.measurable hm]
  congr 1
  ext x
  simp only [mem_preimage,mem_ofPred_eq,mem_zoomPairSet]
  dsimp only [e]
  rw [radialZoom_sub,normalize_smul_of_pos ha]

end Falconer

end OAI

end ExtensionScope139

/- Source: OAI.MeasureTheory.Falconer.Radial.RadialZoomPruning. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope140


namespace OAI

/-! # Pulling conditional radial pruning back to the unchanged original pair law -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_pruning_unzoom (μ ν : Measure (Space d)) [SFinite μ] [SFinite ν]
    {a : ℝ} (ha : 0 < a) (c : Space d)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (H : Set (Space d × Space d)) (hH : MeasurableSet H)
    (hsub : H ⊆ zoomPairSet (radialZoom a ha.ne' c) G)
    (θ : ℝ) (F E : ℝ≥0∞)
    (hdel : ((Measure.map (radialZoom a ha.ne' c) μ).prod
      (Measure.map (radialZoom a ha.ne' c) ν))
      (zoomPairSet (radialZoom a ha.ne' c) G \ H) ≤ E)
    (hbound : ∀ p ∈ H, radialCollisionMass (Measure.map (radialZoom a ha.ne' c) μ) θ p ≤ F) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ E ∧ ∀ p ∈ G', radialCollisionMass μ θ p ≤ F := by
  let e := radialZoom a ha.ne' c
  let G' := (Prod.map e e) ⁻¹' H
  have hG' : MeasurableSet G' := hH.preimage (e.measurable.prodMap e.measurable)
  refine ⟨G',hG',?_,?_,?_⟩
  · intro p hp
    exact (mem_zoomPairSet e G p.1 p.2).mp (hsub hp)
  · have he : (Prod.map e e) ⁻¹' (zoomPairSet e G \ H) = G \ G' := by
      ext p
      change ((e p.1,e p.2) ∈ zoomPairSet e G ∧ (e p.1,e p.2) ∉ H) ↔
        ((p.1,p.2) ∈ G ∧ (e p.1,e p.2) ∉ H)
      rw [mem_zoomPairSet]
    rw [← he,← Measure.map_apply (e.measurable.prodMap e.measurable)
      ((zoomPairSet_measurable e hG).diff hH),← Measure.map_prod_map μ ν e.measurable e.measurable]
    exact hdel
  · intro p hp
    have hh := hbound (e p.1,e p.2) hp
    rwa [radial_collision_zoom μ ha c p.1 p.2 θ] at hh

end Falconer

end OAI

end ExtensionScope140

/- Source: OAI.MeasureTheory.Falconer.Estimates.NonendpointOriginalMiddle. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope141




namespace OAI

/-! # Nonendpoint middle-interval pruning in the original source-cell coordinates -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem nonendpoint_original_middle_pruning (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
    (hqt : q < t) (ht : t-(h:ℝ) < 1) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+2)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (_w₀ : Sphere (h+2)) (c : Space (h+2)) (a : ℝ), 0 < a →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z-c‖ ≤ 1/(4*a)) →
      (∀ᵐ z ∂μ, ‖z-c‖ ≤ 1/(4*a)) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x ((1/(2:ℝ)^j)/a)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/(a*r) ≤ 1/(2:ℝ)^N →
      (a*H)*θ ≤ 1/(2:ℝ)^N →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖c-x‖ ∧ ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^N)^b) ∧
        ∀ p ∈ G', radialCollisionMass μ θ p ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(q+b/2)) := by
  obtain ⟨ε,b,hε,hb,N₀,hN₀⟩ := nonendpoint_middle_radial_pruning hpublished hq hq' hqt ht
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ ν _ _ hν w₀ c a ha G hG hgeom hμ hball hcap r H θ hr hfreeze hwidth hpin
  let e := radialZoom a ha.ne' c
  have hν' : Measure.map e ν univ ≤ 1 := by
    simpa only [Measure.map_apply e.measurable MeasurableSet.univ,preimage_univ] using hν
  have hgeom' : ∀ z x, (z,x) ∈ zoomPairSet e G → z ≠ x ∧ ‖z‖ ≤ 1/4 := by
    intro z x hx
    have hh := hgeom (e.symm z) (e.symm x) hx
    refine ⟨fun he => hh.1 (congrArg e.symm he),?_⟩
    have hn := radialZoom_quarter_bound ha c (e.symm z) hh.2
    change ‖e (e.symm z)‖ ≤ 1/4 at hn
    simpa only [e.apply_symm_apply] using hn
  have hμ' : ∀ᵐ z ∂Measure.map e μ, ‖z‖ ≤ 1/4 := by
    rw [radialZoom_ae_iff μ ha]
    filter_upwards [hμ] with z hz
    exact radialZoom_quarter_bound ha c z hz
  have hball' : ∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      Measure.map e μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t) := by
    intro x j hj
    rw [radialZoom_ball_apply μ ha]
    exact hball _ j hj
  have hcap' : ∀ᵐ z ∂Measure.map e μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      Measure.map e ν {x | (z,x) ∈ zoomPairSet e G ∧
        dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q) := by
    rw [radialZoom_ae_iff μ ha]
    filter_upwards [hcap] with z hz
    intro w j hj
    rw [radialZoom_reverse_cap ν ha c z w _ G hG]
    exact hz w j hj
  have hpin' : ∀ x, (∃ z, (z,x) ∈ zoomPairSet e G) →
      a*r ≤ ‖(0:Space (h+2))-x‖ ∧ ∀ᵐ y ∂Measure.map e μ, ‖y-x‖ ≤ a*H := by
    intro x hx
    obtain ⟨z,hz⟩ := hx
    have hp := hpin (e.symm x) ⟨e.symm z,hz⟩
    have he : e (e.symm x) = x := e.apply_symm_apply x
    refine ⟨?_,?_⟩
    · have hd := radialZoom_pin_distance ha c (e.symm x) hp.1
      change a*r ≤ ‖(0:Space (h+2))-e (e.symm x)‖ at hd
      simpa only [he] using hd
    · have hb := radialZoom_pair_ae_bound μ ha c (e.symm x) hp.2
      change ∀ᵐ y ∂Measure.map e μ, ‖y-e (e.symm x)‖ ≤ a*H at hb
      simpa only [he] using hb
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := hN₀ N hN (Measure.map e μ) (Measure.map e ν) hν'
    w₀ (zoomPairSet e G) (zoomPairSet_measurable e hG) hgeom' hμ' hball' hcap'
    (a*r) (a*H) θ (mul_pos ha hr) hfreeze hwidth hpin'
  exact radial_pruning_unzoom μ ν ha c G hG G' hG' hsub θ _ _ hdel hbound

end Falconer

end OAI

end ExtensionScope141

/- Source: OAI.MeasureTheory.Falconer.Geometry.FiniteScaleBall. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope142


namespace OAI

/-! # Finite-scale balls and the support of the actual rescaled laws -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

theorem finite_scale_ball_extend (μ : Measure X) {δ K s : ℝ}
    (hmass : μ univ ≤ 1) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hball : ∀ x : X, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s)) :
    ∀ x : X, ∀ r : ℝ, δ ≤ r → μ (ball x r) ≤ ENNReal.ofReal (K*r^s) := by
  intro x r hr
  by_cases hr₁ : r ≤ 1
  · exact hball x r hr hr₁
  · have hp : 1 ≤ K*r^s := one_le_mul_of_one_le_of_one_le hK
      (Real.one_le_rpow (le_of_not_ge hr₁) hs)
    exact (measure_mono (subset_univ _)).trans (hmass.trans
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp))

namespace Regularization
variable {d : ℕ}

theorem rescaled_cell_norm_bound (Q : DyadicCube d) (hQ : Q.side = 1)
    (P : CellPath d) {z : Space d} (hz : z ∈ (Q.descendant P).carrier) :
    ‖cellScaleMap P.length (Q.descendant P).center z‖ ≤ Real.sqrt d := by
  have hs : 0 < (Q.descendant P).side := by rw [Q.descendant_side,hQ]; positivity
  have hdist := (Q.descendant P).dist_le hs.le hz ((Q.descendant P).center_mem hs)
  rw [cellScaleMap,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (2:ℝ)^P.length)]
  rw [dist_eq_norm] at hdist
  calc
    _ ≤ (2:ℝ)^P.length*(Real.sqrt d*(Q.descendant P).side) :=
      mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = Real.sqrt d := by rw [Q.descendant_side,hQ]; field_simp

theorem rescaled_conditional_support (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) (P : CellPath d) :
    ∀ᵐ z ∂Measure.map (cellScaleMap P.length (Q.descendant P).center)
      (ProbabilityTheory.cond ρ (Q.descendant P).carrier), ‖z‖ ≤ Real.sqrt d := by
  rw [ae_map_iff (cellScaleMap_continuous _ _).measurable.aemeasurable
    (isClosed_le continuous_norm continuous_const).measurableSet]
  exact ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable
    (fun z hz => rescaled_cell_norm_bound Q hQ P hz)

end Regularization
end Falconer

end OAI

end ExtensionScope142

/- Source: OAI.MeasureTheory.Falconer.Recursion.ProfileIncrementFrostman. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope143


namespace OAI

/-! # Turning a contact-interval profile inequality into actual conditional ball bounds -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem profileDrop_le_of_increment (m : ℝ → ℝ) (N : ℕ) (s E : ℝ)
    {p t : ℕ} (hpt : p ≤ t)
    (hinc : ∀ n, p ≤ n → n ≤ t → s*(n-p:ℕ)/N-E ≤ m n-m p) :
    profileDrop m N s p t ≤ E := by
  obtain ⟨i,hpi,hit,hmin⟩ := PlanarFalconer.intervalMin_attained
    (fun n : ℕ => m n-s*(n:ℝ)/N) hpt
  unfold profileDrop
  rw [hmin]
  have hh := hinc i hpi hit
  rw [Nat.cast_sub hpi] at hh
  have he : s*((i:ℝ)-(p:ℝ))/N = s*(i:ℝ)/N-s*(p:ℝ)/N := by ring
  rw [he] at hh
  linarith

theorem sourceClass_conditional_frostman_of_increment (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) :
    ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^(t-p) ≤ r → r ≤ 1 →
      (Measure.map (cellScaleMap p (Q.descendant P).center)
        (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)) (ball x r) ≤
      ENNReal.ofReal ((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
        ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam)*r^s) := by
  intro x r hr hr1
  apply (sourceClass_conditional_frostman Q hQ μ hN hB hs hwidth hlarge hp₀ hpt htN hP hPpos x r hr hr1).trans
  apply ENNReal.ofReal_le_ofReal
  have hr0 : 0 ≤ r := (show 0 ≤ 1/(2:ℝ)^(t-p) by positivity).trans hr
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr0 s)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  exact add_le_add (profileDrop_le_of_increment _ N s E hpt hinc) le_rfl

end Falconer.Regularization

end OAI

end ExtensionScope143

/- Source: OAI.MeasureTheory.Falconer.Geometry.CellNormalization. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope144




namespace OAI

/-! # The actual cell normalization used by the middle radial interval -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem cell_normalization_map (ρ : Measure (Space d)) (p : ℕ) (c : Space d)
    {b : ℝ} (hb : 0 < b) :
    Measure.map (radialZoom (b*(2:ℝ)^p) (by positivity) c) ρ =
      Measure.map (radialZoom b hb.ne' 0) (Measure.map (cellScaleMap p c) ρ) := by
  rw [Measure.map_map (radialZoom b hb.ne' 0).measurable (cellScaleMap_continuous p c).measurable]
  congr 1
  ext x
  simp only [Function.comp_apply,radialZoom_apply,cellScaleMap,sub_zero,smul_smul]

theorem cell_normalization_support (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) (P : CellPath d) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ z ∂Measure.map (radialZoom (b*(2:ℝ)^P.length) (by positivity) (Q.descendant P).center)
      (ProbabilityTheory.cond ρ (Q.descendant P).carrier), ‖z‖ ≤ b*Real.sqrt d := by
  rw [cell_normalization_map _ _ _ hb]
  apply radialZoom_ae_bound _ hb 0
  simpa only [sub_zero] using rescaled_conditional_support Q hQ ρ P

theorem cell_normalization_quarter_point (Q : DyadicCube d) (hQ : Q.side = 1)
    (P : CellPath d) {b : ℝ} (hb : 0 < b) (hsmall : b*Real.sqrt d ≤ 1/4)
    {z : Space d} (hz : z ∈ (Q.descendant P).carrier) :
    ‖z-(Q.descendant P).center‖ ≤ 1/(4*(b*(2:ℝ)^P.length)) := by
  have hh := rescaled_cell_norm_bound Q hQ P hz
  rw [cellScaleMap,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (2:ℝ)^P.length)] at hh
  have hm := (mul_le_mul_of_nonneg_left hh hb.le).trans hsmall
  apply (le_div_iff₀ (by positivity : 0 < 4*(b*(2:ℝ)^P.length))).mpr
  nlinarith

theorem conditional_frostman_coefficient_ge_one (d N : ℕ) {s E lam : ℝ}
    (hs : 0 ≤ s) (hE : 0 ≤ E) (hlam : 0 ≤ lam) :
    1 ≤ (((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
      ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam) := by
  have hdim : (1:ℝ) ≤ (((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ) := by
    exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ 2*Nat.ceil (2+4*Real.sqrt d)+1) :
      1 ≤ (2*Nat.ceil (2+4*Real.sqrt d)+1)^d)
  have htwo : 1 ≤ (2:ℝ)^s := Real.one_le_rpow (by norm_num) hs
  have hR : 1 ≤ ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam) :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hdim htwo) hR

theorem sourceClass_normalized_conditional_frostman (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E b : ℝ} (hs : 0 ≤ s) (hE : 0 ≤ E) (hlam : 0 ≤ lam)
    (hb : 0 < b) (hb1 : b ≤ 1) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) :
    ∀ x : Space d, ∀ r : ℝ, 0 < r → 1/(2:ℝ)^(t-p) ≤ r →
      Measure.map (radialZoom (b*(2:ℝ)^p) (by positivity) (Q.descendant P).center)
        (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)
        (Metric.ball x r) ≤
      ENNReal.ofReal (((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
        ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam))*b^(-s)*r^s) := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have : IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀)
      (Q.descendant P).carrier) := sourceClass_conditional_probability Q hside μ N B hp₀ P hPpos
  intro x r hr hδ
  rw [cell_normalization_map _ _ _ hb]
  apply radialZoom_frostman_bound _ hb hb1
    (conditional_frostman_coefficient_ge_one d N hs hE hlam) hs (by simp) 0
    (sourceClass_conditional_frostman_of_increment Q hQ μ hN hB hs hwidth hlarge
      hp₀ hpt htN hP hPpos hinc) x r hr hδ

theorem sourceClass_scaled_dyadic_ball (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E b K : ℝ} (hs : 0 ≤ s) (hE : 0 ≤ E) (hlam : 0 ≤ lam)
    (hb : 0 < b) (hb1 : b ≤ 1) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t M : ℕ} (hpt : p ≤ t) (htN : t ≤ N) (hM : M ≤ t-p)
    {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p)
    (hcoef : (((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
      ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam))*b^(-s)) ≤ K) :
    ∀ x : Space d, ∀ j : ℕ, j ≤ M →
      ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier
        (Metric.ball x ((1/(2:ℝ)^j)/(b*(2:ℝ)^p))) ≤
          ENNReal.ofReal (K*(1/(2:ℝ)^j)^s) := by
  intro x j hj
  have ha : 0 < b*(2:ℝ)^p := by positivity
  have hr : 1/(2:ℝ)^(t-p) ≤ 1/(2:ℝ)^j :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (hj.trans hM))
  have hh := sourceClass_normalized_conditional_frostman Q hQ μ hN hB hs hE hlam hb hb1
    hwidth hlarge hp₀ hpt htN hP hPpos hinc
    (radialZoom (b*(2:ℝ)^p) ha.ne' (Q.descendant P).center x)
    (1/(2:ℝ)^j) (by positivity) hr
  rw [radialZoom_ball_apply _ ha] at hh
  have hc : (Q.descendant P).center+(b*(2:ℝ)^p)⁻¹ •
      radialZoom (b*(2:ℝ)^p) ha.ne' (Q.descendant P).center x = x := by
    simp only [radialZoom_apply,smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
    abel
  rw [hc] at hh
  apply hh.trans
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoef (by positivity))

end Falconer.Regularization

end OAI

end ExtensionScope144

/- Source: OAI.MeasureTheory.Falconer.Estimates.SourceClassMiddleData. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope145


namespace OAI

/-! # Actual conditional source data for either middle-interval angular theorem -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem source_class_middle_data (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E b K : ℝ} (hs : 0 ≤ s) (hE : 0 ≤ E) (hlam : 0 ≤ lam)
    (hb : 0 < b) (hb1 : b ≤ 1) (hsmall : b*Real.sqrt d ≤ 1/4)
    (hwidth : (B:ℝ) ≤ lam*(N:ℝ)) (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t M : ℕ} (hpt : p ≤ t) (htN : t ≤ N) (hM : M ≤ t-p)
    {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p)
    (hcoef : (((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
      ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam))*b^(-s)) ≤ K) :
    (∀ z ∈ (Q.descendant P).carrier,
      ‖z-(Q.descendant P).center‖ ≤ 1/(4*(b*(2:ℝ)^p))) ∧
    (∀ᵐ z ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier,
      ‖z-(Q.descendant P).center‖ ≤ 1/(4*(b*(2:ℝ)^p))) ∧
    (∀ x : Space d, ∀ j : ℕ, j ≤ M →
      ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier
        (Metric.ball x ((1/(2:ℝ)^j)/(b*(2:ℝ)^p))) ≤
          ENNReal.ofReal (K*(1/(2:ℝ)^j)^s)) := by
  have hpoint : ∀ z ∈ (Q.descendant P).carrier,
      ‖z-(Q.descendant P).center‖ ≤ 1/(4*(b*(2:ℝ)^p)) := by
    intro z hz
    simpa only [hP] using cell_normalization_quarter_point Q hQ P hb hsmall hz
  refine ⟨hpoint,ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable hpoint,?_⟩
  exact sourceClass_scaled_dyadic_ball Q hQ μ hN hB hs hE hlam hb hb1 hwidth hlarge
    hp₀ hpt htN hM hP hPpos hinc hcoef

end Falconer.Regularization

end OAI

end ExtensionScope145

/- Source: OAI.MeasureTheory.Falconer.Radial.NonendpointSourceMiddle. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope146



namespace OAI

/-! # The nonendpoint middle estimate for an actual regularized source cell -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem nonendpoint_source_class_middle_pruning (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
    (hqt : q < t) (ht : t-(h:ℝ) < 1) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀,
      ∀ (Q : DyadicCube (h+2)), Q.side = 1 →
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsFiniteMeasure ν],
      ν univ ≤ 1 → ∀ N B : ℕ, 0 < N → 0 < B →
      ∀ lam E σ : ℝ, 0 ≤ E → 0 ≤ lam → 0 < σ → σ ≤ 1 → σ*Real.sqrt (h+2:ℕ) ≤ 1/4 →
      (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ p v : ℕ, p ≤ v → v ≤ N → M ≤ v-p →
      ∀ P : CellPath (h+2), P.length = p →
      0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier →
      (∀ n, p ≤ n → n ≤ v →
        t*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) →
      (((((2*Nat.ceil (2+4*Real.sqrt (h+2:ℕ))+1)^(h+2):ℕ):ℝ)*(2:ℝ)^t*
        ((2:ℝ)^N)^(E+2*(((h+2:ℕ):ℝ)+1)*lam))*σ^(-t)) ≤ (1/(2:ℝ)^M)^(-ε) →
      ∀ (_w₀ : Sphere (h+2)) (G : Set (Space (h+2) × Space (h+2))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ z ∈ (Q.descendant P).carrier) →
      (∀ᵐ z ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier,
        ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ M →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^M)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/((σ*(2:ℝ)^p)*r) ≤ 1/(2:ℝ)^M →
      ((σ*(2:ℝ)^p)*H)*θ ≤ 1/(2:ℝ)^M →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖(Q.descendant P).center-x‖ ∧
        ∀ᵐ y ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        ((ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier).prod ν)
          (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^M)^b) ∧
        ∀ z ∈ G', radialCollisionMass
          (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier) θ z ≤
            ENNReal.ofReal ((1/(2:ℝ)^M)^(q+b/2)) := by
  obtain ⟨ε,b,hε,hb,M₀,hM₀⟩ := nonendpoint_original_middle_pruning hpublished hq hq' hqt ht
  refine ⟨ε,b,hε,hb,M₀,?_⟩
  intro M hM Q hQ μ ν _ _ hν N B hN hB lam E σ hE hlam hσ hσ1 hsmall hwidth hlarge
    p₀ hp₀ p v hpv hvN hMv P hP hpos hinc hcoef w₀ G hG hgeom hcap r H θ hr hfreeze hwidth' hpin
  have ht0 : 0 ≤ t := by have hh : (0:ℝ) ≤ h := Nat.cast_nonneg h; linarith
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have : IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀)
      (Q.descendant P).carrier) := sourceClass_conditional_probability Q hside μ N B hp₀ P hpos
  have hdata := source_class_middle_data Q hQ μ hN hB ht0 hE hlam hσ hσ1 hsmall hwidth hlarge
    hp₀ hpv hvN hMv hP hpos hinc hcoef
  exact hM₀ M hM _ ν hν w₀ (Q.descendant P).center (σ*(2:ℝ)^p) (by positivity) G hG
    (fun z x hz => ⟨(hgeom z x hz).1,hdata.1 z (hgeom z x hz).2⟩)
    hdata.2.1 hdata.2.2 hcap r H θ hr hfreeze hwidth' hpin

end Falconer.Regularization

end OAI

end ExtensionScope146

/- Source: OAI.MeasureTheory.Falconer.Radial.ReverseRadialMass. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope147


namespace OAI

/-! # Original reverse cap bounds control radial collision pins -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem reverse_radial_collision_mass (ν : Measure (Space n))
    (G : Set (Space n × Space n)) (z y : Space n) (hy : y ≠ z)
    (hdiag : ∀ x, (z,x) ∈ G → x ≠ z) {D δ K q : ℝ}
    (hD : 0 < D) (hδ : 0 < δ)
    (hbound : ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D)
    (hcap : ∀ u : Space n, ‖u‖ = 1 →
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < 3*(D*δ/‖y-z‖)} ≤
        ENNReal.ofReal (K*(3*(D*δ/‖y-z‖))^q)) :
    ν {x | (z,x) ∈ G ∧ dist (normalize (y-x)) (normalize (z-x)) ≤ δ} ≤
      2*ENNReal.ofReal (K*(3*(D*δ/‖y-z‖))^q) := by
  have hr : 0 < D*δ/‖y-z‖ := div_pos (mul_pos hD hδ)
    (norm_pos_iff.mpr (sub_ne_zero.mpr hy))
  apply (measure_mono (show
    {x | (z,x) ∈ G ∧ dist (normalize (y-x)) (normalize (z-x)) ≤ δ} ⊆
      {x | (z,x) ∈ G ∧ displacementAngle z y x ≤ D*δ/‖y-z‖} from ?_)).trans
    (radial_angle_sublevel ν G z y hy hdiag hr hcap)
  rintro x ⟨hx,hclose⟩
  exact ⟨hx,reverse_radial_collision_angle x z y (Ne.symm (hdiag x hx)) hy (hbound x hx) hclose⟩

end Falconer

end OAI

end ExtensionScope147

/- Source: OAI.MeasureTheory.Falconer.Radial.ReverseRadialTruncation. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope148


namespace OAI

/-! # A truncated-kernel bound for the mass of original collision pins -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem reverse_radial_collision_truncated (ν : Measure (Space n))
    (G : Set (Space n × Space n)) (z y : Space n)
    (hdiag : ∀ x, (z,x) ∈ G → x ≠ z) {D δ K q : ℝ}
    (hD : 1 ≤ D) (hδ : 0 < δ) (hK : 1 ≤ K) (hq : 0 ≤ q)
    (hmass : ν univ ≤ 1) (hyz : ‖y-z‖ ≤ 1)
    (hbound : ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D)
    (hcap : ∀ r : ℝ, δ ≤ r → ∀ u : Space n, ‖u‖ = 1 →
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
        ENNReal.ofReal (K*r^q)) :
    ν {x | (z,x) ∈ G ∧ dist (normalize (y-x)) (normalize (z-x)) ≤ δ} ≤
      ENNReal.ofReal ((2*K*(3*D)^q)*(δ/max ‖y-z‖ δ)^q) := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  by_cases hnear : ‖y-z‖ ≤ δ
  · rw [max_eq_right hnear,div_self hδ.ne',Real.one_rpow,mul_one]
    have hp : 1 ≤ (3*D)^q := Real.one_le_rpow (by linarith) hq
    have hL : 1 ≤ 2*K*(3*D)^q := by nlinarith
    exact ((measure_mono (subset_univ _)).trans hmass).trans
      (by simpa using ENNReal.ofReal_le_ofReal hL)
  · have hr : δ < ‖y-z‖ := lt_of_not_ge hnear
    have hr0 : 0 < ‖y-z‖ := hδ.trans hr
    have hy : y ≠ z := sub_ne_zero.mp (norm_pos_iff.mp hr0)
    have hrange : δ ≤ 3*(D*δ/‖y-z‖) := by
      rw [show 3*(D*δ/‖y-z‖) = 3*D*δ/‖y-z‖ by ring]
      apply (le_div_iff₀ hr0).mpr
      nlinarith
    have hh := reverse_radial_collision_mass ν G z y hy hdiag hD0 hδ hbound
      (fun u hu => hcap (3*(D*δ/‖y-z‖)) hrange u hu)
    apply hh.trans_eq
    rw [max_eq_left hr.le]
    rw [show 3*(D*δ/‖y-z‖) = (3*D)*(δ/‖y-z‖) by ring,
      Real.mul_rpow (by positivity) (by positivity)]
    conv_lhs =>
      lhs
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num]
    rw [← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring

end Falconer

end OAI

end ExtensionScope148

/- Source: OAI.MeasureTheory.Falconer.Radial.RadialCollisionMean. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope149




namespace OAI

/-! # Original-pin radial collision means on a profile interval

The comparison source is the full conditional source law. The reverse pin
law remains a restriction of the original pin measure; no fiber is normalized.
-/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radial_collision_mean_bound (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (z : Space d) {D Kν Kμ q : ℝ} (hD : 1 ≤ D) (hKν : 1 ≤ Kν) (hq : 0 ≤ q)
    (hmass : ν univ ≤ 1) (g k : ℕ)
    (hdiag : ∀ x, (z,x) ∈ G → x ≠ z)
    (hsource : ∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧
      ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D)
    (hball : ∀ j : ℕ, j ≤ g+k →
      μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (Kμ*(1/(2:ℝ)^j)^q))
    (hcap : ∀ r : ℝ, 1/(2:ℝ)^(g+k) ≤ r → ∀ u : Space d, ‖u‖ = 1 →
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (Kν*r^q)) :
    (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ (1/(2:ℝ)^(g+k)) (z,x) ∂ν) ≤
      ENNReal.ofReal (2*Kν*(3*D)^q*(1/(2:ℝ)^(g+k))^q)*
        (ENNReal.ofReal ((2:ℝ)^q)*
          (ENNReal.ofReal Kμ+(k:ℝ≥0∞)*ENNReal.ofReal (Kμ*(2:ℝ)^q))) := by
  let δ : ℝ := 1/(2:ℝ)^(g+k)
  let L : ℝ := 2*Kν*(3*D)^q
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hK0 : 0 < Kν := lt_of_lt_of_le zero_lt_one hKν
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hS : μ.restrict {y | ‖y-z‖ < 1/(2:ℝ)^g} = μ :=
    Measure.restrict_eq_self_of_ae_mem (hsource.mono fun _ h => h.1)
  have hp : ∀ᵐ y ∂μ,
      ν {x | (z,x) ∈ G ∧ dist (normalize (y-x)) (normalize (z-x)) ≤ δ} ≤
        ENNReal.ofReal (L*δ^q)*ENNReal.ofReal ((1/max ‖y-z‖ δ)^q) := by
    filter_upwards [hsource] with y hy
    have hy1 : ‖y-z‖ ≤ 1 := hy.1.le.trans (by
      apply (div_le_one (by positivity)).mpr
      exact one_le_pow₀ (by norm_num))
    have hh := reverse_radial_collision_truncated ν G z y hdiag hD hδ hKν hq hmass hy1 hy.2 hcap
    apply hh.trans_eq
    change ENNReal.ofReal (L*(δ/max ‖y-z‖ δ)^q) = _
    rw [show δ/max ‖y-z‖ δ = δ*(1/max ‖y-z‖ δ) by ring,
      Real.mul_rpow hδ.le (by positivity)]
    rw [← ENNReal.ofReal_mul (mul_nonneg hL (Real.rpow_nonneg hδ.le _))]
    congr 1
    ring
  rw [radial_collision_original_pin_fubini μ ν G hG z]
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (L*δ^q)*ENNReal.ofReal ((1/max ‖y-z‖ δ)^q) ∂μ :=
      lintegral_mono_ae hp
    _ = ENNReal.ofReal (L*δ^q)*(∫⁻ y in {y | ‖y-z‖ < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/max ‖y-z‖ δ)^q) ∂μ) := by
      rw [hS,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := mul_le_mul' le_rfl
      (truncated_scalar_potential_critical μ (fun y => ‖y-z‖) (by fun_prop)
        (fun _ => norm_nonneg _) hq g k hball)

end Falconer

end OAI

end ExtensionScope149

/- Source: OAI.MeasureTheory.Falconer.Radial.RadialMeanPowers. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope150



namespace OAI

/-! # The logarithmic radial mean loss is absorbed by a small scale power -/

namespace Falconer

theorem dyadic_radial_power_cancel (g k : ℕ) (q : ℝ) :
    ((2:ℝ)^g)^q*(1/(2:ℝ)^(g+k))^q = ((2:ℝ)^k)^(-q) := by
  calc
    _ = (((2:ℝ)^g)*(1/(2:ℝ)^(g+k)))^q :=
      (Real.mul_rpow (by positivity) (by positivity)).symm
    _ = (1/(2:ℝ)^k)^q := by congr 1; rw [pow_add]; field_simp
    _ = _ := by rw [one_div,Real.inv_rpow (by positivity),Real.rpow_neg (by positivity)]

theorem eventually_radial_mean_coefficient {D η q : ℝ} (hD : 1 ≤ D) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g k : ℕ, k ≤ N →
      (2*((2:ℝ)^N)^η*(3*D)^q*(1/(2:ℝ)^(g+k))^q)*
        (2:ℝ)^q*(((2:ℝ)^N)^η*((2:ℝ)^g)^q+
          (k:ℝ)*(((2:ℝ)^N)^η*((2:ℝ)^g)^q*(2:ℝ)^q)) ≤
      ((2:ℝ)^N)^(3*η)*((2:ℝ)^k)^(-q) := by
  let B := 2*(3*D)^q*(2:ℝ)^q
  let C := B*(1+(2:ℝ)^q)
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨N₀,hN₀⟩ := PlanarFalconer.fixed_linear_subpower C hC hη
  refine ⟨N₀,fun N hN g k hk => ?_⟩
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hcoef : B*(1+(k:ℝ)*(2:ℝ)^q) ≤ R^η := by
    apply le_trans ?_ (hN₀ N hN)
    have hkn : (k:ℝ) ≤ N := by exact_mod_cast hk
    have hp : 0 ≤ (2:ℝ)^q := by positivity
    have hnum : 1+(k:ℝ)*(2:ℝ)^q ≤ (1+(2:ℝ)^q)*(1+2*(N:ℝ)) := by
      nlinarith [show (0:ℝ) ≤ N from Nat.cast_nonneg N]
    exact (mul_le_mul_of_nonneg_left hnum hB).trans_eq (by dsimp [C]; ring)
  calc
    _ = (B*(1+(k:ℝ)*(2:ℝ)^q))*(R^η*R^η)*
        (((2:ℝ)^g)^q*(1/(2:ℝ)^(g+k))^q) := by dsimp [B,R]; ring
    _ = (B*(1+(k:ℝ)*(2:ℝ)^q))*R^(2*η)*((2:ℝ)^k)^(-q) := by
      rw [dyadic_radial_power_cancel,← Real.rpow_add hR,show η+η = 2*η by ring]
    _ ≤ R^η*R^(2*η)*((2:ℝ)^k)^(-q) := by gcongr
    _ = _ := by
      rw [← Real.rpow_add hR,show η+2*η = 3*η by ring]

end Falconer

end OAI

end ExtensionScope150

/- Source: OAI.MeasureTheory.Falconer.Radial.RadialMeanPowerBound. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope151


namespace OAI

/-! # Uniform power form of the original-pin radial mean bound -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem ennreal_radial_mean_coefficient {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (k : ℕ) :
    ENNReal.ofReal a*(ENNReal.ofReal c*
      (ENNReal.ofReal b+(k:ℝ≥0∞)*ENNReal.ofReal (b*c))) =
        ENNReal.ofReal (a*c*(b+(k:ℝ)*(b*c))) := by
  have he : ENNReal.ofReal b+(k:ℝ≥0∞)*ENNReal.ofReal (b*c) =
      ENNReal.ofReal (b+(k:ℝ)*(b*c)) := by
    rw [ENNReal.ofReal_add hb (by positivity),
      ENNReal.ofReal_mul (Nat.cast_nonneg k),ENNReal.ofReal_natCast]
  rw [he,← ENNReal.ofReal_mul hc,← ENNReal.ofReal_mul ha]
  congr 1
  ring

theorem radial_cap_extend_large (ν : Measure (Space d)) (G : Set (Space d × Space d))
    (z : Space d) {δ K q : ℝ} (hK : 1 ≤ K) (hq : 0 ≤ q) (hmass : ν univ ≤ 1)
    (hcap : ∀ r : ℝ, δ ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K*r^q)) :
    ∀ r : ℝ, δ ≤ r → ∀ u : Space d, ‖u‖ = 1 →
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K*r^q) := by
  intro r hr u hu
  by_cases hr1 : r ≤ 1
  · exact hcap r hr hr1 u hu
  · have hr1' : 1 ≤ r := (lt_of_not_ge hr1).le
    have hp : 1 ≤ r^q := Real.one_le_rpow hr1' hq
    have hb : 1 ≤ K*r^q := by nlinarith
    exact ((measure_mono (subset_univ _)).trans hmass).trans
      (by simpa using ENNReal.ofReal_le_ofReal hb)

theorem eventually_radial_collision_mean {D η q : ℝ}
    (hD : 1 ≤ D) (hη : 0 < η) (hq : 0 ≤ q) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g k : ℕ, k ≤ N →
      ∀ (μ ν : Measure (Space d)) [SFinite μ] [SFinite ν],
      ∀ (G : Set (Space d × Space d)), MeasurableSet G → ∀ z : Space d,
      ν univ ≤ 1 → (∀ x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) →
      (∀ j : ℕ, j ≤ g+k → μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((((2:ℝ)^N)^η*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) →
      (∀ r : ℝ, 1/(2:ℝ)^(g+k) ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^η*r^q)) →
      (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ (1/(2:ℝ)^(g+k)) (z,x) ∂ν) ≤
        ENNReal.ofReal (((2:ℝ)^N)^(3*η)*((2:ℝ)^k)^(-q)) := by
  obtain ⟨N₀,hN₀⟩ := eventually_radial_mean_coefficient hD hη
  refine ⟨N₀,?_⟩
  intro N hN g k hk μ ν _ _ G hG z hmass hdiag hsource hball hcap
  have hK : 1 ≤ ((2:ℝ)^N)^η := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hη.le
  have hb := radial_collision_mean_bound μ ν G hG z hD hK hq hmass g k hdiag hsource hball
    (radial_cap_extend_large ν G z hK hq hmass hcap)
  apply hb.trans
  rw [ennreal_radial_mean_coefficient (by positivity) (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (hN₀ N hN g k hk)

end Falconer

end OAI

end ExtensionScope151

/- Source: OAI.MeasureTheory.Falconer.Radial.OuterRadialPruning. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope152



namespace OAI

/-! # Power-small original-pair deletion on an outer profile interval -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem outer_radial_interval_pruning {D η q : ℝ}
    (hD : 1 ≤ D) (hη : 0 < η) (hq : 0 ≤ q) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g k : ℕ, k ≤ N →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ,
        (∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) ∧
        (∀ j : ℕ, j ≤ g+k → μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((((2:ℝ)^N)^η*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) ∧
        (∀ r : ℝ, 1/(2:ℝ)^(g+k) ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
          ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^η*r^q))) →
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
        (μ.prod ν) (G \ H) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-η)) ∧
        ∀ p ∈ H, radialCollisionMass μ (1/(2:ℝ)^(g+k)) p ≤
          ENNReal.ofReal (((2:ℝ)^N)^(4*η)*((2:ℝ)^k)^(-q)) := by
  obtain ⟨N₀,hN₀⟩ := eventually_radial_collision_mean (d := d) hD hη hq
  refine ⟨N₀,?_⟩
  intro N hN g k hk μ ν _ _ G hG hdiag hdata
  let R : ℝ := (2:ℝ)^N
  let S : ℝ := ((2:ℝ)^k)^(-q)
  have hR : 0 < R := by dsimp [R]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hF : 0 < R^(4*η)*S := by positivity
  have hmean : ∀ᵐ z ∂μ,
      (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ (1/(2:ℝ)^(g+k)) (z,x) ∂ν) ≤
        ENNReal.ofReal (R^(3*η)*S) := by
    filter_upwards [hdata] with z hz
    exact hN₀ N hN g k hk μ ν G hG z (by simp) (hdiag z) hz.1 hz.2.1 hz.2.2
  obtain ⟨H,hH,hHG,hcost,hcap⟩ := radial_collision_pruning μ ν G hG
    (1/(2:ℝ)^(g+k)) (ENNReal.ofReal_pos.mpr hF).ne' ENNReal.ofReal_ne_top hmean
  refine ⟨H,hH,hHG,hcost.trans_eq ?_,hcap⟩
  rw [measure_univ,mul_one,← ENNReal.ofReal_div_of_pos hF]
  congr 1
  calc
    (R^(3*η)*S)/(R^(4*η)*S) = R^(3*η)/R^(4*η) := by
      exact mul_div_mul_right _ _ (ne_of_gt hS)
    _ = R^(3*η-4*η) := (Real.rpow_sub hR _ _).symm
    _ = R^(-η) := by congr 1; ring

end Falconer

end OAI

end ExtensionScope152

/- Source: OAI.MeasureTheory.Falconer.Radial.UniformOuterRadial. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope153


namespace OAI

/-! # A common outer-radial cutoff for all contact exponents above a fixed positive floor -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem eventually_radial_mean_coefficient_uniform {D η₀ q : ℝ} (hD : 1 ≤ D) (hη₀ : 0 < η₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η → ∀ g k : ℕ, k ≤ N →
      (2*((2:ℝ)^N)^η*(3*D)^q*(1/(2:ℝ)^(g+k))^q)*
        (2:ℝ)^q*(((2:ℝ)^N)^η*((2:ℝ)^g)^q+
          (k:ℝ)*(((2:ℝ)^N)^η*((2:ℝ)^g)^q*(2:ℝ)^q)) ≤
      ((2:ℝ)^N)^(3*η)*((2:ℝ)^k)^(-q) := by
  let B := 2*(3*D)^q*(2:ℝ)^q
  let C := B*(1+(2:ℝ)^q)
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨N₀,hN₀⟩ := PlanarFalconer.fixed_linear_subpower C hC hη₀
  refine ⟨N₀,fun N hN η hηge g k hk => ?_⟩
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hcoef : B*(1+(k:ℝ)*(2:ℝ)^q) ≤ R^η := by
    apply le_trans ?_ ((hN₀ N hN).trans (Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ (by norm_num)) hηge))
    have hkn : (k:ℝ) ≤ N := by exact_mod_cast hk
    have hp : 0 ≤ (2:ℝ)^q := by positivity
    have hnum : 1+(k:ℝ)*(2:ℝ)^q ≤ (1+(2:ℝ)^q)*(1+2*(N:ℝ)) := by
      nlinarith [show (0:ℝ) ≤ N from Nat.cast_nonneg N]
    exact (mul_le_mul_of_nonneg_left hnum hB).trans_eq (by dsimp [C]; ring)
  calc
    _ = (B*(1+(k:ℝ)*(2:ℝ)^q))*(R^η*R^η)*
        (((2:ℝ)^g)^q*(1/(2:ℝ)^(g+k))^q) := by dsimp [B,R]; ring
    _ = (B*(1+(k:ℝ)*(2:ℝ)^q))*R^(2*η)*((2:ℝ)^k)^(-q) := by
      rw [dyadic_radial_power_cancel,← Real.rpow_add hR,show η+η = 2*η by ring]
    _ ≤ R^η*R^(2*η)*((2:ℝ)^k)^(-q) := by gcongr
    _ = _ := by
      rw [← Real.rpow_add hR,show η+2*η = 3*η by ring]

theorem eventually_radial_collision_mean_uniform {D η₀ q : ℝ}
    (hD : 1 ≤ D) (hη₀ : 0 < η₀) (hq : 0 ≤ q) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η → ∀ g k : ℕ, k ≤ N →
      ∀ (μ ν : Measure (Space d)) [SFinite μ] [SFinite ν],
      ∀ (G : Set (Space d × Space d)), MeasurableSet G → ∀ z : Space d,
      ν univ ≤ 1 → (∀ x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) →
      (∀ j : ℕ, j ≤ g+k → μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((((2:ℝ)^N)^η*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) →
      (∀ r : ℝ, 1/(2:ℝ)^(g+k) ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^η*r^q)) →
      (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ (1/(2:ℝ)^(g+k)) (z,x) ∂ν) ≤
        ENNReal.ofReal (((2:ℝ)^N)^(3*η)*((2:ℝ)^k)^(-q)) := by
  obtain ⟨N₀,hN₀⟩ := eventually_radial_mean_coefficient_uniform hD hη₀
  refine ⟨N₀,?_⟩
  intro N hN η hηge g k hk μ ν _ _ G hG z hmass hdiag hsource hball hcap
  have hK : 1 ≤ ((2:ℝ)^N)^η := Real.one_le_rpow (one_le_pow₀ (by norm_num)) (hη₀.trans_le hηge).le
  have hb := radial_collision_mean_bound μ ν G hG z hD hK hq hmass g k hdiag hsource hball
    (radial_cap_extend_large ν G z hK hq hmass hcap)
  apply hb.trans
  rw [ennreal_radial_mean_coefficient (by positivity) (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (hN₀ N hN η hηge g k hk)

theorem outer_radial_interval_pruning_uniform {D η₀ q : ℝ}
    (hD : 1 ≤ D) (hη₀ : 0 < η₀) (hq : 0 ≤ q) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η → ∀ g k : ℕ, k ≤ N →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ,
        (∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) ∧
        (∀ j : ℕ, j ≤ g+k → μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((((2:ℝ)^N)^η*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) ∧
        (∀ r : ℝ, 1/(2:ℝ)^(g+k) ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
          ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^η*r^q))) →
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
        (μ.prod ν) (G \ H) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-η)) ∧
        ∀ p ∈ H, radialCollisionMass μ (1/(2:ℝ)^(g+k)) p ≤
          ENNReal.ofReal (((2:ℝ)^N)^(4*η)*((2:ℝ)^k)^(-q)) := by
  obtain ⟨N₀,hN₀⟩ := eventually_radial_collision_mean_uniform (d := d) hD hη₀ hq
  refine ⟨N₀,?_⟩
  intro N hN η hηge g k hk μ ν _ _ G hG hdiag hdata
  let R : ℝ := (2:ℝ)^N
  let S : ℝ := ((2:ℝ)^k)^(-q)
  have hR : 0 < R := by dsimp [R]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hF : 0 < R^(4*η)*S := by positivity
  have hmean : ∀ᵐ z ∂μ,
      (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ (1/(2:ℝ)^(g+k)) (z,x) ∂ν) ≤
        ENNReal.ofReal (R^(3*η)*S) := by
    filter_upwards [hdata] with z hz
    exact hN₀ N hN η hηge g k hk μ ν G hG z (by simp) (hdiag z) hz.1 hz.2.1 hz.2.2
  obtain ⟨H,hH,hHG,hcost,hcap⟩ := radial_collision_pruning μ ν G hG
    (1/(2:ℝ)^(g+k)) (ENNReal.ofReal_pos.mpr hF).ne' ENNReal.ofReal_ne_top hmean
  refine ⟨H,hH,hHG,hcost.trans_eq ?_,hcap⟩
  rw [measure_univ,mul_one,← ENNReal.ofReal_div_of_pos hF]
  congr 1
  calc
    (R^(3*η)*S)/(R^(4*η)*S) = R^(3*η)/R^(4*η) := by
      exact mul_div_mul_right _ _ (ne_of_gt hS)
    _ = R^(3*η-4*η) := (Real.rpow_sub hR _ _).symm
    _ = R^(-η) := by congr 1; ring

end Falconer

end OAI

end ExtensionScope153

/- Source: OAI.MeasureTheory.Falconer.Radial.RadialCollisionWidths. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope154



namespace OAI

/-! # Fixed-width radial collision tests at nearby dyadic depths -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radialCollisionMass_mono (μ : Measure (Space d)) (p : Space d × Space d)
    {δ δ' : ℝ} (h : δ ≤ δ') : radialCollisionMass μ δ p ≤ radialCollisionMass μ δ' p :=
  measure_mono (fun _ hy => hy.trans h)

theorem dyadic_width_rounding (C : ℝ) :
    ∃ J : ℕ, ∀ n : ℕ, J ≤ n → C/(2:ℝ)^n ≤ 1/(2:ℝ)^(n-J) := by
  obtain ⟨J,hJ⟩ := Regularization.fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) C
  have hC : C ≤ (2:ℝ)^J := by simpa only [Real.rpow_one] using hJ J le_rfl
  refine ⟨J,fun n hn => ?_⟩
  have he : 1/(2:ℝ)^(n-J) = (2:ℝ)^J/(2:ℝ)^n := by
    conv_rhs => rw [show n = J+(n-J) by omega,pow_add]
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_right hC (by positivity)

theorem radialCollisionMass_fixed_width (μ : Measure (Space d)) (C : ℝ) :
    ∃ J : ℕ, ∀ n : ℕ, J ≤ n → ∀ p : Space d × Space d,
      radialCollisionMass μ (C/(2:ℝ)^n) p ≤ radialCollisionMass μ (1/(2:ℝ)^(n-J)) p := by
  obtain ⟨J,hJ⟩ := dyadic_width_rounding C
  exact ⟨J,fun n hn p => radialCollisionMass_mono μ p (hJ n hn)⟩

end Falconer

end OAI

end ExtensionScope154

/- Source: OAI.MeasureTheory.Falconer.Radial.OuterRadialWidths. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope155



namespace OAI

/-! # Outer-interval pruning with the fixed widths used by the cell multiplication lemma -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem dyadic_shifted_decay {g v J : ℕ} (h : g+J ≤ v) (q : ℝ) :
    ((2:ℝ)^((v-J)-g))^(-q) = ((2:ℝ)^J)^q*((2:ℝ)^(v-g))^(-q) := by
  have he : v-g = J+((v-J)-g) := by omega
  conv_rhs => rw [he,pow_add]
  rw [Real.mul_rpow (by positivity) (by positivity),Real.rpow_neg (by positivity)]
  rw [← mul_assoc,← Real.rpow_add (by positivity),add_neg_cancel,Real.rpow_zero,one_mul]

theorem outer_radial_interval_fixed_width {D η₀ q : ℝ}
    (hD : 1 ≤ D) (hη₀ : 0 < η₀) (hq : 0 ≤ q) (C : ℝ) :
    ∃ J N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η →
      ∀ g v : ℕ, g+J ≤ v → v ≤ N →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ,
        (∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) ∧
        (∀ j : ℕ, j ≤ v → μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((((2:ℝ)^N)^η*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) ∧
        (∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
          ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^η*r^q))) →
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
        (μ.prod ν) (G \ H) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-η)) ∧
        ∀ p ∈ H, radialCollisionMass μ (C/(2:ℝ)^v) p ≤
          ENNReal.ofReal (((2:ℝ)^N)^(5*η)*((2:ℝ)^(v-g))^(-q)) := by
  obtain ⟨J,hJ⟩ := dyadic_width_rounding C
  obtain ⟨N₁,hN₁⟩ := outer_radial_interval_pruning_uniform (d := d) hD hη₀ hq
  obtain ⟨N₂,hN₂⟩ := Regularization.fixed_constant_absorbed hη₀ (((2:ℝ)^J)^q)
  refine ⟨J,max N₁ N₂,?_⟩
  intro N hN η hη g v hgv hvN μ ν _ _ G hG hdiag hdata
  have hJv : J ≤ v := by omega
  have hg : g ≤ v-J := by omega
  have he : g+((v-J)-g) = v-J := Nat.add_sub_of_le hg
  have hr : 1/(2:ℝ)^v ≤ 1/(2:ℝ)^(v-J) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hdata' : ∀ᵐ z ∂μ,
      (∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) ∧
      (∀ j : ℕ, j ≤ g+((v-J)-g) → μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((((2:ℝ)^N)^η*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) ∧
      (∀ r : ℝ, 1/(2:ℝ)^(g+((v-J)-g)) ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^η*r^q)) := by
    filter_upwards [hdata] with z hz
    refine ⟨hz.1,fun j hj => hz.2.1 j (by omega),?_⟩
    intro r hrr hr1 u hu
    rw [he] at hrr
    exact hz.2.2 r (hr.trans hrr) hr1 u hu
  obtain ⟨H,hH,hHG,hdel,hbound⟩ := hN₁ N ((le_max_left _ _).trans hN) η hη g
    ((v-J)-g) (by omega) μ ν G hG hdiag hdata'
  refine ⟨H,hH,hHG,hdel,fun p hp => ?_⟩
  apply (radialCollisionMass_mono μ p (hJ v hJv)).trans
  rw [← he]
  apply (hbound p hp).trans
  apply ENNReal.ofReal_le_ofReal
  rw [dyadic_shifted_decay hgv]
  have hconst : ((2:ℝ)^J)^q ≤ ((2:ℝ)^N)^η :=
    (hN₂ N ((le_max_right _ _).trans hN)).trans
      (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hη)
  calc
    _ = (((2:ℝ)^N)^(4*η)*((2:ℝ)^J)^q)*((2:ℝ)^(v-g))^(-q) := by ring
    _ ≤ (((2:ℝ)^N)^(4*η)*((2:ℝ)^N)^η)*((2:ℝ)^(v-g))^(-q) := by gcongr
    _ = _ := by rw [← Real.rpow_add (by positivity),show 4*η+η = 5*η by ring]

end Falconer

end OAI

end ExtensionScope155

/- Source: OAI.MeasureTheory.Falconer.Radial.OuterRadialCell. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope156




namespace OAI

/-! # Outer radial pruning for a full conditional law in an original source cell -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem outer_radial_cell_pruning {D η₀ q : ℝ}
    (hD : 1 ≤ D) (hη₀ : 0 < η₀) (hq : 0 ≤ q) (C : ℝ) :
    ∃ J N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η →
      ∀ g v : ℕ, g+J ≤ v → v ≤ N →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ, ∀ᵐ y ∂μ,
        ‖y-z‖ ≤ D/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) →
      (∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1/(2:ℝ)^g →
        μ (Metric.ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^η*((2:ℝ)^g*r)^q)) →
      (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^η*r^q)) →
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
        (μ.prod ν) (G \ H) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-(2*η))) ∧
        ∀ p ∈ H, radialCollisionMass μ (C/(2:ℝ)^v) p ≤
          ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^(v-g))^(-q)) := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  let a : ℝ := 1/(2*D)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; apply (div_le_one (by positivity)).mpr; linarith
  have haD : a*D = 1/2 := by dsimp [a]; field_simp
  let e := radialZoom a ha.ne' (0 : Space d)
  obtain ⟨J,N₁,hN₁⟩ := outer_radial_interval_fixed_width (d := d)
    (by norm_num : (1:ℝ) ≤ 1) (mul_pos (by norm_num : (0:ℝ) < 2) hη₀) hq C
  obtain ⟨N₂,hN₂⟩ := Regularization.fixed_constant_absorbed hη₀ (a^(-q))
  refine ⟨J,max N₁ N₂,?_⟩
  intro N hN η hη g v hgv hvN μ ν _ _ G hG hdiag hgeom hball hcap
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hη0 : 0 < η := hη₀.trans_le hη
  have hK : 1 ≤ R^η := Real.one_le_rpow hR1 hη0.le
  have hcoeff : a^(-q) ≤ R^η :=
    (hN₂ N ((le_max_right _ _).trans hN)).trans
      (Real.rpow_le_rpow_of_exponent_le hR1 hη)
  have hcoeff' : R^η*a^(-q) ≤ R^(2*η) := by
    calc
      _ ≤ R^η*R^η := mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring
  have hballs := radialZoom_scaled_ball_bound μ ha ha1 hK
    (by positivity : 0 < (2:ℝ)^g) hq (by simp) (0 : Space d) hball
  have hdata : ∀ᵐ z ∂Measure.map e μ,
      (∀ᵐ y ∂Measure.map e μ, ‖y-z‖ < 1/(2:ℝ)^g ∧
        ∀ x, (z,x) ∈ zoomPairSet e G → ‖y-x‖ ≤ 1) ∧
      (∀ j : ℕ, j ≤ v → Measure.map e μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((R^(2*η)*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) ∧
      (∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        Measure.map e ν {x | (z,x) ∈ zoomPairSet e G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (R^(2*η)*r^q)) := by
    rw [radialZoom_ae_iff μ ha]
    filter_upwards [hgeom,hcap] with z hz hc
    refine ⟨?_,?_,?_⟩
    · rw [radialZoom_ae_iff μ ha]
      filter_upwards [hz] with y hy
      constructor
      · rw [norm_radialZoom_sub ha]
        calc
          _ ≤ a*(D/(2:ℝ)^g) := mul_le_mul_of_nonneg_left hy.1 ha.le
          _ = (1/2:ℝ)/(2:ℝ)^g := by rw [← mul_div_assoc,haD]
          _ < _ := div_lt_div_of_pos_right (by norm_num) (by positivity)
      · intro x hx
        let x₀ := e.symm x
        have hx' : (e.symm (e z),e.symm x) ∈ G := hx
        have hx₀ : (z,x₀) ∈ G := by simpa only [e.symm_apply_apply] using hx'
        have hxx : e x₀ = x := e.apply_symm_apply x
        rw [← hxx]
        change ‖radialZoom a ha.ne' 0 y-radialZoom a ha.ne' 0 x₀‖ ≤ _
        rw [norm_radialZoom_sub ha]
        exact (mul_le_mul_of_nonneg_left (hy.2 x₀ hx₀) ha.le).trans (by rw [haD]; norm_num)
    · intro j hj
      have hrj : 1/(2:ℝ)^v ≤ 1/(2:ℝ)^j :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hj)
      have hb := hballs (e z) (1/(2:ℝ)^j) (by positivity) hrj
      change Measure.map e μ (Metric.ball (e z) (1/(2:ℝ)^j)) ≤ _
      apply hb.trans
      apply ENNReal.ofReal_le_ofReal
      rw [Real.mul_rpow (by positivity) (by positivity)]
      calc
        _ = (R^η*a^(-q))*(((2:ℝ)^g)^q*(1/(2:ℝ)^j)^q) := by ring
        _ ≤ R^(2*η)*(((2:ℝ)^g)^q*(1/(2:ℝ)^j)^q) :=
          mul_le_mul_of_nonneg_right hcoeff' (by positivity)
        _ = _ := by ring
    · intro r hr hr1 u hu
      rw [radialZoom_reverse_cap ν ha _ z u r G hG]
      apply (hc r hr hr1 u hu).trans
      apply ENNReal.ofReal_le_ofReal
      have hr0 : 0 ≤ r := (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^v).trans hr
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)) (Real.rpow_nonneg hr0 q)
  have hdiag' : ∀ z x, (z,x) ∈ zoomPairSet e G → x ≠ z := by
    intro z x hx heq
    have hh := hdiag (e.symm z) (e.symm x) hx
    exact hh (congrArg e.symm heq)
  obtain ⟨H,hH,hHG,hdel,hbound⟩ := hN₁ N ((le_max_left _ _).trans hN) (2*η)
    (by linarith) g v hgv hvN (Measure.map e μ) (Measure.map e ν) (zoomPairSet e G)
    (zoomPairSet_measurable e hG) hdiag' hdata
  have hbound' : ∀ p ∈ H, radialCollisionMass (Measure.map e μ) (C/(2:ℝ)^v) p ≤
      ENNReal.ofReal (R^(10*η)*((2:ℝ)^(v-g))^(-q)) := by
    intro p hp
    simpa only [show 5*(2*η) = 10*η by ring] using hbound p hp
  exact radial_pruning_unzoom μ ν ha 0 G hG H hH hHG _ _ _ hdel hbound'

end Falconer

end OAI

end ExtensionScope156

/- Source: OAI.MeasureTheory.Falconer.Measures.OriginalConditionalFrostman. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope157


namespace OAI

/-! # Conditional source-ball estimates before changing the original coordinates -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem sourceClass_original_conditional_frostman (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) :
    ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^t ≤ r → r ≤ 1/(2:ℝ)^p →
      ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier (ball x r) ≤
      ENNReal.ofReal ((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
        ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam)*((2:ℝ)^p*r)^s) := by
  intro x r hr hr1
  have hpow : 0 < (2:ℝ)^p := by positivity
  have hscale : (2:ℝ)^p*(1/(2:ℝ)^t) = 1/(2:ℝ)^(t-p) := by
    conv_lhs => rw [show t = p+(t-p) by omega,pow_add]
    field_simp
  have hlo : 1/(2:ℝ)^(t-p) ≤ (2:ℝ)^p*r := by
    rw [← hscale]
    exact mul_le_mul_of_nonneg_left hr hpow.le
  have hhi : (2:ℝ)^p*r ≤ 1 := by
    calc
      _ ≤ (2:ℝ)^p*(1/(2:ℝ)^p) := mul_le_mul_of_nonneg_left hr1 hpow.le
      _ = 1 := by field_simp
  have hh := sourceClass_conditional_frostman_of_increment Q hQ μ hN hB hs hwidth hlarge
    hp₀ hpt htN hP hPpos hinc (cellScaleMap p (Q.descendant P).center x) ((2:ℝ)^p*r) hlo hhi
  rw [rescaled_conditional_ball_apply] at hh
  have hc : (Q.descendant P).center+((2:ℝ)^p)⁻¹ • cellScaleMap p (Q.descendant P).center x = x := by
    simp only [cellScaleMap,smul_smul,inv_mul_cancel₀ hpow.ne',one_smul]
    abel
  have hrad : ((2:ℝ)^p*r)/(2:ℝ)^p = r := by field_simp
  rwa [hc,hrad] at hh

theorem sourceClass_original_conditional_frostman_power (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E η : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p)
    (hcoef : (((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
      ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam) ≤ ((2:ℝ)^N)^η) :
    ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^t ≤ r → r ≤ 1/(2:ℝ)^p →
      ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier (ball x r) ≤
        ENNReal.ofReal (((2:ℝ)^N)^η*((2:ℝ)^p*r)^s) := by
  intro x r hr hr1
  apply (sourceClass_original_conditional_frostman Q hQ μ hN hB hs hwidth hlarge hp₀
    hpt htN hP hPpos hinc x r hr hr1).trans
  apply ENNReal.ofReal_le_ofReal
  have hr0 : 0 ≤ r := (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^t).trans hr
  exact mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (by positivity) _)

end Falconer.Regularization

end OAI

end ExtensionScope157

/- Source: OAI.MeasureTheory.Falconer.Geometry.ConditionalCellGeometry. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope158


namespace OAI

/-! # Original conditional laws stay within the actual dyadic cell diameter -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem conditional_cell_pair_geometry (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) (P : CellPath d) {g : ℕ} (hP : P.length = g)
    {D : ℝ} (hD : Real.sqrt d ≤ D)
    (G : Set (Space d × Space d))
    (hpin : ∀ z x, (z,x) ∈ G → ∀ y ∈ (Q.descendant P).carrier, ‖y-x‖ ≤ D) :
    ∀ᵐ z ∂ProbabilityTheory.cond ρ (Q.descendant P).carrier,
      ∀ᵐ y ∂ProbabilityTheory.cond ρ (Q.descendant P).carrier,
        ‖y-z‖ ≤ D/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D := by
  apply ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable
  intro z hz
  apply ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable
  intro y hy
  refine ⟨?_,fun x hx => hpin z x hx y hy⟩
  have hside : 0 ≤ (Q.descendant P).side := by rw [Q.descendant_side,hQ]; positivity
  have hh := (Q.descendant P).dist_le hside hy hz
  rw [dist_eq_norm,Q.descendant_side,hQ,hP] at hh
  apply hh.trans
  simpa only [mul_one_div] using div_le_div_of_nonneg_right hD
    (by positivity : (0:ℝ) ≤ 2^g)

end Falconer.Regularization

end OAI

end ExtensionScope158

/- Source: OAI.MeasureTheory.Falconer.Radial.SourceClassOuterRadial. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope159



namespace OAI

/-! # Outer-interval pruning for the actual regularized conditional source laws -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem source_class_outer_radial_pruning (Q : DyadicCube d) (hQ : Q.side = 1)
    {D η₀ q : ℝ} (hD : 1 ≤ D) (hDdim : Real.sqrt d ≤ D)
    (hη₀ : 0 < η₀) (hq : 0 ≤ q) (C : ℝ) :
    ∃ J N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η →
      ∀ g v : ℕ, g+J ≤ v → v ≤ N →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ B : ℕ, 0 < N → 0 < B → ∀ lam E : ℝ,
      (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ P : CellPath d, P.length = g →
      0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier →
      (∀ n, g ≤ n → n ≤ v →
        q*(n-g:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ g) →
      (((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^q*
        ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam) ≤ ((2:ℝ)^N)^η →
      ∀ G : Set (Space d × Space d), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ z x, (z,x) ∈ G → ∀ y ∈ (Q.descendant P).carrier, ‖y-x‖ ≤ D) →
      (∀ᵐ z ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier,
        ∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^η*r^q)) →
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
        ((ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier).prod ν)
          (G \ H) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-(2*η))) ∧
        ∀ p ∈ H, radialCollisionMass
          (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)
          (C/(2:ℝ)^v) p ≤ ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^(v-g))^(-q)) := by
  obtain ⟨J,N₀,hN₀⟩ := outer_radial_cell_pruning (d := d) hD hη₀ hq C
  refine ⟨J,N₀,?_⟩
  intro N hN η hη g v hgv hvN μ ν _ _ B hNp hB lam E hwidth hlarge
    p₀ hp₀ P hP hpos hinc hcoef G hG hdiag hpin hcap
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have : IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀)
      (Q.descendant P).carrier) := sourceClass_conditional_probability Q hside μ N B hp₀ P hpos
  exact hN₀ N hN η hη g v hgv hvN _ ν G hG hdiag
    (conditional_cell_pair_geometry Q hQ _ P hP hDdim G hpin)
    (sourceClass_original_conditional_frostman_power Q hQ μ hNp hB hq hwidth hlarge
      hp₀ (by omega) hvN hP hpos hinc hcoef) hcap

end Falconer.Regularization

end OAI

end ExtensionScope159

/- Source: OAI.MeasureTheory.Falconer.Recursion.ProfileRoundContact. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope160



namespace OAI

/-! # Contact intervals tolerate the rounding of their initial dyadic depth -/

namespace Falconer
open Set Filter
open scoped NNReal Topology

theorem profile_contact_move_left {f : ℝ → ℝ} {K : ℝ≥0}
    (hLip : LipschitzOnWith K f (Icc 0 1)) {a A B s E ε : ℝ}
    (ha : 0 ≤ a) (haA : a ≤ A) (hAB : A ≤ B) (hB : B ≤ 1)
    (hs : 0 ≤ s) (hclose : A-a ≤ ε)
    (hcontact : ∀ w ∈ Icc A B, s*(w-A)-E ≤ f w-f A) :
    ∀ w ∈ Icc a B, s*(w-a)-E-((K:ℝ)+s)*ε ≤ f w-f a := by
  have hA0 : 0 ≤ A := ha.trans haA
  have ha1 : a ≤ 1 := (haA.trans hAB).trans hB
  have hA1 : A ≤ 1 := hAB.trans hB
  have hfa : |f A-f a| ≤ (K:ℝ)*(A-a) := by
    simpa only [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr haA)] using
      hLip.dist_le_mul A ⟨hA0,hA1⟩ a ⟨ha,ha1⟩
  have hK := K.coe_nonneg
  intro w hw
  by_cases hAw : A ≤ w
  · have hh := hcontact w ⟨hAw,hw.2⟩
    have he := mul_le_mul_of_nonneg_left hclose (add_nonneg hK hs)
    nlinarith [neg_abs_le (f A-f a)]
  · have hwA : w ≤ A := (lt_of_not_ge hAw).le
    have hw1 : w ≤ 1 := hw.2.trans hB
    have hfw : |f w-f a| ≤ (K:ℝ)*(w-a) := by
      simpa only [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hw.1)] using
        hLip.dist_le_mul w ⟨ha.trans hw.1,hw1⟩ a ⟨ha,ha1⟩
    have hE : 0 ≤ E := by
      have hh := hcontact A ⟨le_rfl,hAB⟩
      simp only [sub_self,mul_zero,zero_sub] at hh
      linarith
    have hwe : w-a ≤ ε := (sub_le_sub_right hwA a).trans hclose
    nlinarith [neg_abs_le (f w-f a),mul_le_mul_of_nonneg_left hwe (add_nonneg hK hs)]

theorem floor_depth_ratio_tendsto {A : ℝ} (hA : 0 ≤ A) :
    Tendsto (fun N : ℕ => (Nat.floor (A*(N:ℝ)):ℝ)/(N:ℝ)) atTop (𝓝 A) :=
  (tendsto_nat_floor_mul_div_atTop hA).comp tendsto_natCast_atTop_atTop

end Falconer

end OAI

end ExtensionScope160

/- Source: OAI.MeasureTheory.Falconer.Recursion.RoundedProfileContact. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope161


namespace OAI

/-! # The three contact inequalities at actual integer dyadic depths -/

namespace Falconer
open Set
open scoped NNReal

theorem floor_depth_ratio_bounds {A : ℝ} (hA : 0 ≤ A) {N : ℕ} (hN : 0 < N) :
    0 ≤ (Nat.floor (A*(N:ℝ)):ℝ)/(N:ℝ) ∧
    (Nat.floor (A*(N:ℝ)):ℝ)/(N:ℝ) ≤ A ∧
    A-(Nat.floor (A*(N:ℝ)):ℝ)/(N:ℝ) ≤ 1/(N:ℝ) := by
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hlo := Nat.floor_le (mul_nonneg hA hNp.le)
  have hhi := Nat.lt_floor_add_one (A*(N:ℝ))
  refine ⟨by positivity,(div_le_iff₀ hNp).mpr hlo,?_⟩
  apply (le_div_iff₀ hNp).mpr
  have he : (A-(Nat.floor (A*(N:ℝ)):ℝ)/(N:ℝ))*(N:ℝ) =
      A*(N:ℝ)-(Nat.floor (A*(N:ℝ)):ℝ) := by field_simp
  rw [he]
  linarith

theorem rounded_profile_contact {f : ℝ → ℝ} {K : ℝ≥0}
    (hLip : LipschitzOnWith K f (Icc 0 1)) {A B q t E : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hfirst : ∀ w ∈ Icc 0 A, q*w-E ≤ f w)
    (hmiddle : ∀ w ∈ Icc A B, t*(w-A)-E ≤ f w-f A)
    (hlast : ∀ w ∈ Icc B 1, q*(w-B)-E ≤ f w-f B)
    {N : ℕ} (hN : 0 < N) :
    let a := Nat.floor (A*(N:ℝ))
    let b := Nat.floor (B*(N:ℝ))
    (∀ j : ℕ, j ≤ a → q*(j:ℝ)/N-E ≤ f ((j:ℝ)/N)) ∧
    (∀ j : ℕ, a ≤ j → j ≤ b →
      t*(j-a:ℕ)/N-E-((K:ℝ)+t)/N ≤ f ((j:ℝ)/N)-f ((a:ℝ)/N)) ∧
    (∀ j : ℕ, b ≤ j → j ≤ N →
      q*(j-b:ℕ)/N-E-((K:ℝ)+q)/N ≤ f ((j:ℝ)/N)-f ((b:ℝ)/N)) := by
  dsimp only
  let a := Nat.floor (A*(N:ℝ))
  let b := Nat.floor (B*(N:ℝ))
  have ha := floor_depth_ratio_bounds hA hN
  have hb := floor_depth_ratio_bounds (hA.trans hAB) hN
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hma := profile_contact_move_left hLip ha.1 ha.2.1 hAB hB ht ha.2.2 hmiddle
  have hlb := profile_contact_move_left hLip hb.1 hb.2.1 hB (le_refl (1:ℝ)) hq hb.2.2 hlast
  refine ⟨?_,?_,?_⟩
  · intro j hj
    have hjA : (j:ℝ)/N ≤ A := (div_le_div_of_nonneg_right (by exact_mod_cast hj) hNp.le).trans ha.2.1
    simpa only [mul_div_assoc] using hfirst ((j:ℝ)/N) ⟨by positivity,hjA⟩
  · intro j haj hjb
    have hlo : (a:ℝ)/N ≤ (j:ℝ)/N := div_le_div_of_nonneg_right (by exact_mod_cast haj) hNp.le
    have hhi : (j:ℝ)/N ≤ B := (div_le_div_of_nonneg_right (by exact_mod_cast hjb) hNp.le).trans hb.2.1
    have hh := hma ((j:ℝ)/N) ⟨hlo,hhi⟩
    rw [Nat.cast_sub haj]
    convert hh using 1
    ring
  · intro j hbj hjN
    have hlo : (b:ℝ)/N ≤ (j:ℝ)/N := div_le_div_of_nonneg_right (by exact_mod_cast hbj) hNp.le
    have hhi : (j:ℝ)/N ≤ 1 := (div_le_one hNp).mpr (by exact_mod_cast hjN)
    have hh := hlb ((j:ℝ)/N) ⟨hlo,hhi⟩
    rw [Nat.cast_sub hbj]
    convert hh using 1
    ring

end Falconer

end OAI

end ExtensionScope161

/- Source: OAI.MeasureTheory.Falconer.Recursion.UniformContactDepths. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope162



namespace OAI

/-! # Uniform integer-depth margins from the compactness contact theorem -/

namespace Falconer

theorem uniform_contact_depth_bounds {A B γ : ℝ} (hγ : 0 < γ)
    (hA : γ ≤ A) (hAB : A+γ ≤ B) (hB : B+γ ≤ 1) (hBA : B+γ ≤ 2*A)
    {N : ℕ} (hN : 0 < N) (hlarge : 4 ≤ γ*(N:ℝ)) :
    let a := Nat.floor (A*(N:ℝ))
    let b := Nat.floor (B*(N:ℝ))
    a ≤ b ∧ b ≤ N ∧ (γ/2)*(N:ℝ) ≤ (a:ℝ) ∧
      (γ/2)*(N:ℝ) ≤ (b-a:ℕ) ∧ γ*(N:ℝ) ≤ (N-b:ℕ) ∧
      (γ/2)*(N:ℝ) ≤ 2*(a:ℝ)-(b:ℝ) := by
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hA0 : 0 ≤ A := hγ.le.trans hA
  have hB0 : 0 ≤ B := by linarith
  have hAB' : A ≤ B := by linarith
  let a := Nat.floor (A*(N:ℝ))
  let b := Nat.floor (B*(N:ℝ))
  have haLo : (a:ℝ) ≤ A*(N:ℝ) := Nat.floor_le (mul_nonneg hA0 hNp.le)
  have hbLo : (b:ℝ) ≤ B*(N:ℝ) := Nat.floor_le (mul_nonneg hB0 hNp.le)
  have haHi : A*(N:ℝ) < (a:ℝ)+1 := Nat.lt_floor_add_one _
  have hbHi : B*(N:ℝ) < (b:ℝ)+1 := Nat.lt_floor_add_one _
  have hab : a ≤ b := Nat.floor_mono (mul_le_mul_of_nonneg_right hAB' hNp.le)
  have hbN : b ≤ N := Nat.floor_le_of_le (by nlinarith [mul_le_mul_of_nonneg_right hB hNp.le])
  have hAm := mul_le_mul_of_nonneg_right hA hNp.le
  have hABm := mul_le_mul_of_nonneg_right hAB hNp.le
  have hBm := mul_le_mul_of_nonneg_right hB hNp.le
  have hBAm := mul_le_mul_of_nonneg_right hBA hNp.le
  refine ⟨hab,hbN,?_,?_,?_,?_⟩
  · nlinarith
  · rw [Nat.cast_sub hab]
    nlinarith
  · rw [Nat.cast_sub hbN]
    nlinarith
  · nlinarith

end Falconer

end OAI

end ExtensionScope162

/- Source: OAI.MeasureTheory.Falconer.Recursion.RoundedContactWidth. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope163


namespace OAI

/-! # Integer contact widths retain the real interval length up to one unit -/

namespace Falconer

theorem rounded_contact_width {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (N : ℕ) :
    let a := Nat.floor (A*(N:ℝ))
    let b := Nat.floor (B*(N:ℝ))
    (B-A)*(N:ℝ)-1 ≤ (b-a:ℕ) ∧ (b-a:ℕ) ≤ (B-A)*(N:ℝ)+1 := by
  have hB : 0 ≤ B := hA.trans hAB
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hab := Nat.floor_mono (mul_le_mul_of_nonneg_right hAB hN)
  have haLo := Nat.floor_le (mul_nonneg hA hN)
  have hbLo := Nat.floor_le (mul_nonneg hB hN)
  have haHi := Nat.lt_floor_add_one (A*(N:ℝ))
  have hbHi := Nat.lt_floor_add_one (B*(N:ℝ))
  dsimp only
  rw [Nat.cast_sub hab]
  constructor <;> nlinarith

end Falconer

end OAI

end ExtensionScope163

/- Source: OAI.MeasureTheory.Falconer.Recursion.SourceClassIntervals. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope164




namespace OAI

/-! # Actual integer-depth three-interval data for each retained source class -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped NNReal
variable {d : ℕ}

theorem source_class_contact_intervals (Q : DyadicCube d) (μ : Measure (Space d))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath d)
    {q t τ γ : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) (hγ : 0 < γ)
    (hlarge : 4 ≤ γ*(N:ℝ))
    (hcontact : RobustProfileContact (sourceUnitProfile Q μ N B p) q t τ γ) :
    ∃ A B' : ℝ, ∃ a b : ℕ,
      γ ≤ B'-A ∧ B'-A ≤ 1 ∧ a ≤ b ∧ b ≤ N ∧
      (B'-A)*(N:ℝ)-1 ≤ (b-a:ℕ) ∧ (b-a:ℕ) ≤ (B'-A)*(N:ℝ)+1 ∧
      (γ/2)*(N:ℝ) ≤ (a:ℝ) ∧ (γ/2)*(N:ℝ) ≤ (b-a:ℕ) ∧
      γ*(N:ℝ) ≤ (N-b:ℕ) ∧ (γ/2)*(N:ℝ) ≤ 2*(a:ℝ)-(b:ℝ) ∧
      (∀ j : ℕ, j ≤ a → q*(j:ℝ)/N-τ*(B'-A) ≤ sourceProfile Q μ N B p j) ∧
      (∀ j : ℕ, a ≤ j → j ≤ b →
        t*(j-a:ℕ)/N-τ*(B'-A)-((d:ℝ)+t)/N ≤
          sourceProfile Q μ N B p j-sourceProfile Q μ N B p a) ∧
      (∀ j : ℕ, b ≤ j → j ≤ N →
        q*(j-b:ℕ)/N-τ*(B'-A)-((d:ℝ)+q)/N ≤
          sourceProfile Q μ N B p j-sourceProfile Q μ N B p b) := by
  obtain ⟨A,B',hA,hAB,hB',hBA,hfirst,hmiddle,hlast⟩ := hcontact
  have hA0 : 0 ≤ A := hγ.le.trans hA
  have hAB' : A ≤ B' := by linarith
  have hB1 : B' ≤ 1 := by linarith
  have hround := rounded_profile_contact
    (sourceUnitProfile_properties Q μ hN hB p).2.2.2.1 hA0 hAB' hB1 hq ht
    hfirst hmiddle hlast hN
  have hdepth := uniform_contact_depth_bounds hγ hA hAB hB' hBA hN hlarge
  have hgap := rounded_contact_width hA0 hAB' N
  refine ⟨A,B',Nat.floor (A*(N:ℝ)),Nat.floor (B'*(N:ℝ)),by linarith,by linarith,
    hdepth.1,hdepth.2.1,hgap.1,hgap.2,hdepth.2.2.1,hdepth.2.2.2.1,
    hdepth.2.2.2.2.1,hdepth.2.2.2.2.2,?_⟩
  simpa only [sourceUnitProfile_at_depth Q μ hN B p,NNReal.coe_natCast] using hround

end Falconer.Regularization

end OAI

end ExtensionScope164

/- Source: OAI.MeasureTheory.Falconer.Incidence.IncidenceMoment. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope165


namespace OAI

/-! # The natural-number incidence moment used to select transverse pins -/

namespace Falconer
open MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

private theorem rpow_pow_nat (x : ℝ≥0∞) (a : ℝ) (k : ℕ) :
    (x^a)^k = x^(a*k) := by
  rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]

theorem incidence_moment (μ : Measure X) (F : X → ℝ≥0∞) (hF : AEMeasurable F μ)
    {k : ℕ} (hk : 2 ≤ k) :
    (∫⁻ x, F x ∂μ)^k ≤ (∫⁻ x, (F x)^k ∂μ)*(μ Set.univ)^(k-1) := by
  have hk' : 1 < (k:ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hk0 : (k:ℝ) ≠ 0 := by linarith
  have hkm0 : (k:ℝ)-1 ≠ 0 := by linarith
  have hc : (k:ℝ).HolderConjugate ((k:ℝ)/((k:ℝ)-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hk').mpr rfl
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc hF
    (aemeasurable_const : AEMeasurable (fun _ : X => (1:ℝ≥0∞)) μ)
  simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_one,
    ENNReal.rpow_natCast] at hH
  have hp := pow_le_pow_left' hH k
  apply hp.trans_eq
  rw [mul_pow,rpow_pow_nat,rpow_pow_nat]
  have hfirst : (1/(k:ℝ))*(k:ℝ) = 1 := by field_simp
  have hsecond : (1/((k:ℝ)/((k:ℝ)-1)))*(k:ℝ) = ((k-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k),Nat.cast_one]
    field_simp
  rw [hfirst,hsecond,ENNReal.rpow_one,ENNReal.rpow_natCast]

end Falconer

end OAI

end ExtensionScope165

/- Source: OAI.MeasureTheory.Falconer.Measures.FiberDensityPruning. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope166



namespace OAI

/-! # Density pruning uses the original fibers in every retained cell -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {P X ι : Type*} [MeasurableSpace P] [MeasurableSpace X]

noncomputable def fiberDensityBad (μ : Measure X) (G : Set (P × X))
    (Q : ι → Set X) (I : Finset ι) (θ : ℝ≥0∞) : Set (P × X) :=
  G ∩ ⋃ i ∈ I, {p | μ (Q i ∩ Prod.mk p ⁻¹' G) < θ*μ (Q i)} ×ˢ Q i

theorem fiberDensityBad_measurable (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ι → Set X)
    (I : Finset ι) (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (θ : ℝ≥0∞) :
    MeasurableSet (fiberDensityBad μ G Q I θ) := by
  apply hG.inter
  apply Finset.measurableSet_biUnion I
  intro i hi
  have hS : MeasurableSet ((univ ×ˢ Q i) ∩ G) := (MeasurableSet.univ.prod (hQ i hi)).inter hG
  have hm : Measurable (fun p => μ (Q i ∩ Prod.mk p ⁻¹' G)) := by
    convert measurable_measure_prodMk_left (ν := μ) hS using 1
    ext p
    congr 1
    ext x
    simp only [mem_inter_iff,mem_preimage,mem_prod,mem_univ,true_and]
  exact (measurableSet_lt hm measurable_const).prod (hQ i hi)

omit [MeasurableSpace P] in
theorem fiberDensityBad_fiber_mass (μ : Measure X) (G : Set (P × X))
    (Q : ι → Set X) (I : Finset ι) (hQ : ∀ i ∈ I, MeasurableSet (Q i))
    (hdisj : (I : Set ι).PairwiseDisjoint Q) (θ : ℝ≥0∞) (p : P) :
    μ (Prod.mk p ⁻¹' fiberDensityBad μ G Q I θ) ≤ θ*μ univ := by
  classical
  let D := I.filter (fun i => μ (Q i ∩ Prod.mk p ⁻¹' G) < θ*μ (Q i))
  have hs : Prod.mk p ⁻¹' fiberDensityBad μ G Q I θ =
      ⋃ i ∈ D, Q i ∩ Prod.mk p ⁻¹' G := by
    ext x
    simp only [fiberDensityBad,mem_preimage,mem_inter_iff,mem_iUnion,mem_prod,
      mem_ofPred_eq,D,Finset.mem_filter]
    aesop
  have hsum : ∑ i ∈ I, μ (Q i) ≤ μ univ := by
    rw [← measure_biUnion_finset hdisj hQ]
    exact measure_mono (subset_univ _)
  rw [hs]
  calc
    _ ≤ ∑ i ∈ D, μ (Q i ∩ Prod.mk p ⁻¹' G) := measure_biUnion_finset_le D _
    _ ≤ ∑ i ∈ D, θ*μ (Q i) := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2.le)
    _ ≤ ∑ i ∈ I, θ*μ (Q i) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = θ*(∑ i ∈ I, μ (Q i)) := (Finset.mul_sum _ _ _).symm
    _ ≤ θ*μ univ := mul_le_mul' le_rfl hsum

theorem fiberDensityBad_product_mass (ν : Measure P) (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ι → Set X)
    (I : Finset ι) (hQ : ∀ i ∈ I, MeasurableSet (Q i))
    (hdisj : (I : Set ι).PairwiseDisjoint Q) (θ : ℝ≥0∞) :
    (ν.prod μ) (fiberDensityBad μ G Q I θ) ≤ (θ*μ univ)*ν univ := by
  rw [Measure.prod_apply (fiberDensityBad_measurable μ G hG Q I hQ θ)]
  calc
    _ ≤ ∫⁻ _p, θ*μ univ ∂ν := lintegral_mono (fiberDensityBad_fiber_mass μ G Q I hQ hdisj θ)
    _ = _ := by rw [lintegral_const,mul_comm]

omit [MeasurableSpace P] in
theorem fiberDensity_retained (μ : Measure X) (G : Set (P × X))
    (Q : ι → Set X) (I : Finset ι) (θ : ℝ≥0∞) {p : P} {x : X}
    (hx : (p,x) ∈ G \ fiberDensityBad μ G Q I θ)
    {i : ι} (hi : i ∈ I) (hxi : x ∈ Q i) :
    θ*μ (Q i) ≤ μ (Q i ∩ Prod.mk p ⁻¹' G) := by
  by_contra! hlt
  apply hx.2
  refine ⟨hx.1,mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,?_⟩⟩⟩
  exact ⟨hlt,hxi⟩

end Falconer

end OAI

end ExtensionScope166

/- Source: OAI.MeasureTheory.Falconer.Measures.MultiscaleDensityPruning. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope167


namespace OAI

/-! # Simultaneous density pruning at finitely many endpoint depths -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {P X ι : Type*} [MeasurableSpace P] [MeasurableSpace X]

noncomputable def multiscaleFiberBad (μ : Measure X) (G : Set (P × X))
    (Q : ℕ → ι → Set X) (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ) : Set (P × X) :=
  ⋃ j ∈ Finset.range (J+1), fiberDensityBad μ G (Q j) (I j) θ

theorem multiscaleFiberBad_measurable (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ℕ → ι → Set X)
    (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i)) : MeasurableSet (multiscaleFiberBad μ G Q I θ J) := by
  apply Finset.measurableSet_biUnion
  intro j hj
  exact fiberDensityBad_measurable μ G hG (Q j) (I j) (hQ j (by simpa using hj)) θ

theorem multiscaleFiberBad_mass (ν : Measure P) (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ℕ → ι → Set X)
    (I : ℕ → Finset ι) (J : ℕ)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j)) (θ : ℝ≥0∞) :
    (ν.prod μ) (multiscaleFiberBad μ G Q I θ J) ≤ (J+1:ℝ≥0∞)*(θ*μ univ)*ν univ := by
  calc
    _ ≤ ∑ j ∈ Finset.range (J+1), (ν.prod μ) (fiberDensityBad μ G (Q j) (I j) θ) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (J+1), (θ*μ univ)*ν univ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjJ : j ≤ J := by simpa using hj
      exact fiberDensityBad_product_mass ν μ G hG (Q j) (I j) (hQ j hjJ) (hdisj j hjJ) θ
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]; ring

omit [MeasurableSpace P] in
theorem multiscaleFiber_retained (μ : Measure X) (G : Set (P × X))
    (Q : ℕ → ι → Set X) (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ)
    {p : P} {x : X} (hx : (p,x) ∈ G \ multiscaleFiberBad μ G Q I θ J)
    {j : ℕ} (hj : j ≤ J) {i : ι} (hi : i ∈ I j) (hxi : x ∈ Q j i) :
    θ*μ (Q j i) ≤ μ (Q j i ∩ Prod.mk p ⁻¹' G) := by
  apply fiberDensity_retained μ G (Q j) (I j) θ ⟨hx.1,?_⟩ hi hxi
  intro hbad
  apply hx.2
  exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨by simpa using hj,hbad⟩⟩

end Falconer

end OAI

end ExtensionScope167

/- Source: OAI.MeasureTheory.Falconer.Measures.PairCorePruning. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope168


namespace OAI

/-! # Core restrictions and density pruning preserve the original pair-cost ledger -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem product_core_compl_null (ν : Measure X) (μ : Measure Y) [SFinite μ] (P : Set X) (S : Set Y)
    (hP : ν Pᶜ = 0) (hS : μ Sᶜ = 0) : (ν.prod μ) (P ×ˢ S)ᶜ = 0 := by
  apply le_antisymm _ zero_le
  calc
    _ ≤ (ν.prod μ) (Pᶜ ×ˢ univ ∪ univ ×ˢ Sᶜ) := by
      apply measure_mono
      intro p hp
      by_cases hx : p.1 ∈ P
      · exact Or.inr ⟨mem_univ _,fun hy => hp ⟨hx,hy⟩⟩
      · exact Or.inl ⟨hx,mem_univ _⟩
    _ ≤ (ν.prod μ) (Pᶜ ×ˢ univ)+(ν.prod μ) (univ ×ˢ Sᶜ) := measure_union_le _ _
    _ = 0 := by simp only [Measure.prod_prod,hP,hS,zero_mul,mul_zero,add_zero]

theorem pair_core_restriction_cost (ν : Measure X) (μ : Measure Y) [SFinite μ] (G : Set (X × Y))
    (P : Set X) (S : Set Y) (hP : ν Pᶜ = 0) (hS : μ Sᶜ = 0) :
    (ν.prod μ) (G ∩ (P ×ˢ S))ᶜ ≤ (ν.prod μ) Gᶜ := by
  rw [compl_inter]
  exact (measure_union_le _ _).trans_eq (by rw [product_core_compl_null ν μ P S hP hS,add_zero])

theorem density_pruned_pair_cost (ν : Measure X) (μ : Measure Y) [SFinite μ]
    (G : Set (X × Y)) (hG : MeasurableSet G) (Q : ℕ → ι → Set Y)
    (I : ℕ → Finset ι) (J : ℕ) (θ : ℝ≥0∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j)) :
    (ν.prod μ) (G \ multiscaleFiberBad μ G Q I θ J)ᶜ ≤
      (ν.prod μ) Gᶜ+(J+1:ℝ≥0∞)*(θ*μ univ)*ν univ := by
  have he : (G \ multiscaleFiberBad μ G Q I θ J)ᶜ =
      Gᶜ ∪ multiscaleFiberBad μ G Q I θ J := by
    classical
    ext p
    simp only [mem_compl_iff, mem_sdiff, mem_union]
    tauto
  rw [he]
  exact (measure_union_le _ _).trans
    (add_le_add le_rfl (multiscaleFiberBad_mass ν μ G hG Q I J hQ hdisj θ))

end Falconer

end OAI

end ExtensionScope168

/- Source: OAI.MeasureTheory.Falconer.Estimates.CellwisePairDeletion. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope169



namespace OAI

/-! # Recombining local pair deletions with their original source-cell masses -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem conditional_pair_mass_reconstruct (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [SFinite ν] (Q : Set X) (hQ : μ Q ≠ 0) (E : Set (X × Y)) :
    μ Q*((ProbabilityTheory.cond μ Q).prod ν) E = ((μ.restrict Q).prod ν) E := by
  rw [ProbabilityTheory.cond,Measure.prod_smul_left,Measure.smul_apply,smul_eq_mul,
    ← mul_assoc,ENNReal.mul_inv_cancel hQ (measure_ne_top μ Q),one_mul]

theorem cellwise_pair_deletion_bound (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (I : Finset ι) (Q : ι → Set X) (E : ι → Set (X × Y))
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hE : ∀ i ∈ I, MeasurableSet (E i))
    (hdisj : (I : Set ι).PairwiseDisjoint Q) (t : ℝ≥0∞)
    (hlocal : ∀ i ∈ I, ((μ.restrict (Q i)).prod ν) (E i) ≤ t*μ (Q i)) :
    (μ.prod ν) (⋃ i ∈ I, E i ∩ (Q i ×ˢ univ)) ≤ t*μ univ := by
  calc
    _ ≤ ∑ i ∈ I, (μ.prod ν) (E i ∩ (Q i ×ˢ univ)) := measure_biUnion_finset_le _ _
    _ = ∑ i ∈ I, ((μ.restrict (Q i)).prod ν) (E i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Measure.restrict_prod_eq_prod_univ,Measure.restrict_apply (hE i hi)]
    _ ≤ ∑ i ∈ I, t*μ (Q i) := Finset.sum_le_sum hlocal
    _ = t*(∑ i ∈ I, μ (Q i)) := (Finset.mul_sum _ _ _).symm
    _ = t*μ (⋃ i ∈ I, Q i) := by rw [measure_biUnion_finset hdisj hQ]
    _ ≤ _ := mul_le_mul' le_rfl (measure_mono (subset_univ _))

theorem conditional_cellwise_pair_deletion (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [SFinite ν] (I : Finset ι) (Q : ι → Set X) (E : ι → Set (X × Y))
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hE : ∀ i ∈ I, MeasurableSet (E i))
    (hpos : ∀ i ∈ I, μ (Q i) ≠ 0) (hdisj : (I : Set ι).PairwiseDisjoint Q) (t : ℝ≥0∞)
    (hlocal : ∀ i ∈ I, ((ProbabilityTheory.cond μ (Q i)).prod ν) (E i) ≤ t) :
    (μ.prod ν) (⋃ i ∈ I, E i ∩ (Q i ×ˢ univ)) ≤ t*μ univ := by
  apply cellwise_pair_deletion_bound μ ν I Q E hQ hE hdisj t
  intro i hi
  rw [← conditional_pair_mass_reconstruct μ ν (Q i) (hpos i hi) (E i),mul_comm t]
  exact mul_le_mul' le_rfl (hlocal i hi)

end Falconer

end OAI

end ExtensionScope169

/- Source: OAI.MeasureTheory.Falconer.Radial.ClasswiseRadialGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope170



namespace OAI

/-! # Recombining radial gains with the original source-class weights -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*}

theorem classwise_radial_gain (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (I : Finset ι) (S : ι → Set (Space d)) (G : ι → Set (Space d × Space d))
    (hS : ∀ i ∈ I, MeasurableSet (S i)) (hG : ∀ i ∈ I, MeasurableSet (G i))
    (hpos : ∀ i ∈ I, μ (S i) ≠ 0) (hdisj : (I : Set ι).PairwiseDisjoint S)
    (t C : ℝ≥0∞) (r : ℝ)
    (hcost : ∀ i ∈ I, (ν.prod (ProbabilityTheory.cond μ (S i))) (G i)ᶜ ≤ t)
    (hcap : ∀ i ∈ I, ∀ x u : Space d,
      ProbabilityTheory.cond μ (S i) {z | (x,z) ∈ G i ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      (ν.prod μ) Hᶜ ≤ μ (⋃ i ∈ I, S i)ᶜ+t ∧
      ∀ x u : Space d, μ {z | (x,z) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
  classical
  let H := ⋃ i ∈ I, G i ∩ (univ ×ˢ S i)
  have hH : MeasurableSet H := Finset.measurableSet_biUnion I
    (fun i hi => (hG i hi).inter (MeasurableSet.univ.prod (hS i hi)))
  have hmass : (∑ i ∈ I, μ (S i)) ≤ 1 := by
    rw [← measure_biUnion_finset hdisj hS]
    exact (measure_mono (subset_univ _)).trans_eq (measure_univ)
  have hreconstruct (i : ι) (hi : i ∈ I) (E : Set (Space d × Space d)) :
      μ (S i)*((ν.prod (ProbabilityTheory.cond μ (S i))) E) =
        (ν.prod (μ.restrict (S i))) E := by
    rw [ProbabilityTheory.cond,Measure.prod_smul_right,Measure.smul_apply,smul_eq_mul,
      ← mul_assoc,ENNReal.mul_inv_cancel (hpos i hi) (measure_ne_top μ _),one_mul]
  refine ⟨H,hH,?_,?_⟩
  · have hsub : Hᶜ ⊆ (univ ×ˢ (⋃ i ∈ I, S i)ᶜ) ∪
        ⋃ i ∈ I, (G i)ᶜ ∩ (univ ×ˢ S i) := by
      intro p hp
      by_cases hs : p.2 ∈ ⋃ i ∈ I, S i
      · obtain ⟨i,hi,hsi⟩ := mem_iUnion₂.mp hs
        right
        refine mem_iUnion₂.mpr ⟨i,hi,?_,mem_univ _,hsi⟩
        intro hgi
        exact hp (mem_iUnion₂.mpr ⟨i,hi,hgi,mem_univ _,hsi⟩)
      · exact Or.inl ⟨mem_univ _,hs⟩
    calc
      _ ≤ (ν.prod μ) (univ ×ˢ (⋃ i ∈ I, S i)ᶜ)+
          (ν.prod μ) (⋃ i ∈ I, (G i)ᶜ ∩ (univ ×ˢ S i)) :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ μ (⋃ i ∈ I, S i)ᶜ+
          ∑ i ∈ I, (ν.prod μ) ((G i)ᶜ ∩ (univ ×ˢ S i)) := by
        simp only [Measure.prod_prod,measure_univ,one_mul]
        exact add_le_add le_rfl (measure_biUnion_finset_le _ _)
      _ ≤ μ (⋃ i ∈ I, S i)ᶜ+∑ i ∈ I, μ (S i)*t := by
        apply add_le_add le_rfl (Finset.sum_le_sum ?_)
        intro i hi
        rw [← Measure.restrict_apply (hG i hi).compl,← Measure.prod_restrict,
          Measure.restrict_univ,← hreconstruct i hi]
        exact mul_le_mul' le_rfl (hcost i hi)
      _ = μ (⋃ i ∈ I, S i)ᶜ+(∑ i ∈ I, μ (S i))*t := by rw [Finset.sum_mul]
      _ ≤ _ := add_le_add le_rfl ((mul_le_mul' hmass le_rfl).trans_eq (one_mul t))
  · intro x u
    let A := fun i => {z | (x,z) ∈ G i ∧ ‖normalize (z-x)-u‖ ≤ r}
    have hsub : {z | (x,z) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ r} ⊆ ⋃ i ∈ I, S i ∩ A i := by
      intro z hz
      obtain ⟨i,hi,hgi,hsi⟩ := mem_iUnion₂.mp hz.1
      exact mem_iUnion₂.mpr ⟨i,hi,hsi.2,hgi,hz.2⟩
    calc
      _ ≤ ∑ i ∈ I, μ (S i ∩ A i) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
      _ = ∑ i ∈ I, μ (S i)*ProbabilityTheory.cond μ (S i) (A i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← ProbabilityTheory.cond_mul_eq_inter (hS i hi) (A i) μ,mul_comm]
      _ ≤ ∑ i ∈ I, μ (S i)*C := Finset.sum_le_sum (fun i hi =>
        mul_le_mul' le_rfl (hcap i hi x u))
      _ = (∑ i ∈ I, μ (S i))*C := (Finset.sum_mul _ _ _).symm
      _ ≤ C := (mul_le_mul' hmass le_rfl).trans_eq (one_mul C)

end Falconer

end OAI

end ExtensionScope170

/- Source: OAI.MeasureTheory.Falconer.Radial.RegularizationRadialGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope171



namespace OAI

/-! # Recombining the actual radial regularization classes without a class-count loss -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem normalized_regularization_class_eq_cond (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (T : List ℕ) :
    normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T =
      ProbabilityTheory.cond μ (regularizationSet Q μ N B T) := by
  unfold normalizedClass classMeasure ProbabilityTheory.cond regularizationSet
  rw [Measure.restrict_apply_univ]

theorem regularization_radial_gain (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hroot : μ Q.carrierᶜ = 0) {N H : ℕ} (hH : 0 < H) (hNH : H ≤ N) (hdN : d+3 ≤ N)
    {threshold : ℝ≥0∞} (hthreshold : 0 < threshold) (t C : ℝ≥0∞) (r : ℝ)
    (hlocal : ∀ T ∈ regularizationIndex Q μ N (N/H) threshold,
      ∃ G : Set (Space d × Space d), MeasurableSet G ∧
        (ν.prod (normalizedClass Q μ (regularizationLeaves Q μ N)
          (regularizationLabel Q μ N (N/H)) T)) Gᶜ ≤ t ∧
        ∀ x u : Space d,
          normalizedClass Q μ (regularizationLeaves Q μ N)
            (regularizationLabel Q μ N (N/H)) T
            {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) :
    ∃ G : Set (Space d × Space d), MeasurableSet G ∧
      (ν.prod μ) Gᶜ ≤ ((2:ℝ≥0∞)^(2*N))⁻¹+(N^(4*H+2):ℕ)*threshold+t ∧
      ∀ x u : Space d, μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
  classical
  let I := regularizationIndex Q μ N (N/H) threshold
  let S := regularizationSet Q μ N (N/H)
  have hex : ∀ T : List ℕ, ∃ G : Set (Space d × Space d), MeasurableSet G ∧
      (T ∈ I → (ν.prod (ProbabilityTheory.cond μ (S T))) Gᶜ ≤ t ∧
        ∀ x u : Space d, ProbabilityTheory.cond μ (S T)
          {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) := by
    intro T
    by_cases hT : T ∈ I
    · obtain ⟨G,hm,hc,hg⟩ := hlocal T hT
      rw [normalized_regularization_class_eq_cond] at hc hg
      exact ⟨G,hm,fun _ => ⟨hc,hg⟩⟩
    · exact ⟨∅,MeasurableSet.empty,fun h => (hT h).elim⟩
  choose G hm hg using hex
  have hpos : ∀ T ∈ I, μ (S T) ≠ 0 := by
    intro T hT
    exact (hthreshold.trans_le (regularizationSet_mass Q μ N (N/H) threshold hT)).ne'
  have hdisj : (I : Set (List ℕ)).PairwiseDisjoint S := by
    intro T _ U _ hTU
    exact regularizationSet_disjoint Q hQ μ N (N/H) hTU
  obtain ⟨G',hG',hc,hcap⟩ := classwise_radial_gain μ ν I S G
    (fun T _ => regularizationSet_measurable Q μ N (N/H) T) (fun T _ => hm T)
    hpos hdisj t C r (fun T hT => (hg T hT).1) (fun T hT => (hg T hT).2)
  refine ⟨G',hG',hc.trans (add_le_add ?_ le_rfl),hcap⟩
  exact regularization_discarded_global Q hQ μ hroot hH hNH hdN threshold

end Falconer.Regularization

end OAI

end ExtensionScope171

/- Source: OAI.MeasureTheory.Falconer.Estimates.SourceClassOriginalLaws. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope172



namespace OAI

/-! # Source regularization preserves almost-everywhere bounds for the original reverse laws -/

namespace Falconer.Regularization
open Set MeasureTheory
variable {d : ℕ}

theorem sourceClass_absolutelyContinuous (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p : CellPath d) : sourceClass Q μ N B p ≪ μ := by
  unfold sourceClass
  rw [normalized_regularization_class_eq_cond]
  exact ProbabilityTheory.cond_absolutelyContinuous

theorem sourceClass_conditional_absolutelyContinuous (Q : DyadicCube d)
    (μ : Measure (Space d)) (N B : ℕ) (p P : CellPath d) :
    ProbabilityTheory.cond (sourceClass Q μ N B p) (Q.descendant P).carrier ≪ μ :=
  ProbabilityTheory.cond_absolutelyContinuous.trans (sourceClass_absolutelyContinuous Q μ N B p)

theorem sourceClass_original_ae (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p : CellPath d) {P : Space d → Prop} (hP : ∀ᵐ z ∂μ, P z) :
    ∀ᵐ z ∂sourceClass Q μ N B p, P z :=
  (sourceClass_absolutelyContinuous Q μ N B p).ae_le hP

theorem sourceClass_conditional_original_ae (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p P : CellPath d) {R : Space d → Prop} (hR : ∀ᵐ z ∂μ, R z) :
    ∀ᵐ z ∂ProbabilityTheory.cond (sourceClass Q μ N B p) (Q.descendant P).carrier, R z :=
  (sourceClass_conditional_absolutelyContinuous Q μ N B p P).ae_le hR

end Falconer.Regularization

end OAI

end ExtensionScope172

/- Source: OAI.MeasureTheory.Falconer.Radial.OccupiedRadialTree. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope173


namespace OAI

/-! # Occupied dyadic trees with a common full-measure source core -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def DyadicCube.emptyTreeCells (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : Set (Space d) :=
  ⋃ n ∈ Finset.range (N+1),
    ⋃ p ∈ cubePaths d n \ Q.occupiedPaths μ n, (Q.descendant p).carrier

noncomputable def DyadicCube.occupiedTreeCore (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : Set (Space d) :=
  Q.carrier \ Q.emptyTreeCells μ N

theorem DyadicCube.emptyTreeCells_measurable (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : MeasurableSet (Q.emptyTreeCells μ N) := by
  apply Finset.measurableSet_biUnion
  intro n _
  exact Finset.measurableSet_biUnion _ (fun p _ => (Q.descendant p).measurable)

theorem DyadicCube.emptyTreeCells_null (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : μ (Q.emptyTreeCells μ N) = 0 := by
  apply le_antisymm _ zero_le
  apply (measure_biUnion_finset_le _ _).trans
  apply Finset.sum_nonpos
  intro n _
  apply (measure_biUnion_finset_le _ _).trans
  apply Finset.sum_nonpos
  intro p hp
  obtain ⟨hp,hno⟩ := Finset.mem_sdiff.mp hp
  have hn : ¬ 0 < μ (Q.descendant p).carrier := by
    intro h
    exact hno (Finset.mem_filter.mpr ⟨hp,h⟩)
  exact le_of_not_gt hn

theorem DyadicCube.occupiedTreeCore_measurable (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : MeasurableSet (Q.occupiedTreeCore μ N) :=
  Q.measurable.diff (Q.emptyTreeCells_measurable μ N)

theorem DyadicCube.occupiedTreeCore_full (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) (hroot : μ Q.carrierᶜ = 0) :
    μ (Q.occupiedTreeCore μ N)ᶜ = 0 := by
  classical
  have he : (Q.occupiedTreeCore μ N)ᶜ = Q.carrierᶜ ∪ Q.emptyTreeCells μ N := by
    ext x
    simp only [occupiedTreeCore,mem_compl_iff,mem_sdiff,mem_union]
    tauto
  rw [he]
  apply le_antisymm _ zero_le
  exact (measure_union_le _ _).trans_eq (by rw [hroot,Q.emptyTreeCells_null,zero_add])

theorem DyadicCube.occupiedTreeCore_cover (Q : DyadicCube d)
    (μ : Measure (Space d)) {N n : ℕ} (hn : n ≤ N)
    {x : Space d} (hx : x ∈ Q.occupiedTreeCore μ N) :
    ∃ p ∈ Q.occupiedPaths μ n, x ∈ (Q.descendant p).carrier := by
  classical
  obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth n hx.1
  refine ⟨p,?_,hxp⟩
  by_contra hno
  exact hx.2 (mem_iUnion₂.mpr ⟨n,Finset.mem_range.mpr (by omega),
    mem_iUnion₂.mpr ⟨p,Finset.mem_sdiff.mpr ⟨hp,hno⟩,hxp⟩⟩)

theorem DyadicCube.occupied_parent (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {a b : ℕ} (hab : a ≤ b)
    {p : List (Fin d → Bool)} (hp : p ∈ Q.occupiedPaths μ b) :
    p.take a ∈ Q.occupiedPaths μ a ∧
      (Q.descendant p).carrier ⊆ (Q.descendant (p.take a)).carrier := by
  obtain ⟨hp,hpos⟩ := Finset.mem_filter.mp hp
  have hlen := (mem_cubePaths d b p).mp hp
  have hsub := Regularization.descendant_subset_take Q hQ p a
  refine ⟨Finset.mem_filter.mpr ⟨?_,hpos.trans_le (measure_mono hsub)⟩,hsub⟩
  exact (mem_cubePaths d a _).mpr (by simp only [List.length_take,hlen,Nat.min_eq_left hab])

theorem DyadicCube.occupied_center_bound (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {n : ℕ} {p : List (Fin d → Bool)}
    (hp : p ∈ Q.occupiedPaths μ n) {z : Space d} (hz : z ∈ (Q.descendant p).carrier) :
    ‖z-(Q.descendant p).center‖ ≤ Real.sqrt d*(Q.side/(2:ℝ)^n) := by
  have hlen := (mem_cubePaths d n p).mp (Finset.mem_filter.mp hp).1
  have hb := (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hz
    ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p))
  simpa only [dist_eq_norm,Q.descendant_side,hlen] using hb

theorem DyadicCube.occupied_diameter_bound (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {n : ℕ} {p : List (Fin d → Bool)}
    (hp : p ∈ Q.occupiedPaths μ n) {y z : Space d}
    (hy : y ∈ (Q.descendant p).carrier) (hz : z ∈ (Q.descendant p).carrier) :
    ‖y-z‖ ≤ Real.sqrt d*(Q.side/(2:ℝ)^n) := by
  have hlen := (mem_cubePaths d n p).mp (Finset.mem_filter.mp hp).1
  simpa only [dist_eq_norm,Q.descendant_side,hlen] using
    (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hy hz

end Falconer

end OAI

end ExtensionScope173

/- Source: OAI.MeasureTheory.Falconer.Estimates.RelativePairCore. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope174





namespace OAI

/-! # Discarding null source and pin sets relative to the incoming relation -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem relative_pair_core_null (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (G : Set (X × Y)) (A : Set X) (P : Set Y) (hA : μ Aᶜ = 0) (hP : ν Pᶜ = 0) :
    (μ.prod ν) (G \ (G ∩ (A ×ˢ P))) = 0 := by
  apply le_antisymm _ zero_le
  apply (measure_mono (show G \ (G ∩ (A ×ˢ P)) ⊆ (A ×ˢ P)ᶜ from ?_)).trans_eq
    (product_core_compl_null μ ν A P hA hP)
  intro x hx hcore
  exact hx.2 ⟨hx.1,hcore⟩

theorem relative_pruning_cost_trans {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (G H K : Set X) {a b : ℝ≥0∞} (hGH : μ (G \ H) ≤ a) (hHK : μ (H \ K) ≤ b) :
    μ (G \ K) ≤ a+b := by
  have hsub : G \ K ⊆ (G \ H) ∪ (H \ K) := by
    intro x hx
    by_cases hh : x ∈ H
    · exact Or.inr ⟨hh,hx.2⟩
    · exact Or.inl ⟨hx.1,hh⟩
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hGH hHK))

namespace Regularization
variable {d : ℕ}

theorem source_class_pair_core (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N B : ℕ) (p : CellPath d) (hp : p ∈ regularizationLeaves Q μ N)
    (A P : Set (Space d)) (hA : MeasurableSet A) (hP : MeasurableSet P)
    (hAfull : μ Aᶜ = 0) (hPfull : ν Pᶜ = 0)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    ∃ G₀ : Set (Space d × Space d), MeasurableSet G₀ ∧ G₀ ⊆ G ∧
      G₀ ⊆ (A ∩ Q.occupiedTreeCore (sourceClass Q μ N B p) N) ×ˢ P ∧
      ((sourceClass Q μ N B p).prod ν) (G \ G₀) = 0 := by
  let ρ := sourceClass Q μ N B p
  have : IsProbabilityMeasure ρ := regularization_class_probability Q hQ μ N B hp
  let S := A ∩ Q.occupiedTreeCore ρ N
  have hS : MeasurableSet S := hA.inter (Q.occupiedTreeCore_measurable ρ N)
  have hSfull : ρ Sᶜ = 0 := by
    rw [show Sᶜ = Aᶜ ∪ (Q.occupiedTreeCore ρ N)ᶜ by exact compl_inter _ _]
    apply le_antisymm _ zero_le
    apply (measure_union_le _ _).trans_eq
    rw [sourceClass_absolutelyContinuous Q μ N B p hAfull,
      Q.occupiedTreeCore_full ρ N (sourceClass_root_null Q hQ μ N B p),add_zero]
  refine ⟨G ∩ (S ×ˢ P),hG.inter (hS.prod hP),inter_subset_left,inter_subset_right,?_⟩
  exact relative_pair_core_null ρ ν G S P hSfull hPfull

end Regularization
end Falconer

end OAI

end ExtensionScope174

/- Source: OAI.MeasureTheory.Falconer.Estimates.ReverseLawTransfer. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope175



namespace OAI

/-! # Original reverse cap and slab bounds on the coarser middle scale -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem reverse_caps_transfer (μ ρ ν : Measure (Space d)) (hρ : ρ ≪ μ)
    {G G' : Set (Space d × Space d)} (hsub : G' ⊆ G)
    {N M : ℕ} (hMN : M ≤ N) {K K' q : ℝ} (hK : K ≤ K')
    (hcap : ∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K*r^q)) :
    ∀ᵐ z ∂ρ, ∀ w : Sphere d, ∀ j : ℕ, j ≤ M →
      ν {x | (z,x) ∈ G' ∧ dist (normalize (x-z)) (w:Space d) < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal (K'*(1/(2:ℝ)^j)^q) := by
  filter_upwards [hρ.ae_le hcap] with z hz
  intro w j hj
  have hr : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^j :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (hj.trans hMN))
  have hr1 : 1/(2:ℝ)^j ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hmono : ν {x | (z,x) ∈ G' ∧ dist (normalize (x-z)) (w:Space d) < 1/(2:ℝ)^j} ≤
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space d) < 1/(2:ℝ)^j} :=
    measure_mono (fun _ hx => ⟨hsub hx.1,hx.2⟩)
  apply hmono.trans ((hz _ hr hr1 w (sphere_norm w)).trans ?_)
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK (by positivity))

theorem reverse_slabs_transfer (μ ρ ν : Measure (Space d)) (hρ : ρ ≪ μ)
    {G G' : Set (Space d × Space d)} (hsub : G' ⊆ G)
    {N M : ℕ} (hMN : M ≤ N) {K K' ζ : ℝ} (hK : K ≤ K')
    (hslab : ∀ᵐ z ∂μ, ∀ u : Space d, ‖u‖ = 1 → ∀ r : ℝ,
      1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {x | (z,x) ∈ G ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤ ENNReal.ofReal (K*r^ζ)) :
    ∀ᵐ z ∂ρ, ∀ w : Sphere d, ∀ r : ℝ, 1/(2:ℝ)^M ≤ r → r ≤ 1 →
      ν {x | (z,x) ∈ G' ∧ |inner ℝ (w:Space d) (normalize (x-z))| ≤ r} ≤
        ENNReal.ofReal (K'*r^ζ) := by
  filter_upwards [hρ.ae_le hslab] with z hz
  intro w r hr hr1
  have hNM : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^M :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hMN)
  have hmono : ν {x | (z,x) ∈ G' ∧ |inner ℝ (w:Space d) (normalize (x-z))| ≤ r} ≤
      ν {x | (z,x) ∈ G ∧ |inner ℝ (w:Space d) (normalize (x-z))| ≤ r} :=
    measure_mono (fun _ hx => ⟨hsub hx.1,hx.2⟩)
  apply hmono.trans ((hz w (sphere_norm w) r (hNM.trans hr) hr1).trans ?_)
  have hr0 : 0 ≤ r := (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^M).trans hr
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hr0 _))

end Falconer

end OAI

end ExtensionScope175

/- Source: OAI.MeasureTheory.Falconer.Angular.ReverseCapsAllRadii. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope176


namespace OAI

/-! # Reverse-cap bounds under source restriction at every original radius -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem reverse_caps_all_radii (μ ρ ν : Measure (Space d)) (hρ : ρ ≪ μ)
    {G G' : Set (Space d × Space d)} (hsub : G' ⊆ G)
    {N v : ℕ} (hvN : v ≤ N) {K K' q : ℝ} (hK : K ≤ K')
    (hcap : ∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K*r^q)) :
    ∀ᵐ z ∂ρ, ∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 →
      ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G' ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K'*r^q) := by
  filter_upwards [hρ.ae_le hcap] with z hz
  intro r hr hr1 u hu
  have hδ : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^v :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hvN)
  have hm : ν {x | (z,x) ∈ G' ∧ dist (normalize (x-z)) u < r} ≤
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} :=
    measure_mono (fun _ hx => ⟨hsub hx.1,hx.2⟩)
  apply hm.trans ((hz r (hδ.trans hr) hr1 u hu).trans ?_)
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg ((by positivity : (0:ℝ) ≤ 1/(2:ℝ)^v).trans hr) _))

end Falconer

end OAI

end ExtensionScope176

/- Source: OAI.MeasureTheory.Falconer.Recursion.RelativeScaleBudget. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope177


namespace OAI

/-! # Uniform constant absorption when passing from the full to the middle scale -/

namespace Falconer

theorem dyadic_relative_scale_bound (N k : ℕ) {α β : ℝ}
    (h : (N:ℝ)*α ≤ (k:ℝ)*β) : ((2:ℝ)^N)^α ≤ ((2:ℝ)^k)^β := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

theorem eventually_relative_scale_constant {η : ℝ} (hη : 0 < η) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k : ℕ, ∀ α β : ℝ,
      (N:ℝ)*(η+α) ≤ (k:ℝ)*β →
      C*((2:ℝ)^N)^α ≤ ((2:ℝ)^k)^β := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hη C
  refine ⟨N₀,fun N hN k α β hbudget => ?_⟩
  calc
    _ ≤ ((2:ℝ)^N)^η*((2:ℝ)^N)^α :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2:ℝ)^N)^(η+α) := (Real.rpow_add (by positivity) _ _).symm
    _ ≤ _ := dyadic_relative_scale_bound N k hbudget

end Falconer

end OAI

end ExtensionScope177

/- Source: OAI.MeasureTheory.Falconer.Geometry.MiddleScaleGeometry. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope178



namespace OAI

/-! # Uniform radial freezing from the integer contact margin -/

namespace Falconer

theorem middle_freeze_bound {b s : ℝ} (hb : 0 < b) (hs : 0 < s)
    {p v : ℕ} (hpv : p ≤ v) (hvp : v ≤ 2*p)
    (hlarge : 1/(2*b*s) ≤ (2:ℝ)^(2*p-v)) :
    (1/2:ℝ)/(b*(2:ℝ)^p*s) ≤ 1/(2:ℝ)^(v-p) := by
  have he : (2:ℝ)^(2*p-v)*(2:ℝ)^(v-p) = (2:ℝ)^p := by
    rw [← pow_add,show 2*p-v+(v-p) = p by omega]
  have hh : (1/2:ℝ) ≤ (2:ℝ)^(2*p-v)*b*s := by
    have h := (div_le_iff₀ (show 0 < 2*b*s by positivity)).mp hlarge
    nlinarith
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simp only [one_mul]
  calc
    (1/2:ℝ)*(2:ℝ)^(v-p) ≤ ((2:ℝ)^(2*p-v)*b*s)*(2:ℝ)^(v-p) :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = b*(2:ℝ)^p*s := by rw [← he]; ring

theorem eventually_uniform_middle_freeze {b s γ : ℝ}
    (hb : 0 < b) (hs : 0 < s) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p v : ℕ, p ≤ v →
      γ*(N:ℝ) ≤ 2*(p:ℝ)-(v:ℝ) →
      (1/2:ℝ)/(b*(2:ℝ)^p*s) ≤ 1/(2:ℝ)^(v-p) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hγ (1/(2*b*s))
  refine ⟨N₀,fun N hN p v hpv hmargin => ?_⟩
  have hvp : v ≤ 2*p := by
    have hnonneg : 0 ≤ γ*(N:ℝ) := mul_nonneg hγ.le (Nat.cast_nonneg N)
    have hh : (v:ℝ) ≤ (2*p:ℕ) := by push_cast; linarith
    exact_mod_cast hh
  apply middle_freeze_bound hb hs hpv hvp
  apply (hN₀ N hN).trans
  have hh : (N:ℝ)*γ ≤ ((2*p-v:ℕ):ℝ)*1 := by
    rw [Nat.cast_sub hvp]
    push_cast
    nlinarith
  simpa only [Real.rpow_one] using dyadic_relative_scale_bound N (2*p-v) hh

theorem eventually_integer_margin {γ : ℝ} (hγ : 0 < γ) (L : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n : ℕ, γ*(N:ℝ) ≤ (n:ℝ) → L ≤ n := by
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt ((L:ℝ)/γ)
  refine ⟨N₀,fun N hN n hn => ?_⟩
  have hN' : (N₀:ℝ) ≤ N := by exact_mod_cast hN
  have hL : (L:ℝ) < γ*(N₀:ℝ) := by
    have hh := (div_lt_iff₀ hγ).mp hN₀
    nlinarith
  have hn' : (L:ℝ) ≤ n := by
    have hh := mul_le_mul_of_nonneg_left hN' hγ.le
    linarith
  exact_mod_cast hn'

theorem middle_width_rounding {b H C : ℝ} (p v J : ℕ) (hpv : p ≤ v)
    (hJ : J ≤ v-p) (hC : b*H*C ≤ (2:ℝ)^J) :
    (b*(2:ℝ)^p*H)*(C/(2:ℝ)^v) ≤ 1/(2:ℝ)^((v-p)-J) := by
  have hv : (2:ℝ)^v = (2:ℝ)^p*(2:ℝ)^(v-p) := by
    rw [← pow_add,Nat.add_sub_of_le hpv]
  have hw : (2:ℝ)^(v-p) = (2:ℝ)^J*(2:ℝ)^((v-p)-J) := by
    rw [← pow_add,Nat.add_sub_of_le hJ]
  calc
    _ = (b*H*C)/(2:ℝ)^(v-p) := by rw [hv]; field_simp
    _ ≤ (2:ℝ)^J/(2:ℝ)^(v-p) := div_le_div_of_nonneg_right hC (by positivity)
    _ = _ := by rw [hw]; field_simp

theorem eventually_contact_middle_depth {γ : ℝ} (hγ : 0 < γ) (J M₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k : ℕ, ∀ Δ : ℝ,
      γ ≤ Δ → Δ*(N:ℝ)-1 ≤ (k:ℝ) →
      M₀ ≤ k-J ∧ (N:ℝ)*Δ ≤ 2*((k-J:ℕ):ℝ) := by
  let L : ℕ := max (J+M₀+1) (2*J+2)
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt ((L:ℝ)/γ)
  refine ⟨N₀,fun N hN k Δ hγΔ hgap => ?_⟩
  have hNN : (N₀:ℝ) ≤ N := by exact_mod_cast hN
  have hlarge : (L:ℝ) < γ*(N:ℝ) := by
    have hh := (div_lt_iff₀ hγ).mp hN₀
    nlinarith
  have hγN : γ*(N:ℝ) ≤ Δ*(N:ℝ) :=
    mul_le_mul_of_nonneg_right hγΔ (Nat.cast_nonneg N)
  have hfirst : J+M₀ ≤ k := by
    have hL : ((J+M₀+1:ℕ):ℝ) ≤ L := by exact_mod_cast le_max_left (J+M₀+1) (2*J+2)
    have hh : ((J+M₀:ℕ):ℝ) ≤ k := by push_cast at hL ⊢; linarith
    exact_mod_cast hh
  have hsecond : 2*J+1 ≤ k := by
    have hL : ((2*J+2:ℕ):ℝ) ≤ L := by exact_mod_cast le_max_right (J+M₀+1) (2*J+2)
    have hh : ((2*J+1:ℕ):ℝ) ≤ k := by push_cast at hL ⊢; linarith
    exact_mod_cast hh
  refine ⟨by omega,?_⟩
  rw [Nat.cast_sub (by omega : J ≤ k)]
  have hh : 2*(J:ℝ)+1 ≤ k := by exact_mod_cast hsecond
  nlinarith

end Falconer

end OAI

end ExtensionScope178

/- Source: OAI.MeasureTheory.Falconer.Geometry.UniformMiddleGeometry. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope179


namespace OAI

/-! # One fixed angular coarsening works for every interval with the contact margins -/

namespace Falconer

theorem uniform_middle_geometry {σ r γ : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (hγ : 0 < γ) (H C : ℝ) (M₀ : ℕ) :
    ∃ J N₀ : ℕ, ∀ N ≥ N₀, ∀ p v : ℕ, ∀ Δ : ℝ,
      p ≤ v → γ ≤ Δ → Δ*(N:ℝ)-1 ≤ (v-p:ℕ) →
      γ*(N:ℝ) ≤ 2*(p:ℝ)-(v:ℝ) →
      let M := (v-p)-J
      J ≤ v-p ∧ M₀ ≤ M ∧ (N:ℝ)*Δ ≤ 2*(M:ℝ) ∧
      8*(1/4:ℝ)^2/((σ*(2:ℝ)^p)*r) ≤ 1/(2:ℝ)^M ∧
      ((σ*(2:ℝ)^p)*H)*(C/(2:ℝ)^v) ≤ 1/(2:ℝ)^M := by
  obtain ⟨J,hJ⟩ := Regularization.fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) (σ*H*C)
  have hC : σ*H*C ≤ (2:ℝ)^J := by simpa only [Real.rpow_one] using hJ J le_rfl
  obtain ⟨N₁,hN₁⟩ := eventually_uniform_middle_freeze hσ hr hγ
  obtain ⟨N₂,hN₂⟩ := eventually_contact_middle_depth hγ J (M₀+1)
  refine ⟨J,max N₁ N₂,?_⟩
  intro N hN p v Δ hpv hγΔ hgap hmargin
  dsimp only
  obtain ⟨hM,hwidth⟩ := hN₂ N ((le_max_right _ _).trans hN) (v-p) Δ hγΔ hgap
  have hJk : J ≤ v-p := by omega
  refine ⟨hJk,by omega,hwidth,?_,middle_width_rounding p v J hpv hJk hC⟩
  have hh := hN₁ N ((le_max_left _ _).trans hN) p v hpv hmargin
  have hδ : 1/(2:ℝ)^(v-p) ≤ 1/(2:ℝ)^((v-p)-J) :=
    one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
  norm_num only [show 8*(1/4:ℝ)^2 = 1/2 by norm_num]
  exact hh.trans hδ

end Falconer

end OAI

end ExtensionScope179

/- Source: OAI.MeasureTheory.Falconer.Measures.CellwiseCollisionPruning. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope180



namespace OAI

/-! # Combining conditional-cell radial pruning with the original source weights -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

theorem cellwise_radial_collision_pruning (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (I : Finset ι) (Q : ι → Set (Space d))
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hpos : ∀ i ∈ I, μ (Q i) ≠ 0)
    (hdisj : (I : Set ι).PairwiseDisjoint Q)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (H : ι → Set (Space d × Space d)) (hH : ∀ i ∈ I, MeasurableSet (H i))
    (δ : ℝ) (F : ι → ℝ≥0∞) (cost : ℝ≥0∞)
    (hcost : ∀ i ∈ I, ((ProbabilityTheory.cond μ (Q i)).prod ν)
      ((G ∩ (Q i ×ˢ univ)) \ H i) ≤ cost)
    (hlocal : ∀ i ∈ I, ∀ p ∈ H i,
      radialCollisionMass (ProbabilityTheory.cond μ (Q i)) δ p ≤ F i) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ cost*μ univ ∧
      ∀ i ∈ I, ∀ p ∈ G', p.1 ∈ Q i →
        radialCollisionMass (ProbabilityTheory.cond μ (Q i)) δ p ≤ F i := by
  classical
  let E := fun i => (G ∩ (Q i ×ˢ univ)) \ H i
  let D := ⋃ i ∈ I, E i ∩ (Q i ×ˢ univ)
  have hE : ∀ i ∈ I, MeasurableSet (E i) := fun i hi =>
    (hG.inter ((hQ i hi).prod MeasurableSet.univ)).diff (hH i hi)
  have hD : MeasurableSet D := Finset.measurableSet_biUnion I
    (fun i hi => (hE i hi).inter ((hQ i hi).prod MeasurableSet.univ))
  refine ⟨G \ D,hG.diff hD,sdiff_subset,?_,?_⟩
  · apply (measure_mono _).trans
      (conditional_cellwise_pair_deletion μ ν I Q E hQ hE hpos hdisj cost hcost)
    intro p hp
    by_contra hn
    exact hp.2 ⟨hp.1,hn⟩
  · intro i hi p hp hpQ
    apply hlocal i hi p
    by_contra hn
    apply hp.2
    exact mem_iUnion₂.mpr ⟨i,hi,⟨⟨⟨hp.1,hpQ,mem_univ _⟩,hn⟩,hpQ,mem_univ _⟩⟩

end Falconer

end OAI

end ExtensionScope180

/- Source: OAI.MeasureTheory.Falconer.Measures.FiniteRelativePruning. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope181


namespace OAI

/-! # Finite pruning relative to the incoming measurable relation -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {X : Type*} [MeasurableSpace X]

theorem finite_relative_pruning (μ : Measure X) (G : Set X) (hG : MeasurableSet G)
    (J : ℕ) (cost : ℕ → ℝ≥0∞) (P : ℕ → X → Prop)
    (hlocal : ∀ j < J, ∃ H : Set X, MeasurableSet H ∧ H ⊆ G ∧
      μ (G \ H) ≤ cost j ∧ ∀ x ∈ H, P j x) :
    ∃ H : Set X, MeasurableSet H ∧ H ⊆ G ∧
      μ (G \ H) ≤ ∑ j ∈ Finset.range J, cost j ∧ ∀ j < J, ∀ x ∈ H, P j x := by
  classical
  have hex : ∀ j : ℕ, ∃ H : Set X, MeasurableSet H ∧ H ⊆ G ∧
      (j < J → μ (G \ H) ≤ cost j ∧ ∀ x ∈ H, P j x) := by
    intro j
    by_cases hj : j < J
    · obtain ⟨H,hH,hHG,hcost,hP⟩ := hlocal j hj
      exact ⟨H,hH,hHG,fun _ => ⟨hcost,hP⟩⟩
    · exact ⟨G,hG,Subset.rfl,fun h => (hj h).elim⟩
  choose H hH hHG hrest using hex
  let B := ⋃ j ∈ Finset.range J, G \ H j
  have hB : MeasurableSet B := Finset.measurableSet_biUnion _ (fun j _ => hG.diff (hH j))
  refine ⟨G \ B,hG.diff hB,sdiff_subset,?_,?_⟩
  · have hsub : G \ (G \ B) ⊆ B := by
      intro x hx
      by_contra hn
      exact hx.2 ⟨hx.1,hn⟩
    apply (measure_mono hsub).trans
    apply (measure_biUnion_finset_le _ _).trans
    exact Finset.sum_le_sum (fun j hj => (hrest j (Finset.mem_range.mp hj)).1)
  · intro j hj x hx
    apply (hrest j hj).2 x
    by_contra hn
    exact hx.2 (mem_iUnion₂.mpr ⟨j,Finset.mem_range.mpr hj,⟨hx.1,hn⟩⟩)

end Falconer

end OAI

end ExtensionScope181

/- Source: OAI.MeasureTheory.Falconer.Estimates.FiniteCellwiseCollision. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope182



namespace OAI

/-! # Finite families of local collision prunings with their original cell weights -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*}

theorem cellwise_collision_pruning_of_exists (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (I : Finset ι) (Q : ι → Set (Space d))
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hpos : ∀ i ∈ I, μ (Q i) ≠ 0)
    (hdisj : (I : Set ι).PairwiseDisjoint Q)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (δ : ℝ) (F : ι → ℝ≥0∞) (cost : ℝ≥0∞)
    (hlocal : ∀ i ∈ I, ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      ((ProbabilityTheory.cond μ (Q i)).prod ν) ((G ∩ (Q i ×ˢ univ)) \ H) ≤ cost ∧
      ∀ p ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q i)) δ p ≤ F i) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ cost*μ univ ∧
      ∀ i ∈ I, ∀ p ∈ H, p.1 ∈ Q i →
        radialCollisionMass (ProbabilityTheory.cond μ (Q i)) δ p ≤ F i := by
  classical
  have hex : ∀ i, ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      (i ∈ I → ((ProbabilityTheory.cond μ (Q i)).prod ν)
        ((G ∩ (Q i ×ˢ univ)) \ H) ≤ cost ∧
        ∀ p ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q i)) δ p ≤ F i) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨H,hH,hcost,hbound⟩ := hlocal i hi
      exact ⟨H,hH,fun _ => ⟨hcost,hbound⟩⟩
    · exact ⟨∅,MeasurableSet.empty,fun h => (hi h).elim⟩
  choose H hH hrest using hex
  exact cellwise_radial_collision_pruning μ ν I Q hQ hpos hdisj G hG H (fun i _ => hH i)
    δ F cost (fun i hi => (hrest i hi).1) (fun i hi => (hrest i hi).2)

theorem finite_cellwise_collision_pruning (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (J : ℕ) (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d))
    (hQ : ∀ j < J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hpos : ∀ j < J, ∀ i ∈ I j, μ (Q j i) ≠ 0)
    (hdisj : ∀ j < J, (I j : Set ι).PairwiseDisjoint (Q j))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (δ : ℕ → ℝ) (F : ℕ → ι → ℝ≥0∞) (cost : ℕ → ℝ≥0∞)
    (hlocal : ∀ j < J, ∀ i ∈ I j, ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      ((ProbabilityTheory.cond μ (Q j i)).prod ν) ((G ∩ (Q j i ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ p ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q j i)) (δ j) p ≤ F j i) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ ∑ j ∈ Finset.range J, cost j*μ univ ∧
      ∀ j < J, ∀ i ∈ I j, ∀ p ∈ H, p.1 ∈ Q j i →
        radialCollisionMass (ProbabilityTheory.cond μ (Q j i)) (δ j) p ≤ F j i := by
  have hlevels : ∀ j < J, ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ cost j*μ univ ∧
      ∀ p ∈ H, ∀ i ∈ I j, p.1 ∈ Q j i →
        radialCollisionMass (ProbabilityTheory.cond μ (Q j i)) (δ j) p ≤ F j i := by
    intro j hj
    obtain ⟨H,hH,hHG,hcost,hbound⟩ := cellwise_collision_pruning_of_exists μ ν (I j) (Q j)
      (hQ j hj) (hpos j hj) (hdisj j hj) G hG (δ j) (F j) (cost j) (hlocal j hj)
    exact ⟨H,hH,hHG,hcost,fun p hp i hi hpQ => hbound i hi p hp hpQ⟩
  obtain ⟨H,hH,hHG,hcost,hbound⟩ := finite_relative_pruning (μ.prod ν) G hG J
    (fun j => cost j*μ univ) (fun j p => ∀ i ∈ I j, p.1 ∈ Q j i →
      radialCollisionMass (ProbabilityTheory.cond μ (Q j i)) (δ j) p ≤ F j i) hlevels
  exact ⟨H,hH,hHG,hcost,fun j hj i hi p hp hpQ => hbound j hj p hp i hi hpQ⟩

end Falconer

end OAI

end ExtensionScope182

/- Source: OAI.MeasureTheory.Falconer.Measures.DensityCellCharge. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope183


namespace OAI

/-! # Charging the full masses of hit children before the final density deletion -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X ι : Type*} [MeasurableSpace X]

theorem density_hit_children_charge (μ : Measure X) (S P T : Set X)
    (hS : MeasurableSet S) (Q : ι → Set X) (I : Finset ι)
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hdisj : (I : Set ι).PairwiseDisjoint Q)
    {θ F : ℝ≥0∞} (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hdensity : ∀ i ∈ I, θ*μ (Q i) ≤ μ (Q i ∩ S))
    (hlocal : ∀ i ∈ I, Q i ∩ S ⊆ P ∩ T)
    (htest : μ (P ∩ T) ≤ F*μ P) :
    (∑ i ∈ I, μ (Q i)) ≤ (θ⁻¹*F)*μ P := by
  have hi : (I : Set ι).PairwiseDisjoint (fun i => Q i ∩ S) := by
    intro i hi j hj hij
    exact (hdisj hi hj hij).mono inter_subset_left inter_subset_left
  have hm : θ*(∑ i ∈ I, μ (Q i)) ≤ F*μ P := by
    calc
      _ = ∑ i ∈ I, θ*μ (Q i) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ I, μ (Q i ∩ S) := Finset.sum_le_sum hdensity
      _ = μ (⋃ i ∈ I, Q i ∩ S) := (measure_biUnion_finset hi (fun i hi => (hQ i hi).inter hS)).symm
      _ ≤ μ (P ∩ T) := measure_mono (iUnion₂_subset hlocal)
      _ ≤ _ := htest
  calc
    _ = θ⁻¹*(θ*(∑ i ∈ I, μ (Q i))) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel hθ.ne' hθtop,one_mul]
    _ ≤ θ⁻¹*(F*μ P) := mul_le_mul' le_rfl hm
    _ = _ := (mul_assoc _ _ _).symm

end Falconer

end OAI

end ExtensionScope183

/- Source: OAI.MeasureTheory.Falconer.Radial.RadialCapTube. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope184


namespace OAI

/-! # Final radial caps put entire hit children in a witness's physical tube -/

namespace Falconer
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radial_cap_child_tube (x z q y u : E) {r D B : ℝ}
    (hq : q ≠ x) (hB : ‖z-x‖ ≤ B)
    (hzcap : ‖normalize (z-x)-u‖ ≤ r) (hqcap : ‖normalize (q-x)-u‖ ≤ r)
    (hy : ‖y-z‖ ≤ D) :
    ‖perpendicularPart (normalize (q-x)) (y-x)‖ ≤ D+2*B*r := by
  let v := normalize (z-x)
  let w := normalize (q-x)
  have hw : ‖w‖ = 1 := norm_normalize (sub_ne_zero.mpr hq)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hr : 0 ≤ r := (norm_nonneg _).trans hzcap
  have hclose : ‖v-w‖ ≤ 2*r := by
    have hh := norm_sub_le_norm_sub_add_norm_sub v u w
    rw [norm_sub_rev u w] at hh
    exact hh.trans (by change _ ≤ 2*r; linarith)
  have hww : perpendicularPart w w = 0 := by simp [perpendicularPart,hw]
  have hv : ‖perpendicularPart w v‖ ≤ 2*r := by
    have hh := norm_perpendicularPart_le hw (v-w)
    rw [perpendicularPart_sub,hww,sub_zero] at hh
    exact hh.trans hclose
  have hzline : ‖perpendicularPart w (z-x)‖ ≤ B*(2*r) := by
    have he : z-x = ‖z-x‖ • v := (norm_smul_normalize (z-x)).symm
    rw [he,perpendicularPart_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul hB hv (norm_nonneg _) hB0
  have he : perpendicularPart w (y-x) = perpendicularPart w (y-z)+perpendicularPart w (z-x) := by
    simp only [perpendicularPart,inner_sub_right,sub_smul]
    abel
  change ‖perpendicularPart w (y-x)‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add ((norm_perpendicularPart_le hw _).trans hy) hzline).trans_eq (by ring))

end Falconer

end OAI

end ExtensionScope184

/- Source: OAI.MeasureTheory.Falconer.Angular.CapDensityCharge. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope185




namespace OAI

/-! # A single retained cap witness charges all hit children of a parent -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

theorem cap_density_children_charge (μ : Measure (Space d))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (J j : ℕ) (hj : j ≤ J)
    (C : Finset ι) (hCI : C ⊆ I j) (P : Set (Space d)) (x u : Space d)
    {r D B : ℝ} {θ F : ℝ≥0∞} (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ i ∈ C, MeasurableSet (Q j i)) (hdisj : (C : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ i ∈ C, Q j i ⊆ P)
    (hdiam : ∀ i ∈ C, ∀ y ∈ Q j i, ∀ z ∈ Q j i, ‖y-z‖ ≤ D)
    (hhit : ∀ i ∈ C, ∃ z ∈ Q j i,
      (x,z) ∈ G \ multiscaleFiberBad μ G Q I θ J ∧
      z ≠ x ∧ ‖z-x‖ ≤ B ∧ ‖normalize (z-x)-u‖ ≤ r)
    (htest : ∀ q ∈ P, (x,q) ∈ G \ multiscaleFiberBad μ G Q I θ J →
      q ≠ x → ‖normalize (q-x)-u‖ ≤ r →
      μ (P ∩ {y | ‖perpendicularPart (normalize (q-x)) (y-x)‖ ≤ D+2*B*r}) ≤ F*μ P) :
    (∑ i ∈ C, μ (Q j i)) ≤ (θ⁻¹*F)*μ P := by
  classical
  by_cases hC : C.Nonempty
  · obtain ⟨i,hi⟩ := hC
    obtain ⟨q,hqQ,hq,hqne,_hqB,hqcap⟩ := hhit i hi
    let T : Set (Space d) := {y | ‖perpendicularPart (normalize (q-x)) (y-x)‖ ≤ D+2*B*r}
    apply density_hit_children_charge μ (Prod.mk x ⁻¹' G) P T
      (hG.preimage (by fun_prop)) (Q j) C hQ hdisj hθ hθtop
    · intro i hi
      obtain ⟨z,hzQ,hz,_hzne,_hzB,_hzcap⟩ := hhit i hi
      exact multiscaleFiber_retained μ G Q I θ J hz hj (hCI hi) hzQ
    · intro i hi y hy
      obtain ⟨z,hzQ,_hz,_hzne,hzB,hzcap⟩ := hhit i hi
      exact ⟨hparent i hi hy.1,
        radial_cap_child_tube x z q y u hqne hzB hzcap hqcap (hdiam i hi y hy.1 z hzQ)⟩
    · exact htest q (hparent i hi hqQ) hq hqne hqcap
  · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    simp only [he,Finset.sum_empty,zero_le]

end Falconer

end OAI

end ExtensionScope185

/- Source: OAI.MeasureTheory.Falconer.Measures.FiniteMassMultiplication. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope186


namespace OAI

/-! # Finite multiplication of the charged hit-cell masses -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {ι : Type*} [DecidableEq ι]

theorem finite_parent_mass_step (P C : Finset ι) (parent : ι → ι)
    (wp wc : ι → ℝ≥0∞) (F : ℝ≥0∞) (hparent : ∀ i ∈ C, parent i ∈ P)
    (hcharge : ∀ p ∈ P, (∑ i ∈ C with parent i = p, wc i) ≤ F*wp p) :
    (∑ i ∈ C, wc i) ≤ F*(∑ p ∈ P, wp p) := by
  classical
  calc
    _ = ∑ p ∈ P, ∑ i ∈ C with parent i = p, wc i :=
      (Finset.sum_fiberwise_of_maps_to hparent wc).symm
    _ ≤ ∑ p ∈ P, F*wp p := Finset.sum_le_sum hcharge
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem finite_mass_multiplication (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (w : ℕ → ι → ℝ≥0∞) (F : ℕ → ℝ≥0∞) (J : ℕ)
    (hparent : ∀ j < J, ∀ i ∈ I (j+1), parent j i ∈ I j)
    (hcharge : ∀ j < J, ∀ p ∈ I j,
      (∑ i ∈ I (j+1) with parent j i = p, w (j+1) i) ≤ F j*w j p) :
    (∑ i ∈ I J, w J i) ≤ (∏ j ∈ Finset.range J, F j)*(∑ i ∈ I 0, w 0 i) := by
  classical
  induction J with
  | zero => simp
  | succ J ih =>
    have hs : (∑ i ∈ I (J+1), w (J+1) i) ≤ F J*(∑ i ∈ I J, w J i) :=
      finite_parent_mass_step (I J) (I (J+1)) (parent J) (w J) (w (J+1)) (F J)
        (hparent J (Nat.lt_succ_self _)) (by
          intro p hp
          exact hcharge J (Nat.lt_succ_self _) p hp)
    have hprev := ih (fun j hj => hparent j (Nat.lt_succ_of_lt hj))
      (fun j hj => hcharge j (Nat.lt_succ_of_lt hj))
    calc
      _ ≤ F J*(∑ i ∈ I J, w J i) := hs
      _ ≤ F J*((∏ j ∈ Finset.range J, F j)*(∑ i ∈ I 0, w 0 i)) := mul_le_mul' le_rfl hprev
      _ = _ := by rw [Finset.prod_range_succ]; ring

end Falconer

end OAI

end ExtensionScope186

/- Source: OAI.MeasureTheory.Falconer.Angular.MultiscaleCapMass. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope187



namespace OAI

/-! # Multiplying actual physical-tube charges for one retained radial cap -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

noncomputable def retainedRadialCap (μ : Measure (Space d)) (G : Set (Space d × Space d))
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ)
    (x u : Space d) (r : ℝ) : Set (Space d) :=
  {z | (x,z) ∈ G \ multiscaleFiberBad μ G Q I θ J ∧ ‖normalize (z-x)-u‖ ≤ r}

noncomputable def radialCapHitCells (μ : Measure (Space d)) (G : Set (Space d × Space d))
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ)
    (x u : Space d) (r : ℝ) (j : ℕ) : Finset ι := by
  classical
  exact (I j).filter (fun i => ∃ z ∈ Q j i, z ∈ retainedRadialCap μ G Q I θ J x u r)

theorem multiscale_physical_cap_mass (μ : Measure (Space d))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (J : ℕ) (x u : Space d) (r B : ℝ) (D : ℕ → ℝ) (θ : ℝ≥0∞) (F : ℕ → ℝ≥0∞)
    (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ j < J, ∀ i ∈ I (j+1),
      parent j i ∈ I j ∧ Q (j+1) i ⊆ Q j (parent j i))
    (hdiam : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, ∀ z ∈ Q (j+1) i, ‖y-z‖ ≤ D j)
    (hbound : ∀ z, (x,z) ∈ G → ‖z-x‖ ≤ B)
    (hne : ∀ z, (x,z) ∈ G → z ≠ x)
    (hlocal : ∀ j < J, ∀ p ∈ I j, ∀ q ∈ Q j p, (x,q) ∈ G → q ≠ x →
      μ (Q j p ∩ {y | ‖perpendicularPart (normalize (q-x)) (y-x)‖ ≤ D j+2*B*r}) ≤ F j*μ (Q j p))
    (hcover : ∀ z ∈ retainedRadialCap μ G Q I θ J x u r, ∃ i ∈ I J, z ∈ Q J i) :
    μ (retainedRadialCap μ G Q I θ J x u r) ≤
      (∏ j ∈ Finset.range J, θ⁻¹*F j)*μ univ := by
  classical
  let H := radialCapHitCells μ G Q I θ J x u r
  have hHI (j : ℕ) : H j ⊆ I j := Finset.filter_subset _ _
  have hmem {j : ℕ} {i : ι} (hi : i ∈ H j) :
      ∃ z ∈ Q j i, z ∈ retainedRadialCap μ G Q I θ J x u r := (Finset.mem_filter.mp hi).2
  have hparents : ∀ j < J, ∀ i ∈ H (j+1), parent j i ∈ H j := by
    intro j hj i hi
    obtain ⟨z,hz,hcap⟩ := hmem hi
    obtain ⟨hp,hsub⟩ := hparent j hj i (hHI _ hi)
    exact Finset.mem_filter.mpr ⟨hp,z,hsub hz,hcap⟩
  have hcharge : ∀ j < J, ∀ p ∈ H j,
      (∑ i ∈ H (j+1) with parent j i = p, μ (Q (j+1) i)) ≤
        (θ⁻¹*F j)*μ (Q j p) := by
    intro j hj p hp
    let C := (H (j+1)).filter (fun i => parent j i = p)
    have hCI : C ⊆ I (j+1) := fun i hi => hHI _ (Finset.mem_filter.mp hi).1
    have hCQ : ∀ i ∈ C, Q (j+1) i ⊆ Q j p := by
      intro i hi
      have hs := (hparent j hj i (hCI hi)).2
      rwa [(Finset.mem_filter.mp hi).2] at hs
    have hCdisj : (C : Set ι).PairwiseDisjoint (Q (j+1)) := by
      intro i hi k hk hne
      exact hdisj (j+1) (by omega) (hCI hi) (hCI hk) hne
    have hh := cap_density_children_charge μ G hG Q I J (j+1) (by omega)
      C hCI (Q j p) x u hθ hθtop
      (fun i hi => hQ (j+1) (by omega) i (hCI hi)) hCdisj hCQ
      (fun i hi => hdiam j hj i (hCI hi))
      (fun i hi => by
        obtain ⟨z,hz,hcap⟩ := hmem (Finset.mem_filter.mp hi).1
        exact ⟨z,hz,hcap.1,hne z hcap.1.1,hbound z hcap.1.1,hcap.2⟩)
      (fun q hqp hq hqn _ => hlocal j hj p (hHI _ hp) q hqp hq.1 hqn)
    exact hh
  have hmul := finite_mass_multiplication H parent (fun j i => μ (Q j i))
    (fun j => θ⁻¹*F j) J hparents hcharge
  have hsub : retainedRadialCap μ G Q I θ J x u r ⊆ ⋃ i ∈ H J, Q J i := by
    intro z hz
    obtain ⟨i,hi,hzi⟩ := hcover z hz
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hi,z,hzi,hz⟩,hzi⟩⟩
  have hzero : (∑ i ∈ H 0, μ (Q 0 i)) ≤ μ univ := by
    rw [← measure_biUnion_finset (fun i hi k hk hik =>
      hdisj 0 (Nat.zero_le _) (hHI _ hi) (hHI _ hk) hik)
      (fun i hi => hQ 0 (Nat.zero_le _) i (hHI _ hi))]
    exact measure_mono (subset_univ _)
  calc
    _ ≤ μ (⋃ i ∈ H J, Q J i) := measure_mono hsub
    _ ≤ ∑ i ∈ H J, μ (Q J i) := measure_biUnion_finset_le _ _
    _ ≤ (∏ j ∈ Finset.range J, θ⁻¹*F j)*(∑ i ∈ H 0, μ (Q 0 i)) := hmul
    _ ≤ _ := mul_le_mul' le_rfl hzero

end Falconer

end OAI

end ExtensionScope187

/- Source: OAI.MeasureTheory.Falconer.Radial.RadialCapCollision. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope188


namespace OAI

/-! # A hit child lies in a slightly enlarged radial collision ball -/

namespace Falconer
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radial_cap_child_distance (x z q y u : E) {r D s : ℝ}
    (hs : 0 < s) (hyx : s ≤ ‖y-x‖) (hzx : z ≠ x)
    (hzcap : ‖normalize (z-x)-u‖ ≤ r) (hqcap : ‖normalize (q-x)-u‖ ≤ r)
    (hyz : ‖y-z‖ ≤ D) :
    dist (normalize (y-x)) (normalize (q-x)) ≤ 2*D/s+2*r := by
  have hnear : dist (normalize (y-x)) (normalize (z-x)) ≤ 2*D/s := by
    apply (le_div_iff₀ hs).mpr
    have hh := normalize_distance_scaled hyx (sub_ne_zero.mpr hzx)
    simp only [dist_eq_norm,sub_sub_sub_cancel_right] at hh ⊢
    nlinarith
  have hcap : dist (normalize (z-x)) (normalize (q-x)) ≤ 2*r := by
    rw [dist_eq_norm]
    have hh := norm_sub_le_norm_sub_add_norm_sub (normalize (z-x)) u (normalize (q-x))
    rw [norm_sub_rev u] at hh
    linarith
  exact (dist_triangle _ _ _).trans (add_le_add hnear hcap)

end Falconer

end OAI

end ExtensionScope188

/- Source: OAI.MeasureTheory.Falconer.Measures.CollisionDensityCharge. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope189




namespace OAI

/-! # Original fiber densities multiply local radial collision tests -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

theorem collision_density_children_charge (μ : Measure (Space d))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (J j : ℕ) (hj : j ≤ J)
    (C : Finset ι) (hCI : C ⊆ I j) (P : Set (Space d)) (x u : Space d)
    {r D s : ℝ} {θ F : ℝ≥0∞} (hs : 0 < s) (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ i ∈ C, MeasurableSet (Q j i)) (hdisj : (C : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ i ∈ C, Q j i ⊆ P)
    (hdiam : ∀ i ∈ C, ∀ y ∈ Q j i, ∀ z ∈ Q j i, ‖y-z‖ ≤ D)
    (hsep : ∀ i ∈ C, ∀ y ∈ Q j i, s ≤ ‖y-x‖)
    (hhit : ∀ i ∈ C, ∃ z ∈ Q j i,
      (x,z) ∈ G \ multiscaleFiberBad μ G Q I θ J ∧ ‖normalize (z-x)-u‖ ≤ r)
    (htest : ∀ q ∈ P, (x,q) ∈ G \ multiscaleFiberBad μ G Q I θ J →
      ‖normalize (q-x)-u‖ ≤ r →
      μ (P ∩ {y | dist (normalize (y-x)) (normalize (q-x)) ≤ 2*D/s+2*r}) ≤ F*μ P) :
    (∑ i ∈ C, μ (Q j i)) ≤ (θ⁻¹*F)*μ P := by
  classical
  by_cases hC : C.Nonempty
  · obtain ⟨i,hi⟩ := hC
    obtain ⟨q,hqQ,hq,hqcap⟩ := hhit i hi
    let T : Set (Space d) := {y | dist (normalize (y-x)) (normalize (q-x)) ≤ 2*D/s+2*r}
    apply density_hit_children_charge μ (Prod.mk x ⁻¹' G) P T
      (hG.preimage (by fun_prop)) (Q j) C hQ hdisj hθ hθtop
    · intro i hi
      obtain ⟨z,hzQ,hz,_⟩ := hhit i hi
      exact multiscaleFiber_retained μ G Q I θ J hz hj (hCI hi) hzQ
    · intro i hi y hy
      obtain ⟨z,hzQ,_hz,hzcap⟩ := hhit i hi
      have hzx : z ≠ x := by
        intro he
        have hh := hsep i hi z hzQ
        rw [he,sub_self,norm_zero] at hh
        linarith
      exact ⟨hparent i hi hy.1,radial_cap_child_distance x z q y u hs
        (hsep i hi y hy.1) hzx hzcap hqcap (hdiam i hi y hy.1 z hzQ)⟩
    · exact htest q (hparent i hi hqQ) hq hqcap
  · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    simp only [he,Finset.sum_empty,zero_le]

end Falconer

end OAI

end ExtensionScope189

/- Source: OAI.MeasureTheory.Falconer.Measures.MultiscaleCollisionMass. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope190



namespace OAI

/-! # Multiplying full conditional radial collision bounds over a source tree -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem multiscale_collision_cap_mass (μ : Measure (Space d))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (J : ℕ) (x u : Space d) (r s : ℝ) (D : ℕ → ℝ) (θ : ℝ≥0∞) (F : ℕ → ℝ≥0∞)
    (hs : 0 < s) (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ j < J, ∀ i ∈ I (j+1),
      parent j i ∈ I j ∧ Q (j+1) i ⊆ Q j (parent j i))
    (hdiam : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, ∀ z ∈ Q (j+1) i, ‖y-z‖ ≤ D j)
    (hsep : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, s ≤ ‖y-x‖)
    (hlocal : ∀ j < J, ∀ p ∈ I j, ∀ q ∈ Q j p, (x,q) ∈ G →
      μ (Q j p ∩ {y | dist (normalize (y-x)) (normalize (q-x)) ≤ 2*D j/s+2*r}) ≤
        F j*μ (Q j p))
    (hcover : ∀ z ∈ retainedRadialCap μ G Q I θ J x u r, ∃ i ∈ I J, z ∈ Q J i) :
    μ (retainedRadialCap μ G Q I θ J x u r) ≤
      (∏ j ∈ Finset.range J, θ⁻¹*F j)*μ univ := by
  classical
  let H := radialCapHitCells μ G Q I θ J x u r
  have hHI (j : ℕ) : H j ⊆ I j := Finset.filter_subset _ _
  have hmem {j : ℕ} {i : ι} (hi : i ∈ H j) :
      ∃ z ∈ Q j i, z ∈ retainedRadialCap μ G Q I θ J x u r := (Finset.mem_filter.mp hi).2
  have hparents : ∀ j < J, ∀ i ∈ H (j+1), parent j i ∈ H j := by
    intro j hj i hi
    obtain ⟨z,hz,hcap⟩ := hmem hi
    obtain ⟨hp,hsub⟩ := hparent j hj i (hHI _ hi)
    exact Finset.mem_filter.mpr ⟨hp,z,hsub hz,hcap⟩
  have hcharge : ∀ j < J, ∀ p ∈ H j,
      (∑ i ∈ H (j+1) with parent j i = p, μ (Q (j+1) i)) ≤
        (θ⁻¹*F j)*μ (Q j p) := by
    intro j hj p hp
    let C := (H (j+1)).filter (fun i => parent j i = p)
    have hCI : C ⊆ I (j+1) := fun i hi => hHI _ (Finset.mem_filter.mp hi).1
    have hCQ : ∀ i ∈ C, Q (j+1) i ⊆ Q j p := by
      intro i hi
      have hs := (hparent j hj i (hCI hi)).2
      rwa [(Finset.mem_filter.mp hi).2] at hs
    have hCdisj : (C : Set ι).PairwiseDisjoint (Q (j+1)) := by
      intro i hi k hk hne
      exact hdisj (j+1) (by omega) (hCI hi) (hCI hk) hne
    have hh := collision_density_children_charge μ G hG Q I J (j+1) (by omega)
      C hCI (Q j p) x u hs hθ hθtop
      (fun i hi => hQ (j+1) (by omega) i (hCI hi)) hCdisj hCQ
      (fun i hi => hdiam j hj i (hCI hi))
      (fun i hi => hsep j hj i (hCI hi))
      (fun i hi => by
        obtain ⟨z,hz,hcap⟩ := hmem (Finset.mem_filter.mp hi).1
        exact ⟨z,hz,hcap.1,hcap.2⟩)
      (fun q hqp hq _ => hlocal j hj p (hHI _ hp) q hqp hq.1)
    exact hh
  have hmul := finite_mass_multiplication H parent (fun j i => μ (Q j i))
    (fun j => θ⁻¹*F j) J hparents hcharge
  have hsub : retainedRadialCap μ G Q I θ J x u r ⊆ ⋃ i ∈ H J, Q J i := by
    intro z hz
    obtain ⟨i,hi,hzi⟩ := hcover z hz
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hi,z,hzi,hz⟩,hzi⟩⟩
  have hzero : (∑ i ∈ H 0, μ (Q 0 i)) ≤ μ univ := by
    rw [← measure_biUnion_finset (fun i hi k hk hik =>
      hdisj 0 (Nat.zero_le _) (hHI _ hi) (hHI _ hk) hik)
      (fun i hi => hQ 0 (Nat.zero_le _) i (hHI _ hi))]
    exact measure_mono (subset_univ _)
  calc
    _ ≤ μ (⋃ i ∈ H J, Q J i) := measure_mono hsub
    _ ≤ ∑ i ∈ H J, μ (Q J i) := measure_biUnion_finset_le _ _
    _ ≤ (∏ j ∈ Finset.range J, θ⁻¹*F j)*(∑ i ∈ H 0, μ (Q 0 i)) := hmul
    _ ≤ _ := mul_le_mul' le_rfl hzero

end Falconer

end OAI

end ExtensionScope190

/- Source: OAI.MeasureTheory.Falconer.Measures.CollisionPruningMultiplication. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope191




namespace OAI

/-! # Multiplying conditional-source radial estimates at retained original witnesses -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem conditional_radial_collision_test (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (P : Set (Space d)) (hP : MeasurableSet P) (x z : Space d) (r : ℝ) (F : ℝ≥0∞)
    (h : radialCollisionMass (ProbabilityTheory.cond μ P) r (z,x) ≤ F) :
    μ (P ∩ {y | dist (normalize (y-x)) (normalize (z-x)) ≤ r}) ≤ F*μ P := by
  rw [← ProbabilityTheory.cond_mul_eq_inter hP _ μ]
  exact mul_le_mul' h le_rfl

theorem radial_collision_pruning_multiplication (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (J : ℕ) (D W : ℕ → ℝ) (r s : ℝ) (θ : ℝ≥0∞) (F : ℕ → ℝ≥0∞)
    (hs : 0 < s) (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ j < J, ∀ i ∈ I (j+1),
      parent j i ∈ I j ∧ Q (j+1) i ⊆ Q j (parent j i))
    (hdiam : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, ∀ z ∈ Q (j+1) i, ‖y-z‖ ≤ D j)
    (hsep : ∀ x, (∃ z, (x,z) ∈ G) → ∀ j < J, ∀ i ∈ I (j+1),
      ∀ y ∈ Q (j+1) i, s ≤ ‖y-x‖)
    (hwidth : ∀ j < J, 2*D j/s+2*r ≤ W j)
    (hlocal : ∀ j < J, ∀ p ∈ I j, ∀ x z, (x,z) ∈ G → z ∈ Q j p →
      radialCollisionMass (ProbabilityTheory.cond μ (Q j p)) (W j) (z,x) ≤ F j)
    (hcover : ∀ x z, (x,z) ∈ G → ∃ i ∈ I J, z ∈ Q J i) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (ν.prod μ) (G \ G') ≤ (J+1:ℝ≥0∞)*(θ*μ univ)*ν univ ∧
      ∀ x u : Space d,
        μ {z | (x,z) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ r} ≤
          (∏ j ∈ Finset.range J, θ⁻¹*F j)*μ univ := by
  let Bad := multiscaleFiberBad μ G Q I θ J
  have hBad : MeasurableSet Bad := multiscaleFiberBad_measurable μ G hG Q I θ J hQ
  let G' := G \ Bad
  have hG' : MeasurableSet G' := hG.diff hBad
  refine ⟨G',hG',sdiff_subset,?_,?_⟩
  · apply (measure_mono _).trans (multiscaleFiberBad_mass ν μ G hG Q I J hQ hdisj θ)
    intro p hp
    by_contra hb
    exact hp.2 ⟨hp.1,hb⟩
  · intro x u
    by_cases hx : ∃ z, (x,z) ∈ G
    · apply multiscale_collision_cap_mass μ G hG Q I parent J x u r s D θ F hs hθ hθtop
        hQ hdisj hparent hdiam (hsep x hx)
      · intro j hj p hp z hz hzg
        apply (measure_mono _).trans
          (conditional_radial_collision_test μ (Q j p) (hQ j hj.le p hp) x z (W j) (F j)
            (hlocal j hj p hp x z hzg hz))
        rintro y ⟨hy,hclose⟩
        exact ⟨hy,hclose.trans (hwidth j hj)⟩
      · intro z hz
        exact hcover x z hz.1.1
    · have he : {z | (x,z) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ r} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hx ⟨z,hz.1.1⟩
      rw [he,measure_empty]
      exact zero_le

end Falconer

end OAI

end ExtensionScope191

/- Source: OAI.MeasureTheory.Falconer.Estimates.SourceCollisionMultiplication. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope192


namespace OAI

/-! # The radial multiplication theorem in source-first original-pair coordinates -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem source_collision_pruning_multiplication (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (J : ℕ) (D W : ℕ → ℝ) (r s : ℝ) (θ : ℝ≥0∞) (F : ℕ → ℝ≥0∞)
    (hs : 0 < s) (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ j < J, ∀ i ∈ I (j+1),
      parent j i ∈ I j ∧ Q (j+1) i ⊆ Q j (parent j i))
    (hdiam : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, ∀ z ∈ Q (j+1) i, ‖y-z‖ ≤ D j)
    (hsep : ∀ x, (∃ z, (z,x) ∈ G) → ∀ j < J, ∀ i ∈ I (j+1),
      ∀ y ∈ Q (j+1) i, s ≤ ‖y-x‖)
    (hwidth : ∀ j < J, 2*D j/s+2*r ≤ W j)
    (hlocal : ∀ j < J, ∀ p ∈ I j, ∀ z x, (z,x) ∈ G → z ∈ Q j p →
      radialCollisionMass (ProbabilityTheory.cond μ (Q j p)) (W j) (z,x) ≤ F j)
    (hcover : ∀ z x, (z,x) ∈ G → ∃ i ∈ I J, z ∈ Q J i) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ (J+1:ℝ≥0∞)*(θ*μ univ)*ν univ ∧
      ∀ x u : Space d,
        μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ r} ≤
          (∏ j ∈ Finset.range J, θ⁻¹*F j)*μ univ := by
  let Gs := Prod.swap ⁻¹' G
  have hGs : MeasurableSet Gs := hG.preimage measurable_swap
  obtain ⟨H,hH,hHG,hdel,hcap⟩ := radial_collision_pruning_multiplication μ ν Gs hGs
    Q I parent J D W r s θ F hs hθ hθtop hQ hdisj hparent hdiam hsep hwidth
    (fun j hj p hp x z hx hz => hlocal j hj p hp z x hx hz) (fun x z hx => hcover z x hx)
  refine ⟨Prod.swap ⁻¹' H,hH.preimage measurable_swap,fun p hp => hHG hp,?_,?_⟩
  · have he : G \ Prod.swap ⁻¹' H = Prod.swap ⁻¹' (Gs \ H) := by
      ext p
      simp only [mem_sdiff,mem_preimage,Gs,Prod.swap_swap]
    rw [he,← Measure.map_apply measurable_swap (hGs.diff hH),Measure.prod_swap]
    exact hdel
  · exact hcap

end Falconer

end OAI

end ExtensionScope192

/- Source: OAI.MeasureTheory.Falconer.Measures.LocalPruningGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope193



namespace OAI

/-! # Original cellwise deletions followed by radial density multiplication -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem radial_gain_of_local_prunings (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [SFinite ν]
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (J : ℕ) (D W : ℕ → ℝ) (r s : ℝ) (θ : ℝ≥0∞) (F cost : ℕ → ℝ≥0∞)
    (hs : 0 < s) (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hpos : ∀ j < J, ∀ i ∈ I j, μ (Q j i) ≠ 0)
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ j < J, ∀ i ∈ I (j+1),
      parent j i ∈ I j ∧ Q (j+1) i ⊆ Q j (parent j i))
    (hdiam : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, ∀ z ∈ Q (j+1) i, ‖y-z‖ ≤ D j)
    (hsep : ∀ x, (∃ z, (z,x) ∈ G) → ∀ j < J, ∀ i ∈ I (j+1),
      ∀ y ∈ Q (j+1) i, s ≤ ‖y-x‖)
    (hwidth : ∀ j < J, 2*D j/s+2*r ≤ W j)
    (hlocal : ∀ j < J, ∀ i ∈ I j, ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      ((ProbabilityTheory.cond μ (Q j i)).prod ν) ((G ∩ (Q j i ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ p ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q j i)) (W j) p ≤ F j)
    (hcover : ∀ z x, (z,x) ∈ G → ∃ i ∈ I J, z ∈ Q J i) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ (∑ j ∈ Finset.range J, cost j*μ univ)+
        (J+1:ℝ≥0∞)*(θ*μ univ)*ν univ ∧
      ∀ x u : Space d,
        μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ r} ≤
          (∏ j ∈ Finset.range J, θ⁻¹*F j)*μ univ := by
  obtain ⟨H,hH,hHG,hdel,hbound⟩ := finite_cellwise_collision_pruning μ ν J I Q
    (fun j hj => hQ j hj.le) hpos (fun j hj => hdisj j hj.le) G hG W
    (fun j _ => F j) cost hlocal
  obtain ⟨G',hG',hsub,hdel',hcap⟩ := source_collision_pruning_multiplication μ ν H hH
    Q I parent J D W r s θ F hs hθ hθtop hQ hdisj hparent hdiam
    (fun x hx => hsep x (by obtain ⟨z,hz⟩ := hx; exact ⟨z,hHG hz⟩)) hwidth
    (fun j hj i hi z x hz hzi => hbound j hj i hi (z,x) hz hzi)
    (fun z x hz => hcover z x (hHG hz))
  refine ⟨G',hG',hsub.trans hHG,?_,hcap⟩
  have hdiff : G \ G' ⊆ (G \ H) ∪ (H \ G') := by
    intro p hp
    by_cases hpH : p ∈ H
    · exact Or.inr ⟨hpH,hp.2⟩
    · exact Or.inl ⟨hp.1,hpH⟩
  exact (measure_mono hdiff).trans ((measure_union_le _ _).trans (add_le_add hdel hdel'))

end Falconer

end OAI

end ExtensionScope193

/- Source: OAI.MeasureTheory.Falconer.Geometry.OccupiedCellSeparation. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope194


namespace OAI

/-! # Separation extends from the full source set to sufficiently small occupied cells -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem exists_mem_cell_source (μ : Measure (Space d)) (A C : Set (Space d))
    (hA : μ Aᶜ = 0) (hC : 0 < μ C) : ∃ z ∈ C, z ∈ A := by
  by_contra hn
  have hsub : C ⊆ Aᶜ := by
    intro z hz hzA
    exact hn ⟨z,hz,hzA⟩
  exact (not_le_of_gt hC) ((measure_mono hsub).trans_eq hA)

theorem occupied_cell_separation (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (A B : Set (Space d)) (hA : μ Aᶜ = 0)
    {s : ℝ} (hsep : ∀ z ∈ A, ∀ x ∈ B, s ≤ ‖z-x‖)
    {n : ℕ} (hsmall : Real.sqrt d*(Q.side/(2:ℝ)^n) ≤ s/2)
    {P : List (Fin d → Bool)} (hP : P ∈ Q.occupiedPaths μ n) :
    ∀ x ∈ B, ∀ y ∈ (Q.descendant P).carrier, s/2 ≤ ‖y-x‖ := by
  obtain ⟨z,hz,hzA⟩ := exists_mem_cell_source μ A (Q.descendant P).carrier hA
    (Finset.mem_filter.mp hP).2
  intro x hx y hy
  have hd := Q.occupied_diameter_bound hQ μ hP hz hy
  have ht := norm_sub_le_norm_sub_add_norm_sub z y x
  have hs := hsep z hzA x hx
  linarith

theorem occupied_cell_center_separation (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (A B : Set (Space d)) (hA : μ Aᶜ = 0)
    {s : ℝ} (hsep : ∀ z ∈ A, ∀ x ∈ B, s ≤ ‖z-x‖)
    {n : ℕ} (hsmall : Real.sqrt d*(Q.side/(2:ℝ)^n) ≤ s/2)
    {P : List (Fin d → Bool)} (hP : P ∈ Q.occupiedPaths μ n) :
    ∀ x ∈ B, s/2 ≤ ‖(Q.descendant P).center-x‖ := by
  intro x hx
  exact occupied_cell_separation Q hQ μ A B hA hsep hsmall hP x hx _
    ((Q.descendant P).center_mem (Q.descendant_side_pos hQ P))

end Falconer

end OAI

end ExtensionScope194

/- Source: OAI.MeasureTheory.Falconer.Estimates.DyadicLocalGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope195



namespace OAI

/-! # Applying local radial collision prunings on the actual occupied dyadic tree -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem dyadic_gain_of_local_prunings (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : DyadicCube d) (hQ : 0 < Q.side) (N J : ℕ) (depth : ℕ → ℕ)
    (hdepth : ∀ j ≤ J, depth j ≤ N) (hmono : ∀ j < J, depth j ≤ depth (j+1))
    (A P : Set (Space d)) (hA : μ Aᶜ = 0) {s : ℝ} (hs : 0 < s)
    (hsep : ∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (hGcore : G ⊆ Q.occupiedTreeCore μ N ×ˢ P)
    (r : ℝ) (W : ℕ → ℝ) (θ : ℝ≥0∞) (F cost : ℕ → ℝ≥0∞)
    (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hsmall : ∀ j < J, Real.sqrt d*(Q.side/(2:ℝ)^depth (j+1)) ≤ s/2)
    (hwidth : ∀ j < J, 2*(Real.sqrt d*(Q.side/(2:ℝ)^depth (j+1)))/(s/2)+2*r ≤ W j)
    (hlocal : ∀ j < J, ∀ p ∈ Q.occupiedPaths μ (depth j),
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      ((ProbabilityTheory.cond μ (Q.descendant p).carrier).prod ν)
        ((G ∩ ((Q.descendant p).carrier ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ z ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q.descendant p).carrier)
        (W j) z ≤ F j) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ (∑ j ∈ Finset.range J, cost j)+(J+1:ℝ≥0∞)*θ ∧
      ∀ x u : Space d, μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ r} ≤
        ∏ j ∈ Finset.range J, θ⁻¹*F j := by
  have hpos : ∀ j < J, ∀ p ∈ Q.occupiedPaths μ (depth j),
      μ (Q.descendant p).carrier ≠ 0 := fun _ _ _ hp => (Finset.mem_filter.mp hp).2.ne'
  have hdisj : ∀ j ≤ J, (Q.occupiedPaths μ (depth j) : Set (List (Fin d → Bool))).PairwiseDisjoint
      (fun p => (Q.descendant p).carrier) := by
    intro j _ p hp q hq hpq
    exact Q.descendants_disjoint
      (((mem_cubePaths d (depth j) p).mp (Finset.mem_filter.mp hp).1).trans
        ((mem_cubePaths d (depth j) q).mp (Finset.mem_filter.mp hq).1).symm) hpq
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := radial_gain_of_local_prunings μ ν G hG
    (fun _ p => (Q.descendant p).carrier) (fun j => Q.occupiedPaths μ (depth j))
    (fun j p => p.take (depth j)) J
    (fun j => Real.sqrt d*(Q.side/(2:ℝ)^depth (j+1))) W r (s/2) θ F cost
    (by positivity) hθ hθtop (fun _ _ p _ => (Q.descendant p).measurable) hpos hdisj
    (fun j hj _ hp => Q.occupied_parent hQ μ (hmono j hj) hp)
    (fun _ _ _ hp _ hy _ hz => Q.occupied_diameter_bound hQ μ hp hy hz)
    (fun x hx j hj p hp y hy => occupied_cell_separation Q hQ μ A P hA hsep
      (hsmall j hj) hp x (by obtain ⟨z,hz⟩ := hx; exact (hGcore hz).2) y hy)
    hwidth hlocal
    (fun z x hz => Q.occupiedTreeCore_cover μ (hdepth J le_rfl) (hGcore hz).1)
  refine ⟨G',hG',hsub,?_,?_⟩
  · simpa only [measure_univ,mul_one] using hdel
  · intro x u
    simpa only [measure_univ,mul_one] using hbound x u

end Falconer

end OAI

end ExtensionScope195

/- Source: OAI.MeasureTheory.Falconer.Recursion.ThreeIntervalPower. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope196



namespace OAI

/-! # The gain on the middle interval absorbs all three density losses -/

namespace Falconer
open scoped ENNReal

theorem three_interval_radial_power (g₀ g₁ g₂ N : ℕ) (hsum : g₀+g₁+g₂ = N)
    {q c β γ e₀ e₂ η : ℝ} (hc : 0 ≤ c)
    (hwidth : β*(N:ℝ) ≤ g₁) (hbudget : e₀+e₂+3*η+γ ≤ c*β) :
    ((2:ℝ)^N)^(e₀+e₂+3*η)*((2:ℝ)^g₀)^(-q)*
      ((2:ℝ)^g₁)^(-q-c)*((2:ℝ)^g₂)^(-q) ≤ ((2:ℝ)^N)^(-q-γ) := by
  have hp (n : ℕ) (t : ℝ) : ((2:ℝ)^n)^t = (2:ℝ)^((n:ℝ)*t) :=
    (Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) n t).symm
  simp_rw [hp,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  have hn : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hsum' : (g₀:ℝ)+g₁+g₂ = N := by exact_mod_cast hsum
  nlinarith [congrArg (fun z : ℝ => z*q) hsum',
    mul_le_mul_of_nonneg_left hbudget hn,mul_le_mul_of_nonneg_left hwidth hc]

end Falconer

end OAI

end ExtensionScope196

/- Source: OAI.MeasureTheory.Falconer.Recursion.ThreeIntervalShift. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope197



namespace OAI

/-! # The three-interval gain with a fixed coarsening of the middle radial scale -/

namespace Falconer

theorem three_interval_shifted_power {a b N J : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    (hJ : J ≤ b-a) {q c β γ η ξ : ℝ} (hc : 0 ≤ c)
    (hwidth : β*(N:ℝ) ≤ (b-a:ℕ))
    (hconst : ((2:ℝ)^J)^(q+c) ≤ ((2:ℝ)^N)^ξ)
    (hbudget : 20*η+4*ξ+γ ≤ c*β) :
    ((2:ℝ)^N)^(20*η+3*ξ)*((2:ℝ)^a)^(-q)*
      (1/(2:ℝ)^((b-a)-J))^(q+c)*((2:ℝ)^(N-b))^(-q) ≤
        ((2:ℝ)^N)^(-q-γ) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  have hmid : (1/(2:ℝ)^((b-a)-J))^(q+c) =
      ((2:ℝ)^J)^(q+c)*((2:ℝ)^(b-a))^(-q-c) := by
    rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity)]
    have hh := dyadic_shifted_decay (g := 0) (v := b-a) (by simpa using hJ) (q+c)
    simpa only [Nat.sub_zero,zero_add,neg_add_rev,sub_eq_add_neg,add_comm] using hh
  rw [hmid]
  calc
    _ ≤ ((2:ℝ)^N)^(20*η+3*ξ)*((2:ℝ)^a)^(-q)*
        (((2:ℝ)^N)^ξ*((2:ℝ)^(b-a))^(-q-c))*((2:ℝ)^(N-b))^(-q) := by
      gcongr
    _ = ((2:ℝ)^N)^(10*η+(10*η+ξ)+3*ξ)*((2:ℝ)^a)^(-q)*
        ((2:ℝ)^(b-a))^(-q-c)*((2:ℝ)^(N-b))^(-q) := by
      conv_rhs => rw [show 10*η+(10*η+ξ)+3*ξ = (20*η+3*ξ)+ξ by ring,Real.rpow_add hR]
      ring
    _ ≤ _ := three_interval_radial_power a (b-a) (N-b) N (by omega) hc hwidth (by linarith)

theorem three_interval_relative_budget {L τ Δ gain γ : ℝ}
    (hΔ : 0 ≤ Δ) (hγ : γ ≤ Δ) (hgain : 0 ≤ gain)
    (hsmall : (20*L+4)*τ ≤ gain/8) :
    20*(L*τ*Δ)+4*(τ*Δ)+(gain*γ/8) ≤ (gain/2)*(Δ/2) := by
  have hscaled := mul_le_mul_of_nonneg_right hsmall hΔ
  have hmargin := mul_le_mul_of_nonneg_left hγ hgain
  nlinarith

end Falconer

end OAI

end ExtensionScope197

/- Source: OAI.MeasureTheory.Falconer.Recursion.ThreeIntervalProduct. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope198



namespace OAI

/-! # The actual three conditional factors, including the density penalties -/

namespace Falconer
open scoped ENNReal

theorem three_density_factor_product {R A B C η ξ : ℝ} (hR : 0 < R)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hC : 0 ≤ C) :
    ((ENNReal.ofReal (R^(-ξ)))⁻¹*ENNReal.ofReal (R^(10*η)*A))*
      ((ENNReal.ofReal (R^(-ξ)))⁻¹*ENNReal.ofReal B)*
      ((ENNReal.ofReal (R^(-ξ)))⁻¹*ENNReal.ofReal (R^(10*η)*C)) =
      ENNReal.ofReal (R^(20*η+3*ξ)*A*B*C) := by
  have hi : (ENNReal.ofReal (R^(-ξ)))⁻¹ = ENNReal.ofReal (R^ξ) := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity),Real.rpow_neg hR.le,inv_inv]
  rw [hi]
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hp : R^ξ*R^(10*η)*R^ξ*R^ξ*R^(10*η) = R^(20*η+3*ξ) := by
    rw [← Real.rpow_add hR,← Real.rpow_add hR,← Real.rpow_add hR,← Real.rpow_add hR]
    congr 1
    ring
  calc
    _ = (R^ξ*R^(10*η)*R^ξ*R^ξ*R^(10*η))*A*B*C := by ring
    _ = _ := by rw [hp]

theorem three_interval_density_product_bound {a b N J : ℕ}
    (hab : a ≤ b) (hbN : b ≤ N) (hJ : J ≤ b-a)
    {q c β γ η ξ : ℝ} (hc : 0 ≤ c)
    (hwidth : β*(N:ℝ) ≤ (b-a:ℕ))
    (hconst : ((2:ℝ)^J)^(q+c) ≤ ((2:ℝ)^N)^ξ)
    (hbudget : 20*η+4*ξ+γ ≤ c*β) :
    ((ENNReal.ofReal (((2:ℝ)^N)^(-ξ)))⁻¹*
        ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^a)^(-q)))*
      ((ENNReal.ofReal (((2:ℝ)^N)^(-ξ)))⁻¹*
        ENNReal.ofReal ((1/(2:ℝ)^((b-a)-J))^(q+c)))*
      ((ENNReal.ofReal (((2:ℝ)^N)^(-ξ)))⁻¹*
        ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^(N-b))^(-q))) ≤
      ENNReal.ofReal (((2:ℝ)^N)^(-q-γ)) := by
  rw [three_density_factor_product (by positivity) (by positivity) (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (three_interval_shifted_power hab hbN hJ hc hwidth hconst hbudget)

end Falconer

end OAI

end ExtensionScope198

/- Source: OAI.MeasureTheory.Falconer.Recursion.ThreeIntervalData. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope199



namespace OAI

/-! # The actual four dyadic depths and three collision factors -/

namespace Falconer
open scoped ENNReal BigOperators

def threeIntervalDepth (a b N j : ℕ) : ℕ :=
  if j = 0 then 0 else if j = 1 then a else if j = 2 then b else N

theorem threeIntervalDepth_le {a b N : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {j : ℕ} (hj : j ≤ 3) : threeIntervalDepth a b N j ≤ N := by
  interval_cases j <;> norm_num [threeIntervalDepth] <;> omega

theorem threeIntervalDepth_mono {a b N : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {j : ℕ} (hj : j < 3) : threeIntervalDepth a b N j ≤ threeIntervalDepth a b N (j+1) := by
  interval_cases j <;> norm_num [threeIntervalDepth] <;> assumption

theorem threeIntervalDepth_child {a b N : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {j : ℕ} (hj : j < 3) : a ≤ threeIntervalDepth a b N (j+1) := by
  interval_cases j <;> norm_num [threeIntervalDepth] <;> omega

noncomputable def threeIntervalFactor (a b N J : ℕ) (q c η : ℝ) (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^a)^(-q))
  else if j = 1 then ENNReal.ofReal ((1/(2:ℝ)^((b-a)-J))^(q+c))
  else ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^(N-b))^(-q))

theorem threeIntervalFactor_product {a b N J : ℕ}
    (hab : a ≤ b) (hbN : b ≤ N) (hJ : J ≤ b-a)
    {q c β γ η ξ : ℝ} (hc : 0 ≤ c)
    (hwidth : β*(N:ℝ) ≤ (b-a:ℕ))
    (hconst : ((2:ℝ)^J)^(q+c) ≤ ((2:ℝ)^N)^ξ)
    (hbudget : 20*η+4*ξ+γ ≤ c*β) :
    (∏ j ∈ Finset.range 3, (ENNReal.ofReal (((2:ℝ)^N)^(-ξ)))⁻¹*
      threeIntervalFactor a b N J q c η j) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-q-γ)) := by
  simpa [Finset.prod_range_succ,threeIntervalFactor] using
    three_interval_density_product_bound hab hbN hJ hc hwidth hconst hbudget

end Falconer

end OAI

end ExtensionScope199

/- Source: OAI.MeasureTheory.Falconer.Recursion.ThreeIntervalDyadicGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope200



namespace OAI

/-! # The three-interval cap gain on the actual occupied source tree -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem three_interval_dyadic_gain (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : DyadicCube d) (hQ : 0 < Q.side) {a b N J : ℕ}
    (hab : a ≤ b) (hbN : b ≤ N) (hJ : J ≤ b-a)
    (A P : Set (Space d)) (hA : μ Aᶜ = 0) {s : ℝ} (hs : 0 < s)
    (hsep : ∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (hGcore : G ⊆ Q.occupiedTreeCore μ N ×ˢ P)
    (W : ℕ → ℝ) (cost : ℕ → ℝ≥0∞)
    {q c β γ η ξ : ℝ} (hc : 0 ≤ c)
    (hwidth : β*(N:ℝ) ≤ (b-a:ℕ))
    (hconst : ((2:ℝ)^J)^(q+c) ≤ ((2:ℝ)^N)^ξ)
    (hbudget : 20*η+4*ξ+γ ≤ c*β)
    (hsmall : ∀ j < 3,
      Real.sqrt d*(Q.side/(2:ℝ)^(threeIntervalDepth a b N (j+1))) ≤ s/2)
    (hW : ∀ j < 3,
      2*(Real.sqrt d*(Q.side/(2:ℝ)^(threeIntervalDepth a b N (j+1))))/(s/2)+
        2*(1/(2:ℝ)^N) ≤ W j)
    (hlocal : ∀ j < 3, ∀ p ∈ Q.occupiedPaths μ (threeIntervalDepth a b N j),
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      ((ProbabilityTheory.cond μ (Q.descendant p).carrier).prod ν)
        ((G ∩ ((Q.descendant p).carrier ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ z ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q.descendant p).carrier)
        (W j) z ≤ threeIntervalFactor a b N J q c η j) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ (∑ j ∈ Finset.range 3, cost j)+
        4*ENNReal.ofReal (((2:ℝ)^N)^(-ξ)) ∧
      ∀ x u : Space d, μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-q-γ)) := by
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := dyadic_gain_of_local_prunings μ ν Q hQ N 3
    (threeIntervalDepth a b N) (fun _ hj => threeIntervalDepth_le hab hbN hj)
    (fun _ hj => threeIntervalDepth_mono hab hbN hj) A P hA hs hsep G hG hGcore
    (1/(2:ℝ)^N) W (ENNReal.ofReal (((2:ℝ)^N)^(-ξ)))
    (threeIntervalFactor a b N J q c η) cost (by positivity) ENNReal.ofReal_ne_top hsmall hW hlocal
  refine ⟨G',hG',hsub,?_,fun x u => (hbound x u).trans ?_⟩
  · norm_num at hdel
    exact hdel
  · exact threeIntervalFactor_product hab hbN hJ hc hwidth hconst hbudget

end Falconer

end OAI

end ExtensionScope200

/- Source: OAI.MeasureTheory.Falconer.Recursion.ContactLossBudget. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope201


namespace OAI

/-! # Uniform comparison of contact-profile losses with the middle angular scale -/

namespace Falconer

theorem dyadic_rpow_div_depth {N : ℕ} (hN : 0 < N) (κ : ℝ) :
    ((2:ℝ)^N)^(κ/(N:ℝ)) = (2:ℝ)^κ := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  field_simp

theorem inverse_dyadic_neg_power (M : ℕ) (ε : ℝ) :
    (1/(2:ℝ)^M)^(-ε) = ((2:ℝ)^M)^ε := by
  rw [one_div,Real.inv_rpow (by positivity),Real.rpow_neg (by positivity),inv_inv]

theorem contact_loss_le (d : ℕ) {τ γ Δ lam : ℝ}
    (hτ : 0 ≤ τ) (hγΔ : γ ≤ Δ) (hlam : lam ≤ τ*γ) :
    τ*γ+τ*Δ+2*((d:ℝ)+1)*lam ≤ ((2*(d:ℝ)+4)*τ)*Δ := by
  have hγ : τ*γ ≤ τ*Δ := mul_le_mul_of_nonneg_left hγΔ hτ
  have hlam' : 2*((d:ℝ)+1)*lam ≤ 2*((d:ℝ)+1)*(τ*Δ) :=
    mul_le_mul_of_nonneg_left (hlam.trans hγ) (by positivity)
  nlinarith

theorem contact_loss_relative_budget {d : ℕ} {τ γ Δ lam ε : ℝ} {N M : ℕ}
    (hτ : 0 ≤ τ) (hγΔ : γ ≤ Δ) (hlam : lam ≤ τ*γ)
    (hsmall : (2*(d:ℝ)+4)*τ ≤ ε/2)
    (hwidth : (N:ℝ)*Δ ≤ 2*(M:ℝ)) :
    (N:ℝ)*(τ*γ+τ*Δ+2*((d:ℝ)+1)*lam) ≤ (M:ℝ)*ε := by
  have hsum := contact_loss_le d hτ hγΔ hlam
  have hc : 0 ≤ (2*(d:ℝ)+4)*τ := by positivity
  calc
    _ ≤ (N:ℝ)*(((2*(d:ℝ)+4)*τ)*Δ) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg N)
    _ = ((N:ℝ)*Δ)*((2*(d:ℝ)+4)*τ) := by ring
    _ ≤ (2*(M:ℝ))*((2*(d:ℝ)+4)*τ) := mul_le_mul_of_nonneg_right hwidth hc
    _ ≤ (2*(M:ℝ))*(ε/2) := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := by ring

theorem eventually_contact_frostman_coefficient (d : ℕ) {τ γ ε : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (hsmall : (2*(d:ℝ)+4)*τ ≤ ε/2)
    (C κ : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < N → ∀ M : ℕ, ∀ Δ lam : ℝ,
      γ ≤ Δ → lam ≤ τ*γ → (N:ℝ)*Δ ≤ 2*(M:ℝ) →
      C*((2:ℝ)^N)^(τ*Δ+κ/(N:ℝ)+2*((d:ℝ)+1)*lam) ≤ (1/(2:ℝ)^M)^(-ε) := by
  obtain ⟨N₀,hN₀⟩ := eventually_relative_scale_constant (mul_pos hτ hγ) (C*(2:ℝ)^κ)
  refine ⟨N₀,?_⟩
  intro N hN hNp M Δ lam hγΔ hlam hwidth
  have hbudget := contact_loss_relative_budget hτ.le hγΔ hlam hsmall hwidth
  have hh := hN₀ N hN M (τ*Δ+2*((d:ℝ)+1)*lam) ε (by nlinarith [hbudget])
  rw [inverse_dyadic_neg_power]
  apply le_trans ?_ hh
  have he : τ*Δ+κ/(N:ℝ)+2*((d:ℝ)+1)*lam =
      κ/(N:ℝ)+(τ*Δ+2*((d:ℝ)+1)*lam) := by ring
  rw [he,Real.rpow_add (by positivity),dyadic_rpow_div_depth hNp]
  ring_nf
  exact le_rfl

theorem eventually_contact_outer_coefficient (d : ℕ) {τ γ : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (C κ : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < N → ∀ Δ lam : ℝ,
      γ ≤ Δ → lam ≤ τ*γ →
      C*((2:ℝ)^N)^(τ*Δ+κ/(N:ℝ)+2*((d:ℝ)+1)*lam) ≤
        ((2:ℝ)^N)^(((2*(d:ℝ)+4)*τ)*Δ) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed (mul_pos hτ hγ) (C*(2:ℝ)^κ)
  refine ⟨N₀,?_⟩
  intro N hN hNp Δ lam hγΔ hlam
  have hR : 0 < (2:ℝ)^N := by positivity
  have he : τ*Δ+κ/(N:ℝ)+2*((d:ℝ)+1)*lam =
      κ/(N:ℝ)+(τ*Δ+2*((d:ℝ)+1)*lam) := by ring
  calc
    _ = (C*(2:ℝ)^κ)*((2:ℝ)^N)^(τ*Δ+2*((d:ℝ)+1)*lam) := by
      rw [he,Real.rpow_add hR,dyadic_rpow_div_depth hNp]
      ring
    _ ≤ ((2:ℝ)^N)^(τ*γ)*((2:ℝ)^N)^(τ*Δ+2*((d:ℝ)+1)*lam) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2:ℝ)^N)^(τ*γ+τ*Δ+2*((d:ℝ)+1)*lam) := by
      rw [← Real.rpow_add hR]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
      (contact_loss_le d hτ.le hγΔ hlam)

theorem middle_scale_power_decay {N M : ℕ} {Δ gain : ℝ}
    (hgain : 0 ≤ gain) (hwidth : (N:ℝ)*Δ ≤ 2*(M:ℝ)) :
    (1/(2:ℝ)^M)^gain ≤ ((2:ℝ)^N)^(-gain*Δ/2) := by
  have he : (1/(2:ℝ)^M)^gain = ((2:ℝ)^M)^(-gain) := by
    rw [one_div,Real.inv_rpow (by positivity),Real.rpow_neg (by positivity)]
  rw [he]
  apply dyadic_relative_scale_bound M N
  have hh := mul_le_mul_of_nonneg_left hwidth hgain
  nlinarith

end Falconer

end OAI

end ExtensionScope201

/- Source: OAI.MeasureTheory.Falconer.Recursion.ThreeIntervalCost. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope202


namespace OAI

/-! # A uniform power bound for the three local deletions and density pruning -/

namespace Falconer

theorem eventually_three_interval_cost {τ γ L gain : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (hL : 1 ≤ 2*L) (hgain : 2*τ ≤ gain) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, ∀ Δ : ℝ, γ ≤ Δ →
      (N:ℝ)*Δ ≤ 2*(M:ℝ) →
      2*((2:ℝ)^N)^(-(2*(L*τ*Δ)))+2*(1/(2:ℝ)^M)^gain+
        4*((2:ℝ)^N)^(-(τ*Δ)) ≤ ((2:ℝ)^N)^(-(τ*γ/2)) := by
  have hη : 0 < τ*γ/2 := by positivity
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hη 8
  refine ⟨N₀,?_⟩
  intro N hN M Δ hγΔ hwidth
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hΔ0 : 0 ≤ Δ := hγ.le.trans hγΔ
  have hbase : τ*γ ≤ τ*Δ := mul_le_mul_of_nonneg_left hγΔ hτ.le
  have houtExp : τ*γ ≤ 2*(L*τ*Δ) := by
    have hh := mul_le_mul_of_nonneg_right hL (mul_nonneg hτ.le hΔ0)
    nlinarith
  have hmidExp : τ*γ ≤ gain*Δ/2 := by
    have hh := mul_le_mul_of_nonneg_right hgain hΔ0
    nlinarith
  have hout : R^(-(2*(L*τ*Δ))) ≤ R^(-(τ*γ)) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  have hmid : (1/(2:ℝ)^M)^gain ≤ R^(-(τ*γ)) :=
    (middle_scale_power_decay (by linarith : 0 ≤ gain) hwidth).trans
      (Real.rpow_le_rpow_of_exponent_le hR1 (by linarith))
  have hdensity : R^(-(τ*Δ)) ≤ R^(-(τ*γ)) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  calc
    _ ≤ 8*R^(-(τ*γ)) := by nlinarith
    _ ≤ R^(τ*γ/2)*R^(-(τ*γ)) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring

end Falconer

end OAI

end ExtensionScope202

/- Source: OAI.MeasureTheory.Falconer.Geometry.OneScaleGeometry. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope203



namespace OAI

/-! # Fixed normalization and collision widths for the three-interval argument -/

namespace Falconer

noncomputable def cellContraction (d : ℕ) : ℝ := 1/(4*(Real.sqrt d+1))

theorem cellContraction_pos (d : ℕ) : 0 < cellContraction d := by
  unfold cellContraction
  positivity

theorem cellContraction_le_one (d : ℕ) : cellContraction d ≤ 1 := by
  unfold cellContraction
  apply (div_le_one (by positivity)).mpr
  nlinarith [Real.sqrt_nonneg (d:ℝ)]

theorem cellContraction_sqrt (d : ℕ) : cellContraction d*Real.sqrt d ≤ 1/4 := by
  unfold cellContraction
  rw [one_div,mul_comm,← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : 0 < 4*(Real.sqrt (d:ℝ)+1))).mpr
  ring_nf
  linarith

theorem dyadic_collision_width (d : ℕ) {s C : ℝ} (hs : 0 < s)
    (hC : 4*Real.sqrt d/s+2 ≤ C) {v N : ℕ} (hvN : v ≤ N) :
    2*(Real.sqrt d*(1/(2:ℝ)^v))/(s/2)+2*(1/(2:ℝ)^N) ≤ C/(2:ℝ)^v := by
  have hδ : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^v :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hvN)
  have he : 2*(Real.sqrt d*(1/(2:ℝ)^v))/(s/2) =
      (4*Real.sqrt d/s)*(1/(2:ℝ)^v) := by
    field_simp
    ring
  rw [he]
  calc
    _ ≤ (4*Real.sqrt d/s)*(1/(2:ℝ)^v)+2*(1/(2:ℝ)^v) := by linarith
    _ = (4*Real.sqrt d/s+2)/(2:ℝ)^v := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hC (by positivity)

theorem eventually_cell_diameter_small (d : ℕ) {γ s : ℝ}
    (hγ : 0 < γ) (hs : 0 < s) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n : ℕ, γ*(N:ℝ) ≤ n →
      Real.sqrt d/(2:ℝ)^n ≤ s/2 := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hγ (2*Real.sqrt d/s)
  refine ⟨N₀,fun N hN n hn => ?_⟩
  have hh : 2*Real.sqrt d/s ≤ (2:ℝ)^n := by
    apply (hN₀ N hN).trans
    have hb : (N:ℝ)*γ ≤ (n:ℝ)*1 := by nlinarith
    simpa only [Real.rpow_one] using dyadic_relative_scale_bound N n hb
  have hh' := (div_le_iff₀ hs).mp hh
  apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^n)).mpr
  nlinarith

end Falconer

end OAI

end ExtensionScope203

/- Source: OAI.MeasureTheory.Falconer.Recursion.NonendpointContactGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope204











namespace OAI

/-! # Nonendpoint one-scale gain for an actual source class with a contact interval

All three local estimates are applied to the original conditional source laws.
The incoming relation and pin law are never renormalized.
-/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem nonendpoint_contact_gain (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
    (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (Q : DyadicCube (h+2)) (hQ : Q.side = 1)
    {D s : ℝ} (hD : 1 ≤ D) (hDdim : Real.sqrt (h+2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε gain : ℝ, 0 < ε ∧ 0 < gain ∧
      ∀ τ γ : ℝ, 0 < τ → 0 < γ →
        (2*((h+2:ℕ):ℝ)+4)*τ ≤ ε/2 →
        (20*(2*((h+2:ℕ):ℝ)+4)+4)*τ ≤ gain/8 → 2*τ ≤ gain →
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ B : ℕ, 0 < B → ∀ lam : ℝ, 0 ≤ lam → lam ≤ τ*γ →
        (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N,
        RobustProfileContact (sourceUnitProfile Q μ N B p₀) q t τ γ →
      ∀ A P : Set (Space (h+2)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+2), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^(τ*γ)*r^q)) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        ((sourceClass Q μ N B p₀).prod ν) (G \ G') ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))) ∧
        ∀ x u : Space (h+2), sourceClass Q μ N B p₀
          {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
            ENNReal.ofReal (((2:ℝ)^N)^(-q-gain*γ/8)) := by
  obtain ⟨ε,gain,hε,hgain,M₀,hmiddle⟩ :=
    nonendpoint_source_class_middle_pruning hpublished hq hq' hqt ht
  refine ⟨ε,gain,hε,hgain,?_⟩
  intro τ γ hτ hγ hτε hτgain hτgain'
  let L : ℝ := 2*((h+2:ℕ):ℝ)+4
  let σ : ℝ := cellContraction (h+2)
  let C : ℝ := 4*Real.sqrt (h+2:ℕ)/s+2
  have hL : 1 ≤ L := by dsimp [L]; have hh := Nat.cast_nonneg (α := ℝ) (h+2); linarith only [hh]
  have hq0 : 0 ≤ q := by have hh := Nat.cast_nonneg (α := ℝ) h; linarith
  have ht0 : 0 ≤ t := hq0.trans hqt.le
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hσ : 0 < σ := cellContraction_pos _
  have hη₀ : 0 < L*τ*γ := by positivity
  obtain ⟨Jo,No,houter⟩ := source_class_outer_radial_pruning Q hQ hD hDdim hη₀ hq0 C
  obtain ⟨Jm,Nm,hgeom⟩ := uniform_middle_geometry hσ (by positivity : 0 < s/2)
    (by positivity : 0 < γ/2) D C M₀
  obtain ⟨Na,hmargin⟩ := eventually_integer_margin (by positivity : 0 < γ/2) Jo
  obtain ⟨Ns,hsmall⟩ := eventually_cell_diameter_small (h+2) (by positivity : 0 < γ/2) hs
  let K : ℝ := (((2*Nat.ceil (2+4*Real.sqrt (h+2:ℕ))+1)^(h+2):ℕ):ℝ)
  obtain ⟨Nf,hfirst⟩ := eventually_contact_outer_coefficient (h+2) hτ hγ (K*(2:ℝ)^q) 0
  obtain ⟨Nl,hlast⟩ := eventually_contact_outer_coefficient (h+2) hτ hγ
    (K*(2:ℝ)^q) (((h+2:ℕ):ℝ)+q)
  obtain ⟨Nt,htcoef⟩ := eventually_contact_frostman_coefficient (h+2) hτ hγ hτε
    (K*(2:ℝ)^t*σ^(-t)) (((h+2:ℕ):ℝ)+t)
  obtain ⟨Nc,hconst⟩ := fixed_constant_absorbed (mul_pos hτ hγ)
    (((2:ℝ)^Jm)^(q+gain/2))
  obtain ⟨Nd,hcost⟩ := eventually_three_interval_cost hτ hγ
    (by linarith : 1 ≤ 2*L) hτgain'
  obtain ⟨Nlarge,hlarge⟩ := exists_nat_gt (4/γ)
  let N₀ := max 1 (max No (max Nm (max Na (max Ns (max Nf (max Nl (max Nt
    (max Nc (max Nd Nlarge)))))))))
  refine ⟨N₀,?_⟩
  intro N hN μ ν _ _ B hB lam hlam hlamτ hblock hblock'
    p₀ hp₀ hcontact A P hA hP hAfull hPfull hsep hpin G hG hcap
  change max 1 (max No (max Nm (max Na (max Ns (max Nf (max Nl (max Nt
    (max Nc (max Nd Nlarge))))))))) ≤ N at hN
  simp only [max_le_iff] at hN
  rcases hN with ⟨h1,hNo,hNm,hNa,hNs,hNf,hNl,hNt,hNc,hNd,hNL⟩
  have hNp : 0 < N := by omega
  have hNN : (Nlarge:ℝ) ≤ N := by exact_mod_cast hNL
  have hlarge' : 4 ≤ γ*(N:ℝ) := by
    have hh := (div_lt_iff₀ hγ).mp hlarge
    nlinarith only [hh,hNN,hγ]
  obtain ⟨α,β,a,b,hγΔ,hΔ1,hab,hbN,hgap,_,ha,_,hNb,hfreeze,hi₀,hi₁,hi₂⟩ :=
    source_class_contact_intervals Q μ hNp hB p₀ hq0 ht0 hγ hlarge' hcontact
  let Δ := β-α
  let η := L*τ*Δ
  let ξ := τ*Δ
  let M := (b-a)-Jm
  have hΔ : 0 < Δ := hγ.trans_le hγΔ
  have hη : L*τ*γ ≤ η := mul_le_mul_of_nonneg_left hγΔ (by positivity)
  obtain ⟨hJm,hM,hNM,hfr,hwi⟩ := hgeom N hNm a b Δ hab
    (by dsimp [Δ]; linarith only [hγΔ,hγ]) hgap hfreeze
  have hJoA : Jo ≤ a := hmargin N hNa a ha
  have hJoB : b+Jo ≤ N := by
    have hh := hmargin N hNa (N-b) (by linarith only [hNb,hγ])
    omega
  have hsmallA : Real.sqrt (h+2:ℕ)*(Q.side/(2:ℝ)^a) ≤ s/2 := by
    rw [hQ,mul_one_div]
    exact hsmall N hNs a ha
  have hsmallAll {n : ℕ} (han : a ≤ n) :
      Real.sqrt (h+2:ℕ)*(Q.side/(2:ℝ)^n) ≤ s/2 := by
    apply le_trans _ hsmallA
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hside.le (by positivity)
        (pow_le_pow_right₀ (by norm_num) han)) (Real.sqrt_nonneg _)
  have hcoef₀ : K*(2:ℝ)^q*((2:ℝ)^N)^(τ*Δ+2*(((h+2:ℕ):ℝ)+1)*lam) ≤
      ((2:ℝ)^N)^η := by
    simpa only [zero_div,add_zero] using hfirst N hNf hNp Δ lam hγΔ hlamτ
  have hcoef₂ := hlast N hNl hNp Δ lam hγΔ hlamτ
  have hcoef₁ : K*(2:ℝ)^t*((2:ℝ)^N)^
      ((τ*Δ+(((h+2:ℕ):ℝ)+t)/(N:ℝ))+2*(((h+2:ℕ):ℝ)+1)*lam)*σ^(-t) ≤
      (1/(2:ℝ)^M)^(-ε) := by
    convert htcoef N hNt hNp M Δ lam hγΔ hlamτ hNM using 1; ring
  have hreverseOuter : ((2:ℝ)^N)^(τ*γ) ≤ ((2:ℝ)^N)^η := by
    apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
    have hh := mul_le_mul_of_nonneg_right hL (mul_nonneg hτ.le hγ.le)
    dsimp [η]
    nlinarith only [hh,hη]
  have hreverseMiddle : ((2:ℝ)^N)^(τ*γ) ≤ (1/(2:ℝ)^M)^(-ε) := by
    rw [inverse_dyadic_neg_power]
    apply dyadic_relative_scale_bound
    have hh := contact_loss_relative_budget hτ.le hγΔ hlamτ hτε hNM
    have hx : 0 ≤ (N:ℝ)*(τ*Δ+2*(((h+2:ℕ):ℝ)+1)*lam) := by positivity
    nlinarith only [hh,hx]
  let ρ := sourceClass Q μ N B p₀
  have : IsProbabilityMeasure ρ := regularization_class_probability Q hside μ N B hp₀
  have hρA : ρ Aᶜ = 0 := sourceClass_absolutelyContinuous Q μ N B p₀ hAfull
  obtain ⟨G₀,hG₀,hG₀G,hG₀core,hnull⟩ :=
    source_class_pair_core Q hside μ ν N B p₀ hp₀ A P hA hP hAfull hPfull G hG
  have hcore : G₀ ⊆ Q.occupiedTreeCore ρ N ×ˢ P := fun _ hz => ⟨(hG₀core hz).1.2,(hG₀core hz).2⟩
  have hdiag {z x : Space (h+2)} (hz : (z,x) ∈ G₀) : z ≠ x := by
    have hh := hsep z (hG₀core hz).1.1 x (hG₀core hz).2
    intro he
    simp only [he,sub_self,norm_zero] at hh
    exact (not_le_of_gt hs) hh
  let cost : ℕ → ℝ≥0∞ := fun j => if j = 1 then 2*ENNReal.ofReal ((1/(2:ℝ)^M)^gain)
    else ENNReal.ofReal (((2:ℝ)^N)^(-(2*η)))
  have hlocal : ∀ j < 3, ∀ p ∈ Q.occupiedPaths ρ (threeIntervalDepth a b N j),
      ∃ H : Set (Space (h+2) × Space (h+2)), MeasurableSet H ∧
      ((ProbabilityTheory.cond ρ (Q.descendant p).carrier).prod ν)
        ((G₀ ∩ ((Q.descendant p).carrier ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ z ∈ H, radialCollisionMass (ProbabilityTheory.cond ρ (Q.descendant p).carrier)
        (C/(2:ℝ)^(threeIntervalDepth a b N (j+1))) z ≤
          threeIntervalFactor a b N Jm q (gain/2) η j := by
    intro j hj p hp
    have hpPos : 0 < ρ (Q.descendant p).carrier := (Finset.mem_filter.mp hp).2
    have hpLen : p.length = threeIntervalDepth a b N j :=
      (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1
    let V := G₀ ∩ ((Q.descendant p).carrier ×ˢ univ)
    have hV : MeasurableSet V := hG₀.inter ((Q.descendant p).measurable.prod MeasurableSet.univ)
    have hVG : V ⊆ G := inter_subset_left.trans hG₀G
    have hVdiag : ∀ z x, (z,x) ∈ V → x ≠ z := fun _ _ hz => (hdiag hz.1).symm
    have hVpin : ∀ z x, (z,x) ∈ V → ∀ y ∈ (Q.descendant p).carrier, ‖y-x‖ ≤ D :=
      fun _ _ hz y hy => hpin y (Q.descendant_subset p hy) _ (hG₀core hz.1).2
    have hac := sourceClass_conditional_absolutelyContinuous Q μ N B p₀ p
    interval_cases j
    · have hlen : p.length = 0 := by simpa [threeIntervalDepth] using hpLen
      obtain ⟨H,hH,_,hd,hk⟩ := houter N hNo η hη 0 a (by omega) (hab.trans hbN)
        μ ν B hNp hB lam (τ*Δ) hblock hblock' p₀ hp₀ p hlen hpPos
        (by intro n _ hn; simpa only [Nat.sub_zero,sourceProfile,Nat.cast_zero,regularizedProfile_zero,sub_zero] using hi₀ n hn)
        hcoef₀ V hV hVdiag hVpin
        (reverse_caps_all_radii μ _ ν hac hVG (hab.trans hbN) hreverseOuter hcap)
      refine ⟨H,hH,?_,?_⟩
      · simpa [cost] using hd
      · simpa [threeIntervalDepth,threeIntervalFactor] using hk
    · have hlen : p.length = a := by simpa [threeIntervalDepth] using hpLen
      have hp' : p ∈ Q.occupiedPaths ρ a := by simpa [threeIntervalDepth] using hp
      let w₀ : Sphere (h+2) := ⟨EuclideanSpace.basisFun (Fin (h+2)) ℝ 0,by
        simpa only [Metric.mem_sphere,dist_zero_right] using
          (EuclideanSpace.basisFun (Fin (h+2)) ℝ).norm_eq_one 0⟩
      obtain ⟨H,hH,_,hd,hk⟩ := hmiddle M hM Q hQ μ ν (by simp) N B hNp hB lam
        (τ*Δ+(((h+2:ℕ):ℝ)+t)/(N:ℝ)) σ (by positivity) hlam hσ
        (cellContraction_le_one _) (cellContraction_sqrt _) hblock hblock' p₀ hp₀
        a b hab hbN (Nat.sub_le _ _) p hlen hpPos
        (by intro n hn hn'; have hh := hi₁ n hn hn'; linarith only [hh]) hcoef₁ w₀ V hV
        (fun z x hz => ⟨hdiag hz.1,hz.2.1⟩)
        (reverse_caps_transfer μ _ ν hac hVG ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans hbN))
          hreverseMiddle hcap)
        (s/2) D (C/(2:ℝ)^b) (by positivity) hfr hwi (by
          intro x hx
          obtain ⟨z,hz⟩ := hx
          refine ⟨occupied_cell_center_separation Q hside ρ A P hρA hsep hsmallA hp'
            x (hG₀core hz.1).2,?_⟩
          exact ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant p).measurable
            (fun y hy => hVpin z x hz y hy))
      refine ⟨H,hH,?_,?_⟩
      · simpa [cost] using hd
      · simpa [threeIntervalDepth,threeIntervalFactor,M] using hk
    · have hlen : p.length = b := by simpa [threeIntervalDepth] using hpLen
      obtain ⟨H,hH,_,hd,hk⟩ := houter N hNo η hη b N hJoB le_rfl
        μ ν B hNp hB lam (τ*Δ+(((h+2:ℕ):ℝ)+q)/(N:ℝ)) hblock hblock' p₀ hp₀ p hlen hpPos
        (by intro n hn hn'; have hh := hi₂ n hn hn'; linarith only [hh])
        hcoef₂ V hV hVdiag hVpin (reverse_caps_all_radii μ _ ν hac hVG le_rfl hreverseOuter hcap)
      refine ⟨H,hH,?_,?_⟩
      · simpa [cost] using hd
      · simpa [threeIntervalDepth,threeIntervalFactor] using hk
  have hβ : (Δ/2)*(N:ℝ) ≤ (b-a:ℕ) := by
    have hh : ((b-a)-Jm:ℕ) ≤ b-a := Nat.sub_le _ _
    have hh' : (M:ℝ) ≤ (b-a:ℕ) := by exact_mod_cast hh
    nlinarith only [hh',hNM]
  have hconst' : ((2:ℝ)^Jm)^(q+gain/2) ≤ ((2:ℝ)^N)^ξ :=
    (hconst N hNc).trans (Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ (by norm_num)) (mul_le_mul_of_nonneg_left hγΔ hτ.le))
  have hbudget : 20*η+4*ξ+gain*γ/8 ≤ (gain/2)*(Δ/2) :=
    three_interval_relative_budget hΔ.le hγΔ hgain.le hτgain
  obtain ⟨G',hG',hsub,hdel,hcaps⟩ := three_interval_dyadic_gain ρ ν Q hside hab hbN hJm
    A P hρA hs hsep G₀ hG₀ hcore
    (fun j => C/(2:ℝ)^(threeIntervalDepth a b N (j+1))) cost
    (by positivity : 0 ≤ gain/2) hβ hconst' hbudget
    (fun j hj => hsmallAll (threeIntervalDepth_child hab hbN hj))
    (fun j hj => by
      rw [hQ]
      exact dyadic_collision_width (h+2) hs le_rfl
        (threeIntervalDepth_le hab hbN (by omega))) hlocal
  refine ⟨G',hG',hsub.trans hG₀G,?_,hcaps⟩
  have hz : (ρ.prod ν) (G \ G₀) ≤ 0 := hnull.le
  have htotal := relative_pruning_cost_trans (ρ.prod ν) G G₀ G' hz hdel
  rw [zero_add] at htotal
  apply htotal.trans
  have hc := hcost N hNd M Δ hγΔ hNM
  have he : (∑ j ∈ Finset.range 3, cost j)+4*ENNReal.ofReal (((2:ℝ)^N)^(-ξ)) =
      ENNReal.ofReal (2*((2:ℝ)^N)^(-(2*η))+2*(1/(2:ℝ)^M)^gain+
        4*((2:ℝ)^N)^(-ξ)) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,cost,show (0:ℕ) ≠ 1 by omega,
      show (2:ℕ) ≠ 1 by omega,ite_false,ite_true,zero_add,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),ENNReal.ofReal_ofNat]
    ring
  rw [he]
  exact ENNReal.ofReal_le_ofReal hc

end Falconer.Regularization

end OAI

end ExtensionScope204

/- Source: OAI.MeasureTheory.Falconer.Radial.RelativeClasswiseRadialGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope205



namespace OAI

/-! # Recombining relative pair refinements with the original source-class weights -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*}

theorem relative_classwise_radial_gain (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G₀ : Set (Space d × Space d)) (hG₀ : MeasurableSet G₀)
    (I : Finset ι) (S : ι → Set (Space d)) (G : ι → Set (Space d × Space d))
    (hS : ∀ i ∈ I, MeasurableSet (S i)) (hG : ∀ i ∈ I, MeasurableSet (G i))
    (hpos : ∀ i ∈ I, μ (S i) ≠ 0) (hdisj : (I : Set ι).PairwiseDisjoint S)
    (t C : ℝ≥0∞) (r : ℝ)
    (hcost : ∀ i ∈ I, (ν.prod (ProbabilityTheory.cond μ (S i))) (G₀ \ G i) ≤ t)
    (hcap : ∀ i ∈ I, ∀ x u : Space d,
      ProbabilityTheory.cond μ (S i) {z | (x,z) ∈ G i ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G₀ ∧
      (ν.prod μ) (G₀ \ H) ≤ μ (⋃ i ∈ I, S i)ᶜ+t ∧
      ∀ x u : Space d, μ {z | (x,z) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
  classical
  let U := ⋃ i ∈ I, G i ∩ (univ ×ˢ S i)
  let H := G₀ ∩ U
  have hH : MeasurableSet H := hG₀.inter (Finset.measurableSet_biUnion I
    (fun i hi => (hG i hi).inter (MeasurableSet.univ.prod (hS i hi))))
  have hmass : (∑ i ∈ I, μ (S i)) ≤ 1 := by
    rw [← measure_biUnion_finset hdisj hS]
    exact (measure_mono (subset_univ _)).trans_eq (measure_univ)
  have hreconstruct (i : ι) (hi : i ∈ I) (E : Set (Space d × Space d)) :
      μ (S i)*((ν.prod (ProbabilityTheory.cond μ (S i))) E) =
        (ν.prod (μ.restrict (S i))) E := by
    rw [ProbabilityTheory.cond,Measure.prod_smul_right,Measure.smul_apply,smul_eq_mul,
      ← mul_assoc,ENNReal.mul_inv_cancel (hpos i hi) (measure_ne_top μ _),one_mul]
  refine ⟨H,hH,inter_subset_left,?_,?_⟩
  · have hsub : G₀ \ H ⊆ (univ ×ˢ (⋃ i ∈ I, S i)ᶜ) ∪
        ⋃ i ∈ I, (G₀ \ G i) ∩ (univ ×ˢ S i) := by
      intro p hp
      by_cases hs : p.2 ∈ ⋃ i ∈ I, S i
      · obtain ⟨i,hi,hsi⟩ := mem_iUnion₂.mp hs
        right
        refine mem_iUnion₂.mpr ⟨i,hi,⟨hp.1,?_⟩,mem_univ _,hsi⟩
        intro hgi
        exact hp.2 ⟨hp.1,mem_iUnion₂.mpr ⟨i,hi,hgi,mem_univ _,hsi⟩⟩
      · exact Or.inl ⟨mem_univ _,hs⟩
    calc
      _ ≤ (ν.prod μ) (univ ×ˢ (⋃ i ∈ I, S i)ᶜ)+
          (ν.prod μ) (⋃ i ∈ I, (G₀ \ G i) ∩ (univ ×ˢ S i)) :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ μ (⋃ i ∈ I, S i)ᶜ+
          ∑ i ∈ I, (ν.prod μ) ((G₀ \ G i) ∩ (univ ×ˢ S i)) := by
        simp only [Measure.prod_prod,measure_univ,one_mul]
        exact add_le_add le_rfl (measure_biUnion_finset_le _ _)
      _ ≤ μ (⋃ i ∈ I, S i)ᶜ+∑ i ∈ I, μ (S i)*t := by
        apply add_le_add le_rfl (Finset.sum_le_sum ?_)
        intro i hi
        rw [← Measure.restrict_apply (hG₀.diff (hG i hi)),← Measure.prod_restrict,
          Measure.restrict_univ,← hreconstruct i hi]
        exact mul_le_mul' le_rfl (hcost i hi)
      _ = μ (⋃ i ∈ I, S i)ᶜ+(∑ i ∈ I, μ (S i))*t := by rw [Finset.sum_mul]
      _ ≤ _ := add_le_add le_rfl ((mul_le_mul' hmass le_rfl).trans_eq (one_mul t))
  · intro x u
    let A := fun i => {z | (x,z) ∈ G i ∧ ‖normalize (z-x)-u‖ ≤ r}
    have hsub : {z | (x,z) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ r} ⊆ ⋃ i ∈ I, S i ∩ A i := by
      intro z hz
      obtain ⟨i,hi,hgi,hsi⟩ := mem_iUnion₂.mp hz.1.2
      exact mem_iUnion₂.mpr ⟨i,hi,hsi.2,hgi,hz.2⟩
    calc
      _ ≤ ∑ i ∈ I, μ (S i ∩ A i) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
      _ = ∑ i ∈ I, μ (S i)*ProbabilityTheory.cond μ (S i) (A i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← ProbabilityTheory.cond_mul_eq_inter (hS i hi) (A i) μ,mul_comm]
      _ ≤ ∑ i ∈ I, μ (S i)*C := Finset.sum_le_sum (fun i hi =>
        mul_le_mul' le_rfl (hcap i hi x u))
      _ = (∑ i ∈ I, μ (S i))*C := (Finset.sum_mul _ _ _).symm
      _ ≤ C := (mul_le_mul' hmass le_rfl).trans_eq (one_mul C)

end Falconer

end OAI

end ExtensionScope205

/- Source: OAI.MeasureTheory.Falconer.Estimates.RelativeRegularizationGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope206



namespace OAI

/-! # Recombining a relative radial refinement of each actual regularization class -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem relative_regularization_radial_gain (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G₀ : Set (Space d × Space d)) (hG₀ : MeasurableSet G₀)
    (hroot : μ Q.carrierᶜ = 0) {N H : ℕ} (hH : 0 < H) (hNH : H ≤ N) (hdN : d+3 ≤ N)
    {threshold : ℝ≥0∞} (hthreshold : 0 < threshold) (t C : ℝ≥0∞) (r : ℝ)
    (hlocal : ∀ T ∈ regularizationIndex Q μ N (N/H) threshold,
      ∃ G : Set (Space d × Space d), MeasurableSet G ∧
        (ν.prod (normalizedClass Q μ (regularizationLeaves Q μ N)
          (regularizationLabel Q μ N (N/H)) T)) (G₀ \ G) ≤ t ∧
        ∀ x u : Space d,
          normalizedClass Q μ (regularizationLeaves Q μ N)
            (regularizationLabel Q μ N (N/H)) T
            {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) :
    ∃ G : Set (Space d × Space d), MeasurableSet G ∧ G ⊆ G₀ ∧
      (ν.prod μ) (G₀ \ G) ≤ ((2:ℝ≥0∞)^(2*N))⁻¹+(N^(4*H+2):ℕ)*threshold+t ∧
      ∀ x u : Space d, μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
  classical
  let I := regularizationIndex Q μ N (N/H) threshold
  let S := regularizationSet Q μ N (N/H)
  have hex : ∀ T : List ℕ, ∃ G : Set (Space d × Space d), MeasurableSet G ∧
      (T ∈ I → (ν.prod (ProbabilityTheory.cond μ (S T))) (G₀ \ G) ≤ t ∧
        ∀ x u : Space d, ProbabilityTheory.cond μ (S T)
          {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) := by
    intro T
    by_cases hT : T ∈ I
    · obtain ⟨G,hm,hc,hg⟩ := hlocal T hT
      rw [normalized_regularization_class_eq_cond] at hc hg
      exact ⟨G,hm,fun _ => ⟨hc,hg⟩⟩
    · exact ⟨∅,MeasurableSet.empty,fun h => (hT h).elim⟩
  choose G hm hg using hex
  have hpos : ∀ T ∈ I, μ (S T) ≠ 0 := by
    intro T hT
    exact (hthreshold.trans_le (regularizationSet_mass Q μ N (N/H) threshold hT)).ne'
  have hdisj : (I : Set (List ℕ)).PairwiseDisjoint S := by
    intro T _ U _ hTU
    exact regularizationSet_disjoint Q hQ μ N (N/H) hTU
  obtain ⟨G',hG',hsub,hc,hcap⟩ := relative_classwise_radial_gain μ ν G₀ hG₀ I S G
    (fun T _ => regularizationSet_measurable Q μ N (N/H) T) (fun T _ => hm T)
    hpos hdisj t C r (fun T hT => (hg T hT).1) (fun T hT => (hg T hT).2)
  refine ⟨G',hG',hsub,hc.trans (add_le_add ?_ le_rfl),hcap⟩
  exact regularization_discarded_global Q hQ μ hroot hH hNH hdN threshold

end Falconer.Regularization

end OAI

end ExtensionScope206

/- Source: OAI.MeasureTheory.Falconer.Estimates.SourceRelativeRegularization. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope207



namespace OAI

/-! # Relative recombination in source-first coordinates -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem source_relative_regularization_gain (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G₀ : Set (Space d × Space d)) (hG₀ : MeasurableSet G₀)
    (hroot : μ Q.carrierᶜ = 0) {N H : ℕ} (hH : 0 < H) (hNH : H ≤ N) (hdN : d+3 ≤ N)
    {threshold : ℝ≥0∞} (hthreshold : 0 < threshold) (t C : ℝ≥0∞) (r : ℝ)
    (hlocal : ∀ p ∈ regularizationLeaves Q μ N,
      regularizationLabel Q μ N (N/H) p ∈ regularizationIndex Q μ N (N/H) threshold →
      ∃ G : Set (Space d × Space d), MeasurableSet G ∧
        ((sourceClass Q μ N (N/H) p).prod ν) (G₀ \ G) ≤ t ∧
        ∀ x u : Space d, sourceClass Q μ N (N/H) p
          {z | (z,x) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) :
    ∃ G : Set (Space d × Space d), MeasurableSet G ∧ G ⊆ G₀ ∧
      (μ.prod ν) (G₀ \ G) ≤ ((2:ℝ≥0∞)^(2*N))⁻¹+(N^(4*H+2):ℕ)*threshold+t ∧
      ∀ x u : Space d, μ {z | (z,x) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
  let S := Prod.swap ⁻¹' G₀
  have hS : MeasurableSet S := hG₀.preimage measurable_swap
  have hclasses : ∀ T ∈ regularizationIndex Q μ N (N/H) threshold,
      ∃ G : Set (Space d × Space d), MeasurableSet G ∧
        (ν.prod (normalizedClass Q μ (regularizationLeaves Q μ N)
          (regularizationLabel Q μ N (N/H)) T)) (S \ G) ≤ t ∧
        ∀ x u : Space d, normalizedClass Q μ (regularizationLeaves Q μ N)
          (regularizationLabel Q μ N (N/H)) T
          {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
    intro T hT
    have hT' := hT
    simp only [regularizationIndex,Finset.mem_filter] at hT'
    obtain ⟨p,hp,hpT⟩ := Finset.mem_image.mp hT'.1
    have : IsProbabilityMeasure (normalizedClass Q μ (regularizationLeaves Q μ N)
        (regularizationLabel Q μ N (N/H)) T) := by
      simpa only [sourceClass,hpT] using regularization_class_probability Q hQ μ N (N/H) hp
    obtain ⟨G,hG,hd,hc⟩ := hlocal p hp (hpT.symm ▸ hT)
    refine ⟨Prod.swap ⁻¹' G,hG.preimage measurable_swap,?_,?_⟩
    · have he : S \ Prod.swap ⁻¹' G = Prod.swap ⁻¹' (G₀ \ G) := rfl
      rw [he,← Measure.map_apply measurable_swap (hG₀.diff hG),Measure.prod_swap]
      simpa only [sourceClass,hpT] using hd
    · simpa only [sourceClass,hpT,mem_preimage,Prod.swap_prod_mk] using hc
  obtain ⟨G,hG,hsub,hd,hc⟩ := relative_regularization_radial_gain Q hQ μ ν S hS
    hroot hH hNH hdN hthreshold t C r hclasses
  refine ⟨Prod.swap ⁻¹' G,hG.preimage measurable_swap,fun z hz => hsub hz,?_,hc⟩
  have he : G₀ \ Prod.swap ⁻¹' G = Prod.swap ⁻¹' (S \ G) := by
    ext z
    simp only [mem_sdiff,mem_preimage,S,Prod.swap_swap]
  rw [he,← Measure.map_apply measurable_swap (hS.diff hG),Measure.prod_swap]
  exact hd

end Falconer.Regularization

end OAI

end ExtensionScope207

/- Source: OAI.MeasureTheory.Falconer.Estimates.OneScaleParameters. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope208



namespace OAI

/-! # Choosing the comparison loss before the compactness contact margin -/

namespace Falconer

theorem one_scale_loss_choice (d : ℕ) {ε gain : ℝ} (hε : 0 < ε) (hgain : 0 < gain) :
    ∃ τ : ℝ, 0 < τ ∧ (2*(d:ℝ)+4)*τ ≤ ε/2 ∧
      (20*(2*(d:ℝ)+4)+4)*τ ≤ gain/8 ∧ 2*τ ≤ gain := by
  let L : ℝ := 2*(d:ℝ)+4
  have hL : 0 < L := by dsimp [L]; positivity
  have hS : 0 < 20*L+4 := by positivity
  let τ := min (min (ε/(2*L)) (gain/(8*(20*L+4)))) (gain/2)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτε : τ ≤ ε/(2*L) := (min_le_left _ _).trans (min_le_left _ _)
  have hτgain : τ ≤ gain/(8*(20*L+4)) := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨τ,hτ,?_,?_,?_⟩
  · change L*τ ≤ ε/2
    calc
      _ ≤ L*(ε/(2*L)) := mul_le_mul_of_nonneg_left hτε hL.le
      _ = _ := by field_simp
  · change (20*L+4)*τ ≤ gain/8
    calc
      _ ≤ (20*L+4)*(gain/(8*(20*L+4))) := mul_le_mul_of_nonneg_left hτgain hS.le
      _ = _ := by field_simp
  · have hh : τ ≤ gain/2 := min_le_right _ _
    linarith

end Falconer

end OAI

end ExtensionScope208

/- Source: OAI.MeasureTheory.Falconer.Radial.WeakRadialLocalBudget. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope209


namespace OAI

/-! # Profile cancellation in the weak radial tube-counting budget -/

namespace Falconer
open Real Filter
open scoped Topology

private theorem real_rpow_nat_power {x : ℝ} (hx : 0 < x) (a : ℝ) (j : ℕ) :
    (x^a)^j = x^(a*(j:ℝ)) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]

theorem weak_radial_profile_cancel {δ D : ℝ} (hδ : 0 < δ) (hD : 0 < D)
    (n : ℕ) (K e τ : ℝ) :
    (K/(δ^(-e)/D^((n:ℝ)/(n+1))))^(n+1)*(δ^(-τ)/D)^n =
      K^(n+1)*δ^((n+1)*e-n*τ) := by
  have hd : (n:ℝ)+1 ≠ 0 := by positivity
  have hroot : (D^((n:ℝ)/(n+1)))^(n+1) = D^n := by
    rw [real_rpow_nat_power hD, Nat.cast_add, Nat.cast_one]
    rw [div_mul_cancel₀ _ hd,Real.rpow_natCast]
  rw [div_div_eq_mul_div,div_pow,mul_pow,div_pow,hroot,
    real_rpow_nat_power hδ,real_rpow_nat_power hδ]
  calc
    _ = K^(n+1)*(δ^(-τ*(n:ℝ))/δ^(-e*((n+1:ℕ):ℝ))) := by
      field_simp [pow_ne_zero n hD.ne']
    _ = _ := by
      rw [← Real.rpow_sub hδ]
      congr 2
      push_cast
      ring

theorem weak_radial_local_count_power {δ D : ℝ} (hδ : 0 < δ) (hD : 0 < D)
    (n : ℕ) (K G e τ η : ℝ) :
    (K/(δ^(-e)/D^((n:ℝ)/(n+1))))^(n+1)*
      (G/(δ^η)^(n+1))^(n*(n+1))*(δ^(-τ)/D)^n =
    (K^(n+1)*G^(n*(n+1)))*
      δ^((n+1)*e-n*τ-η*n*(n+1)^2) := by
  calc
    _ = ((K/(δ^(-e)/D^((n:ℝ)/(n+1))))^(n+1)*(δ^(-τ)/D)^n)*
        (G/(δ^η)^(n+1))^(n*(n+1)) := by ring
    _ = (K^(n+1)*δ^((n+1)*e-n*τ))*
        (G^(n*(n+1))/δ^(η*(((n+1)*(n*(n+1)):ℕ):ℝ))) := by
      rw [weak_radial_profile_cancel hδ hD,div_pow,← pow_mul,real_rpow_nat_power hδ]
    _ = (K^(n+1)*G^(n*(n+1)))*
        (δ^((n+1)*e-n*τ)/δ^(η*(((n+1)*(n*(n+1)):ℕ):ℝ))) := by ring
    _ = _ := by
      rw [← Real.rpow_sub hδ]
      congr 2
      push_cast
      ring

theorem eventually_weak_radial_local_budget (n : ℕ) (K G e τ η u : ℝ)
    (hgap : 0 < (n+1)*e-n*τ-η*n*(n+1)^2-n*u) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧ ∀ D > 0,
      (K/(δ^(-e)/D^((n:ℝ)/(n+1))))^(n+1)*
        (G/(δ^η)^(n+1))^(n*(n+1))*(δ^(-τ)/D)^n < (δ^u)^n := by
  let A : ℝ := K^(n+1)*G^(n*(n+1))
  let gap : ℝ := (n+1)*e-n*τ-η*n*(n+1)^2-n*u
  have hh := (tendsto_rpow_neg_nhdsGT_zero (show -gap < 0 by dsimp [gap]; linarith)).eventually
    (eventually_gt_atTop A)
  filter_upwards [hh,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hd hδ
  refine ⟨hδ.1,fun D hD => ?_⟩
  rw [weak_radial_local_count_power hδ.1 hD]
  calc
    _ < δ^(-gap)*δ^((n+1)*e-n*τ-η*n*(n+1)^2) :=
      mul_lt_mul_of_pos_right hd (Real.rpow_pos_of_pos hδ.1 _)
    _ = (δ^u)^n := by
      rw [← Real.rpow_add hδ.1,real_rpow_nat_power hδ.1]
      congr 1
      dsimp [gap]
      ring

end Falconer

end OAI

end ExtensionScope209

/- Source: OAI.MeasureTheory.Falconer.Radial.WeakRadialParameters. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope210


namespace OAI

/-! # Compatible fixed losses for the local weak radial argument -/

namespace Falconer

theorem weak_radial_local_exponents {n : ℕ} (hn : 1 ≤ n) {e ζ : ℝ}
    (he : 0 < e) (hζ : 0 < ζ) :
    ∃ η τ u ε : ℝ, 0 < η ∧ 0 < τ ∧ 0 < u ∧ 0 < ε ∧
      0 < (n+1)*e-n*τ-η*n*(n+1)^2-n*u ∧ 0 < η*ζ-ε-u := by
  have hN : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD : (0:ℝ) < (n:ℝ)+1 := by positivity
  let η : ℝ := e/(8*(n:ℝ)*((n:ℝ)+1))
  let τ : ℝ := ((n:ℝ)+1)*e/(8*(n:ℝ))
  let u : ℝ := min τ (η*ζ/8)
  let ε : ℝ := η*ζ/8
  have hη : 0 < η := by dsimp [η]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hu : 0 < u := lt_min hτ hε
  refine ⟨η,τ,u,ε,hη,hτ,hu,hε,?_,?_⟩
  · have ht : (n:ℝ)*τ = ((n:ℝ)+1)*e/8 := by
      dsimp [τ]
      field_simp
    have ha : η*(n:ℝ)*((n:ℝ)+1)^2 = ((n:ℝ)+1)*e/8 := by
      dsimp [η]
      field_simp
    have huτ : (n:ℝ)*u ≤ (n:ℝ)*τ :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hN.le
    rw [ht] at huτ
    rw [ht,ha]
    nlinarith [mul_pos hD he]
  · have huε : u ≤ ε := min_le_right _ _
    dsimp [ε] at huε ⊢
    nlinarith [mul_pos hη hζ]

theorem weak_radial_bounded_exponents {n : ℕ} (hn : 1 ≤ n) {e ζ : ℝ}
    (he : 0 < e) (hζ : 0 < ζ) :
    ∃ η τ u ε : ℝ, 0 < η ∧ η ≤ 1/2 ∧ 0 < τ ∧ 0 < u ∧ 0 < ε ∧
      0 < (n+1)*e-n*τ-η*n*(n+1)^2-n*u ∧ 0 < η*ζ-ε-u := by
  have hN : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD : (0:ℝ) < (n:ℝ)+1 := by positivity
  let η₀ : ℝ := e/(8*(n:ℝ)*((n:ℝ)+1))
  let η : ℝ := min η₀ (1/2)
  let τ : ℝ := ((n:ℝ)+1)*e/(8*(n:ℝ))
  let u : ℝ := min τ (η*ζ/8)
  let ε : ℝ := η*ζ/8
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  have hη : 0 < η := lt_min hη₀ (by norm_num)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hu : 0 < u := lt_min hτ hε
  refine ⟨η,τ,u,ε,hη,min_le_right _ _,hτ,hu,hε,?_,?_⟩
  · have ht : (n:ℝ)*τ = ((n:ℝ)+1)*e/8 := by dsimp [τ]; field_simp
    have ha : η₀*(n:ℝ)*((n:ℝ)+1)^2 = ((n:ℝ)+1)*e/8 := by
      dsimp [η₀]
      field_simp
    have hηle : η*(n:ℝ)*((n:ℝ)+1)^2 ≤ η₀*(n:ℝ)*((n:ℝ)+1)^2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) hN.le) (sq_nonneg _)
    have hule : (n:ℝ)*u ≤ (n:ℝ)*τ := mul_le_mul_of_nonneg_left (min_le_left _ _) hN.le
    rw [ht] at hule
    rw [ha] at hηle
    rw [ht]
    nlinarith [mul_pos hD he]
  · have hule : u ≤ ε := min_le_right _ _
    dsimp [ε] at hule ⊢
    nlinarith [mul_pos hη hζ]

end Falconer

end OAI

end ExtensionScope210

/- Source: OAI.MeasureTheory.Falconer.Radial.WeakRadialDeletionBudget. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope211



namespace OAI

/-! # Turning the two actual local incidence losses into a pair deletion bound -/

namespace Falconer
open scoped ENNReal

theorem weak_radial_two_costs {A B u v c : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : c < u) (hv : c < v) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      A*((2:ℝ)^N)^(-u)+B*((2:ℝ)^N)^(-v) ≤ ((2:ℝ)^N)^(-c) := by
  let m := min (u-c) (v-c)
  have hm : 0 < m := lt_min (sub_pos.mpr hu) (sub_pos.mpr hv)
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hm (A+B)
  refine ⟨N₀,fun N hN => ?_⟩
  let R : ℝ := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hu' : -u ≤ -c-m := by have := min_le_left (u-c) (v-c); dsimp [m]; linarith
  have hv' : -v ≤ -c-m := by have := min_le_right (u-c) (v-c); dsimp [m]; linarith
  calc
    _ ≤ A*R^(-c-m)+B*R^(-c-m) := add_le_add
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR hu') hA)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR hv') hB)
    _ = (A+B)*R^(-c-m) := by ring
    _ ≤ R^m*R^(-c-m) := mul_le_mul_of_nonneg_right (hN₀ N hN) (Real.rpow_nonneg hRp.le _)
    _ = R^(-c) := by rw [← Real.rpow_add hRp]; congr 1; ring

theorem weak_radial_local_deletion_budget (d : ℕ) (hd : 0 < d)
    {u v c C : ℝ} (hC : 0 ≤ C) (hu : c*(d:ℝ) < u) (hv : c*(d:ℝ) < v) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ I : ℝ≥0∞,
      I^d ≤ ENNReal.ofReal (((2:ℝ)^N)^(-u))+
        (d:ℝ≥0∞)*ENNReal.ofReal (C*((2:ℝ)^N)^(-v)) →
      I ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  obtain ⟨N₀,hN₀⟩ := weak_radial_two_costs (A := 1) (B := (d:ℝ)*C)
    (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hC) hu hv
  refine ⟨N₀,fun N hN I hI => ?_⟩
  apply (ENNReal.pow_le_pow_left_iff hd.ne').mp
  have hR : 0 < (2:ℝ)^N := by positivity
  have he : (((2:ℝ)^N)^(-c))^d = ((2:ℝ)^N)^(-(c*(d:ℝ))) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hR.le]
    congr 1
    ring
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hR.le _),he]
  apply hI.trans
  have he' : (d:ℝ≥0∞)*ENNReal.ofReal (C*((2:ℝ)^N)^(-v)) =
      ENNReal.ofReal ((d:ℝ)*C*((2:ℝ)^N)^(-v)) := by
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  rw [he',← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by simpa only [one_mul] using hN₀ N hN)

end Falconer

end OAI

end ExtensionScope211

/- Source: OAI.MeasureTheory.Falconer.Radial.WeakRadialTotalCost. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope212



namespace OAI

/-! # Absorbing the actual regularization and radial deletion costs -/

namespace Falconer
open scoped ENNReal

theorem weak_radial_total_real_cost (J k : ℕ) {A lam a b f : ℝ}
    (hA : 0 ≤ A) (hlam : 0 < lam) (ha : 0 < a) (hb : 0 < b) (hf : 0 < f) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((2:ℝ)^N)^(-2:ℝ)+(N:ℝ)^k*((2:ℝ)^N)^(-lam)+
        (J:ℝ)*(A*((2:ℝ)^N)^(-a)+((2:ℝ)^N)^(-b))+
        ((J:ℝ)+1)*((2:ℝ)^N)^(-f) ≤ ((2:ℝ)^N)^(-c) := by
  let q := min (lam/2) (min a (min b (min f 2)))
  have hq : 0 < q := lt_min (half_pos hlam) (lt_min ha (lt_min hb (lt_min hf (by norm_num))))
  have hql : q ≤ lam/2 := min_le_left _ _
  have hqa : q ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hqb : q ≤ b := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hqf : q ≤ f := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hq2 : q ≤ 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let D : ℝ := 2+(J:ℝ)*A+(J:ℝ)+((J:ℝ)+1)
  obtain ⟨N₁,h₁⟩ := PlanarFalconer.fixed_polynomial_subpower k (half_pos hlam)
  obtain ⟨N₂,h₂⟩ := Regularization.fixed_constant_absorbed (half_pos hq) D
  refine ⟨q/2,half_pos hq,max 1 (max N₁ N₂),?_⟩
  intro N hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast ((le_max_left _ _).trans hN)
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let R : ℝ := (2:ℝ)^N
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hp : (N:ℝ)^k ≤ R^(lam/2) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith : (N:ℝ) ≤ 4*(N:ℝ)+1) k).trans (h₁ N hN₁)
  have hpoly : (N:ℝ)^k*R^(-lam) ≤ R^(-q) := by
    calc
      _ ≤ R^(lam/2)*R^(-lam) := mul_le_mul_of_nonneg_right hp (by positivity)
      _ = R^(-(lam/2)) := by rw [← Real.rpow_add hR]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  have hbound : R^(-2:ℝ)+(N:ℝ)^k*R^(-lam)+
      (J:ℝ)*(A*R^(-a)+R^(-b))+((J:ℝ)+1)*R^(-f) ≤ D*R^(-q) := by
    have h2 := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hq2)
    have ha' := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hqa)
    have hb' := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hqb)
    have hf' := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hqf)
    calc
      _ ≤ R^(-q)+R^(-q)+(J:ℝ)*(A*R^(-q)+R^(-q))+((J:ℝ)+1)*R^(-q) := by
        gcongr
      _ = _ := by dsimp [D]; ring
  apply hbound.trans
  calc
    _ ≤ R^(q/2)*R^(-q) := mul_le_mul_of_nonneg_right (h₂ N hN₂) (by positivity)
    _ = R^(-(q/2)) := by rw [← Real.rpow_add hR]; congr 1; ring

theorem dyadic_thin_cost (N : ℕ) : ((2:ℝ≥0∞)^(2*N))⁻¹ =
    ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ)) := by
  rw [Real.rpow_neg (by positivity),Real.rpow_two,
    ENNReal.ofReal_inv_of_pos (by positivity),ENNReal.ofReal_pow (by positivity)]
  rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat,
    ← pow_mul,Nat.mul_comm 2 N]

theorem weak_radial_total_cost (J k : ℕ) {A lam a b f : ℝ}
    (hA : 0 ≤ A) (hlam : 0 < lam) (ha : 0 < a) (hb : 0 < b) (hf : 0 < f) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((2:ℝ≥0∞)^(2*N))⁻¹+(N^k:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-lam))+
        (J:ℝ≥0∞)*(ENNReal.ofReal (A*((2:ℝ)^N)^(-a))+ENNReal.ofReal (((2:ℝ)^N)^(-b)))+
        (J+1:ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^N)^(-f)) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  obtain ⟨c,hc,N₀,hN₀⟩ := weak_radial_total_real_cost J k hA hlam ha hb hf
  refine ⟨c,hc,N₀,fun N hN => ?_⟩
  have hh := ENNReal.ofReal_le_ofReal (hN₀ N hN)
  rw [dyadic_thin_cost]
  convert hh using 1
  simp (disch := positivity) only [ENNReal.ofReal_add,ENNReal.ofReal_mul,
    ENNReal.ofReal_pow,ENNReal.ofReal_natCast,ENNReal.ofReal_one]
  norm_cast

end Falconer

end OAI

end ExtensionScope212

/- Source: OAI.MeasureTheory.Falconer.Estimates.NonendpointOneScale. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope213





namespace OAI

/-! # Uniform nonendpoint one-scale radial improvement

This is one orientation of the preparation lemma. The input reverse caps are
measured using the original probability laws and incoming pair relation.
-/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem nonendpoint_one_scale_gain (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {α t q C D s : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t)
    (ht : t-(h:ℝ) < 1) (htα : t < α) (hC : 0 ≤ C)
    (Q : DyadicCube (h+2)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        μ Q.carrierᶜ = 0 →
        (∀ y : Space (h+2), ∀ r > 0, μ (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space (h+2)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+2), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^q)) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ x u : Space (h+2), μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-q-c)) := by
  obtain ⟨ε₁,gain,hε₁,hgain,hclass⟩ := nonendpoint_contact_gain hpublished hq hq' hqt ht
    Q hQ hD hDdim hs
  obtain ⟨τ,hτ,hτε,hτgain,hτgain'⟩ := one_scale_loss_choice (h+2) hε₁ hgain
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hα : 0 ≤ α := by
    have hh := Nat.cast_nonneg (α := ℝ) h
    linarith only [hh,hq,hqt,htα]
  obtain ⟨lam,γ,hlam,hγ,hlamτ,H,Nc,hH,hcontrols,hcontact⟩ :=
    source_classes_uniform_contact (by omega : 0 < h+2) Q hside hα hqt htα hτ hC
  obtain ⟨Ng,hNg⟩ := hclass τ γ hτ hγ hτε hτgain hτgain'
  obtain ⟨c₀,hc₀,Nd,hNd⟩ := weak_radial_total_cost 0 (4*H+2)
    (A := 0) (by norm_num) hlam (by norm_num : (0:ℝ) < 1)
    (by norm_num : (0:ℝ) < 1) (by positivity : 0 < τ*γ/2)
  let c := min c₀ (gain*γ/8)
  have hc : 0 < c := lt_min hc₀ (by positivity)
  refine ⟨τ*γ,c,mul_pos hτ hγ,hc,max H (max (h+2+3) (max Nc (max Ng Nd))),?_⟩
  intro N hN μ ν _ _ hroot hfrost A P hA hP hAfull hPfull hsep hpin G hG hcap
  simp only [max_le_iff] at hN
  obtain ⟨hHN,hdN,hNc,hNg',hNd'⟩ := hN
  obtain ⟨hNp,hNB,_,hblock,hblock'⟩ := hcontrols N hNc
  have hlocal : ∀ p ∈ regularizationLeaves Q μ N,
      regularizationLabel Q μ N (N/H) p ∈ regularizationIndex Q μ N (N/H)
        (ENNReal.ofReal (((2:ℝ)^N)^(-lam))) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧
        ((sourceClass Q μ N (N/H) p).prod ν) (G \ G') ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))) ∧
        ∀ x u : Space (h+2), sourceClass Q μ N (N/H) p
          {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
            ENNReal.ofReal (((2:ℝ)^N)^(-q-gain*γ/8)) := by
    intro p hp hret
    obtain ⟨G',hG',_,hdel,hbound⟩ := hNg N hNg' μ ν (N/H) hNB lam hlam.le hlamτ
      hblock hblock' p hp (hcontact N hNc μ hfrost p hp hret)
      A P hA hP hAfull hPfull hsep hpin G hG hcap
    exact ⟨G',hG',hdel,hbound⟩
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := source_relative_regularization_gain Q hside μ ν G hG
    hroot hH hHN hdN (by positivity : 0 < ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
    (ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))))
    (ENNReal.ofReal (((2:ℝ)^N)^(-q-gain*γ/8))) (1/(2:ℝ)^N) hlocal
  refine ⟨G',hG',hsub,?_,?_⟩
  · apply hdel.trans
    have hd : ((2:ℝ≥0∞)^(2*N))⁻¹+(N^(4*H+2):ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-lam))+
        ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c₀)) := by
      simpa only [Nat.cast_zero,zero_mul,zero_add,add_zero,Nat.cast_one,one_mul] using hNd N hNd'
    exact hd.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ (by norm_num)) (neg_le_neg (min_le_left _ _))))
  · intro x u
    apply (hbound x u).trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) ?_))
    have hh : c ≤ gain*γ/8 := min_le_right _ _
    linarith only [hh]

end Falconer.Regularization

end OAI

end ExtensionScope213

/- Source: OAI.MeasureTheory.Falconer.ScaleNonendpointOneScale. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope214



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/MeasureTheory/Falconer/Estimates/NonendpointOneScale.lean.
All epsilon/gain/depth constants precede C; C may grow at the current scale.
The smaller incoming cap loss is increased internally to the original budget.
The original q<=1/2 restriction and fixed separation hypotheses remain explicit.
See probe root COPYING/PROVENANCE.json. Compilation and axiom audit pending.
-/

namespace OAI.Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem scale_nonendpoint_one_scale_gain (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {α t q D s : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t)
    (ht : t-(h:ℝ) < 1) (htα : t < α)
    (Q : DyadicCube (h+2)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ C : ℝ, 0 ≤ C → C ≤ ((2:ℝ)^N)^ε →
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        μ Q.carrierᶜ = 0 →
        (∀ y : Space (h+2), ∀ r > 0, μ (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space (h+2)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+2), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^q)) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ x u : Space (h+2), μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-q-c)) := by
  obtain ⟨ε₁,gain,hε₁,hgain,hclass⟩ := nonendpoint_contact_gain hpublished hq hq' hqt ht
    Q hQ hD hDdim hs
  obtain ⟨τ,hτ,hτε,hτgain,hτgain'⟩ := one_scale_loss_choice (h+2) hε₁ hgain
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hα : 0 ≤ α := by
    have hh := Nat.cast_nonneg (α := ℝ) h
    linarith only [hh,hq,hqt,htα]
  obtain ⟨lam,γ,hlam,hγ,hlamτ,H,Nc,hH,hcontrols,hcontact⟩ :=
    scale_source_classes_uniform_contact (by omega : 0 < h+2) Q hside hα hqt htα hτ
  obtain ⟨Ng,hNg⟩ := hclass τ γ hτ hγ hτε hτgain hτgain'
  obtain ⟨c₀,hc₀,Nd,hNd⟩ := weak_radial_total_cost 0 (4*H+2)
    (A := 0) (by norm_num) hlam (by norm_num : (0:ℝ) < 1)
    (by norm_num : (0:ℝ) < 1) (by positivity : 0 < τ*γ/2)
  let c := min c₀ (gain*γ/8)
  have hc : 0 < c := lt_min hc₀ (by positivity)
  let ε := min (τ*γ) (lam/2)
  have hε : 0 < ε := lt_min (mul_pos hτ hγ) (by positivity)
  refine ⟨ε,c,hε,hc,max H (max (h+2+3) (max Nc (max Ng Nd))),?_⟩
  intro N hN C hC hCscale μ ν _ _ hroot hfrost A P hA hP hAfull hPfull hsep hpin G hG hcap
  simp only [max_le_iff] at hN
  obtain ⟨hHN,hdN,hNc,hNg',hNd'⟩ := hN
  obtain ⟨hNp,hNB,_,hblock,hblock'⟩ := hcontrols N hNc
  have hCbudget : C ≤ ((2:ℝ)^N)^(lam/2) :=
    hCscale.trans (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (min_le_right _ _))
  have hcap0 : ∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space (h+2), ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(τ*γ)*r^q) := by
    filter_upwards [hcap] with z hz
    intro r hr hr1 u hu
    have hr0 : 0 ≤ r := (show 0 ≤ 1/(2:ℝ)^N by positivity).trans hr
    exact (hz r hr hr1 u hu).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (min_le_left _ _))
        (Real.rpow_nonneg hr0 _)))
  have hlocal : ∀ p ∈ regularizationLeaves Q μ N,
      regularizationLabel Q μ N (N/H) p ∈ regularizationIndex Q μ N (N/H)
        (ENNReal.ofReal (((2:ℝ)^N)^(-lam))) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧
        ((sourceClass Q μ N (N/H) p).prod ν) (G \ G') ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))) ∧
        ∀ x u : Space (h+2), sourceClass Q μ N (N/H) p
          {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
            ENNReal.ofReal (((2:ℝ)^N)^(-q-gain*γ/8)) := by
    intro p hp hret
    obtain ⟨G',hG',_,hdel,hbound⟩ := hNg N hNg' μ ν (N/H) hNB lam hlam.le hlamτ
      hblock hblock' p hp (hcontact N hNc C hC hCbudget μ hfrost p hp hret)
      A P hA hP hAfull hPfull hsep hpin G hG hcap0
    exact ⟨G',hG',hdel,hbound⟩
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := source_relative_regularization_gain Q hside μ ν G hG
    hroot hH hHN hdN (by positivity : 0 < ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
    (ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))))
    (ENNReal.ofReal (((2:ℝ)^N)^(-q-gain*γ/8))) (1/(2:ℝ)^N) hlocal
  refine ⟨G',hG',hsub,?_,?_⟩
  · apply hdel.trans
    have hd : ((2:ℝ≥0∞)^(2*N))⁻¹+(N^(4*H+2):ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-lam))+
        ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c₀)) := by
      simpa only [Nat.cast_zero,zero_mul,zero_add,add_zero,Nat.cast_one,one_mul] using hNd N hNd'
    exact hd.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ (by norm_num)) (neg_le_neg (min_le_left _ _))))
  · intro x u
    apply (hbound x u).trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) ?_))
    have hh : c ≤ gain*γ/8 := min_le_right _ _
    linarith only [hh]

end OAI.Falconer.Regularization

end ExtensionScope214

/- Source: OAI.MeasureTheory.Falconer.GeneralLabelledFurstenberg. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope215



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/MeasureTheory/Falconer/Angular/AngularGainFinite.lean.
The original proof uses b<=1/2 only when forwarding the finite published input.
Here the genuine general finite theorem supplies that input for every 0<b<f<1.
No published-theorem hypothesis remains. See probe COPYING/PROVENANCE.json.
Fixed-environment compilation and target axiom validation are pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable

theorem general_labelled_furstenberg_obstruction
    {b f : ℝ}
    (hb : 0 < b) (hbf : b < f) (hf : f < 1) :
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ P : Finset (Space 2), P.Nonempty → InBoundedLineChart P →
      FiniteSeparatedAt δ P → NormalizedFiniteBallBound δ f (δ ^ (-ε)) P →
    ∀ T : Space 2 → Finset (Space 2),
      (∀ x ∈ P, (T x).Nonempty ∧ InBoundedLineChart (T x) ∧
        FiniteSeparatedAt δ (T x) ∧ NormalizedFiniteBallBound δ b (δ ^ (-ε)) (T x) ∧
        ∀ l ∈ T x, TubeIncident δ x l) →
    ∀ (ι : Type) [DecidableEq ι] (D : Finset ι) (U : ι → Finset (Space 2)),
      (D.card : ℝ) ≤ δ ^ (-b - ε / 4) →
      (∀ i ∈ D, ((U i).card : ℝ) ≤ δ ^ (-b - ε / 4)) →
      (∀ x ∈ P, ∀ l ∈ T x, ∃ i ∈ D, l ∈ U i) → False := by
  obtain ⟨ε, δ₀, hε, _, hδ₀, hδ₀1, hF⟩ :=
    general_planar_furstenberg hb (hbf.trans hf) hbf (by linarith : f ≤ 2)
  refine ⟨ε, δ₀, hε, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hδsmall P hP hchart hsep hball T hT ι _ D U hD hU hcover
  have hδ1 : δ < 1 := hδsmall.trans_le hδ₀1
  have hlower := hF δ hδ hδsmall.le P hP hchart hsep hball T hT
  have hupper := labelled_line_union_card_le P T D U hcover hU
  have hcard : ((P.biUnion T).card : ℝ) ≤ δ ^ (-2 * b - ε / 2) := by
    calc
      ((P.biUnion T).card : ℝ) ≤ (D.card : ℝ) * δ ^ (-b - ε / 4) := hupper
      _ ≤ δ ^ (-b - ε / 4) * δ ^ (-b - ε / 4) :=
        mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (-2 * b - ε / 2) := by
        rw [← Real.rpow_add hδ]
        congr 1
        ring
  have hstrict : δ ^ (-2 * b - ε / 2) < δ ^ (-2 * b - ε) :=
    Real.rpow_lt_rpow_of_exponent_gt hδ hδ1 (by linarith)
  exact (not_lt_of_ge (hlower.trans hcard)) hstrict

end OAI.Falconer

end ExtensionScope215

/- Source: OAI.MeasureTheory.Falconer.GeneralSampledFurstenberg. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope216



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/MeasureTheory/Falconer/Incidence/SampledFurstenberg.lean.
The original proof uses b<=1/2 only when forwarding the finite published input.
Here the genuine general finite theorem supplies that input for every 0<b<f<1.
No published-theorem hypothesis remains. See probe COPYING/PROVENANCE.json.
Fixed-environment compilation and target axiom validation are pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable

theorem general_sampled_furstenberg_obstruction
    {b f : ℝ}
    (hb : 0 < b) (hbf : b < f) (hf : f < 1) :
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ P : Finset (Space 2), P.Nonempty →
      (∀ x ∈ P, |x 0| ≤ 1 / 4 ∧ |x 1| ≤ 1 / 4) →
      FiniteSeparatedAt δ P → NormalizedFiniteBallBound δ f (δ^(-ε)) P →
    ∀ (ι : Type) [DecidableEq ι] (D : Finset ι) (m : ι → ℝ)
      (S : Space 2 → Finset ι) (U : ι → Finset (Space 2)) (K I : ℝ),
      0 < K → 0 < I → D.Nonempty →
      (D.card : ℝ) * δ^b ≤ 2 →
      (∀ i ∈ D, |m i| ≤ 1 / 2) →
      (∀ a r : ℝ, δ ≤ r → ((D.filter (fun i => |m i-a| ≤ r)).card : ℝ) ≤
        (K * (D.card : ℝ)) * r^b) →
      (∀ x ∈ P, S x ⊆ D ∧ I * (D.card : ℝ) ≤ ((S x).card : ℝ)) →
      2 * 2^b * K^2 / I ≤ δ^(-ε) →
      (D.card : ℝ) ≤ δ^(-b-ε/4) →
      (∀ i ∈ D, ((U i).card : ℝ) ≤ δ^(-b-ε/4)) →
      (∀ x ∈ P, ∀ i ∈ S x, roundedIncidentLine δ x (m i) ∈ U i) → False := by
  obtain ⟨ε, δ₁, hε, hδ₁, _, hF⟩ :=
    general_labelled_furstenberg_obstruction hb hbf hf
  refine ⟨ε, min δ₁ (1/2), hε, lt_min hδ₁ (by norm_num), min_le_right _ _, ?_⟩
  intro δ hδ hδsmall P hP hchart hsep hpoint ι _ D m S U K I hK hI hD
    hsize hm hcount hS hloss hDcard hU hcover
  have hδ1 : δ ≤ 1 / 2 := hδsmall.le.trans (min_le_right _ _)
  let T : Space 2 → Finset (Space 2) := fun x => roundedLineFamily δ x m (S x)
  have hT (x : Space 2) (hx : x ∈ P) :
      (T x).Nonempty ∧ InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
      NormalizedFiniteBallBound δ b (δ^(-ε)) (T x) ∧
      ∀ l ∈ T x, TubeIncident δ x l := by
    have hSn : (S x).Nonempty := by
      apply Finset.card_pos.mp
      have hn : (0 : ℝ) < D.card := by exact_mod_cast hD.card_pos
      have hspos := (mul_pos hI hn).trans_le (hS x hx).2
      exact_mod_cast hspos
    refine ⟨roundedLineFamily_nonempty δ x m hSn, ?_,
      roundedIncidentLine_family_separated hδ x m (S x), ?_, ?_⟩
    · intro l hl
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
      exact roundedIncidentLine_in_chart hδ hδ1 x (hchart x hx).1 (hchart x hx).2
        (m i) (hm i ((hS x hx).1 hi))
    · have hn := roundedLineFamily_normalized_of_large_sample hδ hK hI x m D (S x)
        hD (hS x hx).1 hsize (hS x hx).2 hcount
      intro z r hδr hr
      apply (hn z r hδr hr).trans
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right hloss (Real.rpow_nonneg (hδ.trans_le hδr).le _)
    · intro l hl
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
      exact roundedIncidentLine_incident hδ x (m i)
  have hPchart : InBoundedLineChart P := by
    intro x hx
    exact ⟨(hchart x hx).1.trans (by norm_num), (hchart x hx).2.trans (by norm_num)⟩
  apply hF δ hδ (hδsmall.trans_le (min_le_left _ _)) P hP hPchart hsep hpoint T hT
    ι D U hDcard hU
  intro x hx l hl
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
  exact ⟨i, (hS x hx).1 hi, hcover x hx i hi⟩

end OAI.Falconer

end ExtensionScope216

/- Source: OAI.MeasureTheory.Falconer.GeneralPlanarMeasureIncidence. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope217



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/MeasureTheory/Falconer/Incidence/PlanarIncidence.lean.
The original proof uses b<=1/2 only when forwarding the finite published input.
Here the genuine general finite theorem supplies that input for every 0<b<f<1.
No published-theorem hypothesis remains. See probe COPYING/PROVENANCE.json.
Fixed-environment compilation and target axiom validation are pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable

theorem general_planar_measure_incidence_obstruction
    {b f : ℝ}
    (hb : 0 < b) (hbf : b < f) (hf : f < 1) :
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1/2 ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (X W : Type) [MeasurableSpace X] [MeasurableSpace W]
      (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
      (p : X → Space 2) (m : W → ℝ) (E : X → W → Prop),
      Measurable p → Measurable m → MeasurableSet {z : X × W | E z.1 z.2} →
      (∀ x, |p x 0| ≤ 1/4 ∧ |p x 1| ≤ 1/4) → (∀ w, |m w| ≤ 1/2) →
    ∀ (K B I : ℝ) (n l L H J : ℕ) (A : W → Finset ℝ),
      0 ≤ K → 1 ≤ B → 0 < I → 0 < n → 0 < l →
      δ⁻¹+1 ≤ L → δ⁻¹ ≤ H →
      1 ≤ (n : ℝ)*δ^b → (n : ℝ)*δ^b ≤ 2 →
      1 ≤ (l : ℝ)*δ^f → (l : ℝ)*δ^f ≤ 2 →
      (∀ c r, δ ≤ r → (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ K*r^f) →
      (∀ a r, δ ≤ r → (ν : Measure W).real {w | |m w-a| ≤ r} ≤ K*r^b) →
      I ≤ (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) →
      (((2*L+1)^2*H : ℕ) : ℝ)*exp (-B) ≤ I/16 →
      2*(8*samplingBallLoss K B f/I)^2 ≤ δ^(-ε) →
      8*2^b*(samplingBallLoss K B b)^2/I ≤ δ^(-ε) →
      (n : ℝ) ≤ δ^(-b-ε/4) →
      (∀ w, ((A w).card * (2*J+1) : ℕ) ≤ δ^(-b-ε/4)) →
      (∀ x w, E x w → ∃ a ∈ A w, |p x 1-m w*p x 0-a| ≤ ((J : ℝ)-2)*δ) →
      False := by
  obtain ⟨ε, δ₀, hε, hδ₀, hδ₀', hFurst⟩ :=
    general_sampled_furstenberg_obstruction hb hbf hf
  refine ⟨ε, δ₀, hε, hδ₀, hδ₀', ?_⟩
  intro δ hδ hδsmall X W _ _ μ ν p m E hp hm hE hpchart hmchart
    K B I n l L H J A hK hB hI hn hl hL hH hnsize hnsize' hlsize hlsize'
    hpball hmball hmean hfail hPloss hTloss hnc hAc hcover
  let F : X → W → ℝ := fun x w => if E x w then 1 else 0
  have hF : Measurable (Function.uncurry F) := by
    exact measurable_const.indicator hE
  have hF0 (x : X) (w : W) : 0 ≤ F x w := by simp only [F]; split <;> norm_num
  have hF1 (x : X) (w : W) : F x w ≤ 1 := by simp only [F]; split <;> norm_num
  have hmbound (w : W) (i : Fin 2) : |slopePoint (m w) i| ≤ 1 := by
    fin_cases i
    · exact (hmchart w).trans (by norm_num)
    · simp
  obtain ⟨ω, hω, hgood⟩ := exists_uniform_incidence_sample μ ν (slopePoint ∘ m)
    (continuous_slopePoint.measurable.comp hm) hmbound F hF hF0 hF1 hn hδ hb.le hK hB
    hL hH hnsize (slopePoint_ball_mass_le ν m hmball) hI hmean (hfail.trans (by linarith))
  let G := {x | I/4 ≤ iidAverage (F x) ω}
  have hG : MeasurableSet G := by
    apply measurableSet_le measurable_const
    unfold iidAverage
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    exact hF.comp (measurable_id.prodMk measurable_const)
  have hpbound (x : X) (i : Fin 2) : |p x i| ≤ 1 := by
    fin_cases i
    · exact (hpchart x).1.trans (by norm_num)
    · exact (hpchart x).2.trans (by norm_num)
  obtain ⟨ξ, D, P, hDn, hDG, hPn, hPD, hPsep, hPball⟩ :=
    exists_good_separated_point_sample μ p hp hpbound G hG (by positivity : 0 < I/4)
      hgood hl hδ (hb.trans hbf).le hK hB hL hH hlsize hlsize' hpball
      (by convert hfail using 1; ring)
  have hrep : ∀ x ∈ P, ∃ y : X, p y = x ∧ y ∈ G := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp (hPD hx)
    exact ⟨ξ i, hix, hDG i hi⟩
  let rep : {x // x ∈ P} → X := fun x => Classical.choose (hrep x.val x.property)
  have hrep' (x : Space 2) (hx : x ∈ P) : p (rep ⟨x,hx⟩) = x ∧ rep ⟨x,hx⟩ ∈ G :=
    Classical.choose_spec (hrep x hx)
  let S : Space 2 → Finset (Fin n) := fun x =>
    if hx : x ∈ P then incidentLabels E ω (rep ⟨x,hx⟩) else ∅
  let U : Fin n → Finset (Space 2) := fun i =>
    stripLineCandidates δ (m (ω i)) (A (ω i)) J
  have hPchart (x : Space 2) (hx : x ∈ P) : |x 0| ≤ 1/4 ∧ |x 1| ≤ 1/4 := by
    rw [← (hrep' x hx).1]
    exact hpchart _
  have hPbound : NormalizedFiniteBallBound δ f (δ^(-ε)) P := by
    have he : 2*(2*samplingBallLoss K B f/(I/4))^2 =
        2*(8*samplingBallLoss K B f/I)^2 := by ring
    change NormalizedFiniteBallBound δ f (2*(2*samplingBallLoss K B f/(I/4))^2) P at hPball
    rw [he] at hPball
    intro c r hdr hr1
    apply (hPball c r hdr hr1).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPloss
      (Real.rpow_nonneg (hδ.le.trans hdr) _)) (Nat.cast_nonneg _)
  have hcount (a r : ℝ) (hdr : δ ≤ r) :
      (((Finset.univ : Finset (Fin n)).filter (fun i => |m (ω i)-a| ≤ r)).card : ℝ) ≤
        (samplingBallLoss K B b * ((Finset.univ : Finset (Fin n)).card : ℝ))*r^b := by
    have hh := hω (slopePoint a) r hdr
    simpa only [Function.comp_apply, slopePoint_dist, iidCount_eq_card_filter,
      Finset.card_univ, Fintype.card_fin, Set.mem_ofPred_eq, samplingBallLoss] using hh
  apply hFurst δ hδ hδsmall P hPn hPchart hPsep hPbound (Fin n) Finset.univ
    (m ∘ ω) S U (samplingBallLoss K B b) (I/4)
    (samplingBallLoss_pos hK hB) (by positivity) ⟨⟨0,hn⟩, Finset.mem_univ _⟩
    (by simpa using hnsize') (fun i _ => hmchart (ω i)) hcount
  · intro x hx
    constructor
    · exact Finset.subset_univ _
    · simp only [S, dite_eq_left hx, Finset.card_univ, Fintype.card_fin]
      exact empirical_incidence_card_lower E hn ω _ (hrep' x hx).2
  · convert hTloss using 1; ring
  · simpa using hnc
  · intro i _
    exact (show ((U i).card : ℝ) ≤ ((A (ω i)).card * (2*J+1) : ℕ) by
      exact_mod_cast stripLineCandidates_card_le δ (m (ω i)) (A (ω i)) J).trans (hAc (ω i))
  · intro x hx i hi
    have hiy : E (rep ⟨x,hx⟩) (ω i) := by
      simpa only [S, dite_eq_left hx, incidentLabels, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    apply roundedIncidentLine_mem_stripLineCandidates (C := (J : ℝ)-2) hδ _ J (by linarith)
      x ((hPchart x hx).1.trans (by norm_num))
    obtain ⟨a, ha, he⟩ := hcover _ _ hiy
    rw [(hrep' x hx).1] at he
    exact ⟨a,ha,he⟩

end OAI.Falconer

end ExtensionScope217

/- Source: OAI.MeasureTheory.Falconer.GeneralPlanarMeasureGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope218



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/MeasureTheory/Falconer/Estimates/PlanarGain.lean.
The original proof uses b<=1/2 only when forwarding the finite published input.
Here the genuine general finite theorem supplies that input for every 0<b<f<1.
No published-theorem hypothesis remains. See probe COPYING/PROVENANCE.json.
Fixed-environment compilation and target axiom validation are pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable

theorem general_planar_measure_projection_gain
    {b f : ℝ}
    (hb : 0 < b) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (X W : Type) [MeasurableSpace X] [MeasurableSpace W]
      (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
      (p : X → Space 2) (m : W → ℝ) (E : X → W → Prop),
      Measurable p → Measurable m → MeasurableSet {z : X × W | E z.1 z.2} →
      (∀ x, |p x 0| ≤ 1/4 ∧ |p x 1| ≤ 1/4) → (∀ w, |m w| ≤ 1/2) →
      (∀ c r, δ ≤ r → (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ δ^(-η)*r^f) →
      (∀ a r, δ ≤ r → (ν : Measure W).real {w | |m w-a| ≤ r} ≤ δ^(-η)*r^b) →
    ∀ A : W → Finset ℝ,
      (∀ w, ((A w).card : ℝ) ≤ δ^(-b-η)) →
      (∀ x w, E x w → ∃ a ∈ A w, |p x 1-m w*p x 0-a| ≤ C*δ) →
      (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) ≤ δ^η := by
  obtain ⟨ε, δF, hε, hδF, _, hObs⟩ :=
    general_planar_measure_incidence_obstruction hb hbf hf
  obtain ⟨J, hJ⟩ := exists_nat_ge (C+2)
  let η := min (ε/100) (1/2)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hηε : η ≤ ε/100 := min_le_left _ _
  have hmargin : 4*η < ε := by linarith
  have hready := eventually_planarSamplingReady (f := f) hb hη hη1 hmargin J
  obtain ⟨δ₁, hδ₁, hδready⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0 : ℝ) < 1 by norm_num)).mp hready
  refine ⟨η, min δF δ₁, hη, lt_min hδF hδ₁, ?_⟩
  intro δ hδ hδsmall X W _ _ μ ν p m E hp hm hE hpchart hmchart hpball hmball A hA hcover
  have hr : PlanarSamplingReady δ b f η ε J := hδready ⟨hδ, hδsmall.trans_le (min_le_right _ _)⟩
  have hδ1 : δ ≤ 1 := hr.scale_small.trans (by norm_num)
  obtain ⟨hn, hnsize, hnsize'⟩ := sampling_ceil_size hδ hδ1 hb.le
  obtain ⟨hl, hlsize, hlsize'⟩ := sampling_ceil_size hδ hδ1 (hb.trans hbf).le
  by_contra hnot
  have hmean : δ^η ≤ (∫ w, ∫ x, if E x w then (1 : ℝ) else 0
      ∂(μ : Measure X) ∂(ν : Measure W)) := (lt_of_not_ge hnot).le
  apply hObs δ hδ (hδsmall.trans_le (min_le_left _ _)) X W μ ν p m E hp hm hE hpchart hmchart
    (δ^(-η)) (-10*Real.log δ) (δ^η) (Nat.ceil (δ^(-b))) (Nat.ceil (δ^(-f)))
    (Nat.ceil (δ⁻¹+1)) (Nat.ceil δ⁻¹) J A
    (Real.rpow_nonneg hδ.le _) hr.budget (Real.rpow_pos_of_pos hδ _) hn hl
    (Nat.le_ceil _) (Nat.le_ceil _) hnsize hnsize' hlsize hlsize' hpball hmball
    hmean hr.tail hr.point_loss hr.direction_loss hr.count
  · intro w
    calc
      (((A w).card * (2*J+1) : ℕ) : ℝ) = ((A w).card : ℝ)*(2*J+1) := by norm_cast
      _ ≤ δ^(-b-η)*(2*J+1) := mul_le_mul_of_nonneg_right (hA w) (by positivity)
      _ ≤ δ^(-b-ε/4) := hr.cover
  · intro x w hx
    obtain ⟨a, ha, he⟩ := hcover x w hx
    refine ⟨a, ha, he.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith : C ≤ (J : ℝ)-2) hδ.le

end OAI.Falconer

end ExtensionScope218

/- Source: OAI.MeasureTheory.Falconer.GeneralPlanarUnitTubeGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope219



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Radial/PlanarUnitTubeGain.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_planar_unit_tube_gain
     {b f : ℝ}
    (hb : 0 < b) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (X W : Type) [MeasurableSpace X] [MeasurableSpace W]
      (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
      (p : X → Space 2) (q : W → Space 2) (E : X → W → Prop),
      Measurable p → Measurable q → MeasurableSet {z : X × W | E z.1 z.2} →
      (∀ x, ‖p x‖ ≤ 1/4) → (∀ w, ‖q w‖ = 1) →
      (∀ w, dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
      (∀ c r, δ ≤ r → (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ δ^(-η)*r^f) →
      (∀ c r, δ ≤ r → (ν : Measure W).real {w | dist (q w) c ≤ 2*r} ≤ δ^(-η)*r^b) →
    ∀ (κ : Type) (J : W → Finset κ) (a : κ → Space 2),
      (∀ w, ((J w).card : ℝ) ≤ δ^(-b-η)) →
      (∀ x w, E x w → ∃ i ∈ J w, ‖perpendicularPart (q w) (p x-a i)‖ ≤ C*δ) →
      (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) ≤ δ^η := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := general_planar_measure_projection_gain hb hbf hf ((3/2)*C)
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro δ hδ hδsmall X W _ _ μ ν p q E hp hq hE hpbound hqunit hqchart hpball hqball κ J a hJ hcover
  have hpos (w : W) : 0 < q w 0 := (planarSlope_small_of_axis_close (hqchart w)).1
  have hslope (w : W) : |planarSlope (q w)| ≤ 1/2 :=
    (planarSlope_small_of_axis_close (hqchart w)).2
  let A : W → Finset ℝ := fun w => (J w).image (fun i => planarIntercept (q w) (a i))
  refine hgain δ hδ hδsmall X W μ ν p (fun w => planarSlope (q w)) E hp
    (by unfold planarSlope; fun_prop) hE
    (fun x => ⟨(PiLp.norm_apply_le (p x) 0).trans (hpbound x),
      (PiLp.norm_apply_le (p x) 1).trans (hpbound x)⟩) hslope hpball ?_ A ?_ ?_
  · intro c r hr
    exact (measureReal_mono (μ := (ν : Measure W))
      (planar_slope_ball_subset q hqunit hpos c r)).trans (hqball _ r hr)
  · intro w
    exact (Nat.cast_le.mpr (Finset.card_image_le)).trans (hJ w)
  · intro x w hx
    obtain ⟨i,hi,ht⟩ := hcover x w hx
    refine ⟨planarIntercept (q w) (a i),Finset.mem_image.mpr ⟨i,hi,rfl⟩,?_⟩
    simpa only [mul_assoc] using planar_tube_strip (hpos w).ne' (hslope w) ht


end OAI.Falconer

end ExtensionScope219

/- Source: OAI.MeasureTheory.Falconer.GeneralPlanarAETubeGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope220



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Radial/PlanarAETubeGain.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_planar_ae_tube_gain
     {b f : ℝ}
    (hb : 0 < b) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (X W : Type) [MeasurableSpace X] [MeasurableSpace W]
      (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
      (p : X → Space 2) (q : W → Space 2) (E : X → W → Prop),
      Measurable p → Measurable q → MeasurableSet {z : X × W | E z.1 z.2} →
      (∀ᵐ x ∂(μ : Measure X), ‖p x‖ ≤ 1/4) →
      (∀ᵐ w ∂(ν : Measure W), ‖q w‖ = 1 ∧
        dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
      (∀ c r, δ ≤ r → (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ δ^(-η)*r^f) →
      (∀ c r, δ ≤ r → (ν : Measure W).real {w | dist (q w) c ≤ 2*r} ≤ δ^(-η)*r^b) →
    ∀ (κ : Type) (J : W → Finset κ) (a : κ → Space 2),
      (∀ w, ((J w).card : ℝ) ≤ δ^(-b-η)) →
      (∀ x w, E x w → ∃ i ∈ J w, ‖perpendicularPart (q w) (p x-a i)‖ ≤ C*δ) →
      (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) ≤ δ^η := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := general_planar_unit_tube_gain hb hbf hf C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro δ hδ hδsmall X W _ _ μ ν p q E hp hq hE hpb hqb hpball hqball κ J a hJ hcover
  let F : X → W → Prop := fun x w => E x w ∧ ‖p x‖ ≤ 1/4 ∧
    (‖q w‖ = 1 ∧ dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4)
  have hP : MeasurableSet {x | ‖p x‖ ≤ 1/4} := measurableSet_le hp.norm measurable_const
  have hQ : MeasurableSet {w | ‖q w‖ = 1 ∧
      dist (q w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4} :=
    (measurableSet_eq_fun hq.norm measurable_const).inter
      (measurableSet_le (hq.dist measurable_const) measurable_const)
  have hF : MeasurableSet {z : X × W | F z.1 z.2} :=
    hE.inter ((hP.preimage measurable_fst).inter (hQ.preimage measurable_snd))
  have hpb' (c : Space 2) (r : ℝ) (hr : δ ≤ r) :
      (μ : Measure X).real {x | dist (boundedPlanarPoint (p x)) c ≤ r} ≤ δ^(-η)*r^f := by
    have he : {x | dist (boundedPlanarPoint (p x)) c ≤ r} =ᵐ[(μ : Measure X)]
        {x | dist (p x) c ≤ r} := by
      filter_upwards [hpb] with x hx
      simp only [boundedPlanarPoint_eq hx]
    rw [measureReal_congr he]
    exact hpball c r hr
  have hqb' (c : Space 2) (r : ℝ) (hr : δ ≤ r) :
      (ν : Measure W).real {w | dist (chartedPlanarDirection (q w)) c ≤ 2*r} ≤ δ^(-η)*r^b := by
    have he : {w | dist (chartedPlanarDirection (q w)) c ≤ 2*r} =ᵐ[(ν : Measure W)]
        {w | dist (q w) c ≤ 2*r} := by
      filter_upwards [hqb] with w hw
      simp only [chartedPlanarDirection_eq hw]
    rw [measureReal_congr he]
    exact hqball c r hr
  have hsmall : (∫ w, ∫ x, @ite ℝ (F x w) (Classical.propDecidable (F x w)) 1 0
      ∂(μ : Measure X) ∂(ν : Measure W)) ≤ δ^η := by
    apply hgain δ hδ hδsmall X W μ ν (fun x => boundedPlanarPoint (p x))
      (fun w => chartedPlanarDirection (q w)) F
      (boundedPlanarPoint_measurable.comp hp) (chartedPlanarDirection_measurable.comp hq) hF
      (fun x => boundedPlanarPoint_norm (p x)) (fun w => chartedPlanarDirection_unit (q w))
      (fun w => chartedPlanarDirection_chart (q w)) hpb' hqb' κ J a hJ
    intro x w hx
    obtain ⟨i,hi,ht⟩ := hcover x w hx.1
    refine ⟨i,hi,?_⟩
    rw [boundedPlanarPoint_eq hx.2.1,chartedPlanarDirection_eq hx.2.2]
    exact ht
  have he : (∫ w, ∫ x, @ite ℝ (F x w) (Classical.propDecidable (F x w)) 1 0
      ∂(μ : Measure X) ∂(ν : Measure W)) =
      (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) := by
    apply integral_congr_ae
    filter_upwards [hqb] with w hw
    apply integral_congr_ae
    filter_upwards [hpb] with x hx
    simp only [F,hx,hw,and_true]
  rw [he] at hsmall
  exact hsmall


end OAI.Falconer

end ExtensionScope220

/- Source: OAI.MeasureTheory.Falconer.GeneralPlanarSelectedGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope221



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Estimates/PlanarSelectedGain.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable
variable {d h : ℕ} {κ : Type*}

theorem general_planar_selected_slice_gain
     {b f : ℝ}
    (hb : 0 < b) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (d h : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (A : Fin h → Space d) (z : Space h) (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 2)
      (α : ProbabilityMeasure (Space d)) (β : ProbabilityMeasure (Sphere d))
      (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ) (a : κ → Space d)
      (M K T : ℝ),
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    0 ≤ M → 0 ≤ K → 0 ≤ T → T ≤ δ^(-b-η) →
    (∀ i, ‖A i‖ ≤ M) →
    (∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖) →
    K*((h:ℝ)*δ) < 1 →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-a i)‖ ≤ C*δ) →
    (∀ᵐ x ∂(α : Measure (Space d)), ‖x‖ ≤ 1/4) →
    (∀ᵐ w : Sphere d ∂(β : Measure (Sphere d)),
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
    (∀ c r, δ ≤ r → (α : Measure (Space d)).real
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ r} ≤ δ^(-η)*r^f) →
    (∀ c r, δ ≤ r → (β : Measure (Sphere d)).real
      {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ 2*r}
        ≤ δ^(-η)*r^b) →
    ((α : Measure (Space d)).prod (β : Measure (Sphere d))).real
      (selectedActiveRelation A z δ E J a (δ+(2*(1/4))*δ+(C*δ)*M) T) ≤ δ^η := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := general_planar_ae_tube_gain hb hbf hf C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro δ hδ hδsmall d h κ _ _ A z e α β E J a M K T hE hJ hM hK hT hTbound
    hA hbound hsmall hbounded hanchors hcover hα hβ hpball hqball
  let R := δ+(2*(1/4))*δ+(C*δ)*M
  let F := selectedActiveRelation A z δ E J a R T
  have hF : MeasurableSet F := selectedActiveRelation_measurable A z δ E hE J hJ a R T
  rw [← slice_iterated_incidence (α : Measure (Space d)) (β : Measure (Sphere d)) F hF]
  refine hgain δ hδ hδsmall (Space d) (Sphere d) α β
    (fun x => e ((gaussianRowMap A).ker.orthogonalProjectionOnto x))
    (fun w : Sphere d => normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
    (fun x w => (x,w) ∈ F) (by fun_prop)
    (by unfold NormedSpace.normalize; fun_prop) hF ?_ hβ hpball hqball κ
    (fun w => cappedActiveAnchors A z (J w) a R T)
    (fun i => e ((gaussianRowMap A).ker.orthogonalProjectionOnto (a i))) ?_ ?_
  · filter_upwards [hα] with x hx
    rw [e.norm_map]
    exact ((gaussianRowMap A).ker.norm_starProjection_apply_le x).trans hx
  · intro w
    exact (cappedActiveAnchors_card A z (J w) a R hT).trans hTbound
  · intro x w hx
    exact gaussian_capped_coordinate_cover A z e E J a hM hK hT hA hbound hsmall
      hbounded hanchors hcover hx.2.1 hx.2.2 hx.1


end OAI.Falconer

end ExtensionScope221

/- Source: OAI.MeasureTheory.Falconer.GeneralGaussianPlanarExclusion. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope222



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Slicing/GaussianPlanarExclusion.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_gaussian_planar_slice_exclusion
     {b f : ℝ}
    (hb : 0 < b) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ (N d h : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (A : Fin h → Space d) (z : Space h) (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 2)
      (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ) (a : κ → Space d)
      (K V M T a₀ : ℝ),
    1/(2:ℝ)^N < δ₀ → 0 < K → 0 < V → 0 ≤ M → 0 ≤ T →
    T ≤ (1/(2:ℝ)^N)^(-b-η) →
    1 ≤ a₀ → 1 ≤ 4*K^10*V → 4+8*(h:ℝ) ≤ a₀ →
    (4*K^10*V)*(4*a₀)^f ≤ (1/(2:ℝ)^N)^(-η) →
    (4*K^10*V)*(8*a₀)^b ≤ (1/(2:ℝ)^N)^(-η) →
    (1/(2:ℝ)^N)^η < 1/(4*K^10*V) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ i, ‖A i‖ ≤ M) →
    (∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖) →
    2*((h:ℝ)*(1/(2:ℝ)^N)) < 1 →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) →
    (∀ᵐ w : Sphere d ∂ν, w ∈ gaussianDirectionBand A (1/(2:ℝ)^N) →
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
    gaussianPrunedPairMass μ ν (1/(2:ℝ)^N)
      (fun g : Fin (N+1) => (1/(2:ℝ)^g.val)/2)
      (fun g => ENNReal.ofReal (K^6*(1/(2:ℝ)^g.val)^f))
      (fun g => ENNReal.ofReal (K^3*(1/(2:ℝ)^g.val)^b)) (ENNReal.ofReal (K^3))
      (gaussianActiveRelation E J a
        ((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+(C*(1/(2:ℝ)^N))*M)
        (ENNReal.ofReal T) true) (A,z) ≤ ENNReal.ofReal (1/(4*K*V)) := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := general_planar_selected_slice_gain hb hbf hf C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro N d h κ _ _ A z e μ ν _ _ E J a K V M T a₀ hδsmall hK hV hM hT hTbound
    ha₀ hH haK hpcoef hqcoef hlow hE hJ hA hbound hsmall hEb hanchors hcover hμ hν
  let δ : ℝ := 1/(2:ℝ)^N
  let r : Fin (N+1) → ℝ := fun g => (1/(2:ℝ)^g.val)/2
  let TP : Fin (N+1) → ℝ≥0∞ := fun g => ENNReal.ofReal (K^6*(1/(2:ℝ)^g.val)^f)
  let TD : Fin (N+1) → ℝ≥0∞ := fun g => ENNReal.ofReal (K^3*(1/(2:ℝ)^g.val)^b)
  let α := (gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z))
  let β := (gaussianDirectionSliceMeasure ν A δ).restrict
    (gaussianDirectionGood ν δ r TD (ENNReal.ofReal (K^3)) A)
  let R := δ+(2*(1/4))*δ+(C*δ)*M
  let F := selectedActiveRelation A z δ E J a R T
  have hδ : 0 < δ := by dsimp [δ]; positivity
  by_contra hnot
  have hmass : ENNReal.ofReal (1/(4*K*V)) ≤ (α.prod β) F := by
    have hi := (lt_of_not_ge hnot).le
    change _ ≤ gaussianPrunedIncidence μ ν δ r TP TD (ENNReal.ofReal (K^3)) F (A,z)
    rw [show F = {u | ((A,z),u) ∈ gaussianActiveRelation E J a R (ENNReal.ofReal T) true} ∩
      (gaussianPointBand A z δ ×ˢ gaussianDirectionBand A δ) from rfl,
      gaussian_pruned_incidence_inter_bands μ ν δ r TP TD (ENNReal.ofReal (K^3))
        {u | ((A,z),u) ∈ gaussianActiveRelation E J a R (ENNReal.ofReal T) true} (A,z)]
    exact hi
  have hαmass : α univ ≤ ENNReal.ofReal (K^6) := by
    have hm := gaussianPointGood_mass μ δ r TP (A,z) hμ 0 (by norm_num [r])
    simpa only [TP,Fin.val_zero,pow_zero,div_one,Real.one_rpow,mul_one] using hm
  have hβmass : β univ ≤ ENNReal.ofReal (K^3) := gaussianDirectionGood_mass ν δ r TD _ A
  obtain ⟨hα,hβ,hαratio,hβratio,_,_,hinc⟩ :=
    polynomial_slice_normalization α β F hK hV hαmass hβmass hmass
  let α' := normalizedSliceLaw α hα
  let β' := normalizedSliceLaw β hβ
  have hpball (c : Space 2) (s : ℝ) (hs : δ ≤ s) :
      (α' : Measure (Space d)).real {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s}
        ≤ δ^(-η)*s^f := by
    have hh := gaussian_point_normalized_frostman μ A z e N r TP (fun _ => rfl)
      (by norm_num) (by norm_num : (0:ℝ) < 1) ha₀ hH (pow_nonneg hK.le 6)
      (hb.le.trans hbf.le) hbound (by linarith) (fun _ => le_rfl) hα hαratio c s hs
    simp only [inv_one,one_smul] at hh
    have hs0 : 0 ≤ s := hδ.le.trans hs
    have hc : (4*K^10*V)*(4*a₀*s)^f ≤ δ^(-η)*s^f := by
      rw [Real.mul_rpow (by positivity) hs0]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hpcoef (Real.rpow_nonneg hs0 f)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans (by
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (4*K^10*V)*(4*a₀*s)^f)] using hc)
  have hqball (c : Space 2) (s : ℝ) (hs : δ ≤ s) :
      (β' : Measure (Sphere d)).real
        {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ 2*s}
        ≤ δ^(-η)*s^b := by
    have hs0 : 0 ≤ s := hδ.le.trans hs
    have hh := gaussian_direction_normalized_frostman ν A e N r TD (ENNReal.ofReal (K^3))
      (fun _ => rfl) (by norm_num) ha₀ hH (pow_nonneg hK.le 3) hb.le hbound hsmall
      (by linarith) (fun _ => le_rfl) hβ hβratio c (2*s) (by linarith)
    have hc : (4*K^10*V)*(4*a₀*(2*s))^b ≤ δ^(-η)*s^b := by
      rw [show 4*a₀*(2*s) = (8*a₀)*s by ring,Real.mul_rpow (by positivity) hs0]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hqcoef (Real.rpow_nonneg hs0 b)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans (by
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (4*K^10*V)*(4*a₀*(2*s))^b)] using hc)
  have hαsupport : ∀ᵐ x ∂(α' : Measure (Space d)), ‖x‖ ≤ 1/4 :=
    normalizedSliceLaw_ae α hα (ae_restrict_of_ae (gaussianPointSliceMeasure_ae_of_ae μ A z δ hμ))
  have hβsupport : ∀ᵐ (w : Sphere d) ∂(β' : Measure (Sphere d)),
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 := by
    apply normalizedSliceLaw_ae β hβ
    have hc : ∀ᵐ (w : Sphere d) ∂β, w ∈ gaussianDirectionBand A δ →
        ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
        dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
          (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 :=
      ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_of_ae hν) _)
    have hbnd : ∀ᵐ (w : Sphere d) ∂β, w ∈ gaussianDirectionBand A δ :=
      ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianDirectionBand_measurable A δ)) _)
    filter_upwards [hc,hbnd] with w hw hbnd
    exact hw hbnd
  have hu := hgain δ hδ hδsmall d h κ A z e α' β' E J a M 2 T hE hJ hM (by norm_num)
    hT hTbound hA hbound hsmall hEb hanchors hcover hαsupport hβsupport hpball hqball
  have hl : 1/(4*K^10*V) ≤ ((α' : Measure (Space d)).prod (β' : Measure (Sphere d))).real F := by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) hinc
    simpa only [α',β',Measure.real,ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(4*K^10*V))] using hh
  exact (not_lt_of_ge (hl.trans hu)) hlow


end OAI.Falconer

end ExtensionScope222

/- Source: OAI.MeasureTheory.Falconer.GeneralControlledAngularGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope223



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Angular/ControlledAngularGain.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_controlled_dyadic_angular_gain
     {h : ℕ} {t q : ℝ}
    (hq : (h:ℝ) < q) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (w₀ : Sphere (h+2)) (B : Space h →ₗᵢ[ℝ] Space (h+2))
      (E : Set (Space (h+2) × Sphere (h+2)))
      (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2))
      (ρ Lt Lq K C₀ Nc Z a₀ : ℝ),
    1/(2:ℝ)^N < δ₀ → 0 ≤ ρ → 1/(2:ℝ)^N ≤ ρ →
    (∀ i, inner ℝ (w₀:Space (h+2)) (B (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0) →
    (∀ᵐ w ∂ν, dist w w₀ ≤ ρ) →
    (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2 →
    4*(h:ℝ)*(1/(2:ℝ)^N)+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 →
    (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    0 ≤ Lt → 0 ≤ Lq →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lt*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lq*(1/(2:ℝ)^j)^q)) →
    (∀ᵐ u : Sphere (h+2) × Sphere (h+2) ∂ν.prod ν,
      0 ≤ inner ℝ (u.1:Space (h+2)) (u.2:Space (h+2))) →
    0 < K → 0 < Nc → 0 < Z →
    (4*gaussianVectorBandConstant)^h*Lt*gaussianFrostmanFactor h t ≤ C₀ →
    (2*gaussianPairBandConstant)^h*Lq*gaussianFrostmanFactor h q ≤ C₀ →
    (2*gaussianPairBandConstant)^h*(|Lq*gaussianFrostmanFactor h q|+1) ≤ C₀ →
    ((N+1:ℕ):ℝ)*C₀ ≤ K → C₀ ≤ K → 4*(1+2*(2:ℝ)^h+1) ≤ K →
    (1/4)*((h+2:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N ≤ Z →
    1 ≤ a₀ → 1 ≤ 4*K^10*(2*Z)^h → 4+8*(h:ℝ) ≤ a₀ →
    (4*K^10*(2*Z)^h)*(4*a₀)^(t-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-η) →
    (4*K^10*(2*Z)^h)*(8*a₀)^(q-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-η) →
    (1/(2:ℝ)^N)^η < 1/(4*K^10*(2*Z)^h) →
    K^11*(Nc*(2*((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+
      (C*(1/(2:ℝ)^N))*((h+2:ℝ)*(2*ρ)+1)))^h) ≤ (1/(2:ℝ)^N)^(-(q-(h:ℝ))-η) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc) →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant (h+1) ρ^h)*
      (μ.prod ν) E < ENNReal.ofReal (1/K) := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := general_gaussian_planar_slice_exclusion
    (sub_pos.mpr hq) (by linarith : q-(h:ℝ) < t-(h:ℝ)) ht C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro N κ _ _ μ ν _ _ w₀ B E J a ρ Lt Lq K C₀ Nc Z a₀ hδsmall hρ hδρ
    hB hν hstable hchart hμ hμmass hνmass hLt hLq hμball hνball hpair
    hK hNc hZ hCpoint hCdir hCmass hcard hC₀ hlarge hZbox ha₀ hH haK hpcoef hqcoef hlow
    hTbound hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  let ε : ℝ := (h+2:ℝ)*(2*ρ)
  let M : ℝ := ε+1
  let R : ℝ := δ+(2*(1/4))*δ+(C*δ)*M
  let T : ℝ := K^11*(Nc*(2*R)^h)
  let rows : Fin h → Space (h+2) := fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hrows (i : Fin h) : ‖rows i‖ ≤ 1 := by
    rw [show rows i = B (EuclideanSpace.basisFun (Fin h) ℝ i) from rfl,B.norm_map]
    exact ((EuclideanSpace.basisFun (Fin h) ℝ).norm_eq_one i).le
  have hwB : ∀ᵐ (w : Sphere (h+2)) ∂ν, ∀ i, |inner ℝ (w:Space (h+2)) (rows i)| ≤ ρ := by
    filter_upwards [hν] with w hw i
    exact transverse_frame_chart_bound B (w₀:Space (h+2)) hB hw i
  by_contra hnot
  have hmean := le_of_not_gt hnot
  have hfactor : ENNReal.ofReal ((2:ℝ)^h)*μ univ ≤ ENNReal.ofReal ((2:ℝ)^h) := by
    simpa only [mul_one] using mul_le_mul' le_rfl hμmass
  have hcast : ((h+1:ℕ):ℝ)+1 = (h+2:ℝ) := by push_cast; ring
  obtain ⟨A,hA,z,_,hbig⟩ := dyadic_original_slice_selection rows hrows μ ν N
    (by norm_num : (1/4:ℝ) < 1/2) hμ hδρ hwB hLt hLq (hq.trans hqt) hq hμmass hνmass
    hμball hνball hpair hK (by positivity : 0 ≤ (2:ℝ)^h) hNc hR hCpoint hCdir hCmass
    hcard hC₀ hlarge hfactor E hE J hJ a hJN hmean
    (by rw [hcast]; exact gaussianSelectionThreshold_uniform h hK hZ hZbox)
  rw [hcast] at hA
  obtain ⟨e,_,he⟩ := gaussian_two_dimensional_slice_chart B A w₀ hε hδ.le hρ hB hA hstable hchart
  have hbound := row_kernel_projection_bound A B hA hstable
  have hsmall : 2*((h:ℝ)*δ) < 1 := by
    have hpos : 0 ≤ 4*(h:ℝ)*ε := by positivity
    change 4*(h:ℝ)*δ+ρ+4*(h:ℝ)*ε ≤ 1/4 at hchart
    nlinarith
  have hchartAE : ∀ᵐ (w : Sphere (h+2)) ∂ν, w ∈ gaussianDirectionBand A δ →
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2))))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space (h+2)))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 := by
    filter_upwards [hν] with w hw hband
    exact he w hband hw
  have hupper := hgain N (h+2) h κ A z e μ ν E J a K ((2*Z)^h) M T a₀ hδsmall
    hK (by positivity) hM (by dsimp [T]; positivity) hTbound ha₀ hH haK hpcoef hqcoef hlow
    hE hJ (gaussianRowNeighborhood_norm rows hrows hA) hbound hsmall hEb hanchors hcover hμ hchartAE
  simp only [gaussianSelectionThreshold,gaussianPruningWeight_eq] at hbig
  exact (not_lt_of_ge hupper) hbig


end OAI.Falconer

end ExtensionScope223

/- Source: OAI.MeasureTheory.Falconer.GeneralNonendpointChartGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope224



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Geometry/NonendpointChartGain.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_nonendpoint_chart_angular_gain
     {h : ℕ} {t q C ρ : ℝ}
    (hq : (h:ℝ) < q) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2)
    (hstable : (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2)
    (hchart : 4*(h:ℝ)*ρ+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4) :
    ∃ ε c δ₀ : ℝ, 0 < ε ∧ 0 < c ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (w₀ : Sphere (h+2)) (E : Set (Space (h+2) × Sphere (h+2)))
      (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2)),
    1/(2:ℝ)^N < δ₀ → (∀ᵐ w ∂ν, dist w w₀ ≤ ρ) →
    (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-q-ε)) →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    (μ.prod ν).real E ≤ (1/(2:ℝ)^N)^c := by
  classical
  obtain ⟨η,δF,hη,hδF,hgain⟩ := general_controlled_dyadic_angular_gain hq hqt ht hC
  obtain ⟨Cm,hCm,hcoeff⟩ := exists_gaussian_moment_coefficient h t q
  let κ₀ := η/100
  let ε := κ₀/2
  let c := κ₀/2
  let M := (h+2:ℝ)*(2*ρ)+1
  let Z := M+1
  let V := (2*Z)^h
  let a₀ := 4+8*(h:ℝ)
  let D := 1+2*(1/4)+C*M
  let B₀ := (2:ℝ)^h*gaussianLocalBandConstant (h+1) ρ^h
  have hκ : 0 < κ₀ := by dsimp [κ₀]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hεκ : ε < κ₀ := by dsimp [ε]; linarith
  have hM : 0 < M := by dsimp [M]; positivity
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hV : 1 ≤ V := by
    apply one_le_pow₀
    change 1 ≤ 2*(M+1)
    linarith
  have ha₀ : 1 ≤ a₀ := by dsimp [a₀]; linarith [Nat.cast_nonneg (α := ℝ) h]
  have hD : 0 < D := by dsimp [D]; positivity
  have hB₀ : 0 < B₀ := by
    have hb := gaussianLocalBandConstant_pos (n := h+1) hρ
    dsimp [B₀]
    positivity
  have hplan := eventually_gaussian_planar_loss_budget hη hV ha₀ (t-(h:ℝ))
    (q-(h:ℝ)) ((2*D)^h) (4*(1+2*(2:ℝ)^h+1))
  have hdepth := eventually_dyadic_loss_absorption hεκ Cm
  have habs := (tendsto_rpow_neg_nhdsGT_zero (show -(κ₀-c) < 0 by dsimp [c]; linarith)).eventually
    (eventually_ge_atTop (1/B₀))
  obtain ⟨δ₁,hδ₁,hready⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0:ℝ) < 1 by norm_num)).mp
      (hplan.and (hdepth.and habs))
  refine ⟨ε,c,min δF (min δ₁ (min ρ 1)),hε,hc,
    lt_min hδF (lt_min hδ₁ (lt_min hρ (by norm_num))),?_⟩
  intro N κ _ _ μ ν _ _ w₀ E J a hδsmall hν hμ hμmass hνmass hμball hνball
    hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  let K : ℝ := δ^(-κ₀)
  let L : ℝ := δ^(-ε)
  let Nc : ℝ := δ^(-q-ε)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδρ : δ ≤ ρ := (hδsmall.trans_le (min_le_right _ _)).trans_le
    ((min_le_right _ _).trans (min_le_left _ _)) |>.le
  have hδ1 : δ ≤ 1 := (hδsmall.trans_le (min_le_right _ _)).trans_le
    ((min_le_right _ _).trans (min_le_right _ _)) |>.le
  obtain ⟨hp,⟨_,hd⟩,ha⟩ := hready ⟨hδ,hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
  rcases hp with ⟨_,hlarge,hH,hpcoef,hqcoef,hlow,hcoverScale⟩
  have hL : 1 ≤ L := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show -ε ≤ 0 by linarith)
  have hK : 0 < K := Real.rpow_pos_of_pos hδ _
  have hL0 : 0 ≤ L := by linarith
  have hCmL : 0 ≤ Cm*L := mul_nonneg hCm.le hL0
  have hcard : ((N+1:ℕ):ℝ)*(Cm*L) ≤ K := by
    rw [dyadic_log_depth N] at hd
    simpa only [Nat.cast_add,Nat.cast_one,mul_assoc,mul_comm,mul_left_comm] using hd
  have hCK : Cm*L ≤ K := by
    have hN : (1:ℝ) ≤ (N+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    exact (le_mul_of_one_le_left hCmL hN).trans hcard
  have hpair : ∀ᵐ u : Sphere (h+2) × Sphere (h+2) ∂ν.prod ν,
      0 ≤ inner ℝ (u.1:Space (h+2)) (u.2:Space (h+2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν,Measure.quasiMeasurePreserving_snd.ae hν]
      with u hu hv
    exact sphere_chart_pair_inner_nonnegative u.1 u.2 w₀ (hu.trans hρhalf) (hv.trans hρhalf)
  obtain ⟨B,hB⟩ := exists_transverse_row_frame (h := h) (n := h+1) (by omega) (sphere_norm w₀)
  have hchartδ : 4*(h:ℝ)*δ+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 := by
    nlinarith [mul_le_mul_of_nonneg_left hδρ (by positivity : 0 ≤ 4*(h:ℝ))]
  have hbox : (1/4)*((h+2:ℝ)*(2*ρ)+1)+δ ≤ Z := by
    change (1/4)*M+δ ≤ M+1
    nlinarith
  have hactive : K^11*(Nc*(2*(δ+(2*(1/4))*δ+(C*δ)*M))^h) ≤ δ^(-(q-(h:ℝ))-η) := by
    have hh := gaussian_active_cover_scale h hδ hδ1 hεκ.le hD.le (le_refl Nc)
    have hr : δ+(2*(1/4))*δ+(C*δ)*M = D*δ := by dsimp [D]; ring
    rw [hr]
    exact hh.trans hcoverScale
  have hNc : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc := by
    intro w
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hJN w)
  obtain ⟨hCP,hCD,hCM⟩ := hcoeff L hL
  have hg := hgain N κ μ ν w₀ B E J a ρ L L K (Cm*L) Nc Z a₀
    (hδsmall.trans_le (min_le_left _ _)) hρ.le hδρ hB hν hstable hchartδ hμ hμmass hνmass
    hL0 hL0 hμball hνball hpair hK (Real.rpow_pos_of_pos hδ _) hZ hCP hCD hCM
    hcard hCK hlarge hbox ha₀ hH (le_refl a₀) hpcoef hqcoef hlow hactive
    hE hJ hNc hEb hanchors hcover
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg.le
  have hlocal := gaussianLocalBandConstant_pos (n := h+1) hρ
  have hr' : B₀*(μ.prod ν).real E ≤ δ^κ₀ := by
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ (2:ℝ)^h),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ gaussianLocalBandConstant (h+1) ρ^h),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/K),B₀,Measure.real,one_div,
      K,Real.rpow_neg hδ.le,inv_inv,ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le κ₀),mul_assoc] using hr
  have habs' : (1/B₀)*δ^κ₀ ≤ δ^c := by
    have hh := rpow_absorb_constant (t := -κ₀) (u := -c) hδ (by
      convert ha using 1; ring_nf)
    simpa only [neg_neg] using hh
  have hI : (μ.prod ν).real E ≤ (1/B₀)*δ^κ₀ := by
    calc
      _ = (1/B₀)*(B₀*(μ.prod ν).real E) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hr' (by positivity)
  exact hI.trans habs'


end OAI.Falconer

end ExtensionScope224

/- Source: OAI.MeasureTheory.Falconer.GeneralNonendpointAngularGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope225



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Angular/NonendpointAngularGain.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_nonendpoint_dyadic_angular_gain
     {h : ℕ} {t q C : ℝ}
    (hq : (h:ℝ) < q) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (hC : 0 ≤ C) :
    ∃ ε c δ₀ : ℝ, 0 < ε ∧ 0 < c ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (E : Set (Space (h+2) × Sphere (h+2)))
      (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2)),
    1/(2:ℝ)^N < δ₀ → (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-q-ε)) →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ρ,hρ,hρhalf,hstable,hchart⟩ := exists_small_gaussian_chart_radius h
  obtain ⟨ε,c₁,δ₁,hε,hc₁,hδ₁,hgain⟩ := general_nonendpoint_chart_angular_gain hq hqt ht
    hC hρ hρhalf hstable hchart
  let H : ℝ := (2/ρ+1)^(h+2)
  let c := c₁/2
  have hc : 0 < c := by dsimp [c]; positivity
  have habs := (tendsto_rpow_neg_nhdsGT_zero (show -(c₁-c) < 0 by dsimp [c]; linarith)).eventually
    (eventually_ge_atTop H)
  obtain ⟨δ₂,hδ₂,hready⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0:ℝ) < 1 by norm_num)).mp habs
  refine ⟨ε,c,min δ₁ δ₂,hε,hc,lt_min hδ₁ hδ₂,?_⟩
  intro N κ _ _ μ ν _ _ E J a hδsmall hμ hμmass hνmass hμball hνball hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hH : H*δ^c₁ ≤ δ^c := by
    have ha : H ≤ δ^(-(c₁-c)) := hready ⟨hδ,hδsmall.trans_le (min_le_right _ _)⟩
    have hh := rpow_absorb_constant (t := -c₁) (u := -c) hδ (by
      convert ha using 1; ring_nf)
    simpa only [neg_neg] using hh
  by_contra hn
  have hlarge : ENNReal.ofReal H*ENNReal.ofReal (δ^c₁) < (μ.prod ν) E := by
    apply lt_of_le_of_lt _ (lt_of_not_ge hn)
    rw [← ENNReal.ofReal_mul (by dsimp [H]; positivity)]
    exact ENNReal.ofReal_le_ofReal hH
  obtain ⟨w₀,hw₀⟩ := original_direction_chart_selection μ ν E hE hρ hlarge
  let ν' := ν.restrict (Metric.closedBall w₀ ρ)
  have hνsupport : ∀ᵐ w ∂ν', dist w w₀ ≤ ρ := ae_restrict_mem measurableSet_closedBall
  have hν'mass : ν' univ ≤ 1 := (Measure.restrict_le_self _).trans hνmass
  have hν'ball (x : Sphere (h+2)) (j : ℕ) (hj : j ≤ N) :
      ν' (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (δ^(-ε)*(1/(2:ℝ)^j)^q) :=
    (Measure.restrict_le_self _).trans (hνball x j hj)
  have hg := hgain N κ μ ν' w₀ E J a (hδsmall.trans_le (min_le_left _ _))
    hνsupport hμ hμmass hν'mass hμball hν'ball hE hJ hJN hEb hanchors hcover
  have hgle : (μ.prod ν') E ≤ ENNReal.ofReal (δ^c₁) := by
    simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top (μ.prod ν') E)] using
      ENNReal.ofReal_le_ofReal hg
  exact (not_lt_of_ge hgle) hw₀


end OAI.Falconer

end ExtensionScope225

/- Source: OAI.MeasureTheory.Falconer.GeneralNonendpointTubeGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope226



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Radial/NonendpointTubeGain.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_nonendpoint_dyadic_tube_gain
     {h : ℕ} {t q C : ℝ}
    (hq : (h:ℝ) < q) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (hC : 0 ≤ C) :
    ∃ ε c δ₀ : ℝ, 0 < ε ∧ 0 < c ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν] (E : Set (Space (h+2) × Sphere (h+2))),
    1/(2:ℝ)^N < δ₀ → (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
    MeasurableSet E → (∀ u ∈ E, ‖u.1‖ ≤ 1/4) →
    (∀ w : Sphere (h+2), ∃ S : Finset (Space (h+2)),
      (S.card : ℝ) ≤ (1/(2:ℝ)^N)^(-q-ε) ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S,
        ‖perpendicularPart (w:Space (h+2)) (x-a)‖ ≤ C*(1/(2:ℝ)^N)) →
    (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ε,c,δ₀,hε,hc,hδ₀,hgain⟩ := general_nonendpoint_dyadic_angular_gain hq hqt ht
    (by linarith : 0 ≤ 2*C+1)
  refine ⟨ε,c,δ₀,hε,hc,hδ₀,?_⟩
  intro N μ ν _ _ E hδsmall hμ hμmass hνmass hμball hνball hE hEb hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨G,hG,J,F,hF,hFE,hJ,hcard,hzero,hcoverF⟩ :=
    prepare_original_tube_relation μ E hE hδ (Nat.floor (δ^(-q-ε))) hEb (by
      intro w
      obtain ⟨S,hS,hcoverS⟩ := hcover w
      exact ⟨S,Nat.le_floor hS,hcoverS⟩)
  have hmass : (μ.prod ν) F = (μ.prod ν) E := by
    have hh := product_inter_eq_of_null_original_fibers μ μ ν Measure.AbsolutelyContinuous.rfl
      E F hE hF hzero
    simpa only [inter_eq_right.mpr hFE] using hh
  rw [← hmass]
  refine hgain N {a // a ∈ G} μ ν F J (fun a => a.val) hδsmall hμ hμmass hνmass
    hμball hνball hF hJ ?_ (fun u hu => hEb u (hFE hu)) (fun _ i _ => hG i.val i.property) ?_
  · intro w
    have hh : ((J w).card : ℝ) ≤ (Nat.floor (δ^(-q-ε)) : ℝ) := by exact_mod_cast hcard w
    exact hh.trans (Nat.floor_le (Real.rpow_nonneg hδ.le _))
  · intro u hu
    obtain ⟨a,ha,hp⟩ := hcoverF u hu
    refine ⟨a,ha,?_⟩
    nlinarith


end OAI.Falconer

end ExtensionScope226

/- Source: OAI.MeasureTheory.Falconer.GeneralNonendpointBadDirections. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope227



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Angular/NonendpointBadDirections.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_nonendpoint_bad_direction_envelope 
    {h : ℕ} {t q C : ℝ} (hq : (h:ℝ) < q) (hqt : q < t) (ht : t-(h:ℝ) < 1) (hC : 0 ≤ C) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ : Measure (Space (h+2))) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      ∃ B : Set (Sphere (h+2)), MeasurableSet B ∧
        {w : Sphere (h+2) | ∃ S : Finset (Space (h+2)), (S.card:ℝ) ≤ (1/(2:ℝ)^N)^(-q-b) ∧
          ENNReal.ofReal ((1/(2:ℝ)^N)^b) ≤
            μ {x | ∃ v ∈ S, ‖perpendicularPart (w:Space (h+2)) (x-v)‖ ≤ C*(1/(2:ℝ)^N)}} ⊆ B ∧
        ∀ (ν : Measure (Sphere (h+2))) [IsFiniteMeasure ν], ν univ ≤ 1 →
          (∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
          ν B ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
  classical
  obtain ⟨ε₀,c,δ₀,hε₀,hc,hδ₀,hgain⟩ := general_nonendpoint_dyadic_tube_gain hq hqt ht
    (by linarith : 0 ≤ 2*C+1)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    (dyadic_inverse_tendsto.eventually (Ioo_mem_nhdsGT hδ₀))
  let ε : ℝ := ε₀/2
  let b : ℝ := min ε (c/3)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hb : 0 < b := lt_min hε (by positivity)
  have hεle : ε ≤ ε₀ := by dsimp [ε]; linarith
  have hble : b ≤ ε₀ := (min_le_left _ _).trans hεle
  have hbc : 2*b ≤ c := by have hh := min_le_right ε (c/3); dsimp [b]; linarith
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ _ hμ hμball
  let δ : ℝ := 1/(2:ℝ)^N
  let count : ℕ := Nat.floor (δ^(-q-b))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) : (1:ℝ) ≤ (2:ℝ)^N)
  have hL : δ^(-ε) ≤ δ^(-ε₀) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hεle)
  obtain ⟨G,hG,hnet⟩ := exists_bounded_anchor_net (d := h+2) (1/4) hδ
  let B := finiteBadDirections μ G count (1/4) ((2*C+1)*δ) (ENNReal.ofReal (δ^b))
  refine ⟨B,finiteBadDirections_measurable μ G count _ _ _,?_,?_⟩
  · rintro w ⟨S,hS,hmass⟩
    have hh := original_bad_direction_mem_envelope μ G count (ENNReal.ofReal (δ^b))
      hμ hnet w S (Nat.le_floor hS) hmass
    have he : 2*(C*δ)+δ = (2*C+1)*δ := by ring
    change w ∈ finiteBadDirections μ G count (1/4) (2*(C*δ)+δ) (ENNReal.ofReal (δ^b)) at hh
    rw [he] at hh
    exact hh
  · intro ν _ hνmass hνball
    obtain ⟨J,F,hF,hJ,hJmeas,hFb,hcover,hlower⟩ :=
      exists_finite_bad_incidence μ G count (1/4) ((2*C+1)*δ) (ENNReal.ofReal (δ^b))
    have hcount : (count:ℝ) ≤ δ^(-q-ε₀) :=
      (Nat.floor_le (Real.rpow_nonneg hδ.le _)).trans
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
    have hupper := hgain N μ ν F (hN₀ N hN).2 hμ (by simp) hνmass
      (fun x j hj => (hμball x j hj).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) t))))
      (fun w j hj => (hνball w j hj).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) q))))
      hF hFb (by
          intro w
          refine ⟨J w,?_,?_⟩
          · exact (show ((J w).card:ℝ) ≤ count by exact_mod_cast (hJ w).2).trans hcount
          · intro x hx
            exact hcover (x,w) hx)
    exact ennreal_mass_of_power_incidence hδ hδ1 hbc (ν B) ((hlower ν).trans hupper)


end OAI.Falconer

end ExtensionScope227

/- Source: OAI.MeasureTheory.Falconer.GeneralNonendpointRadialBadDirections. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope228



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Radial/NonendpointRadialBadDirections.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_nonendpoint_radial_bad_directions 
    {h : ℕ} {t q C : ℝ} (hq : (h:ℝ) < q) (hqt : q < t) (ht : t-(h:ℝ) < 1) (hC : 0 ≤ C) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+2)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (w₀ : Sphere (h+2)) (G : Set (Space (h+2) × Space (h+2))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ, ‖z‖ ≤ 1/4) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∃ B : Set (Sphere (h+2)), MeasurableSet B ∧
        {w : Sphere (h+2) | ∃ S : Finset (Space (h+2)),
          (S.card:ℝ) ≤ (1/(2:ℝ)^N)^(-q-b) ∧
          ENNReal.ofReal ((1/(2:ℝ)^N)^b) ≤
            μ {z | ∃ v ∈ S, ‖perpendicularPart (w:Space (h+2)) (z-v)‖ ≤ C*(1/(2:ℝ)^N)}} ⊆ B ∧
        (μ.prod ν) (radialBadWitness w₀ G B) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
  obtain ⟨ε,b,hε,hb,N₀,hN₀⟩ := general_nonendpoint_bad_direction_envelope hq hqt ht hC
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ ν _ _ hν w₀ G hG hdiag hμ hμball hdata
  obtain ⟨B,hB,hcontains,hbound⟩ := hN₀ N hN μ hμ hμball
  refine ⟨B,hB,hcontains,?_⟩
  have hsmall : ∀ᵐ z ∂μ, originalRadialSphereLaw w₀ ν G z B ≤
      ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
    filter_upwards [hdata] with z hz
    apply hbound (originalRadialSphereLaw w₀ ν G z)
      ((originalRadialSphereLaw_mass_le w₀ ν G z).trans hν)
    intro w j hj
    rw [originalRadialSphereLaw_ball w₀ ν G z (hdiag z)]
    exact hz w j hj
  simpa only [measure_univ,mul_one] using radial_bad_witness_mass w₀ μ ν G hG B hB _ hsmall


end OAI.Falconer

end ExtensionScope228

/- Source: OAI.MeasureTheory.Falconer.GeneralNonendpointMiddleRadial. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope229



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Radial/NonendpointMiddleRadial.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_nonendpoint_middle_radial_pruning 
    {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hqt : q < t) (ht : t-(h:ℝ) < 1) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+2)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (_w₀ : Sphere (h+2)) (G : Set (Space (h+2) × Space (h+2))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z‖ ≤ 1/4) →
      (∀ᵐ z ∂μ, ‖z‖ ≤ 1/4) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/r ≤ 1/(2:ℝ)^N →
      H*θ ≤ 1/(2:ℝ)^N →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖(0:Space (h+2))-x‖ ∧
        ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^N)^b) ∧
        ∀ p ∈ G', radialCollisionMass μ θ p ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(q+b/2)) := by
  let C : ℝ := 2*((h+2:ℕ):ℝ)+2
  let L : ℕ := h+5
  let K : ℕ := (2*L+1)^(h+2)
  obtain ⟨ε,b,hε,hb,N₁,hN₁⟩ := general_nonendpoint_radial_bad_directions hq hqt ht
    (show 0 ≤ C by dsimp [C]; positivity)
  obtain ⟨N₂,hN₂⟩ := eventually_heavy_cover_card (q := q) (K := (K:ℝ)) hb (by positivity)
  refine ⟨ε,b,hε,hb,max N₁ N₂,?_⟩
  intro N hN μ ν _ _ hν w₀ G hG hgeom hμ hballs hcaps r H θ hr hfreeze hwidth hpin
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Bad,hBad,hcontains,hbadmass⟩ := hN₁ N ((le_max_left _ _).trans hN) μ ν hν
    w₀ G hG (fun z x hx => (hgeom z x hx).1.symm) hμ hballs hcaps
  have hL : 1+1+((h+1+1:ℕ):ℝ)+1/2 ≤ (L:ℝ) := by dsimp [L]; push_cast; linarith
  have hrobust : (2*((h+1+1:ℕ):ℝ)+1)*δ+2*(2*(1/4)/r)*(1/4+1/4) ≤ C*δ := by
    have he : 2*(2*(1/4:ℝ)/r)*(1/4+1/4) = 8*(1/4:ℝ)^2/r := by ring
    rw [he]
    dsimp [C]
    change 8*(1/4:ℝ)^2/r ≤ δ at hfreeze
    nlinarith
  have henv (v : Sphere (h+2)) (S : Finset (Space (h+2)))
      (hc : (S.card:ℝ≥0∞)*ENNReal.ofReal (δ^(q+b/2)) ≤
        ((2*L+1)^(h+1+1):ℕ)*μ univ)
      (hm : ENNReal.ofReal (δ^b) ≤
        μ {z | ∃ a ∈ S, ‖perpendicularPart (v:Space (h+2)) (z-a)‖ ≤ C*δ}) : v ∈ Bad := by
    apply hcontains
    refine ⟨S,?_,hm⟩
    apply hN₂ N ((le_max_right _ _).trans hN) S.card
    simpa only [measure_univ,mul_one,ENNReal.ofReal_natCast] using hc
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := middle_radial_pruning (θ := θ) (n := h+1) μ ν w₀ G hG
    Bad hBad 0 hr hδ hfreeze (by simpa only [sub_zero] using hμ) hμ
    (fun z x hx => ⟨(hgeom z x hx).1,by simpa only [sub_zero] using (hgeom z x hx).2,
      (hgeom z x hx).2⟩) hpin (by simpa only [one_mul] using hwidth) hrobust (ENNReal.ofReal (δ^(q+b/2)))
    (ENNReal.ofReal (δ^b)) (ENNReal.ofReal (δ^b)) L hL henv hbadmass
  refine ⟨G',hG',hsub,hdel.trans ?_,hbound⟩
  calc
    _ ≤ ENNReal.ofReal (δ^b)+ENNReal.ofReal (δ^b)*1 :=
      add_le_add le_rfl (mul_le_mul' le_rfl hν)
    _ = 2*ENNReal.ofReal (δ^b) := by ring


end OAI.Falconer

end ExtensionScope229

/- Source: OAI.MeasureTheory.Falconer.GeneralNonendpointOriginalMiddle. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope230



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Estimates/NonendpointOriginalMiddle.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_nonendpoint_original_middle_pruning 
    {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hqt : q < t) (ht : t-(h:ℝ) < 1) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+2)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (_w₀ : Sphere (h+2)) (c : Space (h+2)) (a : ℝ), 0 < a →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z-c‖ ≤ 1/(4*a)) →
      (∀ᵐ z ∂μ, ‖z-c‖ ≤ 1/(4*a)) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x ((1/(2:ℝ)^j)/a)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/(a*r) ≤ 1/(2:ℝ)^N →
      (a*H)*θ ≤ 1/(2:ℝ)^N →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖c-x‖ ∧ ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^N)^b) ∧
        ∀ p ∈ G', radialCollisionMass μ θ p ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(q+b/2)) := by
  obtain ⟨ε,b,hε,hb,N₀,hN₀⟩ := general_nonendpoint_middle_radial_pruning hq hqt ht
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ ν _ _ hν w₀ c a ha G hG hgeom hμ hball hcap r H θ hr hfreeze hwidth hpin
  let e := radialZoom a ha.ne' c
  have hν' : Measure.map e ν univ ≤ 1 := by
    simpa only [Measure.map_apply e.measurable MeasurableSet.univ,preimage_univ] using hν
  have hgeom' : ∀ z x, (z,x) ∈ zoomPairSet e G → z ≠ x ∧ ‖z‖ ≤ 1/4 := by
    intro z x hx
    have hh := hgeom (e.symm z) (e.symm x) hx
    refine ⟨fun he => hh.1 (congrArg e.symm he),?_⟩
    have hn := radialZoom_quarter_bound ha c (e.symm z) hh.2
    change ‖e (e.symm z)‖ ≤ 1/4 at hn
    simpa only [e.apply_symm_apply] using hn
  have hμ' : ∀ᵐ z ∂Measure.map e μ, ‖z‖ ≤ 1/4 := by
    rw [radialZoom_ae_iff μ ha]
    filter_upwards [hμ] with z hz
    exact radialZoom_quarter_bound ha c z hz
  have hball' : ∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      Measure.map e μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t) := by
    intro x j hj
    rw [radialZoom_ball_apply μ ha]
    exact hball _ j hj
  have hcap' : ∀ᵐ z ∂Measure.map e μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      Measure.map e ν {x | (z,x) ∈ zoomPairSet e G ∧
        dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q) := by
    rw [radialZoom_ae_iff μ ha]
    filter_upwards [hcap] with z hz
    intro w j hj
    rw [radialZoom_reverse_cap ν ha c z w _ G hG]
    exact hz w j hj
  have hpin' : ∀ x, (∃ z, (z,x) ∈ zoomPairSet e G) →
      a*r ≤ ‖(0:Space (h+2))-x‖ ∧ ∀ᵐ y ∂Measure.map e μ, ‖y-x‖ ≤ a*H := by
    intro x hx
    obtain ⟨z,hz⟩ := hx
    have hp := hpin (e.symm x) ⟨e.symm z,hz⟩
    have he : e (e.symm x) = x := e.apply_symm_apply x
    refine ⟨?_,?_⟩
    · have hd := radialZoom_pin_distance ha c (e.symm x) hp.1
      change a*r ≤ ‖(0:Space (h+2))-e (e.symm x)‖ at hd
      simpa only [he] using hd
    · have hb := radialZoom_pair_ae_bound μ ha c (e.symm x) hp.2
      change ∀ᵐ y ∂Measure.map e μ, ‖y-e (e.symm x)‖ ≤ a*H at hb
      simpa only [he] using hb
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := hN₀ N hN (Measure.map e μ) (Measure.map e ν) hν'
    w₀ (zoomPairSet e G) (zoomPairSet_measurable e hG) hgeom' hμ' hball' hcap'
    (a*r) (a*H) θ (mul_pos ha hr) hfreeze hwidth hpin'
  exact radial_pruning_unzoom μ ν ha c G hG G' hG' hsub θ _ _ hdel hbound


end OAI.Falconer

end ExtensionScope230

/- Source: OAI.MeasureTheory.Falconer.GeneralNonendpointSourceMiddle. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope231



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Radial/NonendpointSourceMiddle.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer.Regularization
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_nonendpoint_source_class_middle_pruning 
    {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hqt : q < t) (ht : t-(h:ℝ) < 1) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀,
      ∀ (Q : DyadicCube (h+2)), Q.side = 1 →
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsFiniteMeasure ν],
      ν univ ≤ 1 → ∀ N B : ℕ, 0 < N → 0 < B →
      ∀ lam E σ : ℝ, 0 ≤ E → 0 ≤ lam → 0 < σ → σ ≤ 1 → σ*Real.sqrt (h+2:ℕ) ≤ 1/4 →
      (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ p v : ℕ, p ≤ v → v ≤ N → M ≤ v-p →
      ∀ P : CellPath (h+2), P.length = p →
      0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier →
      (∀ n, p ≤ n → n ≤ v →
        t*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) →
      (((((2*Nat.ceil (2+4*Real.sqrt (h+2:ℕ))+1)^(h+2):ℕ):ℝ)*(2:ℝ)^t*
        ((2:ℝ)^N)^(E+2*(((h+2:ℕ):ℝ)+1)*lam))*σ^(-t)) ≤ (1/(2:ℝ)^M)^(-ε) →
      ∀ (_w₀ : Sphere (h+2)) (G : Set (Space (h+2) × Space (h+2))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ z ∈ (Q.descendant P).carrier) →
      (∀ᵐ z ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier,
        ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ M →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^M)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/((σ*(2:ℝ)^p)*r) ≤ 1/(2:ℝ)^M →
      ((σ*(2:ℝ)^p)*H)*θ ≤ 1/(2:ℝ)^M →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖(Q.descendant P).center-x‖ ∧
        ∀ᵐ y ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        ((ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier).prod ν)
          (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^M)^b) ∧
        ∀ z ∈ G', radialCollisionMass
          (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier) θ z ≤
            ENNReal.ofReal ((1/(2:ℝ)^M)^(q+b/2)) := by
  obtain ⟨ε,b,hε,hb,M₀,hM₀⟩ := general_nonendpoint_original_middle_pruning hq hqt ht
  refine ⟨ε,b,hε,hb,M₀,?_⟩
  intro M hM Q hQ μ ν _ _ hν N B hN hB lam E σ hE hlam hσ hσ1 hsmall hwidth hlarge
    p₀ hp₀ p v hpv hvN hMv P hP hpos hinc hcoef w₀ G hG hgeom hcap r H θ hr hfreeze hwidth' hpin
  have ht0 : 0 ≤ t := by have hh : (0:ℝ) ≤ h := Nat.cast_nonneg h; linarith
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have : IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀)
      (Q.descendant P).carrier) := sourceClass_conditional_probability Q hside μ N B hp₀ P hpos
  have hdata := source_class_middle_data Q hQ μ hN hB ht0 hE hlam hσ hσ1 hsmall hwidth hlarge
    hp₀ hpv hvN hMv hP hpos hinc hcoef
  exact hM₀ M hM _ ν hν w₀ (Q.descendant P).center (σ*(2:ℝ)^p) (by positivity) G hG
    (fun z x hz => ⟨(hgeom z x hz).1,hdata.1 z (hgeom z x hz).2⟩)
    hdata.2.1 hdata.2.2 hcap r H θ hr hfreeze hwidth' hpin


end OAI.Falconer.Regularization

end ExtensionScope231

/- Source: OAI.MeasureTheory.Falconer.GeneralNonendpointContactGain. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope232



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Recursion/NonendpointContactGain.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer.Regularization
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_nonendpoint_contact_gain 
    {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (Q : DyadicCube (h+2)) (hQ : Q.side = 1)
    {D s : ℝ} (hD : 1 ≤ D) (hDdim : Real.sqrt (h+2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε gain : ℝ, 0 < ε ∧ 0 < gain ∧
      ∀ τ γ : ℝ, 0 < τ → 0 < γ →
        (2*((h+2:ℕ):ℝ)+4)*τ ≤ ε/2 →
        (20*(2*((h+2:ℕ):ℝ)+4)+4)*τ ≤ gain/8 → 2*τ ≤ gain →
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ B : ℕ, 0 < B → ∀ lam : ℝ, 0 ≤ lam → lam ≤ τ*γ →
        (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N,
        RobustProfileContact (sourceUnitProfile Q μ N B p₀) q t τ γ →
      ∀ A P : Set (Space (h+2)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+2), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^(τ*γ)*r^q)) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        ((sourceClass Q μ N B p₀).prod ν) (G \ G') ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))) ∧
        ∀ x u : Space (h+2), sourceClass Q μ N B p₀
          {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
            ENNReal.ofReal (((2:ℝ)^N)^(-q-gain*γ/8)) := by
  obtain ⟨ε,gain,hε,hgain,M₀,hmiddle⟩ :=
    general_nonendpoint_source_class_middle_pruning hq hqt ht
  refine ⟨ε,gain,hε,hgain,?_⟩
  intro τ γ hτ hγ hτε hτgain hτgain'
  let L : ℝ := 2*((h+2:ℕ):ℝ)+4
  let σ : ℝ := cellContraction (h+2)
  let C : ℝ := 4*Real.sqrt (h+2:ℕ)/s+2
  have hL : 1 ≤ L := by dsimp [L]; have hh := Nat.cast_nonneg (α := ℝ) (h+2); linarith only [hh]
  have hq0 : 0 ≤ q := by have hh := Nat.cast_nonneg (α := ℝ) h; linarith
  have ht0 : 0 ≤ t := hq0.trans hqt.le
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hσ : 0 < σ := cellContraction_pos _
  have hη₀ : 0 < L*τ*γ := by positivity
  obtain ⟨Jo,No,houter⟩ := source_class_outer_radial_pruning Q hQ hD hDdim hη₀ hq0 C
  obtain ⟨Jm,Nm,hgeom⟩ := uniform_middle_geometry hσ (by positivity : 0 < s/2)
    (by positivity : 0 < γ/2) D C M₀
  obtain ⟨Na,hmargin⟩ := eventually_integer_margin (by positivity : 0 < γ/2) Jo
  obtain ⟨Ns,hsmall⟩ := eventually_cell_diameter_small (h+2) (by positivity : 0 < γ/2) hs
  let K : ℝ := (((2*Nat.ceil (2+4*Real.sqrt (h+2:ℕ))+1)^(h+2):ℕ):ℝ)
  obtain ⟨Nf,hfirst⟩ := eventually_contact_outer_coefficient (h+2) hτ hγ (K*(2:ℝ)^q) 0
  obtain ⟨Nl,hlast⟩ := eventually_contact_outer_coefficient (h+2) hτ hγ
    (K*(2:ℝ)^q) (((h+2:ℕ):ℝ)+q)
  obtain ⟨Nt,htcoef⟩ := eventually_contact_frostman_coefficient (h+2) hτ hγ hτε
    (K*(2:ℝ)^t*σ^(-t)) (((h+2:ℕ):ℝ)+t)
  obtain ⟨Nc,hconst⟩ := fixed_constant_absorbed (mul_pos hτ hγ)
    (((2:ℝ)^Jm)^(q+gain/2))
  obtain ⟨Nd,hcost⟩ := eventually_three_interval_cost hτ hγ
    (by linarith : 1 ≤ 2*L) hτgain'
  obtain ⟨Nlarge,hlarge⟩ := exists_nat_gt (4/γ)
  let N₀ := max 1 (max No (max Nm (max Na (max Ns (max Nf (max Nl (max Nt
    (max Nc (max Nd Nlarge)))))))))
  refine ⟨N₀,?_⟩
  intro N hN μ ν _ _ B hB lam hlam hlamτ hblock hblock'
    p₀ hp₀ hcontact A P hA hP hAfull hPfull hsep hpin G hG hcap
  change max 1 (max No (max Nm (max Na (max Ns (max Nf (max Nl (max Nt
    (max Nc (max Nd Nlarge))))))))) ≤ N at hN
  simp only [max_le_iff] at hN
  rcases hN with ⟨h1,hNo,hNm,hNa,hNs,hNf,hNl,hNt,hNc,hNd,hNL⟩
  have hNp : 0 < N := by omega
  have hNN : (Nlarge:ℝ) ≤ N := by exact_mod_cast hNL
  have hlarge' : 4 ≤ γ*(N:ℝ) := by
    have hh := (div_lt_iff₀ hγ).mp hlarge
    nlinarith only [hh,hNN,hγ]
  obtain ⟨α,β,a,b,hγΔ,hΔ1,hab,hbN,hgap,_,ha,_,hNb,hfreeze,hi₀,hi₁,hi₂⟩ :=
    source_class_contact_intervals Q μ hNp hB p₀ hq0 ht0 hγ hlarge' hcontact
  let Δ := β-α
  let η := L*τ*Δ
  let ξ := τ*Δ
  let M := (b-a)-Jm
  have hΔ : 0 < Δ := hγ.trans_le hγΔ
  have hη : L*τ*γ ≤ η := mul_le_mul_of_nonneg_left hγΔ (by positivity)
  obtain ⟨hJm,hM,hNM,hfr,hwi⟩ := hgeom N hNm a b Δ hab
    (by dsimp [Δ]; linarith only [hγΔ,hγ]) hgap hfreeze
  have hJoA : Jo ≤ a := hmargin N hNa a ha
  have hJoB : b+Jo ≤ N := by
    have hh := hmargin N hNa (N-b) (by linarith only [hNb,hγ])
    omega
  have hsmallA : Real.sqrt (h+2:ℕ)*(Q.side/(2:ℝ)^a) ≤ s/2 := by
    rw [hQ,mul_one_div]
    exact hsmall N hNs a ha
  have hsmallAll {n : ℕ} (han : a ≤ n) :
      Real.sqrt (h+2:ℕ)*(Q.side/(2:ℝ)^n) ≤ s/2 := by
    apply le_trans _ hsmallA
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hside.le (by positivity)
        (pow_le_pow_right₀ (by norm_num) han)) (Real.sqrt_nonneg _)
  have hcoef₀ : K*(2:ℝ)^q*((2:ℝ)^N)^(τ*Δ+2*(((h+2:ℕ):ℝ)+1)*lam) ≤
      ((2:ℝ)^N)^η := by
    simpa only [zero_div,add_zero] using hfirst N hNf hNp Δ lam hγΔ hlamτ
  have hcoef₂ := hlast N hNl hNp Δ lam hγΔ hlamτ
  have hcoef₁ : K*(2:ℝ)^t*((2:ℝ)^N)^
      ((τ*Δ+(((h+2:ℕ):ℝ)+t)/(N:ℝ))+2*(((h+2:ℕ):ℝ)+1)*lam)*σ^(-t) ≤
      (1/(2:ℝ)^M)^(-ε) := by
    convert htcoef N hNt hNp M Δ lam hγΔ hlamτ hNM using 1; ring
  have hreverseOuter : ((2:ℝ)^N)^(τ*γ) ≤ ((2:ℝ)^N)^η := by
    apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
    have hh := mul_le_mul_of_nonneg_right hL (mul_nonneg hτ.le hγ.le)
    dsimp [η]
    nlinarith only [hh,hη]
  have hreverseMiddle : ((2:ℝ)^N)^(τ*γ) ≤ (1/(2:ℝ)^M)^(-ε) := by
    rw [inverse_dyadic_neg_power]
    apply dyadic_relative_scale_bound
    have hh := contact_loss_relative_budget hτ.le hγΔ hlamτ hτε hNM
    have hx : 0 ≤ (N:ℝ)*(τ*Δ+2*(((h+2:ℕ):ℝ)+1)*lam) := by positivity
    nlinarith only [hh,hx]
  let ρ := sourceClass Q μ N B p₀
  have : IsProbabilityMeasure ρ := regularization_class_probability Q hside μ N B hp₀
  have hρA : ρ Aᶜ = 0 := sourceClass_absolutelyContinuous Q μ N B p₀ hAfull
  obtain ⟨G₀,hG₀,hG₀G,hG₀core,hnull⟩ :=
    source_class_pair_core Q hside μ ν N B p₀ hp₀ A P hA hP hAfull hPfull G hG
  have hcore : G₀ ⊆ Q.occupiedTreeCore ρ N ×ˢ P := fun _ hz => ⟨(hG₀core hz).1.2,(hG₀core hz).2⟩
  have hdiag {z x : Space (h+2)} (hz : (z,x) ∈ G₀) : z ≠ x := by
    have hh := hsep z (hG₀core hz).1.1 x (hG₀core hz).2
    intro he
    simp only [he,sub_self,norm_zero] at hh
    exact (not_le_of_gt hs) hh
  let cost : ℕ → ℝ≥0∞ := fun j => if j = 1 then 2*ENNReal.ofReal ((1/(2:ℝ)^M)^gain)
    else ENNReal.ofReal (((2:ℝ)^N)^(-(2*η)))
  have hlocal : ∀ j < 3, ∀ p ∈ Q.occupiedPaths ρ (threeIntervalDepth a b N j),
      ∃ H : Set (Space (h+2) × Space (h+2)), MeasurableSet H ∧
      ((ProbabilityTheory.cond ρ (Q.descendant p).carrier).prod ν)
        ((G₀ ∩ ((Q.descendant p).carrier ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ z ∈ H, radialCollisionMass (ProbabilityTheory.cond ρ (Q.descendant p).carrier)
        (C/(2:ℝ)^(threeIntervalDepth a b N (j+1))) z ≤
          threeIntervalFactor a b N Jm q (gain/2) η j := by
    intro j hj p hp
    have hpPos : 0 < ρ (Q.descendant p).carrier := (Finset.mem_filter.mp hp).2
    have hpLen : p.length = threeIntervalDepth a b N j :=
      (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1
    let V := G₀ ∩ ((Q.descendant p).carrier ×ˢ univ)
    have hV : MeasurableSet V := hG₀.inter ((Q.descendant p).measurable.prod MeasurableSet.univ)
    have hVG : V ⊆ G := inter_subset_left.trans hG₀G
    have hVdiag : ∀ z x, (z,x) ∈ V → x ≠ z := fun _ _ hz => (hdiag hz.1).symm
    have hVpin : ∀ z x, (z,x) ∈ V → ∀ y ∈ (Q.descendant p).carrier, ‖y-x‖ ≤ D :=
      fun _ _ hz y hy => hpin y (Q.descendant_subset p hy) _ (hG₀core hz.1).2
    have hac := sourceClass_conditional_absolutelyContinuous Q μ N B p₀ p
    interval_cases j
    · have hlen : p.length = 0 := by simpa [threeIntervalDepth] using hpLen
      obtain ⟨H,hH,_,hd,hk⟩ := houter N hNo η hη 0 a (by omega) (hab.trans hbN)
        μ ν B hNp hB lam (τ*Δ) hblock hblock' p₀ hp₀ p hlen hpPos
        (by intro n _ hn; simpa only [Nat.sub_zero,sourceProfile,Nat.cast_zero,regularizedProfile_zero,sub_zero] using hi₀ n hn)
        hcoef₀ V hV hVdiag hVpin
        (reverse_caps_all_radii μ _ ν hac hVG (hab.trans hbN) hreverseOuter hcap)
      refine ⟨H,hH,?_,?_⟩
      · simpa [cost] using hd
      · simpa [threeIntervalDepth,threeIntervalFactor] using hk
    · have hlen : p.length = a := by simpa [threeIntervalDepth] using hpLen
      have hp' : p ∈ Q.occupiedPaths ρ a := by simpa [threeIntervalDepth] using hp
      let w₀ : Sphere (h+2) := ⟨EuclideanSpace.basisFun (Fin (h+2)) ℝ 0,by
        simpa only [Metric.mem_sphere,dist_zero_right] using
          (EuclideanSpace.basisFun (Fin (h+2)) ℝ).norm_eq_one 0⟩
      obtain ⟨H,hH,_,hd,hk⟩ := hmiddle M hM Q hQ μ ν (by simp) N B hNp hB lam
        (τ*Δ+(((h+2:ℕ):ℝ)+t)/(N:ℝ)) σ (by positivity) hlam hσ
        (cellContraction_le_one _) (cellContraction_sqrt _) hblock hblock' p₀ hp₀
        a b hab hbN (Nat.sub_le _ _) p hlen hpPos
        (by intro n hn hn'; have hh := hi₁ n hn hn'; linarith only [hh]) hcoef₁ w₀ V hV
        (fun z x hz => ⟨hdiag hz.1,hz.2.1⟩)
        (reverse_caps_transfer μ _ ν hac hVG ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans hbN))
          hreverseMiddle hcap)
        (s/2) D (C/(2:ℝ)^b) (by positivity) hfr hwi (by
          intro x hx
          obtain ⟨z,hz⟩ := hx
          refine ⟨occupied_cell_center_separation Q hside ρ A P hρA hsep hsmallA hp'
            x (hG₀core hz.1).2,?_⟩
          exact ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant p).measurable
            (fun y hy => hVpin z x hz y hy))
      refine ⟨H,hH,?_,?_⟩
      · simpa [cost] using hd
      · simpa [threeIntervalDepth,threeIntervalFactor,M] using hk
    · have hlen : p.length = b := by simpa [threeIntervalDepth] using hpLen
      obtain ⟨H,hH,_,hd,hk⟩ := houter N hNo η hη b N hJoB le_rfl
        μ ν B hNp hB lam (τ*Δ+(((h+2:ℕ):ℝ)+q)/(N:ℝ)) hblock hblock' p₀ hp₀ p hlen hpPos
        (by intro n hn hn'; have hh := hi₂ n hn hn'; linarith only [hh])
        hcoef₂ V hV hVdiag hVpin (reverse_caps_all_radii μ _ ν hac hVG le_rfl hreverseOuter hcap)
      refine ⟨H,hH,?_,?_⟩
      · simpa [cost] using hd
      · simpa [threeIntervalDepth,threeIntervalFactor] using hk
  have hβ : (Δ/2)*(N:ℝ) ≤ (b-a:ℕ) := by
    have hh : ((b-a)-Jm:ℕ) ≤ b-a := Nat.sub_le _ _
    have hh' : (M:ℝ) ≤ (b-a:ℕ) := by exact_mod_cast hh
    nlinarith only [hh',hNM]
  have hconst' : ((2:ℝ)^Jm)^(q+gain/2) ≤ ((2:ℝ)^N)^ξ :=
    (hconst N hNc).trans (Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ (by norm_num)) (mul_le_mul_of_nonneg_left hγΔ hτ.le))
  have hbudget : 20*η+4*ξ+gain*γ/8 ≤ (gain/2)*(Δ/2) :=
    three_interval_relative_budget hΔ.le hγΔ hgain.le hτgain
  obtain ⟨G',hG',hsub,hdel,hcaps⟩ := three_interval_dyadic_gain ρ ν Q hside hab hbN hJm
    A P hρA hs hsep G₀ hG₀ hcore
    (fun j => C/(2:ℝ)^(threeIntervalDepth a b N (j+1))) cost
    (by positivity : 0 ≤ gain/2) hβ hconst' hbudget
    (fun j hj => hsmallAll (threeIntervalDepth_child hab hbN hj))
    (fun j hj => by
      rw [hQ]
      exact dyadic_collision_width (h+2) hs le_rfl
        (threeIntervalDepth_le hab hbN (by omega))) hlocal
  refine ⟨G',hG',hsub.trans hG₀G,?_,hcaps⟩
  have hz : (ρ.prod ν) (G \ G₀) ≤ 0 := hnull.le
  have htotal := relative_pruning_cost_trans (ρ.prod ν) G G₀ G' hz hdel
  rw [zero_add] at htotal
  apply htotal.trans
  have hc := hcost N hNd M Δ hγΔ hNM
  have he : (∑ j ∈ Finset.range 3, cost j)+4*ENNReal.ofReal (((2:ℝ)^N)^(-ξ)) =
      ENNReal.ofReal (2*((2:ℝ)^N)^(-(2*η))+2*(1/(2:ℝ)^M)^gain+
        4*((2:ℝ)^N)^(-ξ)) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,cost,show (0:ℕ) ≠ 1 by omega,
      show (2:ℕ) ≠ 1 by omega,ite_false,ite_true,zero_add,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),ENNReal.ofReal_ofNat]
    ring
  rw [he]
  exact ENNReal.ofReal_le_ofReal hc


end OAI.Falconer.Regularization

end ExtensionScope232

/- Source: OAI.MeasureTheory.Falconer.GeneralScaleNonendpointOneScale. Hash in EXTENSION_PROVENANCE.json. -/
section ExtensionScope233



/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original: lean/OAI/MeasureTheory/Falconer/Estimates/NonendpointOneScale.lean. The geometric/probability proof is retained.
The half-range premise was used only as a forwarded argument; here the actual
general finite theorem supplies the input for 0<q-h<t-h<1. No published
input hypothesis remains. Geometry/support/mass/cap assumptions are retained.
See probe COPYING/PROVENANCE. Fixed-environment compilation/audit pending.
-/

namespace OAI.Falconer.Regularization
open Set MeasureTheory Real Filter NormedSpace
open scoped ENNReal NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable


theorem general_scale_nonendpoint_one_scale_gain 
    {h : ℕ} {α t q D s : ℝ}
    (hq : (h:ℝ) < q) (hqt : q < t)
    (ht : t-(h:ℝ) < 1) (htα : t < α)
    (Q : DyadicCube (h+2)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ C : ℝ, 0 ≤ C → C ≤ ((2:ℝ)^N)^ε →
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        μ Q.carrierᶜ = 0 →
        (∀ y : Space (h+2), ∀ r > 0, μ (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space (h+2)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+2), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^q)) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ x u : Space (h+2), μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-q-c)) := by
  obtain ⟨ε₁,gain,hε₁,hgain,hclass⟩ := general_nonendpoint_contact_gain hq hqt ht
    Q hQ hD hDdim hs
  obtain ⟨τ,hτ,hτε,hτgain,hτgain'⟩ := one_scale_loss_choice (h+2) hε₁ hgain
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hα : 0 ≤ α := by
    have hh := Nat.cast_nonneg (α := ℝ) h
    linarith only [hh,hq,hqt,htα]
  obtain ⟨lam,γ,hlam,hγ,hlamτ,H,Nc,hH,hcontrols,hcontact⟩ :=
    scale_source_classes_uniform_contact (by omega : 0 < h+2) Q hside hα hqt htα hτ
  obtain ⟨Ng,hNg⟩ := hclass τ γ hτ hγ hτε hτgain hτgain'
  obtain ⟨c₀,hc₀,Nd,hNd⟩ := weak_radial_total_cost 0 (4*H+2)
    (A := 0) (by norm_num) hlam (by norm_num : (0:ℝ) < 1)
    (by norm_num : (0:ℝ) < 1) (by positivity : 0 < τ*γ/2)
  let c := min c₀ (gain*γ/8)
  have hc : 0 < c := lt_min hc₀ (by positivity)
  let ε := min (τ*γ) (lam/2)
  have hε : 0 < ε := lt_min (mul_pos hτ hγ) (by positivity)
  refine ⟨ε,c,hε,hc,max H (max (h+2+3) (max Nc (max Ng Nd))),?_⟩
  intro N hN C hC hCscale μ ν _ _ hroot hfrost A P hA hP hAfull hPfull hsep hpin G hG hcap
  simp only [max_le_iff] at hN
  obtain ⟨hHN,hdN,hNc,hNg',hNd'⟩ := hN
  obtain ⟨hNp,hNB,_,hblock,hblock'⟩ := hcontrols N hNc
  have hCbudget : C ≤ ((2:ℝ)^N)^(lam/2) :=
    hCscale.trans (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (min_le_right _ _))
  have hcap0 : ∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space (h+2), ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(τ*γ)*r^q) := by
    filter_upwards [hcap] with z hz
    intro r hr hr1 u hu
    have hr0 : 0 ≤ r := (show 0 ≤ 1/(2:ℝ)^N by positivity).trans hr
    exact (hz r hr hr1 u hu).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (min_le_left _ _))
        (Real.rpow_nonneg hr0 _)))
  have hlocal : ∀ p ∈ regularizationLeaves Q μ N,
      regularizationLabel Q μ N (N/H) p ∈ regularizationIndex Q μ N (N/H)
        (ENNReal.ofReal (((2:ℝ)^N)^(-lam))) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧
        ((sourceClass Q μ N (N/H) p).prod ν) (G \ G') ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))) ∧
        ∀ x u : Space (h+2), sourceClass Q μ N (N/H) p
          {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
            ENNReal.ofReal (((2:ℝ)^N)^(-q-gain*γ/8)) := by
    intro p hp hret
    obtain ⟨G',hG',_,hdel,hbound⟩ := hNg N hNg' μ ν (N/H) hNB lam hlam.le hlamτ
      hblock hblock' p hp (hcontact N hNc C hC hCbudget μ hfrost p hp hret)
      A P hA hP hAfull hPfull hsep hpin G hG hcap0
    exact ⟨G',hG',hdel,hbound⟩
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := source_relative_regularization_gain Q hside μ ν G hG
    hroot hH hHN hdN (by positivity : 0 < ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
    (ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))))
    (ENNReal.ofReal (((2:ℝ)^N)^(-q-gain*γ/8))) (1/(2:ℝ)^N) hlocal
  refine ⟨G',hG',hsub,?_,?_⟩
  · apply hdel.trans
    have hd : ((2:ℝ≥0∞)^(2*N))⁻¹+(N^(4*H+2):ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-lam))+
        ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c₀)) := by
      simpa only [Nat.cast_zero,zero_mul,zero_add,add_zero,Nat.cast_one,one_mul] using hNd N hNd'
    exact hd.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ (by norm_num)) (neg_le_neg (min_le_left _ _))))
  · intro x u
    apply (hbound x u).trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) ?_))
    have hh : c ≤ gain*γ/8 := min_le_right _ _
    linarith only [hh]


end OAI.Falconer.Regularization

end ExtensionScope233
