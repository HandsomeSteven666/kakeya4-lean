import Kakeya4.Construction.Combinatorics.CylinderVolume
import Kakeya4.Construction.Combinatorics.CarrierOverlap
import Kakeya4.Construction.Combinatorics.PairwiseSelection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Convex.Measure
import Kakeya4.Construction.Imported.NuminaThickness.Thickness.BoundingBox

/-!
# Transfer of a sampled convex-clustering certificate to a line cap

The weighted certificate is produced from compact convex-body weighted tests, extending them to
finite-volume convex sets. The sampled certificate controls truncated line tests and the
resulting line cap. The complete WeightedPlanks estimate, shading and subsequent losses remain
separate from these sampling and geometric interfaces.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open ProbabilityTheory
open Real
open scoped ENNReal

namespace Kakeya4.Construction

/-- The indicator of an event, viewed as a real Bernoulli random variable. -/
noncomputable def eventIndicator {Ω : Type*} (A : Set Ω) : Ω → ℝ := by
  classical
  exact fun ω => if ω ∈ A then 1 else 0

/-- Product law for independent Bernoulli inclusion choices indexed by a finite family. -/
noncomputable def bernoulliProductSampleMeasure {ι : Type*} [Fintype ι]
    (p : ι → unitInterval) : Measure (ι → Bool) :=
  Measure.pi (fun i => ProbabilityTheory.bernoulliMeasure true false (p i))

/-- The finite included set represented by a Bernoulli product outcome. -/
def bernoulliProductSample {ι : Type*} [Fintype ι] (ω : ι → Bool) : Finset ι :=
  Finset.univ.filter (fun i => ω i = true)

/-- The indices in a finite family whose entire tube set is contained in a given test set.  For a
convex box `Q`, this is the exact finite analogue of the manuscript's `J_Q` family. -/
def tubeIndicesContainedInSet {ι : Type*} (indices : Finset ι) {E : Type*}
    (tube : ι → Set E) (K : Set E) : Finset ι := by
  classical
  exact indices.filter (fun i => tube i ⊆ K)

/-- Inclusion probabilities obtained by normalizing nonnegative weights by a positive scale.
The pointwise upper bound by `scale` is an explicit hypothesis, so this construction never silently
clips or changes a manuscript weight. -/
noncomputable def bernoulliInclusionProbabilitiesFromWeights {ι : Type*}
    (weights : ι → ℝ) (scale : ℝ) (hscale : 0 < scale)
    (hweights : ∀ i, 0 ≤ weights i ∧ weights i ≤ scale) : ι → unitInterval :=
  fun i => ⟨weights i / scale,
    ⟨div_nonneg (hweights i).1 hscale.le, (div_le_one hscale).2 (hweights i).2⟩⟩

@[simp] theorem bernoulliInclusionProbabilitiesFromWeights_coe {ι : Type*}
    (weights : ι → ℝ) (scale : ℝ) (hscale : 0 < scale)
    (hweights : ∀ i, 0 ≤ weights i ∧ weights i ≤ scale) (i : ι) :
    (bernoulliInclusionProbabilitiesFromWeights weights scale hscale hweights i : ℝ) =
      weights i / scale := rfl

@[simp] theorem mem_bernoulliProductSample {ι : Type*} [Fintype ι]
    (ω : ι → Bool) (i : ι) : i ∈ bernoulliProductSample ω ↔ ω i = true := by
  simp [bernoulliProductSample]

/-- The finite Bernoulli product law is a probability measure. -/
theorem bernoulliProductSampleMeasure_isProbabilityMeasure {ι : Type*} [Fintype ι]
    (p : ι → unitInterval) : IsProbabilityMeasure (bernoulliProductSampleMeasure p) := by
  change IsProbabilityMeasure
    (Measure.pi (fun i => ProbabilityTheory.bernoulliMeasure true false (p i)))
  infer_instance

/-- Coordinate inclusion indicators are mutually independent under the finite Bernoulli product
law. -/
theorem bernoulliProductSample_indicators_iIndepFun {ι : Type*} [Fintype ι]
    (p : ι → unitInterval) :
    iIndepFun (fun i => eventIndicator {ω : ι → Bool | ω i = true})
      (bernoulliProductSampleMeasure p) := by
  classical
  have hcoord :
      iIndepFun (fun i (ω : ι → Bool) => ω i)
        (Measure.pi (fun i => ProbabilityTheory.bernoulliMeasure true false (p i))) := by
    exact iIndepFun_pi (fun _ => aemeasurable_id)
  let toRealIndicator : ∀ _i : ι, Bool → ℝ := fun _ b => if b then 1 else 0
  have hindicator :
      iIndepFun (fun i (ω : ι → Bool) => toRealIndicator i (ω i))
        (bernoulliProductSampleMeasure p) := by
    exact hcoord.comp toRealIndicator (by intro i; fun_prop)
  apply (iIndepFun_congr (fun i => ae_of_all _ fun ω => ?_)).2 hindicator
  cases h : ω i <;> simp [eventIndicator, h, toRealIndicator]

/-- Coordinate inclusion events are measurable in the Bernoulli product sample space. -/
theorem measurableSet_bernoulliProductSample_inclusion {ι : Type*} [Fintype ι]
    (i : ι) : MeasurableSet {ω : ι → Bool | ω i = true} := by
  exact MeasurableSet.preimage (measurableSet_singleton true) (measurable_pi_apply i)

/-- Each coordinate is included with its prescribed Bernoulli probability. -/
theorem bernoulliProductSample_event_real {ι : Type*} [Fintype ι]
    (p : ι → unitInterval) (i : ι) :
    (bernoulliProductSampleMeasure p).real {ω : ι → Bool | ω i = true} = (p i : ℝ) := by
  classical
  let factors : ι → Measure Bool :=
    fun j => ProbabilityTheory.bernoulliMeasure true false (p j)
  have hmap := congrArg (fun ν : Measure Bool => ν {true})
    (MeasureTheory.measurePreserving_eval factors i).map_eq
  rw [Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton true)] at hmap
  have hpre : Function.eval i ⁻¹' ({true} : Set Bool) =
      {ω : ι → Bool | ω i = true} := by
    ext ω
    simp [Function.eval]
  rw [hpre] at hmap
  simpa [Measure.real, bernoulliProductSampleMeasure, factors] using
    congrArg ENNReal.toReal hmap

/-- Exact MGF of a Bernoulli event indicator on a probability space. -/
theorem eventIndicator_mgf_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω)
    (hA : MeasurableSet A) (t : ℝ) :
    mgf (eventIndicator A) μ t = 1 + μ.real A * (Real.exp t - 1) := by
  classical
  rw [mgf]
  have hpoint (ω : Ω) :
      Real.exp (t * eventIndicator A ω) = A.indicator (fun _ : Ω => Real.exp t - 1) ω + 1 := by
    by_cases hω : ω ∈ A <;> simp [eventIndicator, hω]
  calc
    ∫ ω, Real.exp (t * eventIndicator A ω) ∂μ =
        ∫ ω, A.indicator (fun _ : Ω => Real.exp t - 1) ω + 1 ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ hpoint
    _ = (∫ ω, A.indicator (fun _ : Ω => Real.exp t - 1) ω ∂μ) +
        ∫ _ : Ω, (1 : ℝ) ∂μ := by
        exact integral_add ((integrable_indicator_iff hA).2 integrableOn_const)
          (integrable_const _)
    _ = μ.real A * (Real.exp t - 1) + 1 := by
          rw [integral_indicator_const _ hA, integral_const]
          simp [smul_eq_mul]
    _ = 1 + μ.real A * (Real.exp t - 1) := by ring

/-- Bernoulli MGF is bounded by the exponential of its event mass. -/
theorem eventIndicator_mgf_le_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω)
    (hA : MeasurableSet A) (t : ℝ) :
    mgf (eventIndicator A) μ t ≤ Real.exp (μ.real A * (Real.exp t - 1)) := by
  rw [eventIndicator_mgf_eq μ A hA t]
  calc
    1 + μ.real A * (Real.exp t - 1) =
        μ.real A * (Real.exp t - 1) + 1 := by ring
    _ ≤ Real.exp (μ.real A * (Real.exp t - 1)) := Real.add_one_le_exp _

/-- The number of successful events in a finite family, as a real-valued random variable. -/
def finiteEventCount {Ω ι : Type*} (J : Finset ι) (events : ι → Set Ω) : Ω → ℝ :=
  fun ω => ∑ i ∈ J, eventIndicator (events i) ω

/-- The real-valued count of successful coordinate events is the cardinality of the filtered
Bernoulli sample. -/
theorem finiteEventCount_bernoulliCoordinates_eq_cardFilter {ι : Type*}
    (J : Finset ι) (ω : ι → Bool) :
    finiteEventCount J (fun i => {ω : ι → Bool | ω i = true}) ω =
      (J.filter (fun i => ω i = true)).card := by
  classical
  simp only [finiteEventCount, eventIndicator, Set.mem_setOf_eq]
  rw [Finset.sum_boole]

/-- Chernoff's MGF upper-tail inequality for a finite sum of independent Bernoulli event
indicators. The sample space and independence are explicit inputs; the result factors the MGF into
the product of the individual Bernoulli MGFs, ready for a later estimate in terms of event
probabilities. -/
theorem finiteEventCount_upperTail_le_exp_mul_prod_mgf
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (J : Finset ι) (events : ι → Set Ω)
    (hmeas : ∀ i, MeasurableSet (events i))
    (hindep : iIndepFun (fun i => eventIndicator (events i)) μ)
    (t threshold : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | threshold ≤ finiteEventCount J events ω} ≤
      Real.exp (-t * threshold) *
        ∏ i ∈ J, mgf (eventIndicator (events i)) μ t := by
  classical
  letI : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  let X : ι → Ω → ℝ := fun i => eventIndicator (events i)
  let Z : Ω → ℝ := finiteEventCount J events
  have hXmeas : ∀ i, Measurable (X i) := by
    intro i
    change Measurable (fun ω => if ω ∈ events i then 1 else 0)
    exact Measurable.ite (hmeas i) measurable_const measurable_const
  have hZmeas : Measurable Z := by
    change Measurable (fun ω => ∑ i ∈ J, X i ω)
    exact Finset.measurable_sum J (by
      intro i hi
      exact hXmeas i)
  have hZle (ω : Ω) : Z ω ≤ (J.card : ℝ) := by
    dsimp [Z, finiteEventCount, X, eventIndicator]
    calc
      (∑ i ∈ J, if ω ∈ events i then (1 : ℝ) else 0) ≤
          ∑ i ∈ J, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            split_ifs <;> norm_num
      _ = (J.card : ℝ) := by simp
  have hInt : Integrable (fun ω => Real.exp (t * Z ω)) μ := by
    have hmeasExp : Measurable (fun ω => Real.exp (t * Z ω)) := (hZmeas.const_mul t).exp
    refine Integrable.of_bound hmeasExp.aestronglyMeasurable
      (Real.exp (t * (J.card : ℝ))) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hZle ω) ht)
  have hmgfZ : mgf Z μ t =
      ∏ i ∈ J, mgf (eventIndicator (events i)) μ t := by
    change mgf (fun ω => ∑ i ∈ J, eventIndicator (events i) ω) μ t = _
    rw [← Finset.sum_fn]
    exact hindep.mgf_sum (t := t) (fun i => hXmeas i) J
  calc
    μ.real {ω | threshold ≤ Z ω} ≤ Real.exp (-t * threshold) * mgf Z μ t :=
      measure_ge_le_exp_mul_mgf threshold ht hInt
    _ = exp (-t * threshold) * ∏ i ∈ J, mgf (X i) μ t := by
      rw [hmgfZ]
    _ = exp (-t * threshold) * ∏ i ∈ J, mgf (eventIndicator (events i)) μ t := by
      rfl

/-- Chernoff's lower-tail inequality for a finite sum of independent Bernoulli event indicators.
The parameter is nonpositive, as in Mathlib's lower-tail MGF theorem. -/
theorem finiteEventCount_lowerTail_le_exp_mul_prod_mgf
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (J : Finset ι) (events : ι → Set Ω)
    (hmeas : ∀ i, MeasurableSet (events i))
    (hindep : iIndepFun (fun i => eventIndicator (events i)) μ)
    (t threshold : ℝ) (ht : t ≤ 0) :
    μ.real {ω | finiteEventCount J events ω ≤ threshold} ≤
      Real.exp (-t * threshold) *
        ∏ i ∈ J, mgf (eventIndicator (events i)) μ t := by
  classical
  letI : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  let X : ι → Ω → ℝ := fun i => eventIndicator (events i)
  let Z : Ω → ℝ := finiteEventCount J events
  have hXmeas : ∀ i, Measurable (X i) := by
    intro i
    change Measurable (fun ω => if ω ∈ events i then 1 else 0)
    exact Measurable.ite (hmeas i) measurable_const measurable_const
  have hZmeas : Measurable Z := by
    change Measurable (fun ω => ∑ i ∈ J, X i ω)
    exact Finset.measurable_sum J (by
      intro i hi
      exact hXmeas i)
  have hZnonneg (ω : Ω) : 0 ≤ Z ω := by
    dsimp [Z, finiteEventCount, X, eventIndicator]
    exact Finset.sum_nonneg fun i hi => by split_ifs <;> norm_num
  have hInt : Integrable (fun ω => Real.exp (t * Z ω)) μ := by
    have hmeasExp : Measurable (fun ω => Real.exp (t * Z ω)) := (hZmeas.const_mul t).exp
    refine Integrable.of_bound hmeasExp.aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hmul : t * Z ω ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht (hZnonneg ω)
    simpa using Real.exp_le_exp.mpr hmul
  have hmgfZ : mgf Z μ t =
      ∏ i ∈ J, mgf (eventIndicator (events i)) μ t := by
    change mgf (fun ω => ∑ i ∈ J, eventIndicator (events i) ω) μ t = _
    rw [← Finset.sum_fn]
    exact hindep.mgf_sum (t := t) (fun i => hXmeas i) J
  calc
    μ.real {ω | Z ω ≤ threshold} ≤ Real.exp (-t * threshold) * mgf Z μ t :=
      measure_le_le_exp_mul_mgf threshold ht hInt
    _ = Real.exp (-t * threshold) *
          ∏ i ∈ J, mgf (eventIndicator (events i)) μ t := by rw [hmgfZ]
    _ = Real.exp (-t * threshold) *
          ∏ i ∈ J, mgf (eventIndicator (events i)) μ t := rfl

/-- Lower-tail bound for the number of selected coordinates in a finite Bernoulli product sample,
with the individual MGF bounds written directly in terms of the prescribed inclusion probabilities.
-/
theorem bernoulliProductSample_filter_lowerTail_le_exp_mul_prod_exp
    {ι : Type*} [Fintype ι] (p : ι → unitInterval) (J : Finset ι)
    (t threshold : ℝ) (ht : t ≤ 0) :
    (bernoulliProductSampleMeasure p).real
        {ω | ((J.filter (fun i => ω i = true)).card : ℝ) ≤ threshold} ≤
      Real.exp (-t * threshold) *
        ∏ i ∈ J, Real.exp ((p i : ℝ) * (Real.exp t - 1)) := by
  classical
  let events : ι → Set (ι → Bool) := fun i => {ω | ω i = true}
  have hindep := bernoulliProductSample_indicators_iIndepFun p
  have hprob : IsProbabilityMeasure (bernoulliProductSampleMeasure p) :=
    bernoulliProductSampleMeasure_isProbabilityMeasure p
  letI := hprob
  have hprod :
      (∏ i ∈ J, mgf (eventIndicator (events i)) (bernoulliProductSampleMeasure p) t) ≤
        ∏ i ∈ J, Real.exp ((p i : ℝ) * (Real.exp t - 1)) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact mgf_nonneg
    · intro i hi
      calc
        mgf (eventIndicator (events i)) (bernoulliProductSampleMeasure p) t ≤
            Real.exp ((bernoulliProductSampleMeasure p).real (events i) *
              (Real.exp t - 1)) :=
          eventIndicator_mgf_le_exp (bernoulliProductSampleMeasure p) (events i)
            (measurableSet_bernoulliProductSample_inclusion i) t
        _ = Real.exp ((p i : ℝ) * (Real.exp t - 1)) := by
          rw [bernoulliProductSample_event_real p i]
  have hset :
      {ω | ((J.filter (fun i => ω i = true)).card : ℝ) ≤ threshold} =
        {ω | finiteEventCount J events ω ≤ threshold} := by
    ext ω
    change ((J.filter (fun i => ω i = true)).card : ℝ) ≤ threshold ↔
      finiteEventCount J (fun i => {ω : ι → Bool | ω i = true}) ω ≤ threshold
    rw [finiteEventCount_bernoulliCoordinates_eq_cardFilter J ω]
  calc
    (bernoulliProductSampleMeasure p).real
        {ω | ((J.filter (fun i => ω i = true)).card : ℝ) ≤ threshold} =
        (bernoulliProductSampleMeasure p).real
          {ω | finiteEventCount J events ω ≤ threshold} := by rw [hset]
    _ ≤ Real.exp (-t * threshold) *
          ∏ i ∈ J, mgf (eventIndicator (events i)) (bernoulliProductSampleMeasure p) t :=
      finiteEventCount_lowerTail_le_exp_mul_prod_mgf _ J events
        (fun i => measurableSet_bernoulliProductSample_inclusion i) hindep t threshold ht
    _ ≤ Real.exp (-t * threshold) *
          ∏ i ∈ J, Real.exp ((p i : ℝ) * (Real.exp t - 1)) :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le

/-- Manuscript-scale lower tail for the total Bernoulli sample.  If `S` is the exact sum of the
inclusion probabilities, then the probability that the real sample cardinality is below `S/2` is
at most `exp(-S/8)`. -/
theorem bernoulliProductSample_card_lt_half_sum_le_exp_of_sum_eq
    {ι : Type*} [Fintype ι] (p : ι → unitInterval) (S : ℝ)
    (hS : (∑ i ∈ Finset.univ, (p i : ℝ)) = S) :
    (bernoulliProductSampleMeasure p).real
      {ω : ι → Bool | ((bernoulliProductSample ω).card : ℝ) < S / 2} ≤
        Real.exp (-S / 8) := by
  classical
  letI := bernoulliProductSampleMeasure_isProbabilityMeasure p
  have hS_nonneg : 0 ≤ S := by
    rw [← hS]
    apply Finset.sum_nonneg
    intro i hi
    exact (p i).property.1
  have hsmall : Real.exp (-1) ≤ (3 : ℝ) / 8 := by
    have h := Real.exp_neg_one_lt_d9
    have h' : Real.exp (-1) < (919698603 / 2500000000 : ℝ) := by
      norm_num at h
      exact h
    have hrat : (919698603 / 2500000000 : ℝ) ≤ 3 / 8 := by norm_num
    exact h'.le.trans hrat
  have hExponent : -(-1 : ℝ) * (S / 2) + S * (Real.exp (-1) - 1) ≤ -S / 8 := by
    have hmul := mul_le_mul_of_nonneg_left hsmall hS_nonneg
    nlinarith [hmul]
  have hcard (ω : ι → Bool) :
      (bernoulliProductSample ω).card =
        (Finset.univ.filter (fun i => ω i = true)).card := by
    simp [bernoulliProductSample]
  have hsubset :
      {ω : ι → Bool | ((bernoulliProductSample ω).card : ℝ) < S / 2} ⊆
        {ω : ι → Bool | (((Finset.univ : Finset ι).filter
          (fun i => ω i = true)).card : ℝ) ≤ S / 2} := by
    intro ω hω
    change ((bernoulliProductSample ω).card : ℝ) < S / 2 at hω
    rw [hcard ω] at hω
    exact hω.le
  have hlow := bernoulliProductSample_filter_lowerTail_le_exp_mul_prod_exp p
    Finset.univ (-1) (S / 2) (by norm_num)
  have hprod :
      (∏ i ∈ Finset.univ, Real.exp ((p i : ℝ) * (Real.exp (-1) - 1))) =
        Real.exp (S * (Real.exp (-1) - 1)) := by
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.sum_mul, hS]
  calc
    (bernoulliProductSampleMeasure p).real
        {ω : ι → Bool | ((bernoulliProductSample ω).card : ℝ) < S / 2} ≤
        (bernoulliProductSampleMeasure p).real
          {ω : ι → Bool | (((Finset.univ : Finset ι).filter
            (fun i => ω i = true)).card : ℝ) ≤ S / 2} :=
      measureReal_mono hsubset
    _ ≤ Real.exp (-(-1 : ℝ) * (S / 2)) *
          ∏ i ∈ Finset.univ, Real.exp ((p i : ℝ) * (Real.exp (-1) - 1)) := hlow
    _ = Real.exp (-(-1 : ℝ) * (S / 2) + S * (Real.exp (-1) - 1)) := by
      rw [hprod, ← Real.exp_add]
    _ ≤ Real.exp (-S / 8) := Real.exp_le_exp.mpr hExponent

/-- A natural sample-size failure below a cutoff no larger than `S/2` is contained in the
manuscript's real lower-tail event. -/
theorem bernoulliProductSample_card_lt_minSize_le_exp_of_sum_eq
    {ι : Type*} [Fintype ι] (p : ι → unitInterval) (S : ℝ)
    (hS : (∑ i ∈ Finset.univ, (p i : ℝ)) = S) (minSize : ℕ)
    (hmin : (minSize : ℝ) ≤ S / 2) :
    (bernoulliProductSampleMeasure p).real
      {ω : ι → Bool | (bernoulliProductSample ω).card < minSize} ≤ Real.exp (-S / 8) := by
  letI := bernoulliProductSampleMeasure_isProbabilityMeasure p
  have hsubset :
      {ω : ι → Bool | (bernoulliProductSample ω).card < minSize} ⊆
        {ω : ι → Bool | ((bernoulliProductSample ω).card : ℝ) < S / 2} := by
    intro ω hω
    have hcast : ((bernoulliProductSample ω).card : ℝ) < (minSize : ℝ) := by
      exact_mod_cast hω
    exact hcast.trans_le hmin
  exact (measureReal_mono hsubset).trans
    (bernoulliProductSample_card_lt_half_sum_le_exp_of_sum_eq p S hS)

/-- Convert a real-valued event probability bound back to the original ENNReal measure. -/
theorem measure_le_ofReal_of_measureReal_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : Set Ω) (B : ℝ) (hprob : μ.real s ≤ B) :
    μ s ≤ ENNReal.ofReal B := by
  calc
    μ s = ENNReal.ofReal (μ.real s) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hprob

/-- ENNReal-measure form of the manuscript's strict `N_sample < S/2` lower-tail event. -/
theorem bernoulliProductSample_card_lt_half_sum_measure_le_of_sum_eq
    {ι : Type*} [Fintype ι] (p : ι → unitInterval) (S : ℝ)
    (hS : (∑ i ∈ Finset.univ, (p i : ℝ)) = S) :
    bernoulliProductSampleMeasure p
      {ω : ι → Bool | ((bernoulliProductSample ω).card : ℝ) < S / 2} ≤
        ENNReal.ofReal (Real.exp (-S / 8)) := by
  letI := bernoulliProductSampleMeasure_isProbabilityMeasure p
  apply measure_le_ofReal_of_measureReal_le
  exact bernoulliProductSample_card_lt_half_sum_le_exp_of_sum_eq p S hS

/-- ENNReal-measure version of the manuscript's `exp(-S/8)` sample-size lower tail, ready to be
added to the failure mass consumed by the common-good-sample selector. -/
theorem bernoulliProductSample_card_lt_minSize_measure_le_of_sum_eq
    {ι : Type*} [Fintype ι] (p : ι → unitInterval) (S : ℝ)
    (hS : (∑ i ∈ Finset.univ, (p i : ℝ)) = S) (minSize : ℕ)
    (hmin : (minSize : ℝ) ≤ S / 2) :
    bernoulliProductSampleMeasure p
      {ω : ι → Bool | (bernoulliProductSample ω).card < minSize} ≤
        ENNReal.ofReal (Real.exp (-S / 8)) := by
  letI := bernoulliProductSampleMeasure_isProbabilityMeasure p
  apply measure_le_ofReal_of_measureReal_le
  exact bernoulliProductSample_card_lt_minSize_le_exp_of_sum_eq p S hS minSize hmin

/-- Upper-tail bound for the number of selected coordinates in a finite Bernoulli product sample.
If the sum of inclusion probabilities over `J` is at most `meanBound`, then the probability that
at least `threshold` indices of `J` are selected is bounded by the exponential Chernoff estimate.
This is the direct finite-family interface for a single box test once its expected count is bounded.
-/
theorem bernoulliProductSample_filter_upperTail_le_exp_of_sum_le
    {ι : Type*} [Fintype ι] (p : ι → unitInterval) (J : Finset ι)
    (t threshold meanBound : ℝ) (ht : 0 ≤ t)
    (hmean : (∑ i ∈ J, (p i : ℝ)) ≤ meanBound) :
    (bernoulliProductSampleMeasure p).real
        {ω | threshold ≤ ((J.filter (fun i => ω i = true)).card : ℝ)} ≤
      Real.exp (-t * threshold + (Real.exp t - 1) * meanBound) := by
  classical
  let events : ι → Set (ι → Bool) := fun i => {ω | ω i = true}
  have hindep := bernoulliProductSample_indicators_iIndepFun p
  have hprob := bernoulliProductSampleMeasure_isProbabilityMeasure p
  letI := hprob
  have hset :
      {ω | threshold ≤ ((J.filter (fun i => ω i = true)).card : ℝ)} =
        {ω | threshold ≤ finiteEventCount J events ω} := by
    ext ω
    change threshold ≤ ((J.filter (fun i => ω i = true)).card : ℝ) ↔
      threshold ≤ finiteEventCount J (fun i => {ω : ι → Bool | ω i = true}) ω
    rw [finiteEventCount_bernoulliCoordinates_eq_cardFilter J ω]
  have hmgf :
      ∏ i ∈ J, Real.exp ((p i : ℝ) * (Real.exp t - 1)) ≤
        Real.exp ((Real.exp t - 1) * meanBound) := by
    calc
      ∏ i ∈ J, Real.exp ((p i : ℝ) * (Real.exp t - 1)) =
          Real.exp ((∑ i ∈ J, (p i : ℝ)) * (Real.exp t - 1)) := by
            rw [← Real.exp_sum, Finset.sum_mul]
      _ ≤ Real.exp (meanBound * (Real.exp t - 1)) :=
        Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hmean
            (sub_nonneg.mpr (Real.one_le_exp ht)))
      _ = Real.exp ((Real.exp t - 1) * meanBound) := by ring_nf
  calc
    (bernoulliProductSampleMeasure p).real
        {ω | threshold ≤ ((J.filter (fun i => ω i = true)).card : ℝ)} =
        (bernoulliProductSampleMeasure p).real
          {ω | threshold ≤ finiteEventCount J events ω} := by rw [hset]
    _ ≤ Real.exp (-t * threshold) *
          ∏ i ∈ J, mgf (eventIndicator (events i))
            (bernoulliProductSampleMeasure p) t :=
      finiteEventCount_upperTail_le_exp_mul_prod_mgf _ J events
        (fun i => measurableSet_bernoulliProductSample_inclusion i) hindep t threshold ht
    _ ≤ Real.exp (-t * threshold) *
          ∏ i ∈ J, Real.exp ((p i : ℝ) * (Real.exp t - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Finset.prod_le_prod₀
      · intro i hi
        exact mgf_nonneg
      · intro i hi
        calc
          mgf (eventIndicator (events i)) (bernoulliProductSampleMeasure p) t ≤
              Real.exp ((bernoulliProductSampleMeasure p).real (events i) *
                (Real.exp t - 1)) :=
            eventIndicator_mgf_le_exp (bernoulliProductSampleMeasure p) (events i)
              (measurableSet_bernoulliProductSample_inclusion i) t
          _ = Real.exp ((p i : ℝ) * (Real.exp t - 1)) := by
            rw [bernoulliProductSample_event_real p i]
    _ ≤ Real.exp (-t * threshold) *
          Real.exp ((Real.exp t - 1) * meanBound) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-t * threshold + (Real.exp t - 1) * meanBound) := by
      rw [← Real.exp_add]

/-- A weighted convex-count estimate for a common-volume family implies the probability-sum
bound required by the single-box Bernoulli Chernoff theorem. The weights are normalized by `scale`
exactly as in the manuscript; `tubeVolume` and `boxVolume` are explicit positive real inputs. -/
theorem bernoulliWeight_sum_le_boxVolume_div_tubeVolume
    {ι : Type*} (weights : ι → ℝ) (scale tubeVolume boxVolume : ℝ) (J : Finset ι)
    (hscale : 0 < scale) (htube : 0 < tubeVolume)
    (hweights : ∀ i, 0 ≤ weights i ∧ weights i ≤ scale)
    (hweighted : (∑ i ∈ J, weights i * tubeVolume) ≤ scale * boxVolume) :
    (∑ i ∈ J,
      (bernoulliInclusionProbabilitiesFromWeights weights scale hscale hweights i : ℝ)) ≤
        boxVolume / tubeVolume := by
  have hsum :
      (∑ i ∈ J,
        (bernoulliInclusionProbabilitiesFromWeights weights scale hscale hweights i : ℝ)) =
          (∑ i ∈ J, weights i) / scale := by
    simp [bernoulliInclusionProbabilitiesFromWeights, Finset.sum_div]
  have hweighted' : (∑ i ∈ J, weights i) * tubeVolume ≤ scale * boxVolume := by
    simpa only [Finset.sum_mul] using hweighted
  rw [hsum, div_le_div_iff₀ hscale htube]
  nlinarith [hweighted']

/-- Weighted single-box sampling estimate matching the normalized-weight step in the manuscript.
If every index has weight in `[0, scale]`, and the common tube-volume weighted sum over the
box-eligible family is at most `scale * boxVolume`, then independent sampling with probabilities
`weight / scale` satisfies the explicit Chernoff upper-tail bound with mean proxy
`boxVolume / tubeVolume`. -/
theorem bernoulliProductSample_weightedBox_upperTail
    {ι : Type*} [Fintype ι] (weights : ι → ℝ) (scale tubeVolume boxVolume : ℝ)
    (J : Finset ι) (hscale : 0 < scale) (htube : 0 < tubeVolume)
    (hweights : ∀ i, 0 ≤ weights i ∧ weights i ≤ scale)
    (hweighted : (∑ i ∈ J, weights i * tubeVolume) ≤ scale * boxVolume)
    (t threshold : ℝ) (ht : 0 ≤ t) :
    (bernoulliProductSampleMeasure
      (bernoulliInclusionProbabilitiesFromWeights weights scale hscale hweights)).real
        {ω | threshold ≤ ((J.filter (fun i => ω i = true)).card : ℝ)} ≤
      Real.exp (-t * threshold + (Real.exp t - 1) * (boxVolume / tubeVolume)) := by
  exact bernoulliProductSample_filter_upperTail_le_exp_of_sum_le _ J t threshold
    (boxVolume / tubeVolume) ht
    (bernoulliWeight_sum_le_boxVolume_div_tubeVolume weights scale tubeVolume boxVolume J
      hscale htube hweights hweighted)

/-- Explicit finite-family form of the weighted convex-clustering hypothesis used in the
manuscript's sampling step.  The tube family, real volume values, weights, and scale are caller
data; the certificate records the actual convex-test inequality and does not construct that
inequality from GWZ inputs. Tests with real-valued volume must have finite volume: otherwise
`∞.toReal = 0` would incorrectly force positive tube weights to vanish on the whole-space test. -/
structure WeightedConvexClusteringCertificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} (indices : Finset ι) (tube : ι → Set E) (weights : ι → ℝ)
    (scale : ℝ) : Prop where
  weights_nonneg : ∀ i, 0 ≤ weights i
  tube_convex : ∀ i, Convex ℝ (tube i)
  tube_volume_pos : ∀ i, 0 < (volume (tube i)).toReal
  tube_volume_ne_top : ∀ i, volume (tube i) ≠ ⊤
  convex_test_bound : ∀ K : Set E, Convex ℝ K → volume K ≠ ⊤ → ∀ J : Finset ι,
    J ⊆ indices → (∀ i ∈ J, tube i ⊆ K) →
    (∑ i ∈ J, weights i * (volume (tube i)).toReal) ≤
      scale * (volume K).toReal

/-- Produce the sampling certificate from the manuscript's actual compact convex-body weighted
test inequality. The proof extends the test to every finite-volume convex set via its closure,
then passes from the full indexed family to any subfamily by nonnegativity. Neither closedness
of the caller's test set nor a pre-existing sampling certificate is assumed. -/
theorem weightedConvexClusteringCertificate_of_compact_convex_body_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {ι : Type*} [DecidableEq ι] (indices : Finset ι) (tube : ι → Set E)
    (weights : ι → ℝ) (scale : ℝ) (hscale : 0 ≤ scale)
    (hweights : ∀ i, 0 ≤ weights i) (hconvex : ∀ i, Convex ℝ (tube i))
    (hpos : ∀ i, 0 < (volume (tube i)).toReal)
    (htop : ∀ i, volume (tube i) ≠ ⊤)
    (hbody : ∀ K : Set E, IsCompact K → Convex ℝ K → 0 < volume K →
      (∑ i ∈ tubeIndicesContainedInSet indices tube K, weights i * (volume (tube i)).toReal) ≤
        scale * (volume K).toReal) :
    WeightedConvexClusteringCertificate indices tube weights scale := by
  classical
  refine ⟨hweights, hconvex, hpos, htop, ?_⟩
  intro K hK hKtop J hJ hcontained
  by_cases hJempty : J = ∅
  · simpa [hJempty] using mul_nonneg hscale (ENNReal.toReal_nonneg : 0 ≤ (volume K).toReal)
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hJempty
  have hi0 : volume (tube i) ≠ 0 := by
    intro hz
    simpa [hz] using hpos i
  have hK0 : volume K ≠ 0 :=
    ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hi0) (measure_mono (hcontained i hi)))
  have hbounded := hK.isBounded_of_volume_ne_zero_of_ne_top hK0 hKtop
  have hclosure : volume (closure K) = volume K :=
    measure_closure_of_null_frontier (hK.addHaar_frontier volume)
  have hbound := hbody (closure K) hbounded.isCompact_closure hK.closure
    (by rw [hclosure]; exact pos_iff_ne_zero.mpr hK0)
  have hsubset : J ⊆ tubeIndicesContainedInSet indices tube (closure K) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨hJ hj, (hcontained j hj).trans subset_closure⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun j => weights j * (volume (tube j)).toReal) hsubset
    (fun j _ _ => mul_nonneg (hweights j) ENNReal.toReal_nonneg)
  exact hsum.trans (by simpa only [hclosure] using hbound)

/-- Testing the weighted convex-clustering certificate on one tube proves the normalized
Bernoulli prerequisite `weight i ≤ scale`.  Positivity of the tube volume is essential and is
recorded in the certificate. -/
theorem WeightedConvexClusteringCertificate.weight_le_scale
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {indices : Finset ι} {tube : ι → Set E} {weights : ι → ℝ}
    {scale : ℝ} (cert : WeightedConvexClusteringCertificate indices tube weights scale)
    (i : ι) (hi : i ∈ indices) : weights i ≤ scale := by
  have htest := cert.convex_test_bound (tube i) (cert.tube_convex i)
    (cert.tube_volume_ne_top i) {i}
    (by simpa using hi) (by intro j hj; simp only [Finset.mem_singleton] at hj; simpa [hj])
  have hsingle : weights i * (volume (tube i)).toReal ≤
      scale * (volume (tube i)).toReal := by simpa using htest
  nlinarith [cert.tube_volume_pos i]

/-- A convex clustering test on a box, plus the common tube-volume identity, gives precisely the
weighted hypothesis consumed by the single-box Bernoulli tail theorem. -/
theorem WeightedConvexClusteringCertificate.box_weighted_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {indices : Finset ι} {tube : ι → Set E} {weights : ι → ℝ}
    {scale boxVolume tubeVolume : ℝ}
    (cert : WeightedConvexClusteringCertificate indices tube weights scale)
    (K : Set E) (hK : Convex ℝ K) (hKtop : volume K ≠ ⊤)
    (J : Finset ι) (hJ : J ⊆ indices)
    (hcontained : ∀ i ∈ J, tube i ⊆ K)
    (hbox : (volume K).toReal = boxVolume)
    (hcommon : ∀ i ∈ J, (volume (tube i)).toReal = tubeVolume) :
    (∑ i ∈ J, weights i * tubeVolume) ≤ scale * boxVolume := by
  have h := cert.convex_test_bound K hK hKtop J hJ hcontained
  rw [hbox] at h
  have hsum : (∑ i ∈ J, weights i * tubeVolume) =
      ∑ i ∈ J, weights i * (volume (tube i)).toReal := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcommon i hi]
  rw [hsum]
  exact h

/-- End-to-end single-box call from the weighted convex certificate to the Bernoulli sample
count.  The caller supplies the concrete convex box, its volume, the common tube volume, and the
containment predicate defining its eligible indices. -/
theorem WeightedConvexClusteringCertificate.box_upperTail
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] {indices : Finset ι} {tube : ι → Set E}
    {weights : ι → ℝ} {scale boxVolume tubeVolume : ℝ}
    (cert : WeightedConvexClusteringCertificate indices tube weights scale)
    (K : Set E) (hK : Convex ℝ K) (hKtop : volume K ≠ ⊤)
    (J : Finset ι) (hJ : J ⊆ indices)
    (hcontained : ∀ i ∈ J, tube i ⊆ K)
    (hbox : (volume K).toReal = boxVolume)
    (hcommon : ∀ i ∈ J, (volume (tube i)).toReal = tubeVolume)
    (hindices : indices = Finset.univ)
    (hscale : 0 < scale) (htube : 0 < tubeVolume)
    (t threshold : ℝ) (ht : 0 ≤ t) :
    (bernoulliProductSampleMeasure
      (bernoulliInclusionProbabilitiesFromWeights weights scale hscale
        (fun i => ⟨cert.weights_nonneg i,
          cert.weight_le_scale i (by simpa [hindices])⟩))).real
        {ω | threshold ≤ ((J.filter (fun i => ω i = true)).card : ℝ)} ≤
      Real.exp (-t * threshold + (Real.exp t - 1) * (boxVolume / tubeVolume)) := by
  exact bernoulliProductSample_weightedBox_upperTail weights scale tubeVolume boxVolume J
    hscale htube (fun i => ⟨cert.weights_nonneg i,
      cert.weight_le_scale i (by simpa [hindices])⟩)
    (cert.box_weighted_bound K hK hKtop J hJ hcontained hbox hcommon) t threshold ht

/-- ENNReal measure estimate for the selector's natural-number box failure event.  The strict
failure condition `boxBound < count` is converted exactly to the real Chernoff threshold
`boxBound + 1`; all weighted convex, common-volume, and containment inputs remain explicit. -/
theorem WeightedConvexClusteringCertificate.boxFailure_measure_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {indices : Finset ι}
    {tube : ι → Set E} {weights : ι → ℝ} {scale boxVolume tubeVolume : ℝ}
    (cert : WeightedConvexClusteringCertificate indices tube weights scale)
    (K : Set E) (hK : Convex ℝ K) (hKtop : volume K ≠ ⊤)
    (hbox : (volume K).toReal = boxVolume)
    (hcommon : ∀ i ∈ tubeIndicesContainedInSet indices tube K,
      (volume (tube i)).toReal = tubeVolume)
    (hindices : indices = Finset.univ) (hscale : 0 < scale) (htube : 0 < tubeVolume)
    (boxBound : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    bernoulliProductSampleMeasure
        (bernoulliInclusionProbabilitiesFromWeights weights scale hscale
          (fun i => ⟨cert.weights_nonneg i,
            cert.weight_le_scale i (by simpa [hindices])⟩))
      {ω : ι → Bool | boxBound <
        (bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube K).card} ≤
      ENNReal.ofReal (Real.exp
        (-t * ((boxBound + 1 : ℕ) : ℝ) +
          (Real.exp t - 1) * (boxVolume / tubeVolume))) := by
  classical
  let p := bernoulliInclusionProbabilitiesFromWeights weights scale hscale
    (fun i => ⟨cert.weights_nonneg i,
      cert.weight_le_scale i (by simpa [hindices])⟩)
  let J := tubeIndicesContainedInSet indices tube K
  let μ := bernoulliProductSampleMeasure p
  letI : IsProbabilityMeasure μ := bernoulliProductSampleMeasure_isProbabilityMeasure p
  have hJ : J ⊆ indices := by
    dsimp [J, tubeIndicesContainedInSet]
    exact Finset.filter_subset _ _
  have hcontained : ∀ i ∈ J, tube i ⊆ K := by
    intro i hi
    exact (Finset.mem_filter.mp (show i ∈ indices.filter (fun i => tube i ⊆ K) from by
      simpa [J, tubeIndicesContainedInSet] using hi)).2
  have hreal := cert.box_upperTail K hK hKtop J hJ hcontained hbox hcommon hindices
    hscale htube t ((boxBound + 1 : ℕ) : ℝ) ht
  have hset :
      {ω : ι → Bool | boxBound <
          (bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube K).card} =
        {ω : ι → Bool | ((boxBound + 1 : ℕ) : ℝ) ≤
          ((J.filter (fun i => ω i = true)).card : ℝ)} := by
    ext ω
    have hcount :
        (bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube K).card =
          (J.filter (fun i => ω i = true)).card := by
      have hfinset : bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube K =
          J.filter (fun i => ω i = true) := by
        ext i
        simp [bernoulliProductSample, J, tubeIndicesContainedInSet, and_comm]
      rw [hfinset]
    change boxBound <
      (bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube K).card ↔
        ((boxBound + 1 : ℕ) : ℝ) ≤ ((J.filter (fun i => ω i = true)).card : ℝ)
    rw [hcount]
    exact_mod_cast (Nat.lt_iff_add_one_le (m := boxBound)
      (n := (J.filter (fun i => ω i = true)).card))
  have hprob : μ.real
      {ω : ι → Bool | ((boxBound + 1 : ℕ) : ℝ) ≤
        ((J.filter (fun i => ω i = true)).card : ℝ)} ≤
      Real.exp (-t * ((boxBound + 1 : ℕ) : ℝ) +
        (Real.exp t - 1) * (boxVolume / tubeVolume)) := by
    simpa [μ, p, J] using hreal
  rw [hset]
  simpa [μ, p] using measure_le_ofReal_of_measureReal_le μ _ _ hprob

/-- The fixed-parameter (`t=1`) box tail has the source manuscript's logarithmic rate.
If the box mean ratio is at least `c`, the natural threshold is at least
`L (1+ell)` times that ratio, `L ≥ 2`, and `L*c ≥ d+2`, then the actual ENNReal
box-failure measure is at most `ofReal (δ^(d+2))`, where `δ = exp(-ell)`.
The logarithmic scale, ratio lower bound, and threshold inequality are explicit inputs. -/
theorem WeightedConvexClusteringCertificate.boxFailure_measure_le_of_logarithmic_threshold
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {indices : Finset ι}
    {tube : ι → Set E} {weights : ι → ℝ} {scale boxVolume tubeVolume : ℝ}
    (cert : WeightedConvexClusteringCertificate indices tube weights scale)
    (K : Set E) (hK : Convex ℝ K) (hbox : (volume K).toReal = boxVolume)
    (hcommon : ∀ i ∈ tubeIndicesContainedInSet indices tube K,
      (volume (tube i)).toReal = tubeVolume)
    (hindices : indices = Finset.univ) (hscale : 0 < scale) (htube : 0 < tubeVolume)
    (boxBound d : ℕ) (δ ell L c : ℝ) (hell : 0 ≤ ell)
    (hδ : Real.exp (-ell) = δ)
    (hL : 2 ≤ L) (hc : 0 < c)
    (hLc : ((d + 2 : ℕ) : ℝ) ≤ L * c)
    (hratio : c ≤ boxVolume / tubeVolume)
    (hthreshold : L * (1 + ell) * (boxVolume / tubeVolume) ≤
      ((boxBound + 1 : ℕ) : ℝ)) :
    bernoulliProductSampleMeasure
        (bernoulliInclusionProbabilitiesFromWeights weights scale hscale
          (fun i => ⟨cert.weights_nonneg i,
            cert.weight_le_scale i (by simpa [hindices])⟩))
      {ω : ι → Bool | boxBound <
        (bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube K).card} ≤
      ENNReal.ofReal (δ ^ (d + 2)) := by
  have hr_nonneg : 0 ≤ boxVolume / tubeVolume := le_trans hc.le hratio
  have hExp1 : Real.exp 1 - 1 ≤ 2 := by
    have := Real.exp_one_lt_three
    linarith
  have hLell : 0 ≤ L * ell := mul_nonneg (le_trans (by norm_num) hL) hell
  have hLfactor : L * ell ≤ L * (1 + ell) - 2 := by
    nlinarith [hL]
  have hscaled : L * ell * (boxVolume / tubeVolume) ≤
      (L * (1 + ell) - 2) * (boxVolume / tubeVolume) :=
    mul_le_mul_of_nonneg_right hLfactor hr_nonneg
  have hscaled' : L * ell * c ≤ L * ell * (boxVolume / tubeVolume) :=
    mul_le_mul_of_nonneg_left hratio hLell
  have hdegree : ((d + 2 : ℕ) : ℝ) * ell ≤ L * c * ell :=
    mul_le_mul_of_nonneg_right hLc hell
  have hexponent :
      -((boxBound + 1 : ℕ) : ℝ) + (Real.exp 1 - 1) * (boxVolume / tubeVolume) ≤
        -((d + 2 : ℕ) : ℝ) * ell := by
    calc
      -((boxBound + 1 : ℕ) : ℝ) + (Real.exp 1 - 1) * (boxVolume / tubeVolume)
          ≤ -(L * (1 + ell) * (boxVolume / tubeVolume)) +
              2 * (boxVolume / tubeVolume) := by
                gcongr
      _ = -(L * (1 + ell) - 2) * (boxVolume / tubeVolume) := by ring
      _ ≤ -(L * ell * (boxVolume / tubeVolume)) := by linarith
      _ ≤ -(L * ell * c) := by linarith
      _ = -(L * c * ell) := by ring
      _ ≤ -((d + 2 : ℕ) : ℝ) * ell := by linarith
  have hexp : Real.exp
      (-((boxBound + 1 : ℕ) : ℝ) + (Real.exp 1 - 1) * (boxVolume / tubeVolume)) ≤
        δ ^ (d + 2) := by
    calc
      _ ≤ Real.exp (-((d + 2 : ℕ) : ℝ) * ell) := Real.exp_le_exp.mpr hexponent
      _ = δ ^ (d + 2) := by
        rw [← hδ, ← Real.exp_nat_mul]
        congr 1
        ring
  calc
    _ ≤ ENNReal.ofReal (Real.exp
        (-1 * ((boxBound + 1 : ℕ) : ℝ) +
          (Real.exp 1 - 1) * (boxVolume / tubeVolume))) :=
      cert.boxFailure_measure_le K hK
        (by
          have hmul : c * tubeVolume ≤ boxVolume := (le_div_iff₀ htube).mp hratio
          have hvol : 0 < boxVolume := (mul_pos hc htube).trans_le hmul
          intro hz
          have hzero : boxVolume = 0 := by rw [← hbox, hz, ENNReal.toReal_top]
          linarith)
        hbox hcommon hindices hscale htube boxBound 1 (by norm_num)
    _ ≤ ENNReal.ofReal (δ ^ (d + 2)) := ENNReal.ofReal_le_ofReal (by simpa using hexp)

/-- A finite-family certificate controlling the total carrier volume of every subfamily
contained in a convex test set. This is the precise input consumed by the line-cap transfer. -/
structure SampledConvexClusteringCertificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} (indices : Finset ι) (core : ι → Set E) (δ : ℝ) (A : ℝ≥0∞) : Prop where
  convex_test_bound : ∀ K : Set E, Convex ℝ K → ∀ J : Finset ι, J ⊆ indices →
    (∀ i ∈ J, Metric.cthickening δ (core i) ⊆ K) →
    (∑ i ∈ J, volume (Metric.cthickening δ (core i))) ≤ A * volume K

/-- A finite collection of box-count bounds and a lower bound on sample size hold in one
realization whenever the sum of their failure probabilities is strictly below one.

The probability estimates are explicit inputs. In particular, this lemma is only the finite
union-bound step of the manuscript's Bernoulli sampling argument; it does not establish the
Chernoff bounds or construct the Bernoulli sample space. -/
theorem exists_sample_with_box_bounds_of_failure_mass
    {Ω ι β : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (hprob : μ Set.univ = 1)
    (boxes : Finset β)
    (sample : Ω → Finset ι) (boxIndices : β → Finset ι)
    (boxBound : β → ℕ) (minSize : ℕ)
    (hfail : ∑ q ∈ boxes,
        μ {ω | boxBound q < (sample ω ∩ boxIndices q).card} +
      μ {ω | (sample ω).card < minSize} < 1) :
    ∃ ω, minSize ≤ (sample ω).card ∧
      ∀ q ∈ boxes, (sample ω ∩ boxIndices q).card ≤ boxBound q := by
  classical
  let badBox : β → Set Ω := fun q =>
    {ω | boxBound q < (sample ω ∩ boxIndices q).card}
  let badSize : Set Ω := {ω | (sample ω).card < minSize}
  let bad : Set Ω := (⋃ q ∈ boxes, badBox q) ∪ badSize
  have hbox := measure_biUnion_finset_le boxes badBox (μ := μ)
  have hbad := measure_union_le (μ := μ) (⋃ q ∈ boxes, badBox q) badSize
  have hmeasure : μ bad ≤ ∑ q ∈ boxes, μ (badBox q) + μ badSize := by
    calc
      μ bad ≤ μ (⋃ q ∈ boxes, badBox q) + μ badSize := hbad
      _ ≤ (∑ q ∈ boxes, μ (badBox q)) + μ badSize := by gcongr
  have hlt : μ bad < 1 := by
    apply lt_of_le_of_lt hmeasure
    simpa [badBox, badSize] using hfail
  have hne : bad ≠ Set.univ := by
    intro hEq
    have hle : 1 ≤ μ bad := by
      rw [← hprob, hEq]
    exact (not_lt_of_ge hle) hlt
  have hexists : ∃ ω, ω ∉ bad := by
    by_contra h
    have hall : ∀ ω, ω ∈ bad := by
      simpa only [not_exists, not_not] using h
    apply hne
    ext ω
    simp only [Set.mem_univ, iff_true]
    exact hall ω
  obtain ⟨ω, hω⟩ := hexists
  have hω' : ω ∉ (⋃ q ∈ boxes, badBox q) ∧ ω ∉ badSize := by
    simpa [bad] using hω
  refine ⟨ω, ?_, ?_⟩
  · by_contra hsize
    exact hω'.2 (by simpa [badSize] using hsize)
  · intro q hq
    by_contra hbound
    have hbadq : ω ∈ badBox q := by
      simpa [badBox] using Nat.lt_of_not_ge hbound
    apply hω'.1
    simp only [Set.mem_iUnion]
    exact ⟨q, hq, hbadq⟩

/-- The Bernoulli realization's intersection count on `J_Q` is exactly the filtered sample count
used by the Chernoff theorems. -/
theorem bernoulliProductSample_inter_tubeIndices_card_eq_filter
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ω : ι → Bool) (indices : Finset ι)
    {E : Type*} (tube : ι → Set E) (K : Set E) :
    (bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube K).card =
      ((tubeIndicesContainedInSet indices tube K).filter (fun i => ω i = true)).card := by
  classical
  have hset : bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube K =
      (tubeIndicesContainedInSet indices tube K).filter (fun i => ω i = true) := by
    ext i
    simp [bernoulliProductSample, tubeIndicesContainedInSet, and_comm]
  rw [hset]

/-- Specialization of the finite common-good-sample selector to the manuscript's tube-in-box
index family and the actual Bernoulli product realization.  Failure probabilities remain explicit
inputs; this theorem only connects their event counts to the shared selector. -/
theorem exists_bernoulliProductSample_with_convexBoxBounds_of_failure_mass
    {ι β E : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (p : ι → unitInterval) (indices : Finset ι) (tube : ι → Set E)
    (boxes : Finset β) (box : β → Set E) (boxBound : β → ℕ) (minSize : ℕ)
    (hfail : ∑ q ∈ boxes,
        bernoulliProductSampleMeasure p
          {ω | boxBound q <
            (bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube (box q)).card} +
      bernoulliProductSampleMeasure p
        {ω | (bernoulliProductSample ω).card < minSize} < 1) :
    ∃ ω, minSize ≤ (bernoulliProductSample ω).card ∧
      ∀ q ∈ boxes,
        (bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube (box q)).card ≤
          boxBound q := by
  have hprob : (bernoulliProductSampleMeasure p) Set.univ = 1 :=
    (bernoulliProductSampleMeasure_isProbabilityMeasure p).measure_univ
  exact exists_sample_with_box_bounds_of_failure_mass (bernoulliProductSampleMeasure p)
    hprob boxes bernoulliProductSample
    (fun q => tubeIndicesContainedInSet indices tube (box q)) boxBound minSize hfail

/-- A single explicit Chernoff budget for a finite convex-box family and the Bernoulli sample-size
lower tail produces one realization satisfying every natural box count and the requested minimum
sample size. The convex-clustering certificate, box geometry, common tube volume, and strict total
budget are all caller inputs; this theorem only assembles the proved per-box and sample-size bounds
with the finite common-sample selector. -/
theorem WeightedConvexClusteringCertificate.exists_sample_with_boxBounds_of_chernoff_budget
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    {indices : Finset ι} {tube : ι → Set E} {weights : ι → ℝ}
    {scale tubeVolume : ℝ}
    (cert : WeightedConvexClusteringCertificate indices tube weights scale)
    (hindices : indices = Finset.univ) (hscale : 0 < scale) (htube : 0 < tubeVolume)
    (boxes : Finset β) (box : β → Set E) (boxVolume : β → ℝ)
    (hboxConvex : ∀ q ∈ boxes, Convex ℝ (box q))
    (hboxTop : ∀ q ∈ boxes, volume (box q) ≠ ⊤)
    (hboxVolume : ∀ q ∈ boxes, (volume (box q)).toReal = boxVolume q)
    (hcommon : ∀ q ∈ boxes, ∀ i ∈ tubeIndicesContainedInSet indices tube (box q),
      (volume (tube i)).toReal = tubeVolume)
    (boxBound : β → ℕ) (t : β → ℝ) (ht : ∀ q ∈ boxes, 0 ≤ t q)
    (S : ℝ)
    (hS : (∑ i ∈ Finset.univ,
      ((bernoulliInclusionProbabilitiesFromWeights weights scale hscale
        (fun i => ⟨cert.weights_nonneg i,
          cert.weight_le_scale i (by simpa [hindices])⟩) i : unitInterval) : ℝ)) = S)
    (minSize : ℕ) (hmin : (minSize : ℝ) ≤ S / 2)
    (hbudget : (∑ q ∈ boxes, ENNReal.ofReal (Real.exp
        (-t q * ((boxBound q + 1 : ℕ) : ℝ) +
          (Real.exp (t q) - 1) * (boxVolume q / tubeVolume)))) +
        ENNReal.ofReal (Real.exp (-S / 8)) < 1) :
    ∃ ω, minSize ≤ (bernoulliProductSample ω).card ∧
      ∀ q ∈ boxes,
        (bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube (box q)).card ≤
          boxBound q := by
  classical
  let p := bernoulliInclusionProbabilitiesFromWeights weights scale hscale
    (fun i => ⟨cert.weights_nonneg i,
      cert.weight_le_scale i (by simpa [hindices])⟩)
  let μ := bernoulliProductSampleMeasure p
  have hboxSum :
      (∑ q ∈ boxes, μ {ω | boxBound q <
        (bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube (box q)).card}) ≤
      ∑ q ∈ boxes, ENNReal.ofReal (Real.exp
        (-t q * ((boxBound q + 1 : ℕ) : ℝ) +
          (Real.exp (t q) - 1) * (boxVolume q / tubeVolume))) := by
    apply Finset.sum_le_sum
    intro q hq
    exact cert.boxFailure_measure_le (box q) (hboxConvex q hq) (hboxTop q hq) (hboxVolume q hq)
      (hcommon q hq) hindices hscale htube (boxBound q) (t q) (ht q hq)
  have hsample := bernoulliProductSample_card_lt_minSize_measure_le_of_sum_eq p S
    (by simpa [p] using hS) minSize hmin
  have hfail :
      (∑ q ∈ boxes, μ {ω | boxBound q <
        (bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube (box q)).card}) +
        μ {ω | (bernoulliProductSample ω).card < minSize} < 1 := by
    calc
      _ ≤ (∑ q ∈ boxes, ENNReal.ofReal (Real.exp
          (-t q * ((boxBound q + 1 : ℕ) : ℝ) +
            (Real.exp (t q) - 1) * (boxVolume q / tubeVolume)))) +
            ENNReal.ofReal (Real.exp (-S / 8)) := add_le_add hboxSum hsample
      _ < 1 := hbudget
  exact exists_bernoulliProductSample_with_convexBoxBounds_of_failure_mass p indices tube
    boxes box boxBound minSize (by simpa [μ] using hfail)

/-- Pay a uniform logarithmic box-tail rate against the cardinality of the finite box family.
If each box has failure measure at most `ofReal (δ^(d+2))`, the explicit product of the box
count and this rate, together with the Bernoulli sample-size lower-tail term, is the complete
finite-union budget consumed here. The geometric box family and its cardinality bound remain
caller inputs. -/
theorem WeightedConvexClusteringCertificate.exists_sample_with_boxBounds_of_logarithmic_budget
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    {indices : Finset ι} {tube : ι → Set E} {weights : ι → ℝ}
    {scale tubeVolume : ℝ}
    (cert : WeightedConvexClusteringCertificate indices tube weights scale)
    (hindices : indices = Finset.univ) (hscale : 0 < scale) (htube : 0 < tubeVolume)
    (δ ell L c : ℝ) (hell : 0 ≤ ell) (hδ : Real.exp (-ell) = δ)
    (d : ℕ) (hL : 2 ≤ L) (hc : 0 < c)
    (hLc : ((d + 2 : ℕ) : ℝ) ≤ L * c)
    (boxes : Finset β) (box : β → Set E) (boxVolume : β → ℝ)
    (hboxConvex : ∀ q ∈ boxes, Convex ℝ (box q))
    (hboxVolume : ∀ q ∈ boxes, (volume (box q)).toReal = boxVolume q)
    (hcommon : ∀ q ∈ boxes, ∀ i ∈ tubeIndicesContainedInSet indices tube (box q),
      (volume (tube i)).toReal = tubeVolume)
    (hratio : ∀ q ∈ boxes, c ≤ boxVolume q / tubeVolume)
    (boxBound : β → ℕ)
    (hthreshold : ∀ q ∈ boxes,
      L * (1 + ell) * (boxVolume q / tubeVolume) ≤ ((boxBound q + 1 : ℕ) : ℝ))
    (S : ℝ)
    (hS : (∑ i ∈ Finset.univ,
      ((bernoulliInclusionProbabilitiesFromWeights weights scale hscale
        (fun i => ⟨cert.weights_nonneg i,
          cert.weight_le_scale i (by simpa [hindices])⟩) i : unitInterval) : ℝ)) = S)
    (minSize : ℕ) (hmin : (minSize : ℝ) ≤ S / 2)
    (hbudget : (boxes.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ (d + 2)) +
      ENNReal.ofReal (Real.exp (-S / 8)) < 1) :
    ∃ ω, minSize ≤ (bernoulliProductSample ω).card ∧
      ∀ q ∈ boxes,
        (bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube (box q)).card ≤
          boxBound q := by
  classical
  let p := bernoulliInclusionProbabilitiesFromWeights weights scale hscale
    (fun i => ⟨cert.weights_nonneg i,
      cert.weight_le_scale i (by simpa [hindices])⟩)
  let μ := bernoulliProductSampleMeasure p
  have hboxSum :
      (∑ q ∈ boxes, μ {ω | boxBound q <
        (bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube (box q)).card}) ≤
      (boxes.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ (d + 2)) := by
    calc
      _ ≤ ∑ q ∈ boxes, ENNReal.ofReal (δ ^ (d + 2)) := by
        apply Finset.sum_le_sum
        intro q hq
        exact cert.boxFailure_measure_le_of_logarithmic_threshold
          (box q) (hboxConvex q hq) (hboxVolume q hq) (hcommon q hq)
          hindices hscale htube (boxBound q) d δ ell L c hell hδ hL hc hLc
          (hratio q hq) (hthreshold q hq)
      _ ≤ (boxes.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ (d + 2)) := by
        calc
          _ ≤ boxes.card • ENNReal.ofReal (δ ^ (d + 2)) :=
            Finset.sum_le_card_nsmul boxes
              (fun _ => ENNReal.ofReal (δ ^ (d + 2)))
              (ENNReal.ofReal (δ ^ (d + 2))) (by intro q hq; exact le_of_eq rfl)
          _ = (boxes.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ (d + 2)) := by simp
  have hsample := bernoulliProductSample_card_lt_minSize_measure_le_of_sum_eq p S
    (by simpa [p] using hS) minSize hmin
  have hfail :
      (∑ q ∈ boxes, μ {ω | boxBound q <
        (bernoulliProductSample ω ∩ tubeIndicesContainedInSet indices tube (box q)).card}) +
        μ {ω | (bernoulliProductSample ω).card < minSize} < 1 := by
    calc
      _ ≤ (boxes.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ (d + 2)) +
          ENNReal.ofReal (Real.exp (-S / 8)) := add_le_add hboxSum hsample
      _ < 1 := hbudget
  exact exists_bernoulliProductSample_with_convexBoxBounds_of_failure_mass p indices tube
    boxes box boxBound minSize (by simpa [μ] using hfail)

/-- A source-style cardinality bound `C / δ^d` pays for the logarithmic box failure rate
`δ^(d+2)` at total cost `C * δ^2`. The sample-size tail remains an explicit part of the
budget. This lemma performs only the numerical payment; it constructs no geometric box net. -/
theorem ennreal_polynomial_box_budget_lt_one_of_small_scale
    {β : Type*} [DecidableEq β] (boxes : Finset β)
    (C δ S : ℝ) (d : ℕ) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hcard : (boxes.card : ℝ≥0∞) ≤ ENNReal.ofReal (C / δ ^ d))
    (hbudget : ENNReal.ofReal (C * δ ^ 2) +
      ENNReal.ofReal (Real.exp (-S / 8)) < 1) :
    (boxes.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ (d + 2)) +
      ENNReal.ofReal (Real.exp (-S / 8)) < 1 := by
  have htail : (boxes.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ (d + 2)) ≤
      ENNReal.ofReal (C * δ ^ 2) := by
    calc
      _ ≤ ENNReal.ofReal (C / δ ^ d) * ENNReal.ofReal (δ ^ (d + 2)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ENNReal.ofReal (C * δ ^ 2) := by
        rw [← ENNReal.ofReal_mul (div_nonneg hC (pow_nonneg hδ.le d))]
        congr 1
        rw [pow_add]
        field_simp [ne_of_gt (pow_pos hδ d)]
  exact lt_of_le_of_lt (add_le_add htail le_rfl) hbudget

/-- An exact repeated-core class has multiplicity at most the convex-clustering constant.

This only handles indices whose core sets are equal. It does not imply pairwise essential
distinctness for different but nearby line segments. The positive finite carrier volume is exposed
as an input so the lemma also applies to settings beyond unit-segment tubes. -/
theorem card_eq_core_le_of_sampledConvexClustering
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} (indices J : Finset ι) (core : ι → Set E) (δ : ℝ)
    (A : ℝ≥0∞) (cert : SampledConvexClusteringCertificate indices core δ A)
    (hJ : J ⊆ indices) (C : Set E)
    (hcore : ∀ i ∈ J, core i = C) (hC : Convex ℝ C)
    (hvol_pos : 0 < volume (Metric.cthickening δ C))
    (hvol_top : volume (Metric.cthickening δ C) < ∞) :
    (J.card : ℝ≥0∞) ≤ A := by
  let K := Metric.cthickening δ C
  have hKconv : Convex ℝ K := hC.cthickening δ
  have hKsubset : ∀ i ∈ J, Metric.cthickening δ (core i) ⊆ K := by
    intro i hi
    rw [hcore i hi]
  have hsum := cert.convex_test_bound K hKconv J hJ hKsubset
  have hsumEq : (∑ i ∈ J, volume (Metric.cthickening δ (core i))) =
      (J.card : ℝ≥0∞) * volume K := by
    calc
      (∑ i ∈ J, volume (Metric.cthickening δ (core i))) =
          ∑ i ∈ J, volume K := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hcore i hi]
      _ = _ := by simp [K]
  have hmul : volume K * (J.card : ℝ≥0∞) ≤ volume K * A := by
    calc
      volume K * (J.card : ℝ≥0∞) = (J.card : ℝ≥0∞) * volume K := mul_comm _ _
      _ ≤ A * volume K := by simpa [K, hsumEq] using hsum
      _ = volume K * A := mul_comm _ _
  exact (ENNReal.mul_le_mul_iff_right hvol_pos.ne' hvol_top.ne).mp hmul

/-- Any tube-core family whose selected cores are within `4δ` of a line has its entire δ-carriers
in the truncated convex line test. The sampled convex-clustering certificate then bounds the sum
of carrier volumes by `50 R` times the reference unit-segment carrier volume. -/
theorem lineCap_carrierVolume_sum_le_of_sampledConvexClustering
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) {ι : Type*} (indices lineCap : Finset ι)
    (core : ι → Set E) (δ R : ℝ) (A : ℝ≥0∞)
    (hδ : 0 ≤ δ) (hR : 0 ≤ R) (cert : SampledConvexClusteringCertificate indices core δ A)
    (hcap : lineCap ⊆ indices)
    (hne : ∀ i ∈ lineCap, (core i).Nonempty)
    (hcompact : ∀ i ∈ lineCap, IsCompact (core i))
    (hball : ∀ i ∈ lineCap, Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (o d : E) (hd : ‖d‖ = 1)
    (hline : ∀ i ∈ lineCap, core i ⊆ Metric.cthickening (4 * δ)
      (Set.range (fun t : ℝ => o + t • d))) :
    (∑ i ∈ lineCap, volume (Metric.cthickening δ (core i))) ≤
      A * ENNReal.ofReal (50 * R) *
        volume (Metric.cthickening δ ((segment ℝ o (o + d)))) := by
  let K := Metric.closedBall (0 : E) R ∩ Metric.cthickening (5 * δ)
    (Set.range (fun t : ℝ => o + t • d))
  have hKconv : Convex ℝ K := by
    simpa [K] using convex_closedBall_inter_lineCthickening o d R (5 * δ)
  have hcapCarrier : ∀ i ∈ lineCap, Metric.cthickening δ (core i) ⊆ K := by
    intro i hi
    have hinc := cthickening_subset_truncatedBallLineTest_of_core_subset
      o d R δ (hcompact i hi) (hne i hi) hδ (hline i hi) (hball i hi)
    simpa [K] using hinc
  have hcert := cert.convex_test_bound K hKconv lineCap hcap hcapCarrier
  have hvol := volume_closedBall_inter_fiveCthickening_le_mul_unitSegment
    hdim d o hd hR hδ
  calc
    (∑ i ∈ lineCap, volume (Metric.cthickening δ (core i))) ≤ A * volume K := by
      simpa [K] using hcert
    _ ≤ A * (ENNReal.ofReal (50 * R) *
        volume (Metric.cthickening δ ((segment ℝ o (o + d))))) := by
      calc
        A * volume K = volume K * A := mul_comm _ _
        _ ≤ (ENNReal.ofReal (50 * R) *
            volume (Metric.cthickening δ ((segment ℝ o (o + d))))) * A :=
          mul_le_mul_left hvol A
        _ = A * (ENNReal.ofReal (50 * R) *
            volume (Metric.cthickening δ ((segment ℝ o (o + d))))) := by ac_rfl
    _ = A * ENNReal.ofReal (50 * R) *
        volume (Metric.cthickening δ ((segment ℝ o (o + d)))) := by ac_rfl

/-- Counting form of `lineCap_carrierVolume_sum_le_of_sampledConvexClustering` when the selected
tubes have the common unit-segment carrier volume. -/
theorem lineCap_card_mul_unitTubeVolume_le_of_sampledConvexClustering
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) {ι : Type*} (indices lineCap : Finset ι)
    (core : ι → Set E) (δ R : ℝ) (A : ℝ≥0∞)
    (hδ : 0 ≤ δ) (hR : 0 ≤ R) (cert : SampledConvexClusteringCertificate indices core δ A)
    (hcap : lineCap ⊆ indices)
    (hne : ∀ i ∈ lineCap, (core i).Nonempty)
    (hcompact : ∀ i ∈ lineCap, IsCompact (core i))
    (hball : ∀ i ∈ lineCap, Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (o d : E) (hd : ‖d‖ = 1)
    (hline : ∀ i ∈ lineCap, core i ⊆ Metric.cthickening (4 * δ)
      (Set.range (fun t : ℝ => o + t • d)))
    (hvolume : ∀ i ∈ lineCap,
      volume (Metric.cthickening δ (core i)) =
        volume (Metric.cthickening δ ((segment ℝ o (o + d))))) :
    ((lineCap.card : ℝ≥0∞) *
      volume (Metric.cthickening δ ((segment ℝ o (o + d))))) ≤
      (A * ENNReal.ofReal (50 * R)) *
        volume (Metric.cthickening δ ((segment ℝ o (o + d)))) := by
  have hsum := lineCap_carrierVolume_sum_le_of_sampledConvexClustering
    hdim indices lineCap core δ R A hδ hR cert hcap hne hcompact hball o d hd hline
  have hsumEq : (∑ i ∈ lineCap, volume (Metric.cthickening δ (core i))) =
      (lineCap.card : ℝ≥0∞) * volume (Metric.cthickening δ ((segment ℝ o (o + d)))) := by
    calc
      (∑ i ∈ lineCap, volume (Metric.cthickening δ (core i))) =
          ∑ i ∈ lineCap, volume (Metric.cthickening δ ((segment ℝ o (o + d)))) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hvolume i hi
      _ = _ := by simp
  rw [hsumEq] at hsum
  simpa [mul_assoc] using hsum


/-- Actual cardinal line-cap estimate, after cancelling the positive finite unit-tube volume.
The convex-clustering certificate remains an explicit input; this theorem does not prove the
sampling argument that supplies it. -/
theorem lineCap_card_le_of_sampledConvexClustering
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) {ι : Type*} (indices lineCap : Finset ι)
    (core : ι → Set E) (δ R : ℝ) (A : ℝ≥0∞)
    (hδ : 0 ≤ δ) (hδpos : 0 < δ) (hR : 0 ≤ R)
    (cert : SampledConvexClusteringCertificate indices core δ A)
    (hcap : lineCap ⊆ indices)
    (hne : ∀ i ∈ lineCap, (core i).Nonempty)
    (hcompact : ∀ i ∈ lineCap, IsCompact (core i))
    (hball : ∀ i ∈ lineCap, Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (o d : E) (hd : ‖d‖ = 1)
    (hline : ∀ i ∈ lineCap, core i ⊆ Metric.cthickening (4 * δ)
      (Set.range (fun t : ℝ => o + t • d)))
    (hvolume : ∀ i ∈ lineCap,
      volume (Metric.cthickening δ (core i)) =
        volume (Metric.cthickening δ (segment ℝ o (o + d)))) :
    (lineCap.card : ℝ≥0∞) ≤ A * ENNReal.ofReal (50 * R) := by
  have hscaled := lineCap_card_mul_unitTubeVolume_le_of_sampledConvexClustering
    hdim indices lineCap core δ R A hδ hR cert hcap hne hcompact hball o d hd hline hvolume
  let v := volume (Metric.cthickening δ (segment ℝ o (o + d)))
  have hbounds := volume_unitAxisSegment_cthickening_bounds hdim d hd hδ
  have hvpos : 0 < v := by
    dsimp [v]
    rw [volume_cthickening_segment_translate o d hδ]
    have hpos : 0 < ENNReal.ofReal δ ^ 2 * ENNReal.ofReal Real.pi := by
      positivity
    exact lt_of_lt_of_le hpos hbounds.1
  have hvfinite : v < ∞ := by
    dsimp [v]
    rw [volume_cthickening_segment_translate o d hδ]
    have hfinite : ENNReal.ofReal (1 + 2 * δ) *
        (ENNReal.ofReal δ ^ 2 * ENNReal.ofReal Real.pi) < ∞ := by
      apply ENNReal.mul_lt_top
      · exact ENNReal.ofReal_lt_top
      · apply ENNReal.mul_lt_top
        · exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
        · exact ENNReal.ofReal_lt_top
    exact lt_of_le_of_lt hbounds.2 hfinite
  have hmul : v * (lineCap.card : ℝ≥0∞) ≤
      v * (A * ENNReal.ofReal (50 * R)) := by
    calc
      v * (lineCap.card : ℝ≥0∞) =
          (lineCap.card : ℝ≥0∞) * v := mul_comm _ _
      _ ≤ (A * ENNReal.ofReal (50 * R)) * v := hscaled
      _ = v * (A * ENNReal.ofReal (50 * R)) := mul_comm _ _
  exact (ENNReal.mul_le_mul_iff_right hvpos.ne' hvfinite.ne).mp hmul

/-- Line-carrier count in the exact geometric form used by the Numina line-essential-distinctness
interface: the *whole* `δ`-carrier is assumed to lie in the `5δ` neighborhood of the affine line.
Unlike `lineCap_card_le_of_sampledConvexClustering`, this theorem does not require a separate
`4δ` core-neighborhood premise, compactness, or nonemptiness; those are unnecessary once carrier
containment in the truncated convex test is supplied directly. -/
theorem lineCarrierCap_card_le_of_sampledConvexClustering
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) {ι : Type*} (indices lineCap : Finset ι)
    (core : ι → Set E) (δ R : ℝ) (A : ℝ≥0∞)
    (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (cert : SampledConvexClusteringCertificate indices core δ A)
    (hcap : lineCap ⊆ indices)
    (hball : ∀ i ∈ lineCap,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (o d : E) (hd : ‖d‖ = 1)
    (hline : ∀ i ∈ lineCap,
      Metric.cthickening δ (core i) ⊆
        Metric.cthickening (5 * δ) (Set.range (fun t : ℝ => o + t • d)))
    (hvolume : ∀ i ∈ lineCap,
      volume (Metric.cthickening δ (core i)) =
        volume (Metric.cthickening δ (segment ℝ o (o + d))))
    (hvol_pos : 0 < volume (Metric.cthickening δ (segment ℝ o (o + d))))
    (hvol_top : volume (Metric.cthickening δ (segment ℝ o (o + d))) < ∞) :
    (lineCap.card : ℝ≥0∞) ≤ A * ENNReal.ofReal (50 * R) := by
  let K := Metric.closedBall (0 : E) R ∩ Metric.cthickening (5 * δ)
    (Set.range (fun t : ℝ => o + t • d))
  have hKconv : Convex ℝ K := by
    simpa [K] using convex_closedBall_inter_lineCthickening o d R (5 * δ)
  have hcarrier : ∀ i ∈ lineCap, Metric.cthickening δ (core i) ⊆ K := by
    intro i hi x hx
    exact ⟨hball i hi hx, hline i hi hx⟩
  have hcert := cert.convex_test_bound K hKconv lineCap hcap hcarrier
  have hKvol := volume_closedBall_inter_fiveCthickening_le_mul_unitSegment
    hdim d o hd hR hδ
  have hsumEq : (∑ i ∈ lineCap, volume (Metric.cthickening δ (core i))) =
      (lineCap.card : ℝ≥0∞) *
        volume (Metric.cthickening δ (segment ℝ o (o + d))) := by
    calc
      (∑ i ∈ lineCap, volume (Metric.cthickening δ (core i))) =
          ∑ i ∈ lineCap,
            volume (Metric.cthickening δ (segment ℝ o (o + d))) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hvolume i hi
      _ = _ := by simp
  have hscaled := calc
      (lineCap.card : ℝ≥0∞) *
          volume (Metric.cthickening δ (segment ℝ o (o + d)))
        = ∑ i ∈ lineCap, volume (Metric.cthickening δ (core i)) := hsumEq.symm
      _ ≤ A * volume K := by simpa [K] using hcert
      _ ≤ A * (ENNReal.ofReal (50 * R) *
          volume (Metric.cthickening δ (segment ℝ o (o + d)))) := by
        calc
          A * volume K = volume K * A := mul_comm _ _
          _ ≤ (ENNReal.ofReal (50 * R) *
              volume (Metric.cthickening δ (segment ℝ o (o + d)))) * A :=
            mul_le_mul_left hKvol A
          _ = A * (ENNReal.ofReal (50 * R) *
              volume (Metric.cthickening δ (segment ℝ o (o + d)))) := by ac_rfl
      _ = (A * ENNReal.ofReal (50 * R)) *
          volume (Metric.cthickening δ (segment ℝ o (o + d))) := by ac_rfl
  have hmul :
      volume (Metric.cthickening δ (segment ℝ o (o + d))) *
          (lineCap.card : ℝ≥0∞) ≤
        volume (Metric.cthickening δ (segment ℝ o (o + d))) *
          (A * ENNReal.ofReal (50 * R)) := by
    simpa [mul_comm] using hscaled
  exact (ENNReal.mul_le_mul_iff_right hvol_pos.ne' hvol_top.ne).mp hmul

/-- Natural-number line budget adapter. The explicit `hbudget` is the paid conversion from the
real/ENNReal convex-clustering constant and the geometric `50R` factor to the integer cap used by
finite ED-selection theorems; no rounding or asymptotic loss is hidden in this interface. -/
theorem lineCarrierCap_natBound_of_sampledConvexClustering
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) {ι : Type*} (indices lineCap : Finset ι)
    (core : ι → Set E) (δ R : ℝ) (A : ℝ≥0∞)
    (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (cert : SampledConvexClusteringCertificate indices core δ A)
    (hcap : lineCap ⊆ indices)
    (hball : ∀ i ∈ lineCap,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (o d : E) (hd : ‖d‖ = 1)
    (hline : ∀ i ∈ lineCap,
      Metric.cthickening δ (core i) ⊆
        Metric.cthickening (5 * δ) (Set.range (fun t : ℝ => o + t • d)))
    (hvolume : ∀ i ∈ lineCap,
      volume (Metric.cthickening δ (core i)) =
        volume (Metric.cthickening δ (segment ℝ o (o + d))))
    (hvol_pos : 0 < volume (Metric.cthickening δ (segment ℝ o (o + d))))
    (hvol_top : volume (Metric.cthickening δ (segment ℝ o (o + d))) < ∞)
    (C : ℕ) (hbudget : A * ENNReal.ofReal (50 * R) ≤ (C : ℝ≥0∞)) :
    lineCap.card ≤ C := by
  have hcount := lineCarrierCap_card_le_of_sampledConvexClustering
    hdim indices lineCap core δ R A hδ hR cert hcap hball o d hd hline hvolume
    hvol_pos hvol_top
  have hcount' : (lineCap.card : ℝ≥0∞) ≤ (C : ℝ≥0∞) := le_trans hcount hbudget
  exact_mod_cast hcount'

/-- Variable-radius carrier line-cap estimate. For line tests at radius `κδ`, the geometric
payment is `2Rκ²`, exposed explicitly instead of reusing the radius-five `50R` factor. -/
theorem lineCarrierCap_card_le_of_sampledConvexClustering_at_radius
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) {ι : Type*} (indices lineCap : Finset ι)
    (core : ι → Set E) (δ R κ : ℝ) (A : ℝ≥0∞)
    (hδ : 0 ≤ δ) (hR : 0 ≤ R) (hκ : 0 ≤ κ)
    (cert : SampledConvexClusteringCertificate indices core δ A)
    (hcap : lineCap ⊆ indices)
    (hball : ∀ i ∈ lineCap,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (o d : E) (hd : ‖d‖ = 1)
    (hline : ∀ i ∈ lineCap,
      Metric.cthickening δ (core i) ⊆
        Metric.cthickening (κ * δ) (Set.range (fun t : ℝ => o + t • d)))
    (hvolume : ∀ i ∈ lineCap,
      volume (Metric.cthickening δ (core i)) =
        volume (Metric.cthickening δ (segment ℝ o (o + d))))
    (hvol_pos : 0 < volume (Metric.cthickening δ (segment ℝ o (o + d))))
    (hvol_top : volume (Metric.cthickening δ (segment ℝ o (o + d))) < ∞) :
    (lineCap.card : ℝ≥0∞) ≤ A * ENNReal.ofReal (2 * R * κ ^ 2) := by
  let K := Metric.closedBall (0 : E) R ∩ Metric.cthickening (κ * δ)
    (Set.range (fun t : ℝ => o + t • d))
  have hKconv : Convex ℝ K := by
    simpa [K] using convex_closedBall_inter_lineCthickening o d R (κ * δ)
  have hcarrier : ∀ i ∈ lineCap, Metric.cthickening δ (core i) ⊆ K := by
    intro i hi x hx
    exact ⟨hball i hi hx, hline i hi hx⟩
  have hcert := cert.convex_test_bound K hKconv lineCap hcap hcarrier
  have hKvol := volume_closedBall_inter_scaledCthickening_le_mul_unitSegment
    hdim d o hd hR hδ hκ
  have hsumEq : (∑ i ∈ lineCap, volume (Metric.cthickening δ (core i))) =
      (lineCap.card : ℝ≥0∞) *
        volume (Metric.cthickening δ (segment ℝ o (o + d))) := by
    calc
      (∑ i ∈ lineCap, volume (Metric.cthickening δ (core i))) =
          ∑ i ∈ lineCap, volume (Metric.cthickening δ (segment ℝ o (o + d))) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hvolume i hi
      _ = _ := by simp
  have hscaled := calc
      (lineCap.card : ℝ≥0∞) *
          volume (Metric.cthickening δ (segment ℝ o (o + d)))
        = ∑ i ∈ lineCap, volume (Metric.cthickening δ (core i)) := hsumEq.symm
      _ ≤ A * volume K := by simpa [K] using hcert
      _ ≤ A * (ENNReal.ofReal (2 * R * κ ^ 2) *
          volume (Metric.cthickening δ (segment ℝ o (o + d)))) := by
        calc
          A * volume K = volume K * A := mul_comm _ _
          _ ≤ (ENNReal.ofReal (2 * R * κ ^ 2) *
              volume (Metric.cthickening δ (segment ℝ o (o + d)))) * A :=
            mul_le_mul_left hKvol A
          _ = A * (ENNReal.ofReal (2 * R * κ ^ 2) *
              volume (Metric.cthickening δ (segment ℝ o (o + d)))) := by ac_rfl
      _ = (A * ENNReal.ofReal (2 * R * κ ^ 2)) *
          volume (Metric.cthickening δ (segment ℝ o (o + d))) := by ac_rfl
  have hmul :
      volume (Metric.cthickening δ (segment ℝ o (o + d))) *
          (lineCap.card : ℝ≥0∞) ≤
        volume (Metric.cthickening δ (segment ℝ o (o + d))) *
          (A * ENNReal.ofReal (2 * R * κ ^ 2)) := by
    simpa [mul_comm] using hscaled
  exact (ENNReal.mul_le_mul_iff_right hvol_pos.ne' hvol_top.ne).mp hmul

/-- Uniform line-essential-distinctness budget for a whole finite family. For every affine line
with unit direction, the subfamily whose complete carriers lie in its `5δ` neighborhood has at
most `C` members. The caller supplies the sampled convex certificate, uniform ball containment,
common unit-segment carrier volume, and the explicit integer payment `A * 50R ≤ C`. -/
noncomputable def lineCarrierCapFilter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} (indices : Finset ι) (core : ι → Set E) (δ : ℝ)
    (o d : E) : Finset ι := by
  classical
  exact indices.filter (fun i => Metric.cthickening δ (core i) ⊆
    Metric.cthickening (5 * δ) (Set.range (fun t : ℝ => o + t • d)))

/-- The complete-carrier line filter at the caller-chosen radius `κδ`. -/
noncomputable def lineCarrierCapFilterAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} (indices : Finset ι) (core : ι → Set E) (δ κ : ℝ)
    (o d : E) : Finset ι := by
  classical
  exact indices.filter (fun i => Metric.cthickening δ (core i) ⊆
    Metric.cthickening (κ * δ) (Set.range (fun t : ℝ => o + t • d)))

theorem sampledConvexClustering_uniform_lineCarrierBudget
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) {ι : Type*} (indices : Finset ι)
    (core : ι → Set E) (δ R : ℝ) (A : ℝ≥0∞)
    (hδ : 0 ≤ δ) (hδpos : 0 < δ) (hR : 0 ≤ R)
    (cert : SampledConvexClusteringCertificate indices core δ A)
    (hball : ∀ i ∈ indices,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (hvolume : ∀ o d : E, ‖d‖ = 1 → ∀ i ∈ indices,
      volume (Metric.cthickening δ (core i)) =
        volume (Metric.cthickening δ (segment ℝ o (o + d))))
    (C : ℕ) (hbudget : A * ENNReal.ofReal (50 * R) ≤ (C : ℝ≥0∞)) :
    ∀ o d : E, ‖d‖ = 1 →
      (lineCarrierCapFilter indices core δ o d).card ≤ C := by
  classical
  intro o d hd
  let cap := lineCarrierCapFilter indices core δ o d
  have hcap : cap ⊆ indices := Finset.filter_subset _ _
  have hballCap : ∀ i ∈ cap,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R := by
    intro i hi
    exact hball i (Finset.mem_filter.mp hi).1
  have hline : ∀ i ∈ cap,
      Metric.cthickening δ (core i) ⊆
        Metric.cthickening (5 * δ) (Set.range (fun t : ℝ => o + t • d)) := by
    intro i hi
    simpa [cap, lineCarrierCapFilter] using (Finset.mem_filter.mp hi).2
  have hvolumeCap : ∀ i ∈ cap,
      volume (Metric.cthickening δ (core i)) =
        volume (Metric.cthickening δ (segment ℝ o (o + d))) := by
    intro i hi
    exact hvolume o d hd i (hcap hi)
  have hvbounds := volume_unitAxisSegment_cthickening_bounds hdim d hd hδ
  have hvpos : 0 < volume (Metric.cthickening δ (segment ℝ o (o + d))) := by
    rw [volume_cthickening_segment_translate o d hδ]
    have hpos : 0 < ENNReal.ofReal δ ^ 2 * ENNReal.ofReal Real.pi := by positivity
    exact lt_of_lt_of_le hpos hvbounds.1
  have hvupper : volume (Metric.cthickening δ (segment ℝ o (o + d))) < ∞ := by
    rw [volume_cthickening_segment_translate o d hδ]
    have hfinite : ENNReal.ofReal (1 + 2 * δ) *
        (ENNReal.ofReal δ ^ 2 * ENNReal.ofReal Real.pi) < ∞ := by
      apply ENNReal.mul_lt_top
      · exact ENNReal.ofReal_lt_top
      · apply ENNReal.mul_lt_top
        · exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
        · exact ENNReal.ofReal_lt_top
    exact lt_of_le_of_lt hvbounds.2 hfinite
  simpa [cap] using lineCarrierCap_natBound_of_sampledConvexClustering
    hdim indices cap core δ R A hδ hR cert hcap hballCap o d hd hline hvolumeCap
    hvpos hvupper C hbudget

/-- Uniform all-lines natural budget for a caller-chosen line-neighborhood radius `κδ`.
The extra geometric cost is exactly represented by the explicit `2Rκ²` payment. -/
theorem sampledConvexClustering_uniform_lineCarrierBudget_at_radius
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) {ι : Type*} (indices : Finset ι)
    (core : ι → Set E) (δ R κ : ℝ) (A : ℝ≥0∞)
    (hδ : 0 ≤ δ) (hδpos : 0 < δ) (hR : 0 ≤ R) (hκ : 0 ≤ κ)
    (cert : SampledConvexClusteringCertificate indices core δ A)
    (hball : ∀ i ∈ indices,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (hvolume : ∀ o d : E, ‖d‖ = 1 → ∀ i ∈ indices,
      volume (Metric.cthickening δ (core i)) =
        volume (Metric.cthickening δ (segment ℝ o (o + d))))
    (C : ℕ) (hbudget : A * ENNReal.ofReal (2 * R * κ ^ 2) ≤ (C : ℝ≥0∞)) :
    ∀ o d : E, ‖d‖ = 1 →
      (lineCarrierCapFilterAt indices core δ κ o d).card ≤ C := by
  classical
  intro o d hd
  let cap := lineCarrierCapFilterAt indices core δ κ o d
  have hcap : cap ⊆ indices := Finset.filter_subset _ _
  have hballCap : ∀ i ∈ cap,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R := by
    intro i hi
    exact hball i (hcap hi)
  have hline : ∀ i ∈ cap,
      Metric.cthickening δ (core i) ⊆
        Metric.cthickening (κ * δ) (Set.range (fun t : ℝ => o + t • d)) := by
    intro i hi
    simpa [cap, lineCarrierCapFilterAt] using (Finset.mem_filter.mp hi).2
  have hvolumeCap : ∀ i ∈ cap,
      volume (Metric.cthickening δ (core i)) =
        volume (Metric.cthickening δ (segment ℝ o (o + d))) := by
    intro i hi
    exact hvolume o d hd i (hcap hi)
  have hvbounds := volume_unitAxisSegment_cthickening_bounds hdim d hd hδ
  have hvpos : 0 < volume (Metric.cthickening δ (segment ℝ o (o + d))) := by
    rw [volume_cthickening_segment_translate o d hδ]
    have hpos : 0 < ENNReal.ofReal δ ^ 2 * ENNReal.ofReal Real.pi := by positivity
    exact lt_of_lt_of_le hpos hvbounds.1
  have hvupper : volume (Metric.cthickening δ (segment ℝ o (o + d))) < ∞ := by
    rw [volume_cthickening_segment_translate o d hδ]
    have hfinite : ENNReal.ofReal (1 + 2 * δ) *
        (ENNReal.ofReal δ ^ 2 * ENNReal.ofReal Real.pi) < ∞ := by
      apply ENNReal.mul_lt_top
      · exact ENNReal.ofReal_lt_top
      · apply ENNReal.mul_lt_top
        · exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
        · exact ENNReal.ofReal_lt_top
    exact lt_of_le_of_lt hvbounds.2 hfinite
  have hcount := lineCarrierCap_card_le_of_sampledConvexClustering_at_radius
    hdim indices cap core δ R κ A hδ hR hκ cert hcap hballCap o d hd hline
    hvolumeCap hvpos hvupper
  have hcount' : (cap.card : ℝ≥0∞) ≤ (C : ℝ≥0∞) := le_trans hcount hbudget
  exact_mod_cast hcount'

/-- Compose a supplied pair-conflict-to-line-containment theorem with the sampled convex
line-budget and the finite weighted/cardinality selector. The caller's geometric implication
is explicit input: this theorem does not assert that non-essential-distinct tubes satisfy it.
Once that implication is proved for a local tube model, the selected conflict-free subfamily
retains both the specified shade weight and cardinality with the same factor `C + 1`. -/
theorem exists_pairwise_conflictFree_retaining_weight_and_card_of_lineBudget
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) {ι : Type*} (indices : Finset ι)
    (core : ι → Set E) (δ R κ : ℝ) (A : ℝ≥0∞) (C : ℕ)
    (hδpos : 0 < δ) (hR : 0 ≤ R) (hκ : 0 ≤ κ)
    (cert : SampledConvexClusteringCertificate indices core δ A)
    (hball : ∀ i ∈ indices,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (origin direction : ι → E)
    (hdirection : ∀ i ∈ indices, ‖direction i‖ = 1)
    (hvolume : ∀ i ∈ indices, ∀ j ∈ indices,
      volume (Metric.cthickening δ (core j)) =
        volume (Metric.cthickening δ (segment ℝ (origin i) (origin i + direction i))))
    (hbudget : A * ENNReal.ofReal (2 * R * κ ^ 2) ≤ (C : ℝ≥0∞))
    (conflict : ι → ι → Prop)
    (hsymm : ∀ i j, conflict i j → conflict j i)
    (hirr : ∀ i, ¬ conflict i i)
    (hconflictLine : ∀ i ∈ indices, ∀ j ∈ indices, conflict j i →
      Metric.cthickening δ (core j) ⊆ Metric.cthickening (κ * δ)
        (Set.range (fun t : ℝ => origin i + t • direction i)))
    (weight : ι → ℝ≥0∞) :
    ∃ selected ⊆ indices,
      (selected : Set ι).Pairwise (fun i j => ¬ conflict i j) ∧
      ∑ j ∈ indices, weight j ≤ (C + 1 : ℕ) * ∑ j ∈ selected, weight j ∧
      indices.card ≤ (C + 1) * selected.card := by
  classical
  have hdegree : ∀ i ∈ indices, {j ∈ (indices : Set ι) | conflict j i}.ncard ≤ C := by
    intro i hi
    let cap := lineCarrierCapFilterAt indices core δ κ (origin i) (direction i)
    have hcap : cap ⊆ indices := Finset.filter_subset _ _
    have hballCap : ∀ j ∈ cap,
        Metric.cthickening δ (core j) ⊆ Metric.closedBall 0 R := by
      intro j hj
      exact hball j (hcap hj)
    have hcapLine : ∀ j ∈ cap,
        Metric.cthickening δ (core j) ⊆ Metric.cthickening (κ * δ)
          (Set.range (fun t : ℝ => origin i + t • direction i)) := by
      intro j hj
      simpa [cap, lineCarrierCapFilterAt] using (Finset.mem_filter.mp hj).2
    have hvolumeCap : ∀ j ∈ cap,
        volume (Metric.cthickening δ (core j)) =
          volume (Metric.cthickening δ
            (segment ℝ (origin i) (origin i + direction i))) := by
      intro j hj
      exact hvolume i hi j (hcap hj)
    have hunitBounds := volume_unitAxisSegment_cthickening_bounds
      hdim (direction i) (hdirection i hi) hδpos.le
    have hrefPos : 0 < volume (Metric.cthickening δ
        (segment ℝ (origin i) (origin i + direction i))) := by
      rw [volume_cthickening_segment_translate]
      · exact lt_of_lt_of_le (by positivity) hunitBounds.1
      · exact hδpos.le
    have hrefTop : volume (Metric.cthickening δ
        (segment ℝ (origin i) (origin i + direction i))) < ∞ := by
      rw [volume_cthickening_segment_translate]
      · have hfinite : ENNReal.ofReal (1 + 2 * δ) *
            (ENNReal.ofReal δ ^ 2 * ENNReal.ofReal Real.pi) < ∞ := by
          apply ENNReal.mul_lt_top
          · exact ENNReal.ofReal_lt_top
          · apply ENNReal.mul_lt_top
            · exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
            · exact ENNReal.ofReal_lt_top
        exact lt_of_le_of_lt hunitBounds.2 hfinite
      · exact hδpos.le
    have hcapCount := lineCarrierCap_card_le_of_sampledConvexClustering_at_radius
      hdim indices cap core δ R κ A hδpos.le hR hκ cert hcap hballCap
      (origin i) (direction i) (hdirection i hi) hcapLine hvolumeCap hrefPos hrefTop
    have hcapCount' : (cap.card : ℝ≥0∞) ≤ (C : ℝ≥0∞) := le_trans hcapCount hbudget
    have hcapCard : cap.card ≤ C := by exact_mod_cast hcapCount'
    have hconflictSub :
        {j ∈ (indices : Set ι) | conflict j i} ⊆ (cap : Set ι) := by
      intro j hj
      rcases Set.mem_setOf.mp hj with ⟨hjmem, hji⟩
      have hline := hconflictLine i hi j hjmem hji
      change j ∈ cap
      simp only [cap, lineCarrierCapFilterAt, Finset.mem_filter]
      exact ⟨hjmem, hline⟩
    have hcard := Set.ncard_le_ncard hconflictSub cap.finite_toSet
    rw [Set.ncard_coe_finset] at hcard
    exact hcard.trans hcapCard
  exact exists_pairwise_conflictFree_retaining_weight_and_card
    indices conflict hsymm hirr hdegree weight

/-- A carrier-essentially-distinct subfamily with every loss exposed.

The geometric input `hnonEDLine` says that every non-essentially-distinct pair has the second
whole carrier inside a caller-chosen `κδ` neighborhood of the first core line. Together with the
sampled convex-clustering certificate and its explicit `2Rκ²` payment, this gives conflict degree
at most `C`; the selector then costs exactly `C + 1` in shade mass, cardinality, and fullness.
The local profile input transfers with the same factor and the caller's monotone Katz–Tao
statistic does not increase under passage to a subfamily. Finally, `hpowerPayment` is the explicit
scale absorption needed to turn `C + 1` into `δ⁻ε`.

This theorem does not prove `hnonEDLine`, construct the sampled certificate, or establish the
Frostman/Katz–Tao hypotheses. In particular, those hypotheses must be verified for the actual
GWZ family before this interface can be applied. -/
theorem exists_pairwise_carrierED_subfamily_with_explicit_losses
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (core : ι → Set E)
    (δ R κ ε : ℝ) (A : ℝ≥0∞) (C : ℕ)
    (hδpos : 0 < δ) (hR : 0 ≤ R) (hκ : 0 ≤ κ) (_hε : 0 < ε)
    (cert : SampledConvexClusteringCertificate indices core δ A)
    (hball : ∀ i ∈ indices,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (origin direction : ι → E)
    (hdirection : ∀ i ∈ indices, ‖direction i‖ = 1)
    (hvolume : ∀ i ∈ indices, ∀ j ∈ indices,
      volume (Metric.cthickening δ (core j)) =
        volume (Metric.cthickening δ (segment ℝ (origin i) (origin i + direction i))))
    (hbudget : A * ENNReal.ofReal (2 * R * κ ^ 2) ≤ (C : ℝ≥0∞))
    (hnonEDLine : ∀ i ∈ indices, ∀ j ∈ indices,
      ¬ IsCarrierEssentiallyDistinct
          (Metric.cthickening δ (core j)) (Metric.cthickening δ (core i)) →
        Metric.cthickening δ (core j) ⊆
          Metric.cthickening (κ * δ)
            (Set.range (fun t : ℝ => origin i + t • direction i)))
    (shadeMass carrierMass : ι → ℝ≥0∞) (τ : ℝ≥0∞)
    (hfull : τ * (∑ j ∈ indices, carrierMass j) ≤ ∑ j ∈ indices, shadeMass j)
    {σ : Type*} (localTest : σ → Finset ι) (localScale : σ → ℝ≥0∞)
    (frostmanConstant : ℝ≥0∞)
    (hlocal : ∀ s,
      (∑ j ∈ indices.filter (· ∈ localTest s), shadeMass j) ≤
        frostmanConstant * (∑ j ∈ indices, shadeMass j) * localScale s)
    (katzTaoStatistic : Finset ι → ℝ≥0∞)
    (hkatzTaoMono : ∀ J K : Finset ι, J ⊆ K →
      katzTaoStatistic J ≤ katzTaoStatistic K)
    (hpowerPayment : ((C + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-ε))) :
    ∃ selected ⊆ indices,
      (selected : Set ι).Pairwise (fun i j =>
        IsCarrierEssentiallyDistinct
          (Metric.cthickening δ (core i)) (Metric.cthickening δ (core j))) ∧
      (∑ j ∈ indices, shadeMass j ≤
        (C + 1 : ℕ) * ∑ j ∈ selected, shadeMass j) ∧
      indices.card ≤ (C + 1) * selected.card ∧
      (τ * (∑ j ∈ selected, carrierMass j) ≤
        (C + 1 : ℕ) * ∑ j ∈ selected, shadeMass j) ∧
      (∀ s,
        (∑ j ∈ selected.filter (· ∈ localTest s), shadeMass j) ≤
          (C + 1 : ℕ) * frostmanConstant *
            (∑ j ∈ selected, shadeMass j) * localScale s) ∧
      katzTaoStatistic selected ≤ katzTaoStatistic indices ∧
      ((indices.card : ℝ≥0∞) ≤
        ENNReal.ofReal (δ ^ (-ε)) * (selected.card : ℝ≥0∞)) ∧
      (∑ j ∈ indices, shadeMass j ≤
        ENNReal.ofReal (δ ^ (-ε)) * ∑ j ∈ selected, shadeMass j) ∧
      (∀ s,
        (∑ j ∈ selected.filter (· ∈ localTest s), shadeMass j) ≤
          ENNReal.ofReal (δ ^ (-ε)) * frostmanConstant *
            (∑ j ∈ selected, shadeMass j) * localScale s) := by
  classical
  let carrier : ι → Set E := fun i => Metric.cthickening δ (core i)
  let conflict : ι → ι → Prop := fun i j =>
    i ∈ indices ∧ j ∈ indices ∧ i ≠ j ∧
      ¬ IsCarrierEssentiallyDistinct (carrier i) (carrier j)
  have hsymm : ∀ i j, conflict i j → conflict j i := by
    intro i j hij
    rcases hij with ⟨hi, hj, hijne, hnot⟩
    refine ⟨hj, hi, hijne.symm, ?_⟩
    intro hED
    apply hnot
    unfold IsCarrierEssentiallyDistinct at hED ⊢
    simpa [Set.inter_comm, max_comm] using hED
  have hirr : ∀ i, ¬ conflict i i := by
    intro i hi
    exact hi.2.2.1 rfl
  have hconflictLine : ∀ i ∈ indices, ∀ j ∈ indices, conflict j i →
      Metric.cthickening δ (core j) ⊆
        Metric.cthickening (κ * δ)
          (Set.range (fun t : ℝ => origin i + t • direction i)) := by
    intro i hi j hj hji
    exact hnonEDLine i hi j hj hji.2.2.2
  obtain ⟨selected, hsub, hpair, hmass, hcard⟩ :=
    exists_pairwise_conflictFree_retaining_weight_and_card_of_lineBudget
      hdim indices core δ R κ A C hδpos hR hκ cert hball origin direction
      hdirection hvolume hbudget conflict hsymm hirr hconflictLine shadeMass
  have hpairED : (selected : Set ι).Pairwise (fun i j =>
      IsCarrierEssentiallyDistinct (carrier i) (carrier j)) := by
    intro i hi j hj hij
    by_contra hnot
    have hconf : conflict i j := ⟨hsub hi, hsub hj, hij, hnot⟩
    exact hpair hi hj hij hconf
  have hfullSelected :=
    selectedFullness_mul_le_degreePlusOne_of_massRetention
      indices selected hsub C τ carrierMass shadeMass hfull hmass
  have hlocalSelected :=
    selectedLocalMass_le_of_massRetention
      indices selected hsub C shadeMass localTest localScale frostmanConstant hmass hlocal
  have hmassPaid : ∑ j ∈ indices, shadeMass j ≤
      ENNReal.ofReal (δ ^ (-ε)) * ∑ j ∈ selected, shadeMass j := by
    calc
      (∑ j ∈ indices, shadeMass j) ≤
          (C + 1 : ℕ) * ∑ j ∈ selected, shadeMass j := hmass
      _ ≤ ENNReal.ofReal (δ ^ (-ε)) * ∑ j ∈ selected, shadeMass j := by
        gcongr
  have hcardENN : (indices.card : ℝ≥0∞) ≤
      ((C + 1 : ℕ) : ℝ≥0∞) * (selected.card : ℝ≥0∞) := by
    exact_mod_cast hcard
  have hcardPaid : (indices.card : ℝ≥0∞) ≤
      ENNReal.ofReal (δ ^ (-ε)) * (selected.card : ℝ≥0∞) := by
    calc
      (indices.card : ℝ≥0∞) ≤
          ((C + 1 : ℕ) : ℝ≥0∞) * (selected.card : ℝ≥0∞) := hcardENN
      _ ≤ ENNReal.ofReal (δ ^ (-ε)) * (selected.card : ℝ≥0∞) := by
        gcongr
  have hlocalPaid : ∀ s,
      (∑ j ∈ selected.filter (· ∈ localTest s), shadeMass j) ≤
        ENNReal.ofReal (δ ^ (-ε)) * frostmanConstant *
          (∑ j ∈ selected, shadeMass j) * localScale s := by
    intro s
    calc
      (∑ j ∈ selected.filter (· ∈ localTest s), shadeMass j) ≤
          (C + 1 : ℕ) * frostmanConstant *
            (∑ j ∈ selected, shadeMass j) * localScale s := hlocalSelected s
      _ ≤ ENNReal.ofReal (δ ^ (-ε)) * frostmanConstant *
            (∑ j ∈ selected, shadeMass j) * localScale s := by
        gcongr
  have hKT := hkatzTaoMono selected indices hsub
  exact ⟨selected, hsub, hpairED, hmass, hcard, hfullSelected,
    hlocalSelected, hKT, hcardPaid, hmassPaid, hlocalPaid⟩

/-- The pairwise carrier-ED selector specialized to centered unit-segment carriers.

Compared with `exists_pairwise_carrierED_subfamily_with_explicit_losses`, this wrapper proves the
non-ED-to-line-containment input from the actual same-scale carrier geometry. It still requires the
sampled convex-clustering certificate, the common-volume test, the line-cap budget at radius
`27δ`, the original fullness and local-mass estimates, Katz--Tao monotonicity, and the explicit
`C+1 ≤ δ⁻ε` payment from the caller. -/
theorem exists_pairwise_centeredUnitCarrierED_subfamily_with_explicit_losses
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (core : ι → Set E) (origin direction : ι → E)
    (δ R ε : ℝ) (A : ℝ≥0∞) (C : ℕ)
    (hδpos : 0 < δ) (hR : 0 ≤ R) (_hε : 0 < ε)
    (cert : SampledConvexClusteringCertificate indices core δ A)
    (hball : ∀ i ∈ indices,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (hcentered : ∀ i ∈ indices,
      core i = centeredUnitSegment (origin i) (direction i))
    (hdirection : ∀ i ∈ indices, ‖direction i‖ = 1)
    (hvolume : ∀ i ∈ indices, ∀ j ∈ indices,
      volume (Metric.cthickening δ (core j)) =
        volume (Metric.cthickening δ
          (segment ℝ (origin i) (origin i + direction i))))
    (hbudget : A * ENNReal.ofReal (2 * R * (27 : ℝ) ^ 2) ≤ (C : ℝ≥0∞))
    (shadeMass carrierMass : ι → ℝ≥0∞) (τ : ℝ≥0∞)
    (hfull : τ * (∑ j ∈ indices, carrierMass j) ≤ ∑ j ∈ indices, shadeMass j)
    {σ : Type*} (localTest : σ → Finset ι) (localScale : σ → ℝ≥0∞)
    (frostmanConstant : ℝ≥0∞)
    (hlocal : ∀ s,
      (∑ j ∈ indices.filter (· ∈ localTest s), shadeMass j) ≤
        frostmanConstant * (∑ j ∈ indices, shadeMass j) * localScale s)
    (katzTaoStatistic : Finset ι → ℝ≥0∞)
    (hkatzTaoMono : ∀ J K : Finset ι, J ⊆ K →
      katzTaoStatistic J ≤ katzTaoStatistic K)
    (hpowerPayment : ((C + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-ε))) :
    ∃ selected ⊆ indices,
      (selected : Set ι).Pairwise (fun i j =>
        IsCarrierEssentiallyDistinct
          (Metric.cthickening δ (core i)) (Metric.cthickening δ (core j))) ∧
      (∑ j ∈ indices, shadeMass j ≤
        (C + 1 : ℕ) * ∑ j ∈ selected, shadeMass j) ∧
      indices.card ≤ (C + 1) * selected.card ∧
      (τ * (∑ j ∈ selected, carrierMass j) ≤
        (C + 1 : ℕ) * ∑ j ∈ selected, shadeMass j) ∧
      (∀ s,
        (∑ j ∈ selected.filter (· ∈ localTest s), shadeMass j) ≤
          (C + 1 : ℕ) * frostmanConstant *
            (∑ j ∈ selected, shadeMass j) * localScale s) ∧
      katzTaoStatistic selected ≤ katzTaoStatistic indices ∧
      ((indices.card : ℝ≥0∞) ≤
        ENNReal.ofReal (δ ^ (-ε)) * (selected.card : ℝ≥0∞)) ∧
      (∑ j ∈ indices, shadeMass j ≤
        ENNReal.ofReal (δ ^ (-ε)) * ∑ j ∈ selected, shadeMass j) ∧
      (∀ s,
        (∑ j ∈ selected.filter (· ∈ localTest s), shadeMass j) ≤
          ENNReal.ofReal (δ ^ (-ε)) * frostmanConstant *
            (∑ j ∈ selected, shadeMass j) * localScale s) := by
  have hnonEDLine : ∀ i ∈ indices, ∀ j ∈ indices,
      ¬ IsCarrierEssentiallyDistinct
          (Metric.cthickening δ (core j)) (Metric.cthickening δ (core i)) →
        Metric.cthickening δ (core j) ⊆
          Metric.cthickening (27 * δ)
            (Set.range (fun t : ℝ => origin i + t • direction i)) := by
    intro i hi j hj hnot
    have hnot' : ¬ IsCarrierEssentiallyDistinct
        (centeredUnitCarrier δ (origin i) (direction i))
        (centeredUnitCarrier δ (origin j) (direction j)) := by
      intro hED
      apply hnot
      unfold IsCarrierEssentiallyDistinct at hED ⊢
      simpa [Set.inter_comm, max_comm, centeredUnitCarrier,
        hcentered i hi, hcentered j hj] using hED
    have hgeom := centeredUnitCarrier_subset_lineCthickening_of_not_essentiallyDistinct
      hdim hδpos (origin i) (origin j) (direction i) (direction j)
      (hdirection i hi) (hdirection j hj) hnot'
    simpa [centeredUnitCarrier, hcentered i hi, hcentered j hj] using hgeom
  exact exists_pairwise_carrierED_subfamily_with_explicit_losses
    hdim indices core δ R 27 ε A C hδpos hR (by norm_num) _hε cert hball
    origin direction hdirection hvolume hbudget hnonEDLine shadeMass carrierMass τ hfull
    localTest localScale frostmanConstant hlocal katzTaoStatistic hkatzTaoMono hpowerPayment

/--
Compile the finite box-count conclusion of the weighted Bernoulli sampler into the convex-test
certificate consumed by the line-cap theorems.

The caller supplies (i) the manuscript's weighted convex-clustering input, (ii) a finite box family
with its logarithmic sampling budget and common tube-volume data, and (iii) a covering/volume
comparison saying every relevant convex test is dominated by one of those boxes. The proof then
produces one actual Bernoulli sample and a `SampledConvexClusteringCertificate` with constant
`A * C`. This theorem does not construct the box family or prove those geometric/source inputs.
-/
theorem WeightedConvexClusteringCertificate.exists_sample_with_sampledConvexClusteringCertificate_of_logarithmic_box_cover
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    {indices : Finset ι} {core : ι → Set E} {weights : ι → ℝ}
    {scale tubeVolume : ℝ}
    (δ : ℝ)
    (weightedCert : WeightedConvexClusteringCertificate indices
      (fun i => Metric.cthickening δ (core i)) weights scale)
    (hindices : indices = Finset.univ) (hscale : 0 < scale) (htube : 0 < tubeVolume)
    (ell L c : ℝ) (hell : 0 ≤ ell) (hδ : Real.exp (-ell) = δ)
    (d : ℕ) (hL : 2 ≤ L) (hc : 0 < c)
    (hLc : ((d + 2 : ℕ) : ℝ) ≤ L * c)
    (boxes : Finset β) (box : β → Set E) (boxVolume : β → ℝ)
    (hboxConvex : ∀ q ∈ boxes, Convex ℝ (box q))
    (hboxVolume : ∀ q ∈ boxes, (volume (box q)).toReal = boxVolume q)
    (hcommon : ∀ i ∈ indices,
      (volume (Metric.cthickening δ (core i))).toReal = tubeVolume)
    (hratio : ∀ q ∈ boxes, c ≤ boxVolume q / tubeVolume)
    (boxBound : β → ℕ)
    (hthreshold : ∀ q ∈ boxes,
      L * (1 + ell) * (boxVolume q / tubeVolume) ≤ ((boxBound q + 1 : ℕ) : ℝ))
    (S : ℝ)
    (hS : (∑ i ∈ Finset.univ,
      ((bernoulliInclusionProbabilitiesFromWeights weights scale hscale
        (fun i => ⟨weightedCert.weights_nonneg i,
          weightedCert.weight_le_scale i (by simpa [hindices])⟩) i : unitInterval) : ℝ)) = S)
    (minSize : ℕ) (hmin : (minSize : ℝ) ≤ S / 2)
    (hbudget : (boxes.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ (d + 2)) +
      ENNReal.ofReal (Real.exp (-S / 8)) < 1)
    (A C : ℝ≥0∞)
    (hboxCost : ∀ q ∈ boxes,
      (boxBound q : ℝ≥0∞) * ENNReal.ofReal tubeVolume ≤ A * volume (box q))
    (hboxCover : ∀ K : Set E, Convex ℝ K →
      (∃ i ∈ indices, Metric.cthickening δ (core i) ⊆ K) →
      ∃ q ∈ boxes,
        (∀ i ∈ indices, Metric.cthickening δ (core i) ⊆ K →
          Metric.cthickening δ (core i) ⊆ box q) ∧
          volume (box q) ≤ C * volume K) :
    ∃ ω, minSize ≤ (bernoulliProductSample ω).card ∧
      (∀ q ∈ boxes,
        (bernoulliProductSample ω ∩
          tubeIndicesContainedInSet indices (fun i => Metric.cthickening δ (core i))
            (box q)).card ≤ boxBound q) ∧
      SampledConvexClusteringCertificate (bernoulliProductSample ω) core δ (A * C) := by
  classical
  obtain ⟨ω, hsize, hcounts⟩ :=
    weightedCert.exists_sample_with_boxBounds_of_logarithmic_budget
      hindices hscale htube δ ell L c hell hδ d hL hc hLc boxes box boxVolume
      hboxConvex hboxVolume
      (fun q hq i hi => hcommon i (Finset.mem_filter.mp hi).1)
      hratio boxBound hthreshold S hS minSize hmin hbudget
  refine ⟨ω, hsize, hcounts, ?_⟩
  constructor
  intro K hK J hJ hcontained
  by_cases hJempty : J = ∅
  · simp [hJempty]
  · obtain ⟨i, hiJ⟩ := Finset.nonempty_iff_ne_empty.mpr hJempty
    have hiIndices : i ∈ indices := by simp [hindices]
    obtain ⟨q, hq, hqContain, hqVolume⟩ := hboxCover K hK
      ⟨i, hiIndices, hcontained i hiJ⟩
    have hJsubset : J ⊆ bernoulliProductSample ω ∩
        tubeIndicesContainedInSet indices (fun i => Metric.cthickening δ (core i))
          (box q) := by
      intro j hj
      refine Finset.mem_inter.mpr ⟨hJ hj, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨by simp [hindices], hqContain j (by simp [hindices]) (hcontained j hj)⟩
    have hcardNat := (Finset.card_le_card hJsubset).trans (hcounts q hq)
    have hcard : (J.card : ℝ≥0∞) ≤ (boxBound q : ℝ≥0∞) := by
      exact_mod_cast hcardNat
    have hvolumeSum : (∑ i ∈ J, volume (Metric.cthickening δ (core i))) =
        (J.card : ℝ≥0∞) * ENNReal.ofReal tubeVolume := by
      calc
        (∑ i ∈ J, volume (Metric.cthickening δ (core i))) =
            ∑ i ∈ J, ENNReal.ofReal tubeVolume := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjIndices : j ∈ indices := by simp [hindices]
          calc
            volume (Metric.cthickening δ (core j)) =
                ENNReal.ofReal ((volume (Metric.cthickening δ (core j))).toReal) := by
              exact (ENNReal.ofReal_toReal (weightedCert.tube_volume_ne_top j)).symm
            _ = ENNReal.ofReal tubeVolume := by rw [hcommon j hjIndices]
        _ = (J.card : ℝ≥0∞) * ENNReal.ofReal tubeVolume := by simp
    calc
      (∑ i ∈ J, volume (Metric.cthickening δ (core i))) =
          (J.card : ℝ≥0∞) * ENNReal.ofReal tubeVolume := hvolumeSum
      _ ≤ (boxBound q : ℝ≥0∞) * ENNReal.ofReal tubeVolume := by gcongr
      _ ≤ A * volume (box q) := hboxCost q hq
      _ ≤ A * (C * volume K) := by gcongr
      _ = (A * C) * volume K := by rw [mul_assoc]

/-- The natural logarithmic box threshold obtained by rounding the source bound down. -/
def logarithmicConvexBoxBound {β : Type*} (L ell tubeVolume : ℝ)
    (boxVolume : β → ℝ) (q : β) : ℕ :=
  ⌊L * (1 + ell) * (boxVolume q / tubeVolume)⌋₊

/-- Rounding the source logarithmic threshold down gives both the threshold inequality required
by the Chernoff selector and its matching volume cost. The only geometric data consumed here are
the actual finite volume of each box and its positive lower volume ratio; the caller no longer
has to provide an unrelated `hboxCost` estimate or choose an oversized integer threshold. -/
theorem logarithmicConvexBoxBound_threshold_and_cost
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {β : Type*} [DecidableEq β] (boxes : Finset β) (box : β → Set E)
    (boxVolume : β → ℝ) {tubeVolume ell L c : ℝ}
    (htube : 0 < tubeVolume) (hell : 0 ≤ ell) (hL : 2 ≤ L) (hc : 0 < c)
    (hboxVolume : ∀ q ∈ boxes, (volume (box q)).toReal = boxVolume q)
    (hboxTop : ∀ q ∈ boxes, volume (box q) < ∞)
    (hratio : ∀ q ∈ boxes, c ≤ boxVolume q / tubeVolume) :
    (∀ q ∈ boxes,
      L * (1 + ell) * (boxVolume q / tubeVolume) ≤
        ((logarithmicConvexBoxBound L ell tubeVolume boxVolume q + 1 : ℕ) : ℝ)) ∧
    (∀ q ∈ boxes,
      (logarithmicConvexBoxBound L ell tubeVolume boxVolume q : ℝ≥0∞) *
          ENNReal.ofReal tubeVolume ≤
        ENNReal.ofReal (L * (1 + ell)) * volume (box q)) := by
  constructor
  · intro q hq
    simpa [logarithmicConvexBoxBound, Nat.cast_add] using
      (Nat.lt_floor_add_one
        (L * (1 + ell) * (boxVolume q / tubeVolume))).le
  · intro q hq
    let x := L * (1 + ell) * (boxVolume q / tubeVolume)
    have hratioNonneg : 0 ≤ boxVolume q / tubeVolume :=
      (le_trans hc.le (hratio q hq))
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hfloor : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx
    have hreal : (Nat.floor x : ℝ) * tubeVolume ≤
        (L * (1 + ell)) * boxVolume q := by
      calc
        (Nat.floor x : ℝ) * tubeVolume ≤ x * tubeVolume :=
          mul_le_mul_of_nonneg_right hfloor htube.le
        _ = (L * (1 + ell)) * boxVolume q := by
          dsimp [x]
          field_simp [ne_of_gt htube]
    have hvolumeEq : volume (box q) = ENNReal.ofReal (boxVolume q) := by
      rw [← hboxVolume q hq]
      exact (ENNReal.ofReal_toReal (ne_of_lt (hboxTop q hq))).symm
    rw [logarithmicConvexBoxBound, hvolumeEq]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ L * (1 + ell))]
    exact ENNReal.ofReal_le_ofReal hreal

/-- Compile source-style logarithmic box bounds directly into a sampled convex-clustering
certificate, with the natural box threshold fixed to `floor(L (1+ell) |Q|/v)`. This removes
the separate caller-supplied `boxBound`, threshold inequality, and `hboxCost` fields from the
finite-box compiler. The actual weighted certificate, finite box family, total failure budget,
and convex-test covering statement remain explicit inputs. -/
theorem WeightedConvexClusteringCertificate.exists_sample_with_sampledConvexClusteringCertificate_of_floor_logarithmic_box_cover
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    {indices : Finset ι} {core : ι → Set E} {weights : ι → ℝ}
    {scale tubeVolume : ℝ}
    (δ : ℝ)
    (weightedCert : WeightedConvexClusteringCertificate indices
      (fun i => Metric.cthickening δ (core i)) weights scale)
    (hindices : indices = Finset.univ) (hscale : 0 < scale) (htube : 0 < tubeVolume)
    (ell L c : ℝ) (hell : 0 ≤ ell) (hδ : Real.exp (-ell) = δ)
    (d : ℕ) (hL : 2 ≤ L) (hc : 0 < c)
    (hLc : ((d + 2 : ℕ) : ℝ) ≤ L * c)
    (boxes : Finset β) (box : β → Set E) (boxVolume : β → ℝ)
    (hboxConvex : ∀ q ∈ boxes, Convex ℝ (box q))
    (hboxVolume : ∀ q ∈ boxes, (volume (box q)).toReal = boxVolume q)
    (hboxTop : ∀ q ∈ boxes, volume (box q) < ∞)
    (hcommon : ∀ i ∈ indices,
      (volume (Metric.cthickening δ (core i))).toReal = tubeVolume)
    (hratio : ∀ q ∈ boxes, c ≤ boxVolume q / tubeVolume)
    (S : ℝ)
    (hS : (∑ i ∈ Finset.univ,
      ((bernoulliInclusionProbabilitiesFromWeights weights scale hscale
        (fun i => ⟨weightedCert.weights_nonneg i,
          weightedCert.weight_le_scale i (by simpa [hindices])⟩) i : unitInterval) : ℝ)) = S)
    (minSize : ℕ) (hmin : (minSize : ℝ) ≤ S / 2)
    (hbudget : (boxes.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ (d + 2)) +
      ENNReal.ofReal (Real.exp (-S / 8)) < 1)
    (C : ℝ≥0∞)
    (hboxCover : ∀ K : Set E, Convex ℝ K →
      (∃ i ∈ indices, Metric.cthickening δ (core i) ⊆ K) →
      ∃ q ∈ boxes,
        (∀ i ∈ indices, Metric.cthickening δ (core i) ⊆ K →
          Metric.cthickening δ (core i) ⊆ box q) ∧
          volume (box q) ≤ C * volume K) :
    ∃ ω, minSize ≤ (bernoulliProductSample ω).card ∧
      (∀ q ∈ boxes,
        (bernoulliProductSample ω ∩
          tubeIndicesContainedInSet indices
            (fun i => Metric.cthickening δ (core i)) (box q)).card ≤
          logarithmicConvexBoxBound L ell tubeVolume boxVolume q) ∧
      SampledConvexClusteringCertificate (bernoulliProductSample ω) core δ
        (ENNReal.ofReal (L * (1 + ell)) * C) := by
  obtain ⟨hthreshold, hcost⟩ := logarithmicConvexBoxBound_threshold_and_cost
    boxes box boxVolume htube hell hL hc hboxVolume hboxTop hratio
  exact WeightedConvexClusteringCertificate.exists_sample_with_sampledConvexClusteringCertificate_of_logarithmic_box_cover
    δ weightedCert hindices hscale htube ell L c hell hδ d hL hc hLc boxes box boxVolume
    hboxConvex hboxVolume hcommon hratio
    (logarithmicConvexBoxBound L ell tubeVolume boxVolume) hthreshold
    S hS minSize hmin hbudget (ENNReal.ofReal (L * (1 + ell))) C hcost hboxCover

/-- End-to-end floor-log sampling interface for a uniform line-carrier count.

The floor-log box sampler supplies one sampled convex-clustering certificate.  The already
proved `50R` carrier transfer then bounds, in that same realization, every line cap formed by
sampled carriers.  The caller still supplies the weighted convex estimate, box cover and
probability budget, as well as the ball containment, common segment-carrier volumes and the
explicit integer payment; this theorem does not derive those inputs from GWZ data. -/
theorem WeightedConvexClusteringCertificate.exists_sample_with_uniform_lineCarrierBudget_of_floor_logarithmic_box_cover
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    {indices : Finset ι} {core : ι → Set E} {weights : ι → ℝ}
    {scale tubeVolume : ℝ}
    (hdim : Module.finrank ℝ E = 3)
    (δ : ℝ)
    (weightedCert : WeightedConvexClusteringCertificate indices
      (fun i => Metric.cthickening δ (core i)) weights scale)
    (hindices : indices = Finset.univ) (hscale : 0 < scale) (htube : 0 < tubeVolume)
    (ell L c : ℝ) (hell : 0 ≤ ell) (hδ : Real.exp (-ell) = δ)
    (d : ℕ) (hL : 2 ≤ L) (hc : 0 < c)
    (hLc : ((d + 2 : ℕ) : ℝ) ≤ L * c)
    (boxes : Finset β) (box : β → Set E) (boxVolume : β → ℝ)
    (hboxConvex : ∀ q ∈ boxes, Convex ℝ (box q))
    (hboxVolume : ∀ q ∈ boxes, (volume (box q)).toReal = boxVolume q)
    (hboxTop : ∀ q ∈ boxes, volume (box q) < ∞)
    (hcommon : ∀ i ∈ indices,
      (volume (Metric.cthickening δ (core i))).toReal = tubeVolume)
    (hratio : ∀ q ∈ boxes, c ≤ boxVolume q / tubeVolume)
    (S : ℝ)
    (hS : (∑ i ∈ Finset.univ,
      ((bernoulliInclusionProbabilitiesFromWeights weights scale hscale
        (fun i => ⟨weightedCert.weights_nonneg i,
          weightedCert.weight_le_scale i (by simpa [hindices])⟩) i : unitInterval) : ℝ)) = S)
    (minSize : ℕ) (hmin : (minSize : ℝ) ≤ S / 2)
    (hbudget : (boxes.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ (d + 2)) +
      ENNReal.ofReal (Real.exp (-S / 8)) < 1)
    (boxCost : ℝ≥0∞)
    (hboxCover : ∀ K : Set E, Convex ℝ K →
      (∃ i ∈ indices, Metric.cthickening δ (core i) ⊆ K) →
      ∃ q ∈ boxes,
        (∀ i ∈ indices, Metric.cthickening δ (core i) ⊆ K →
          Metric.cthickening δ (core i) ⊆ box q) ∧
          volume (box q) ≤ boxCost * volume K)
    (R : ℝ) (hR : 0 ≤ R)
    (hcarrierBall : ∀ i ∈ indices,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R)
    (hcarrierVolume : ∀ o v : E, ‖v‖ = 1 → ∀ i ∈ indices,
      volume (Metric.cthickening δ (core i)) =
        volume (Metric.cthickening δ (segment ℝ o (o + v))))
    (lineCapBound : ℕ)
    (hlineCapBudget :
      (ENNReal.ofReal (L * (1 + ell)) * boxCost) * ENNReal.ofReal (50 * R) ≤
        (lineCapBound : ℝ≥0∞)) :
    ∃ ω, minSize ≤ (bernoulliProductSample ω).card ∧
      ∀ o v : E, ‖v‖ = 1 →
        (lineCarrierCapFilter (bernoulliProductSample ω) core δ o v).card ≤ lineCapBound := by
  have hδpos : 0 < δ := by
    rw [← hδ]
    exact Real.exp_pos _
  have hδnonneg : 0 ≤ δ := hδpos.le
  obtain ⟨ω, hsampleSize, _, hsampleCert⟩ :=
    WeightedConvexClusteringCertificate.exists_sample_with_sampledConvexClusteringCertificate_of_floor_logarithmic_box_cover
      δ weightedCert hindices hscale htube ell L c hell hδ d hL hc hLc boxes box boxVolume
      hboxConvex hboxVolume hboxTop hcommon hratio S hS minSize hmin hbudget boxCost hboxCover
  refine ⟨ω, hsampleSize, ?_⟩
  have hsampleIndices : ∀ i ∈ bernoulliProductSample ω, i ∈ indices := by
    intro i hi
    rw [hindices]
    exact Finset.mem_univ i
  have hsampleBall : ∀ i ∈ bernoulliProductSample ω,
      Metric.cthickening δ (core i) ⊆ Metric.closedBall 0 R := by
    intro i hi
    exact hcarrierBall i (hsampleIndices i hi)
  have hsampleVolume : ∀ o v : E, ‖v‖ = 1 → ∀ i ∈ bernoulliProductSample ω,
      volume (Metric.cthickening δ (core i)) =
        volume (Metric.cthickening δ (segment ℝ o (o + v))) := by
    intro o v hv i hi
    exact hcarrierVolume o v hv i (hsampleIndices i hi)
  intro o v hv
  exact sampledConvexClustering_uniform_lineCarrierBudget hdim
    (bernoulliProductSample ω) core δ R
    (ENNReal.ofReal (L * (1 + ell)) * boxCost)
    hδnonneg hδpos hR hsampleCert hsampleBall hsampleVolume lineCapBound hlineCapBudget
    o v hv

end Kakeya4.Construction
