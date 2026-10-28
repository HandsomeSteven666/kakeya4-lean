import OAI.MeasureTheory.Falconer.Estimates.PlanarGain
import OAI.MeasureTheory.Falconer.GeneralPlanarMeasureIncidence

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
