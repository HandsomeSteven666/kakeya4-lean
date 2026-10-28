import OAI.MeasureTheory.Falconer.Angular.AngularGainFinite
import OAI.MeasureTheory.Falconer.GeneralPlanarIncidence

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
