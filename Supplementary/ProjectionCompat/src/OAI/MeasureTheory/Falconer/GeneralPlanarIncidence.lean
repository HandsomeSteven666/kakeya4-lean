import OAI.MeasureTheory.Falconer.Incidence.OriginalBlockIncidence
import OAI.MeasureTheory.Falconer.Estimates.OriginalWeakCosts
import OAI.MeasureTheory.Falconer.Incidence.IncidenceScaleChoice

/-!
Adapted from OpenAI math, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/MeasureTheory/Falconer/Campaign123PlanarFurstenbergProof.lean:13-51.
Apache-2.0; see COPYING and PROVENANCE.json in the compatibility-probe root.

Only the finite planar proof is retained. The parameter choice additionally pays
1-b, allowing the general range 0<b<min(f,1), f<=2. Constants are chosen before
all scales and all configurations. This is a probe until fixed-environment
compilation and its complete axiom closure have passed.
-/

noncomputable section
namespace OAI.Falconer

/-- General finite planar incidence gain, with all numerical budgets discharged internally. -/
theorem general_planar_furstenberg {b f : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hbf : b < f) (hf2 : f ≤ 2) :
    ∃ ε δ₀ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ P : Finset (Space 2), P.Nonempty → InBoundedLineChart P →
        FiniteSeparatedAt δ P → NormalizedFiniteBallBound δ f (δ^(-ε)) P →
      ∀ V : Space 2 → Finset (Space 2),
        (∀ x ∈ P, (V x).Nonempty ∧ InBoundedLineChart (V x) ∧
          FiniteSeparatedAt δ (V x) ∧ NormalizedFiniteBallBound δ b (δ^(-ε)) (V x) ∧
          ∀ l ∈ V x, TubeIncident δ x l) →
        δ^(-2*b-ε) ≤ ((P.biUnion V).card : ℝ) := by
  let κ := min b (min (1-b) (min (f-b) (1/100:ℝ)))/16
  have hκ : 0 < κ := div_pos
    (lt_min hb (lt_min (sub_pos.mpr hb1) (lt_min (sub_pos.mpr hbf) (by norm_num)))) (by norm_num)
  have hκb : κ ≤ b/16 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hκmargin : κ ≤ (1-b)/16 := div_le_div_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  have hκg : κ ≤ (f-b)/16 := div_le_div_of_nonneg_right
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) (by norm_num)
  have hκone : κ ≤ (1/100:ℝ)/16 := div_le_div_of_nonneg_right
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) (by norm_num)
  obtain ⟨B,hB,_,lam,ζ,hlam,hζ,M,_,hblock⟩ := original_block_incidence hκ
    (by linarith : κ ≤ 1/100) (by linarith : κ ≤ b) (by linarith : b ≤ 1-8*κ)
    (by linarith : b+8*κ ≤ f) hf2
  have hC : 0 ≤ originalIncidenceCost B := by unfold originalIncidenceCost; positivity
  obtain ⟨ε,hε,hε1,_,_,N0,_,habsorb⟩ := exists_incidence_absorption_parameters hlam hζ
    (originalIncidenceCost B) hC
  let δ0 := min 1 (1/(4*(2:ℝ)^(B*(M+N0+1))))
  have hδ0 : 0 < δ0 := lt_min (by norm_num) (by positivity)
  refine ⟨ε,δ0,hε,(by linarith : ε ≤ 1),hδ0,min_le_left _ _,?_⟩
  intro δ hδ hδsmall P hP hPchart hPsep hPball V hV
  have hδ1 : δ ≤ 1 := hδsmall.trans (min_le_left _ _)
  have hsmall : δ ≤ 1/(4*(2:ℝ)^(B*(M+N0+1))) := hδsmall.trans (min_le_right _ _)
  obtain ⟨m,hm,hscale,hscale'⟩ := incidence_block_scale_choice hB hδ hsmall
  have hmM : M ≤ m := by omega
  have hNm : m ≤ m*B := Nat.le_mul_of_pos_right m hB
  have hNN : N0 ≤ m*B := by omega
  obtain ⟨hpoly,hfinal⟩ := habsorb (m*B) hNN
  have hcost := original_weak_costs hδ hδ1 hε.le hε1 hlam.le hb.le hb1.le
    (by linarith : 0 ≤ f) hf2 hscale' hpoly hfinal
  have hK : 1 ≤ δ^(-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hcard := hblock m hmM δ (δ^(-ε)) hδ hδ1 hK hscale hcost.1
    P hP hPchart hPsep hPball V hV
  have hcoeff : 0 < 162*δ^(-ε)*δ^b*(16*(1/(2:ℝ)^(m*B))/δ+1)^2 := by positivity
  exact (mul_le_mul_iff_right₀ hcoeff).mp (hcost.2.trans hcard)

end OAI.Falconer
