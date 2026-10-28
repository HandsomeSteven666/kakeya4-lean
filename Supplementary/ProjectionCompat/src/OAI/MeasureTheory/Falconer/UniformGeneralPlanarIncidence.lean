import OAI.MeasureTheory.Falconer.UniformOriginalBlockIncidence
import OAI.MeasureTheory.Falconer.Estimates.OriginalWeakCosts
import OAI.MeasureTheory.Falconer.Incidence.IncidenceScaleChoice

/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/MeasureTheory/Falconer/Campaign123PlanarFurstenbergProof.lean:13-51.
The numeric absorption proof is retained, with constants chosen before all b,f
in the fixed kappa parameter band. See the probe root COPYING and PROVENANCE.json.
Pending fixed-environment compilation and complete axiom-closure validation.
-/

namespace OAI.Falconer

/-- One finite incidence gain and scale threshold work throughout the fixed kappa parameter band. -/
theorem general_planar_furstenberg_uniform {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε δ₀ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {b f : ℝ}, κ ≤ b → b ≤ 1-8*κ → b+8*κ ≤ f → f ≤ 2 →
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ P : Finset (Space 2), P.Nonempty → InBoundedLineChart P →
        FiniteSeparatedAt δ P → NormalizedFiniteBallBound δ f (δ^(-ε)) P →
      ∀ V : Space 2 → Finset (Space 2),
        (∀ x ∈ P, (V x).Nonempty ∧ InBoundedLineChart (V x) ∧
          FiniteSeparatedAt δ (V x) ∧ NormalizedFiniteBallBound δ b (δ^(-ε)) (V x) ∧
          ∀ l ∈ V x, TubeIncident δ x l) →
        δ^(-2*b-ε) ≤ ((P.biUnion V).card : ℝ) := by
  obtain ⟨B,hB,_,lam,ζ,hlam,hζ,M,_,hblock⟩ := original_block_incidence_all_parameters hκ hκ1
  have hC : 0 ≤ originalIncidenceCost B := by unfold originalIncidenceCost; positivity
  obtain ⟨ε,hε,hε1,_,_,N0,_,habsorb⟩ := exists_incidence_absorption_parameters hlam hζ
    (originalIncidenceCost B) hC
  let δ0 := min 1 (1/(4*(2:ℝ)^(B*(M+N0+1))))
  have hδ0 : 0 < δ0 := lt_min (by norm_num) (by positivity)
  refine ⟨ε,δ0,hε,(by linarith : ε ≤ 1),hδ0,min_le_left _ _,?_⟩
  intro b f hbκ hbmargin hbf hf2 δ hδ hδsmall P hP hPchart hPsep hPball V hV
  have hb : 0 < b := hκ.trans_le hbκ
  have hb1 : b ≤ 1 := by linarith
  have hblock := hblock hbκ hbmargin hbf hf2
  have hδ1 : δ ≤ 1 := hδsmall.trans (min_le_left _ _)
  have hsmall : δ ≤ 1/(4*(2:ℝ)^(B*(M+N0+1))) := hδsmall.trans (min_le_right _ _)
  obtain ⟨m,hm,hscale,hscale'⟩ := incidence_block_scale_choice hB hδ hsmall
  have hmM : M ≤ m := by omega
  have hNm : m ≤ m*B := Nat.le_mul_of_pos_right m hB
  have hNN : N0 ≤ m*B := by omega
  obtain ⟨hpoly,hfinal⟩ := habsorb (m*B) hNN
  have hcost := original_weak_costs hδ hδ1 hε.le hε1 hlam.le hb.le hb1
    (by linarith : 0 ≤ f) hf2 hscale' hpoly hfinal
  have hK : 1 ≤ δ^(-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hcard := hblock m hmM δ (δ^(-ε)) hδ hδ1 hK hscale hcost.1
    P hP hPchart hPsep hPball V hV
  have hcoeff : 0 < 162*δ^(-ε)*δ^b*(16*(1/(2:ℝ)^(m*B))/δ+1)^2 := by positivity
  exact (mul_le_mul_iff_right₀ hcoeff).mp (hcost.2.trans hcard)

end OAI.Falconer
