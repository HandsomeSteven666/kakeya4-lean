import OAI.MeasureTheory.Falconer.FourierProductSplit
import OAI.MeasureTheory.Falconer.FourierInductionParameters
import Kakeya4.Hard.MultiplicativeConvolution.TwoFactorConsumer

/-! The full original finite-scale Fourier statement, proved by actual factor merging. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal BigOperators

def FourierDecayAt {n : ℕ} (kernel : SmoothKernel) (s : Fin n → ℝ) : Prop :=
  ∃ r₀ ε τ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 < ε ∧ ε ≤ 1 ∧ 0 < τ ∧ τ ≤ 1 ∧
    ∀ (μ : Fin n → Measure ℝ), (∀ j, IsProbabilityMeasure (μ j)) →
      (∀ j, UnitSupported (μ j)) → ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (∀ j, smoothEnergy kernel.law (s j) r (μ j) ≤ ENNReal.ofReal (r^(-ε))) →
      ∀ ξ : ℝ, r⁻¹ ≤ |ξ| → |ξ| ≤ 2*r⁻¹ →
        ‖fourier (productLaw μ) ξ‖ ≤ |ξ|^(-τ)

theorem fourierDecayAt_all (kernel : SmoothKernel) : ∀ n : ℕ, 2 ≤ n →
    ∀ s : Fin n → ℝ, (∀ j, 0 < s j ∧ s j ≤ 1) → 1 < ∑ j, s j → FourierDecayAt kernel s := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn s hs hsum
    by_cases hn2 : n=2
    · subst n
      exact finiteScaleDecay_two kernel s hs hsum
    have hn3 : 3 ≤ n := by omega
    obtain ⟨m,rfl⟩ : ∃ m : ℕ, n=m+3 := ⟨n-3,by omega⟩
    let T : ℝ := ∑ j : Fin (m+1), s j.succ.succ
    have hT : 0 < T := Finset.sum_pos (fun j _ ↦ (hs j.succ.succ).1) Finset.univ_nonempty
    have hsum' : 1 < s 0+s 1+T := by
      have heq : (∑ j : Fin (m+3), s j) = s 0+s 1+T := by
        rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
        change s 0+(s 1+T)=s 0+s 1+T
        ring
      rwa [heq] at hsum
    obtain ⟨u,v,hu,hus,hv,hvt,huv1,huvT⟩ :=
      exists_interior_merge_exponents (hs 0).1 (hs 1).1 hT hsum'
    let w : Fin (m+2) → ℝ := Fin.cons (u+v) (fun j : Fin (m+1) ↦ s j.succ.succ)
    have hw : ∀ j, 0 < w j ∧ w j ≤ 1 := by
      intro j
      refine Fin.cases ?_ (fun j ↦ hs j.succ.succ) j
      change 0 < u+v ∧ u+v ≤ 1
      exact ⟨add_pos hu hv,huv1.le⟩
    have hwsum : 1 < ∑ j, w j := by
      rw [Fin.sum_univ_succ]
      change 1 < u+v+T
      exact huvT
    obtain ⟨rI,εI,τI,hrI,hrI1,hεI,hεI1,hτI,hτI1,hdecay⟩ :=
      ih (m+2) (by omega) (by omega) w hw hwsum
    obtain ⟨N,hN,hpacket⟩ := exists_uniform_normalized_flattening_packet kernel
      (lt_min hu hv) hεI
    obtain ⟨εF,δF,hεF,hδF,hδF1,hmerge⟩ := hpacket u v (min_le_left _ _) (min_le_right _ _) huv1
    let R : ℝ := 4*((2^N:ℕ):ℝ)
    have hpNat : 1 ≤ (2:ℕ)^N := by
      have hp : 0 < (2:ℕ)^N := by positivity
      omega
    have hpCast : (1:ℝ) ≤ ((2^N:ℕ):ℝ) := by exact_mod_cast hpNat
    have hR2 : 2 ≤ R := by
      calc
        (2:ℝ) ≤ 4*1 := by norm_num
        _ ≤ 4*((2^N:ℕ):ℝ) := mul_le_mul_of_nonneg_left hpCast (by norm_num)
    have hR1 : 1 ≤ R := by linarith
    have hR : 0 < R := by linarith
    obtain ⟨δL,hδL,hδL1,hlower⟩ := exists_uniform_lower_exponent_cap kernel hεF
    obtain ⟨δS,hδS,hδS1,hfine⟩ := exists_fixed_finer_input_energy_cap kernel hR2 hεI
    let δ₀ : ℝ := min δF (min δL (min δS rI))
    let ε : ℝ := min 1 (min (εF/2) (εI/2))
    let p : ℕ := 2^(N+2)
    have hp : 0 < p := by dsimp [p]; positivity
    have hpR : 0 < (p:ℝ) := Nat.cast_pos.mpr hp
    have hpR1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast (show 1≤p by omega)
    have hε : 0 < ε := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεF' : ε ≤ εF/2 := (min_le_right _ _).trans (min_le_left _ _)
    have hεI' : ε ≤ εI/2 := (min_le_right _ _).trans (min_le_right _ _)
    have hδ₀ : 0 < δ₀ := lt_min hδF (lt_min hδL (lt_min hδS hrI))
    have hδ₀1 : δ₀ ≤ 1 := (min_le_left _ _).trans hδF1
    have hτ : 0 < τI/(p:ℝ) := div_pos hτI hpR
    have hτ1 : τI/(p:ℝ) ≤ 1 := (div_le_one hpR).mpr (hτI1.trans hpR1)
    refine ⟨δ₀,ε,τI/(p:ℝ),hδ₀,hδ₀1,hε,hε1,hτ,hτ1,?_⟩
    intro μ hprob hunit δ hδ hδsmall hcap ξ hξlo hξhi
    let (j : Fin (m+3)) : IsProbabilityMeasure (μ j) := hprob j
    have hδ1 : δ ≤ 1 := hδsmall.trans hδ₀1
    have hδF' : δ ≤ δF := hδsmall.trans (min_le_left _ _)
    have hδL' : δ ≤ δL := (hδsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
    have hδS' : δ ≤ δS := ((hδsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
    have hδI' : δ ≤ rI := ((hδsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
    have hinput (j : Fin (m+3)) (q : ℝ) (hq : ε ≤ q) :
        smoothEnergy kernel.law (s j) δ (μ j) ≤ ENNReal.ofReal (δ^(-q)) := by
      exact (hcap j).trans (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : -q≤-ε)))
    have hμu := hlower δ hδ hδL' (μ 0) (hunit 0) u (s 0) hu hus (hs 0).2
      (hinput 0 (εF/2) hεF')
    have hμv := hlower δ hδ hδL' (μ 1) (hunit 1) v (s 1) hv hvt (hs 1).2
      (hinput 1 (εF/2) hεF')
    let ρ := additiveLawPower (differenceLaw (μ 0) ∗ₘ differenceLaw (μ 1)) (2^N)
    have : IsProbabilityMeasure (differenceLaw (μ 0)) := by unfold differenceLaw; infer_instance
    have : IsProbabilityMeasure (differenceLaw (μ 1)) := by unfold differenceLaw; infer_instance
    have : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
    have hmerged := hmerge δ hδ hδF' (μ 0) (μ 1) (hunit 0) (hunit 1) hμu hμv
    change UnitSupported (ρ.map (fun x : ℝ ↦ x/R)) ∧
      smoothEnergy kernel.law (u+v) (δ/R) (ρ.map (fun x : ℝ ↦ x/R)) ≤
        ENNReal.ofReal ((δ/R)^(-εI)) at hmerged
    let M : Fin (m+2) → Measure ℝ := Fin.cons (ρ.map (fun x : ℝ ↦ x/R))
      (fun j : Fin (m+1) ↦ μ j.succ.succ)
    have hprobM : ∀ j, IsProbabilityMeasure (M j) := by
      intro j
      refine Fin.cases ?_ (fun j ↦ hprob j.succ.succ) j
      dsimp [M]
      rw [Fin.cons_zero]
      infer_instance
    have hunitM : ∀ j, UnitSupported (M j) := by
      intro j
      exact Fin.cases hmerged.1 (fun j ↦ hunit j.succ.succ) j
    have hcapM : ∀ j, smoothEnergy kernel.law (w j) (δ/R) (M j) ≤
        ENNReal.ofReal ((δ/R)^(-εI)) := by
      intro j
      refine Fin.cases hmerged.2 ?_ j
      intro j
      exact hfine δ hδ hδS' (μ j.succ.succ) (s j.succ.succ)
        (hinput j.succ.succ (εI/2) hεI')
    have hband := normalized_frequency_band hδ hR hξlo hξhi
    have hIH := hdecay M hprobM hunitM (δ/R) (div_pos hδ hR)
      ((div_le_self hδ.le hR1).trans hδI') hcapM (R*ξ) hband.1 hband.2
    let (j : Fin (m+2)) : IsProbabilityMeasure (M j) := hprobM j
    rw [productLaw_finSucc] at hIH
    change ‖fourier ((ρ.map (fun x : ℝ ↦ x/R)) ∗ₘ
      productLaw (fun j : Fin (m+1) ↦ μ j.succ.succ)) (R*ξ)‖ ≤ |R*ξ|^(-τI) at hIH
    have htrans := norm_fourier_three_product_le_normalized_flattened_power
      (μ 0) (μ 1) (productLaw (fun j : Fin (m+1) ↦ μ j.succ.succ)) ξ N
    have hb : ‖fourier (productLaw μ) ξ‖^p ≤ |R*ξ|^(-τI) := by
      rw [productLaw_first_two]
      exact htrans.trans hIH
    have hξ : 0 < |ξ| := (inv_pos.mpr hδ).trans_le hξlo
    simpa only [neg_div] using fourier_power_root_after_normalization hp hR1 hξ hτI.le hb

theorem finiteScaleDecay_all (kernel : SmoothKernel) : FiniteScaleDecay kernel :=
  fourierDecayAt_all kernel

theorem manuscriptDecay_proof : ManuscriptDecay := finiteScaleDecay_all fixedKernel

#print axioms FourierDecayAt
#print axioms fourierDecayAt_all
#print axioms finiteScaleDecay_all
#print axioms manuscriptDecay_proof
end OAI.Falconer
