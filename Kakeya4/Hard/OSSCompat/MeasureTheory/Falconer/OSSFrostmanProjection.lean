






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.DyadicProjectionScaleTransfer

/-! Original OSS Frostman projection endpoint at every sufficiently small scale.
No dyadic-resolution hypothesis remains in this statement. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

theorem OSS_Frostman_projection {s t σ : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hσ : 0 ≤ σ) (hσmax : σ < min (s+t) 1) :
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
    ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ δ₀ → ∀ C : ℝ, 1 ≤ C → C ≤ δ^(-ε) →
    ∀ μ : Fin 4 → Measure ℝ, ∀ [∀ i, IsProbabilityMeasure (μ i)],
      (∀ i, UnitSupported (μ i)) →
      (∀ (i : Fin 4) (z r : ℝ), 0 < r →
        μ i (ball z r) ≤ ENNReal.ofReal (C*r^(if i.val < 2 then s else t))) →
    ∀ ρ : Measure (Space 2), ∀ [IsProbabilityMeasure ρ], FrostmanBallBound ρ (s+t) C →
      (∀ᵐ x ∂ρ, ∀ i : Fin 2, |x i| ≤ 1) →
      ∃ Bad : Set (Fin 4 → ℝ), MeasurableSet Bad ∧
        Measure.pi μ Bad ≤ ENNReal.ofReal (δ^ε) ∧
        ∀ w ∉ Bad, ∀ G : Set (Space 2), ENNReal.ofReal (δ^ε) ≤ ρ G →
          (Nat.ceil (δ^(-σ)) : ℕ∞) ≤ externalCoveringNumber ⟨δ,hδ.le⟩
            ((fun x ↦ (w 2-w 3)*x 0+(w 0-w 1)*x 1) '' G) := by
  classical
  let σ' := (σ+min (s+t) 1)/2
  have hσσ' : σ < σ' := by dsimp [σ']; linarith
  have hσ'max : σ' < min (s+t) 1 := by dsimp [σ']; linarith
  obtain ⟨ep,hep,Np,hNp⟩ := dyadic_OSS_Frostman_projection hs hs1 ht ht1
    (hσ.trans hσσ'.le) hσ'max
  let ε := ep/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨Nc,hNc⟩ := Regularization.fixed_constant_absorbed (sub_pos.mpr hσσ') ((2:ℝ)^σ)
  let M := max Np (max Nc 1)
  let δ₀ := ((2:ℝ)^M)⁻¹
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδ₀1 : δ₀ ≤ 1 := by
    dsimp [δ₀]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  refine ⟨ε,δ₀,hε,hδ₀,hδ₀1,?_⟩
  intro δ hδ hδsmall C hC hCb μ _ hμ hb ρ _ hρ hcube
  obtain ⟨N,hNM,hδD,hDδ⟩ := exists_coarser_dyadic_above_depth M hδ hδsmall
  have hN1 : 1 ≤ N := (le_max_right Nc 1).trans ((le_max_right Np (max Nc 1)).trans hNM)
  have hR2 : (2:ℝ) ≤ (2:ℝ)^N := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hN1
  obtain ⟨hmass,hcoef⟩ := coarser_dyadic_threshold_budget hR2 hδ hDδ hep.le
  have hbudget : C ≤ ((2:ℝ)^N)^ep := hCb.trans hcoef
  obtain ⟨Bad,hBad,hbad,hgood⟩ := hNp N ((le_max_left Np (max Nc 1)).trans hNM)
    C hC hbudget μ hμ hb ρ hρ hcube
  refine ⟨Bad,hBad,hbad.trans (ENNReal.ofReal_le_ofReal hmass),?_⟩
  intro w hw G hG
  have hproj := hgood w hw G ((ENNReal.ofReal_le_ofReal hmass).trans hG)
  have hexp : δ^(-σ) ≤ ((2:ℝ)^N)^σ' := coarser_dyadic_cover_exponent
    (by positivity) hδ hDδ hσ (hNc N ((le_max_left Nc 1).trans ((le_max_right Np (max Nc 1)).trans hNM)))
  have hn : Nat.ceil (δ^(-σ)) ≤ Nat.ceil (((2:ℝ)^N)^σ') := Nat.ceil_mono hexp
  apply (show (Nat.ceil (δ^(-σ)) : ℕ∞) ≤ Nat.ceil (((2:ℝ)^N)^σ') by exact_mod_cast hn).trans
  exact hproj.trans (externalCoveringNumber_anti (show (⟨δ,hδ.le⟩ : ℝ≥0) ≤ ⟨((2:ℝ)^N)⁻¹,by positivity⟩ from hδD))

#print axioms OSS_Frostman_projection
end OAI.Falconer
