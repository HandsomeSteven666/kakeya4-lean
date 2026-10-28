import OAI.MeasureTheory.Falconer.BilinearDifferenceLargeImage

/-! The actual large-image consequence of OSS, with original outer mass.
All probabilistic and projection certificates are constructed internally. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

theorem uniform_bilinear_difference_large_image {s t σ : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hσ : 0 ≤ σ) (hσmax : σ < min (s+t) 1) :
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
    ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ δ₀ → ∀ C : ℝ, 1 ≤ C → C ≤ δ^(-ε) →
    ∀ μ : Fin 4 → Measure ℝ, ∀ [∀ i, IsProbabilityMeasure (μ i)],
      (∀ i, UnitSupported (μ i)) →
      (∀ (i : Fin 4) (z r : ℝ), 0 < r →
        μ i (ball z r) ≤ ENNReal.ofReal (C*r^(if i.val < 2 then s else t))) →
    ∀ η ρ : Measure (Space 2), ∀ [IsProbabilityMeasure η] [IsProbabilityMeasure ρ],
      FrostmanBallBound ρ (s+t) C → (∀ᵐ x ∂ρ, ∀ i : Fin 2, |x i| ≤ 1) →
      ∀ E : Set ℝ, ENNReal.ofReal (δ^ε) ≤ bilinearDifferenceLaw μ η ρ E →
        (Nat.ceil (δ^(-σ)) : ℕ∞) ≤ externalCoveringNumber ⟨δ,hδ.le⟩ E := by
  obtain ⟨e,δP,he,hδP,hδP1,hOSS⟩ := OSS_Frostman_projection hs hs1 ht ht1 hσ hσmax
  let ε := e/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεe : ε ≤ e := by dsimp [ε]; linarith
  obtain ⟨δH,hδH,hδH1,hsmall⟩ := exists_scale_rpow_le_half (by positivity : 0 < e/4)
  refine ⟨ε,min δP δH,hε,lt_min hδP hδH,(min_le_left _ _).trans hδP1,?_⟩
  intro δ hδ hδsmall C hC hCb μ _ hμ hb η ρ _ _ hρ hcube E hE
  have hδ1 : δ ≤ 1 := (hδsmall.trans (min_le_left _ _)).trans hδP1
  have hbudget : C ≤ δ^(-e) := hCb.trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hεe))
  obtain ⟨Bad,hBad,hbad,hgood⟩ := hOSS δ hδ (hδsmall.trans (min_le_left _ _)) C hC hbudget μ hμ hb ρ hρ hcube
  have hquarter : δ^ε ≤ (1/4:ℝ) := by
    have hh := hsmall δ hδ (hδsmall.trans (min_le_right _ _))
    have hh' := mul_le_mul hh hh (Real.rpow_nonneg hδ.le _) (by norm_num : (0:ℝ) ≤ 1/2)
    have heq : δ^(e/4)*δ^(e/4) = δ^ε := by rw [← Real.rpow_add hδ]; congr 1; dsimp [ε]; ring
    rw [heq] at hh'
    norm_num at hh'
    exact hh'
  have hsquare : (δ^ε)^2 = δ^e := by
    rw [pow_two,← Real.rpow_add hδ]
    congr 1; dsimp [ε]; ring
  have hstrict : 2*δ^e < δ^ε := by
    rw [← hsquare]
    have hx : 0 < δ^ε := Real.rpow_pos_of_pos hδ _
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hquarter)]
  apply bilinear_difference_large_image_of_OSS μ η ρ ⟨δ,hδ.le⟩
    (ENNReal.ofReal (δ^e)) (Nat.ceil (δ^(-σ))) Bad hBad
    (fun w hw G hG ↦ by
      change (Nat.ceil (δ^(-σ)) : ℕ∞) ≤ externalCoveringNumber ⟨δ,hδ.le⟩
        ((fun x ↦ (w 2-w 3)*x 0+(w 0-w 1)*x 1) '' G)
      exact hgood w hw G hG) E
  calc
    _ ≤ ENNReal.ofReal (δ^e)+ENNReal.ofReal (δ^e) := add_le_add hbad le_rfl
    _ = ENNReal.ofReal (2*δ^e) := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    _ < ENNReal.ofReal (δ^ε) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hstrict
    _ ≤ _ := hE

#print axioms uniform_bilinear_difference_large_image
end OAI.Falconer
