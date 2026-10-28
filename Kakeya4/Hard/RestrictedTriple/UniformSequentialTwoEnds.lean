import Kakeya4.Hard.RestrictedTriple.SequentialPowerBudget

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Classical

namespace Kakeya4.Hard.RestrictedTriple

/-- Uniform payment for the actual normalized c=p^(44 eta), K=p^(-44 eta) input.
One threshold precedes p, every zeta in[0,1], and the actual finite graph.
All final statistics use the common explicit exponent133 eta+2 zeta. -/
theorem exists_uniform_sequential_two_ends {η : ℝ} (hη : 0 < η) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ < 1 ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 → ∀ Q : Finset Triple, Q.Nonempty →
        standardTripleGeometry Q → tripleSeparated p Q →
        coordinateDensity (p^(44*η)) (activeTripleClasses Q) (Q.image tripleVertexMap) →
        (∀ j, finiteFrostman p (p^(-44*η)) (activeTripleClasses Q j)) →
        ∃ w₁ w₂ : ℝ, (p/2 ≤ w₁ ∧ w₁ ≤ 1) ∧ (p/2 ≤ w₂ ∧ w₂ ≤ 1) ∧
          ∃ L₁ L₂ : AffineLine, ∃ T : Finset Triple,
            T ⊆ Q ∧ T.Nonempty ∧ standardTripleGeometry T ∧ tripleSeparated p T ∧
            (∀ x ∈ activeTripleClasses T 1, x ∈ lineNeighborhood w₁ L₁) ∧
            (∀ x ∈ activeTripleClasses T 2, x ∈ lineNeighborhood w₂ L₂) ∧
            p^(133*η+2*ζ)*(Q.card : ℝ) ≤ (T.card : ℝ) ∧
            coordinateDensity (p^(133*η+2*ζ)) (activeTripleClasses T) (T.image tripleVertexMap) ∧
            (∀ j, finiteFrostman p (p^(-(133*η+2*ζ))) (activeTripleClasses T j)) ∧
            (∀ r : ℝ, p ≤ r → ∀ L : AffineLine,
              (((activeTripleClasses T 1).filter (fun x ↦ x ∈ lineNeighborhood r L)).card : ℝ) ≤
                p^(-(133*η+2*ζ))*(r/w₁)^ζ*((activeTripleClasses T 1).card : ℝ)) ∧
            (∀ r : ℝ, p ≤ r → ∀ L : AffineLine,
              (((activeTripleClasses T 2).filter (fun x ↦ x ∈ lineNeighborhood r L)).card : ℝ) ≤
                p^(-(133*η+2*ζ))*(r/w₂)^ζ*((activeTripleClasses T 2).card : ℝ)) := by
  obtain ⟨p₀,hp₀,hp₀1,hpay⟩ := exists_constant_power_payment 256 (by norm_num) hη
  refine ⟨p₀,hp₀,hp₀1,?_⟩
  intro p hp hpp ζ hζ hζ1 Q hne hgeom hsep hdense hF
  have hp1 : p ≤ 1 := (hpp.trans_lt hp₀1).le
  have hpay256 := hpay p hp hpp
  obtain ⟨w₁,w₂,hw₁,hw₂,L₁,L₂,T,hTQ,hTne,hgeomT,hsepT,hstrip₁,hstrip₂,hmass,hden,hFT,hnc₁,hnc₂⟩ :=
    exists_sequential_two_ends_graph hp hp1 hζ hζ1 (Real.rpow_pos_of_pos hp _) (by positivity)
      Q hne hgeom hsep hdense hF
  have hw₁p : 0 < w₁ := lt_of_lt_of_le (by positivity : 0 < p/2) hw₁.1
  have hw₂p : 0 < w₂ := lt_of_lt_of_le (by positivity : 0 < p/2) hw₂.1
  have hmassCoef : p^(133*η+2*ζ) ≤ (p^(44*η))^2*w₁^ζ*w₂^ζ/64 := by
    refine (Real.rpow_le_rpow_of_exponent_ge hp hp1 (show 89*η+2*ζ ≤ 133*η+2*ζ by linarith)).trans ?_
    exact sequential_mass_power_payment hp hpay256 hw₁.1 hw₂.1 hζ hζ1
  have hdenCoef : p^(133*η+2*ζ) ≤ p^(44*η)/256 := by
    refine (Real.rpow_le_rpow_of_exponent_ge hp hp1 (show 45*η ≤ 133*η+2*ζ by linarith)).trans ?_
    exact sequential_density_power_payment hp hpay256
  have hFcoef : 64*p^(-44*η)/((p^(44*η))^2*w₁^ζ*w₂^ζ) ≤ p^(-(133*η+2*ζ)) := by
    have hh := sequential_Frostman_power_payment hp hpay256 hw₁.1 hw₂.1 hζ hζ1
    rwa [show -133*η-2*ζ = -(133*η+2*ζ) by ring] at hh
  have hC : p^(-89*η) ≤ p^(-(133*η+2*ζ)) :=
    Real.rpow_le_rpow_of_exponent_ge hp hp1 (by linarith)
  have hstripCoeffs := sequential_strip_power_payment hp hp1 hη.le hpay256
  have hC₁ := hstripCoeffs.1.trans hC
  have hC₂ := hstripCoeffs.2.trans hC
  refine ⟨w₁,w₂,hw₁,hw₂,L₁,L₂,T,hTQ,hTne,hgeomT,hsepT,hstrip₁,hstrip₂,
    (mul_le_mul_of_nonneg_right hmassCoef (Nat.cast_nonneg _)).trans hmass,
    coordinateDensity_mono hdenCoef hden,
    (fun j ↦ finiteFrostman_mono hp.le hFcoef (hFT j)),?_,?_⟩
  · intro r hr L
    refine (hnc₁ r hr L).trans ?_
    have hrp : 0 < r := hp.trans_le hr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁
      (Real.rpow_pos_of_pos (div_pos hrp hw₁p) ζ).le) (Nat.cast_nonneg _)
  · intro r hr L
    refine (hnc₂ r hr L).trans ?_
    have hrp : 0 < r := hp.trans_le hr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₂
      (Real.rpow_pos_of_pos (div_pos hrp hw₂p) ζ).le) (Nat.cast_nonneg _)

end Kakeya4.Hard.RestrictedTriple
