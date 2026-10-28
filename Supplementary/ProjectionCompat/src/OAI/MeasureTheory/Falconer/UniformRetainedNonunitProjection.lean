import OAI.MeasureTheory.Falconer.NonunitProjectionCollision

/-! A genuine nonunit coefficient projection from original retained pairs.
No covering refinement or unproved scale transport is assumed. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal NNReal BigOperators

theorem uniform_retained_nonunit_projection {σ p S : ℝ}
    (hσ : 0 < σ) (hσp : σ < p) (hpS : p < S) :
    ∃ e τ κ : ℝ, 0 < e ∧ 0 < τ ∧ 0 < κ ∧ κ*S = e ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ C : ℝ, 1 ≤ C → C ≤ ((2:ℝ)^N)^e →
    ∀ μ ν : ProbabilityMeasure (Space 2), ∀ H : Set (Space 2 × Space 2),
      MeasurableSet H → (∀ z ∈ H, ((2:ℝ)^N)^(-κ) ≤ dist z.1 z.2) →
      RadialCapBound μ ν H N e p →
    ∀ ρ : Measure (Space 2), ∀ [IsProbabilityMeasure ρ], FrostmanBallBound ρ S C →
      (∀ᵐ z : Space 2 × Space 2 ∂(ρ.prod ρ), ‖z.1-z.2‖ ≤ 4) →
      ∃ Bad : Set (Space 2 × Space 2), MeasurableSet Bad ∧
        ((μ : Measure (Space 2)).prod ν) Bad ≤
          ((μ : Measure (Space 2)).prod ν) Hᶜ + ENNReal.ofReal (((2:ℝ)^N)^(-τ)) ∧
        ∀ z ∉ Bad, z ∈ H ∧ ∀ G : Set (Space 2), ((2:ℝ)^N)^(-e) ≤ (ρ G).toReal →
          (Nat.ceil (((2:ℝ)^N)^σ) : ℕ∞) ≤ externalCoveringNumber
            ⟨((2:ℝ)^N)⁻¹,by positivity⟩
            ((fun x ↦ (z.2 1-z.1 1)*x 0+(z.1 0-z.2 0)*x 1) '' G) := by
  obtain ⟨e,τ,he,hτ,N₀,huniform⟩ := uniform_scaled_kaufman_collision_bad_set hσ hσp hpS
  have hS : 0 < S := (hσ.trans hσp).trans hpS
  let κ := e/S
  have hκ : 0 < κ := div_pos he hS
  have hκS : κ*S = e := by dsimp [κ]; field_simp
  have hκp : κ*p ≤ e := by
    calc
      _ ≤ κ*S := mul_le_mul_of_nonneg_left hpS.le hκ.le
      _ = _ := hκS
  refine ⟨e,τ,κ,he,hτ,hκ,hκS,N₀,?_⟩
  intro N hN C hC hCb μ ν H hH hsize hcap ρ _ hfrost hdiam
  let R : ℝ := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hneq : ∀ z ∈ H, z.1 ≠ z.2 := by
    intro z hz heq
    have hh := hsize z hz
    rw [heq,dist_self] at hh
    exact (not_le_of_gt (by positivity : 0 < R^(-κ))) hh
  let θ := retainedDirectionLaw μ ν H
  let : SFinite θ := by dsimp [θ,retainedDirectionLaw]; infer_instance
  have hK : 1 ≤ R^e := Real.one_le_rpow hR he.le
  obtain ⟨B,hB,hBad,hgood⟩ := huniform N hN κ hκ.le hκp (R^e) C hK le_rfl hC hCb ρ θ
    (retained_direction_sphere_carried μ ν H hneq) (retained_direction_mass_le_one μ ν H)
    (fun w hw r hr hr1 ↦ retained_direction_unit_cap μ ν H hH hcap w hw r hr hr1) hfrost hdiam
  let Bad := Hᶜ ∪ ((fun z ↦ radialDirection z.1 z.2) ⁻¹' B)
  refine ⟨Bad,hH.compl.union (hB.preimage radial_pair_direction_measurable),?_,?_⟩
  · exact (retained_direction_bad_lift μ ν H B hB).trans (add_le_add le_rfl hBad)
  · intro z hz
    have hzH : z ∈ H := by by_contra hn; exact hz (Or.inl hn)
    have hzB : radialDirection z.1 z.2 ∉ B := fun hb ↦ hz (Or.inr hb)
    refine ⟨hzH,?_⟩
    let v := z.2-z.1
    have hvsize : R^(-κ) ≤ ‖v‖ := by
      change R^(-κ) ≤ ‖z.2-z.1‖
      rw [norm_sub_rev]
      simpa only [dist_eq_norm] using hsize z hzH
    have hraw := (nonunit_direction_collision_le ρ hR0 v hvsize).trans (hgood _ hzB).le
    have hreal : (directionProjectionCollision ρ v (3/R)).toReal ≤ R^(-(σ+2*e)) := by
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hraw
      rw [ENNReal.toReal_ofReal (by positivity)] at hh
      exact hh
    have heq : {w : Space 2 × Space 2 |
        |((z.2 1-z.1 1)*w.1 0+(z.1 0-z.2 0)*w.1 1)-
          ((z.2 1-z.1 1)*w.2 0+(z.1 0-z.2 0)*w.2 1)| < 3/R} =
        {w | |v 0*(w.1-w.2) 1-v 1*(w.1-w.2) 0| < 3/R} := by
      ext w
      simp only [mem_ofPred_eq,PiLp.sub_apply]
      have hh : ((z.2 1-z.1 1)*w.1 0+(z.1 0-z.2 0)*w.1 1)-
          ((z.2 1-z.1 1)*w.2 0+(z.1 0-z.2 0)*w.2 1) =
          -(v 0*(w.1 1-w.2 1)-v 1*(w.1 0-w.2 0)) := by dsimp [v]; ring
      rw [hh,abs_neg]
    have hc : ((ρ.prod ρ) {w | |((z.2 1-z.1 1)*w.1 0+(z.1 0-z.2 0)*w.1 1)-
        ((z.2 1-z.1 1)*w.2 0+(z.1 0-z.2 0)*w.2 1)| < 3/R}).toReal ≤ R^(-(σ+2*e)) := by
      rw [heq]; exact hreal
    have hcover := external_projection_cover_card_lower ρ
      (fun x : Space 2 ↦ (z.2 1-z.1 1)*x 0+(z.1 0-z.2 0)*x 1) (by fun_prop)
      (by positivity : 0 ≤ R^(-e)) (by positivity : 0 < R^(-(σ+2*e))) ⟨R⁻¹,by positivity⟩
      (by rw [div_eq_mul_inv]; linarith [inv_pos.mpr hR0] : 2*R⁻¹ < 3/R) hc
    simpa only [kaufman_cover_exponent_identity hR0] using hcover

#print axioms uniform_retained_nonunit_projection
end OAI.Falconer
