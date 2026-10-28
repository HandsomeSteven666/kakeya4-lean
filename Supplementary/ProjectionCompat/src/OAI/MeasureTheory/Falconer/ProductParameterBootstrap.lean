import OAI.MeasureTheory.Falconer.ProductParameterNormalization

/-! Genuine four-real-marginal consumer of the unseparated bootstrap. The
initial cap and all planar Frostman data are proved internally from the
original marginal ball bounds. The final pair relation and mass are pulled
back to the original parameter-product laws. -/

set_option autoImplicit false
namespace OAI.Falconer.Regularization
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem uniform_parameter_product_bootstrap
    {s t σ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hσ : 0 < σ) (hσmax : σ < min (s+t) 1) (η : ℝ) (hη : 0 < η) :
    ∃ ε τ : ℝ, 0 < ε ∧ 0 < τ ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ C : ℝ, 1 ≤ C → C ≤ ((2:ℝ)^N)^ε →
    ∀ μ₁ μ₂ ν₁ ν₂ : Measure ℝ,
      ∀ [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂],
      UnitSupported μ₁ → UnitSupported μ₂ → UnitSupported ν₁ → UnitSupported ν₂ →
      (∀ z r : ℝ, 0 < r → μ₁ (closedBall z r) ≤ ENNReal.ofReal (C*r^s)) →
      (∀ z r : ℝ, 0 < r → μ₂ (closedBall z r) ≤ ENNReal.ofReal (C*r^s)) →
      (∀ z r : ℝ, 0 < r → ν₁ (closedBall z r) ≤ ENNReal.ofReal (C*r^t)) →
      (∀ z r : ℝ, 0 < r → ν₂ (closedBall z r) ≤ ENNReal.ofReal (C*r^t)) →
      ∃ H : Set (Space 2 × Space 2), MeasurableSet H ∧
        H ⊆ wideParameterRoot.carrier ×ˢ wideParameterRoot.carrier ∧
        ((parameterProductProbability μ₁ ν₁ : Measure (Space 2)).prod
          (parameterProductProbability μ₂ ν₂)) Hᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-τ)) ∧
        RadialCapBound (parameterProductProbability μ₁ ν₁) (parameterProductProbability μ₂ ν₂) H N η σ := by
  classical
  let m := min (s+t) 1
  let α := (σ+m)/2
  let v := (σ+α)/2
  let a := min (min s t) σ/2
  have hσα : σ < α := by dsimp [α]; linarith
  have hαm : α < m := by dsimp [α]; linarith
  have hα : 0 < α := hσ.trans hσα
  have hα1 : α ≤ 1 := hαm.le.trans (min_le_right _ _)
  have hαS : α ≤ s+t := hαm.le.trans (min_le_left _ _)
  have hσv : σ < v := by dsimp [v]; linarith
  have hvα : v < α := by dsimp [v]; linarith
  have hv1 : v < 1 := hvα.trans_le hα1
  have hmin : 0 < min (min s t) σ := lt_min (lt_min hs ht) hσ
  have ha : 0 < a := by dsimp [a]; positivity
  have haσ : a ≤ σ := by have hh := min_le_right (min s t) σ; dsimp [a]; linarith
  have haT : a ≤ min s t := by have hh := min_le_left (min s t) σ; dsimp [a]; linarith
  obtain ⟨e0,τ,he0,hτ,Nb,hNb⟩ := uniform_unseparated_radial_bootstrap ha haσ hσv hv1 hvα hα1 η hη
  let ε := e0/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨Nc,hNc⟩ := fixed_constant_absorbed (by positivity : 0 < e0/2) 32
  refine ⟨ε,τ,hε,hτ,max Nb Nc,?_⟩
  intro N hN C hC hCbudget μ₁ μ₂ ν₁ ν₂ _ _ _ _ hμ₁ hμ₂ hν₁ hν₂ hbμ₁ hbμ₂ hbν₁ hbν₂
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hR0 : 0 < (2:ℝ)^N := by positivity
  have hCC : C*C ≤ ((2:ℝ)^N)^(e0/2) := calc
    _ ≤ ((2:ℝ)^N)^ε*((2:ℝ)^N)^ε := mul_le_mul hCbudget hCbudget hC0 (Real.rpow_nonneg hR0.le _)
    _ = _ := by rw [← Real.rpow_add hR0]; congr 1; dsimp [ε]; ring
  have hcoef : 32*C*C ≤ ((2:ℝ)^N)^e0 := calc
    _ = 32*(C*C) := by ring
    _ ≤ 32*((2:ℝ)^N)^(e0/2) := mul_le_mul_of_nonneg_left hCC (by norm_num)
    _ ≤ ((2:ℝ)^N)^(e0/2)*((2:ℝ)^N)^(e0/2) :=
      mul_le_mul_of_nonneg_right (hNc N ((le_max_right _ _).trans hN)) (by positivity)
    _ = _ := by rw [← Real.rpow_add hR0]; congr 1; ring
  have hseedBudget : 32*C ≤ ((2:ℝ)^N)^e0 := by
    have hsq : C ≤ C*C := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hC hC0
    exact (mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 32)).trans
      (by simpa only [mul_assoc] using hcoef)
  have hcoef16 : 16*C*C ≤ ((2:ℝ)^N)^e0 := by
    have hh := mul_le_mul_of_nonneg_right (show (16:ℝ) ≤ 32 by norm_num) (mul_nonneg hC0 hC0)
    have hh' : 16*C*C ≤ 32*C*C := by simpa only [mul_assoc] using hh
    exact hh'.trans hcoef
  have hraise (ξ : ProbabilityMeasure (Space 2))
      (hξ : FrostmanBallBound (ξ : Measure (Space 2)) (s+t) (16*C*C)) :
      FrostmanBallBound (ξ : Measure (Space 2)) α (((2:ℝ)^N)^e0) := by
    apply probability_frostman_lower_exponent (ξ : Measure (Space 2)) hα.le hαS (Real.one_le_rpow hR he0.le)
    intro z r hr
    exact (hξ z r hr).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcoef16 (Real.rpow_nonneg hr.le _)))
  let law₁ := quarterParameterProbability μ₁ ν₁
  let law₂ := quarterParameterProbability μ₂ ν₂
  let Q := centeredUnitCube 2
  let G := Q.carrier ×ˢ Q.carrier
  have hroot₁ : (law₁ : Measure (Space 2)) Q.carrierᶜ = 0 := quarter_parameter_root_carried μ₁ ν₁ hμ₁ hν₁
  have hroot₂ : (law₂ : Measure (Space 2)) Q.carrierᶜ = 0 := quarter_parameter_root_carried μ₂ ν₂ hμ₂ hν₂
  have hseed : RadialCapBound law₁ law₂ G N e0 a :=
    (quarter_parameter_products_initial_radial_cap μ₁ μ₂ ν₁ ν₂ hC hs.le hs1 ht.le ht1
      hbμ₁ hbμ₂ hbν₁ hbν₂ hseedBudget).lower_exponent haT
  obtain ⟨H,hH,hHG,hdel,hcap⟩ := hNb a ⟨le_rfl,haσ⟩ N ((le_max_left _ _).trans hN)
    (((2:ℝ)^N)^e0) (by positivity) le_rfl law₁ law₂
    (hraise _ (quarter_parameter_full_frostman μ₁ ν₁ hC0 hs1 ht1 hbμ₁ hbν₁))
    (hraise _ (quarter_parameter_full_frostman μ₂ ν₂ hC0 hs1 ht1 hbμ₂ hbν₂))
    Q rfl hroot₁ hroot₂ G (Q.measurable.prod Q.measurable) hseed
  have hOutside : ((law₁ : Measure (Space 2)).prod law₂) Gᶜ = 0 :=
    product_core_compl_null (law₁ : Measure (Space 2)) (law₂ : Measure (Space 2)) Q.carrier Q.carrier hroot₁ hroot₂
  have hBad : ((law₁ : Measure (Space 2)).prod law₂) Hᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-τ)) := by
    have hsub : Hᶜ ⊆ (G \ H) ∪ Gᶜ := by
      intro z hz
      by_cases hg : z ∈ G
      · exact Or.inl ⟨hg,hz⟩
      · exact Or.inr hg
    exact (measure_mono hsub).trans ((measure_union_le _ _).trans
      (by simpa only [hOutside,add_zero] using add_le_add hdel (le_refl (((law₁ : Measure (Space 2)).prod law₂) Gᶜ))))
  let f := parameterQuarterZoom
  let H₀ := (Prod.map f f) ⁻¹' H
  have hH₀ : MeasurableSet H₀ := hH.preimage (f.measurable.prodMap f.measurable)
  have hzoom : zoomPairSet f H₀ = H := by
    ext z
    change (f (f.symm z.1),f (f.symm z.2)) ∈ H ↔ z ∈ H
    rw [f.apply_symm_apply,f.apply_symm_apply]
  have hH₀sub : H₀ ⊆ wideParameterRoot.carrier ×ˢ wideParameterRoot.carrier := by
    intro z hz
    have hh := hHG hz
    change f z.1 ∈ Q.carrier ∧ f z.2 ∈ Q.carrier at hh
    rw [← parameter_quarter_root_preimage]
    exact hh
  have hzoomCompl : zoomPairSet f H₀ᶜ = Hᶜ := by rw [← hzoom]; rfl
  have hmass := zoom_pair_mass f (parameterProductProbability μ₁ ν₁ : Measure (Space 2))
    (parameterProductProbability μ₂ ν₂ : Measure (Space 2)) H₀ᶜ hH₀.compl
  rw [hzoomCompl] at hmass
  have hcap₀ : RadialCapBound (parameterProductProbability μ₁ ν₁) (parameterProductProbability μ₂ ν₂) H₀ N η σ := by
    apply (RadialCapBound.radialZoom_iff (by norm_num : (0:ℝ) < 1/4) (0:Space 2)).mp
    change RadialCapBound law₁ law₂ (zoomPairSet f H₀) N η σ
    rw [hzoom]
    exact hcap
  exact ⟨H₀,hH₀,hH₀sub,hmass.symm.trans_le hBad,hcap₀⟩

#print axioms uniform_parameter_product_bootstrap
end OAI.Falconer.Regularization
