






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.UniformUnseparatedRadialBootstrap
import Kakeya4.Hard.MultiplicativeConvolution.ProductSlabBound

/-! Actual parameter-product probabilities and their initial radial cap.
The existing project proof of the all-normal product slab estimate is consumed
directly. A larger half-open root contains every closed unit input point,
including zero and the boundary. No source support is discarded here. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

noncomputable def parameterProductProbability (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : ProbabilityMeasure (Space 2) :=
  ⟨planarProductLaw μ ν,inferInstance⟩

noncomputable def wideParameterRoot : DyadicCube 2 :=
  ⟨WithLp.toLp 2 (fun _ => (-2:ℝ)),4⟩

theorem normalized_cap_cross_bound (u w : Space 2) (hu : ‖u‖ = 1) {r : ℝ}
    (hcap : dist (normalize w) u ≤ r) :
    |u 1*w 0-u 0*w 1| ≤ 2*‖w‖*r := by
  have hu0 : |u 0| ≤ 1 := by simpa only [Real.norm_eq_abs,hu] using PiLp.norm_apply_le u 0
  have hu1 : |u 1| ≤ 1 := by simpa only [Real.norm_eq_abs,hu] using PiLp.norm_apply_le u 1
  have hd : ‖normalize w-u‖ ≤ r := by simpa only [dist_eq_norm] using hcap
  have h0 : |(normalize w) 0-u 0| ≤ r := by
    simpa only [PiLp.sub_apply,Real.norm_eq_abs] using (PiLp.norm_apply_le (normalize w-u) 0).trans hd
  have h1 : |(normalize w) 1-u 1| ≤ r := by
    simpa only [PiLp.sub_apply,Real.norm_eq_abs] using (PiLp.norm_apply_le (normalize w-u) 1).trans hd
  have hc : |u 1*(normalize w) 0-u 0*(normalize w) 1| ≤ 2*r := calc
    _ = |u 1*((normalize w) 0-u 0)-u 0*((normalize w) 1-u 1)| := by congr 1; ring
    _ ≤ |u 1*((normalize w) 0-u 0)|+|u 0*((normalize w) 1-u 1)| := abs_sub _ _
    _ ≤ 1*r+1*r := add_le_add
      (by rw [abs_mul]; exact mul_le_mul hu1 h0 (abs_nonneg _) (by norm_num))
      (by rw [abs_mul]; exact mul_le_mul hu0 h1 (abs_nonneg _) (by norm_num))
    _ = _ := by ring
  have hcoord (i : Fin 2) : w i = ‖w‖*(normalize w) i := by
    have hh := congrArg (fun z : Space 2 => z i) (norm_smul_normalize w)
    simpa only [PiLp.smul_apply,smul_eq_mul] using hh.symm
  calc
    _ = ‖w‖*|u 1*(normalize w) 0-u 0*(normalize w) 1| := by
      rw [hcoord 0,hcoord 1,
        show u 1*(‖w‖*(normalize w) 0)-u 0*(‖w‖*(normalize w) 1) =
          ‖w‖*(u 1*(normalize w) 0-u 0*(normalize w) 1) by ring,
        abs_mul,abs_of_nonneg (norm_nonneg w)]
    _ ≤ ‖w‖*(2*r) := mul_le_mul_of_nonneg_left hc (norm_nonneg w)
    _ = _ := by ring

theorem root_radial_cap_mass_of_slabs (ν : Measure (Space 2)) (Q : DyadicCube 2)
    {K T D : ℝ} (hD : 0 < D)
    (hdiam : ∀ x ∈ Q.carrier, ∀ z ∈ Q.carrier, ‖x-z‖ ≤ D)
    (hslab : ∀ a b c : ℝ, a^2+b^2 = 1 → ∀ R > 0,
      ν (planarSlab a b c R) ≤ ENNReal.ofReal (K*R^T))
    (z u : Space 2) (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 < r) :
    ν {x | (z,x) ∈ Q.carrier ×ˢ Q.carrier ∧ dist (radialDirection z x) u < r} ≤
      ENNReal.ofReal (K*(2*D*r)^T) := by
  have hsquare : (u 1)^2+(-u 0)^2 = 1 := by
    have hh := EuclideanSpace.real_norm_sq_eq u
    simp only [hu,one_pow,Fin.sum_univ_two] at hh
    nlinarith
  apply (measure_mono (show {x | (z,x) ∈ Q.carrier ×ˢ Q.carrier ∧ dist (radialDirection z x) u < r} ⊆
      planarSlab (u 1) (-u 0) (u 1*z 0-u 0*z 1) (2*D*r) from ?_)).trans
    (hslab _ _ _ hsquare _ (by positivity))
  intro x hx
  have hcross := normalized_cap_cross_bound u (x-z) hu hx.2.le
  have hd := hdiam x hx.1.2 z hx.1.1
  have hbound : 2*‖x-z‖*r ≤ 2*D*r :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) hr.le
  have he : u 1*x 0+(-u 0)*x 1-(u 1*z 0-u 0*z 1) = u 1*(x-z) 0-u 0*(x-z) 1 := by
    simp only [PiLp.sub_apply]
    ring
  change |u 1*x 0+(-u 0)*x 1-(u 1*z 0-u 0*z 1)| ≤ _
  rw [he]
  exact hcross.trans hbound

theorem product_parameter_root_cap_mass (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {C s t : ℝ}
    (hC : 1 ≤ C) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hμ : ∀ z R : ℝ, 0 < R → μ (closedBall z R) ≤ ENNReal.ofReal (C*R^s))
    (hν : ∀ z R : ℝ, 0 < R → ν (closedBall z R) ≤ ENNReal.ofReal (C*R^t))
    (z u : Space 2) (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 < r) :
    planarProductLaw μ ν {x | (z,x) ∈ wideParameterRoot.carrier ×ˢ wideParameterRoot.carrier ∧
      dist (radialDirection z x) u < r} ≤ ENNReal.ofReal (32*C*r^(min s t)) := by
  have hdiam : ∀ x ∈ wideParameterRoot.carrier, ∀ z ∈ wideParameterRoot.carrier, ‖x-z‖ ≤ (8:ℝ) := by
    intro x hx z hz
    have hb := wideParameterRoot.dist_le (by norm_num [wideParameterRoot]) hx hz
    have hroot : Real.sqrt (2:ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
    norm_num only [wideParameterRoot,Nat.cast_ofNat] at hb
    rw [dist_eq_norm] at hb
    linarith
  have hslab : ∀ a b c : ℝ, a^2+b^2 = 1 → ∀ R > 0,
      planarProductLaw μ ν (planarSlab a b c R) ≤ ENNReal.ofReal ((2*C)*R^(min s t)) := by
    intro a b c hn R hR
    exact planarProductLaw_unit_normal_slab_bound μ ν hC hs hs1 ht ht1 hμ hν a b c hn hR
  apply (root_radial_cap_mass_of_slabs (planarProductLaw μ ν) wideParameterRoot
    (by norm_num : (0:ℝ) < 8) hdiam hslab z u hu hr).trans
  apply ENNReal.ofReal_le_ofReal
  have hpower : (16:ℝ)^(min s t) ≤ 16 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 16)
      ((min_le_left s t).trans hs1)
    simpa only [Real.rpow_one] using hh
  rw [show 2*(8:ℝ)*r = 16*r by ring,Real.mul_rpow (by norm_num) hr.le]
  calc
    _ = (2*C)*(16:ℝ)^(min s t)*r^(min s t) := by ring
    _ ≤ (2*C)*16*r^(min s t) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpower (by have := hC; positivity)) (by positivity)
    _ = _ := by ring

theorem parameter_products_initial_radial_cap (μ₁ μ₂ ν₁ ν₂ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    {C s t e : ℝ} {N : ℕ}
    (hC : 1 ≤ C) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hμ₁ : ∀ z R : ℝ, 0 < R → μ₁ (closedBall z R) ≤ ENNReal.ofReal (C*R^s))
    (hμ₂ : ∀ z R : ℝ, 0 < R → μ₂ (closedBall z R) ≤ ENNReal.ofReal (C*R^s))
    (hν₁ : ∀ z R : ℝ, 0 < R → ν₁ (closedBall z R) ≤ ENNReal.ofReal (C*R^t))
    (hν₂ : ∀ z R : ℝ, 0 < R → ν₂ (closedBall z R) ≤ ENNReal.ofReal (C*R^t))
    (hbudget : 32*C ≤ ((2:ℝ)^N)^e) :
    RadialCapBound (parameterProductProbability μ₁ ν₁) (parameterProductProbability μ₂ ν₂)
      (wideParameterRoot.carrier ×ˢ wideParameterRoot.carrier) N e (min s t) := by
  have hRpos : 0 < ((2:ℝ)^N)⁻¹ := by positivity
  constructor
  · intro z hz u hu r hr hr1
    exact (product_parameter_root_cap_mass μ₂ ν₂ hC hs hs1 ht ht1 hμ₂ hν₂ z u hu (hRpos.trans_le hr)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (hRpos.trans_le hr).le _)))
  · intro x hx u hu r hr hr1
    have he : {z | (z,x) ∈ wideParameterRoot.carrier ×ˢ wideParameterRoot.carrier ∧ dist (radialDirection x z) u < r} =
        {z | (x,z) ∈ wideParameterRoot.carrier ×ˢ wideParameterRoot.carrier ∧ dist (radialDirection x z) u < r} := by
      ext z
      exact and_congr (and_comm) Iff.rfl
    rw [he]
    exact (product_parameter_root_cap_mass μ₁ ν₁ hC hs hs1 ht ht1 hμ₁ hν₁ x u hu (hRpos.trans_le hr)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (hRpos.trans_le hr).le _)))

#print axioms normalized_cap_cross_bound
#print axioms root_radial_cap_mass_of_slabs
#print axioms product_parameter_root_cap_mass
#print axioms parameter_products_initial_radial_cap
end OAI.Falconer
