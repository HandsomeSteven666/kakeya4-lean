import OAI.MeasureTheory.Falconer.FlatteningJointLayerConsumer

/-! Quantitative local L2 bounds obtained from one actual selected layer. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem energy_le_real_quotient_of_product_bound (E V : ℝ≥0∞) {x C : ℝ}
    (hx : 0 < x) (hC : 0 ≤ C) (hV : ENNReal.ofReal x ≤ V)
    (hprod : E*V ≤ ENNReal.ofReal C) : E ≤ ENNReal.ofReal (C/x) := by
  have hc : ENNReal.ofReal (C/x)*ENNReal.ofReal x = ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_mul (div_nonneg hC hx.le)]
    congr 1
    exact div_mul_cancel₀ _ hx.ne'
  apply (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr hx).ne' ENNReal.ofReal_ne_top).mp
  exact ((mul_le_mul_right hV E).trans hprod).trans_eq hc.symm

theorem ceil_scale_volume_lower_bound {r b : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ((5*r)^b*r) ≤
      (Nat.ceil ((5*r)^b):ℝ≥0∞)*ENNReal.ofReal r := by
  rw [ENNReal.ofReal_mul (by positivity : 0≤(5*r)^b)]
  exact mul_le_mul_left (ENNReal.ofReal_le_natCast.mpr (Nat.le_ceil _)) _

theorem OSS_original_energy_slow_local_L2_bound (kernel : SmoothKernel) {s t η a : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s+t ≤ 1) (hη : 0 < η) (ha : 0 < a) :
    ∃ ε e M T P r₀ : ℝ,
    0 < ε ∧ 0 < e ∧ 0 < M ∧ 0 < T ∧ 0 < P ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ r : ℝ, 0 < r → r ≤ r₀ → ∃ L : ℕ,
      (2:ℝ)^L ≤ 2*max 1 (M/r) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ r → r ≤ δ^a →
      ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        UnitSupported μ → UnitSupported ν →
        smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-ε)) →
        smoothEnergy kernel.law t δ ν ≤ ENNReal.ofReal (δ^(-ε)) →
        ∀ k : ℕ, 2 ≤ k →
        let ρ := additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k
        ENNReal.ofReal (r^e)*densityL2 ρ (kernelProfile kernel r) ≤
          densityL2 (ρ ∗ ρ) (kernelProfile kernel r) →
        densityL2 (ρ ∗ ρ) (kernelProfile kernel r) ≤
          ENNReal.ofReal (max (T*((L:ℝ)+1)^2)
            (P*((L:ℝ)+1)^4/((5*r)^(-s-t+η)*r))) := by
  obtain ⟨ε,e,M,T,P,r₀,hε,he,hM,hT,hP,hr₀,hr₀1,hjoint⟩ :=
    OSS_original_energy_joint_layer_bounds kernel hs ht hst hη ha
  refine ⟨ε,e,M,T,P,r₀,hε,he,hM,hT,hP,hr₀,hr₀1,?_⟩
  intro r hr hrr
  obtain ⟨L,hL,hchoose⟩ := hjoint r hr hrr
  refine ⟨L,hL,?_⟩
  intro δ hδ hδr hwindow μ ν _ _ hμU hνU hμE hνE k hk ρ hslow
  have hLcast : ENNReal.ofReal ((L:ℝ)+1) = ((L+1:ℕ):ℝ≥0∞) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num)]
    simp
  rcases hchoose δ hδ hδr hwindow μ ν hμU hνU hμE hνE k hk hslow with hlo | ⟨j,_,hV,hprod⟩
  · apply hlo.trans
    rw [← hLcast,← ENNReal.ofReal_pow (by positivity : 0≤(L:ℝ)+1),
      ← ENNReal.ofReal_mul hT.le]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  · have hprod' : densityL2 (ρ ∗ ρ) (kernelProfile kernel r) *
        volume (flatteningCellDyadicLevel (additiveDensity ρ (kernelProfile kernel r)) r j) ≤
        ENNReal.ofReal (P*((L:ℝ)+1)^4) := by
      simpa only [ENNReal.ofReal_mul hP.le,ENNReal.ofReal_pow (by positivity : 0≤(L:ℝ)+1),hLcast] using hprod
    exact (energy_le_real_quotient_of_product_bound _ _ (by positivity) (by positivity)
      ((ceil_scale_volume_lower_bound hr).trans hV) hprod').trans
      (ENNReal.ofReal_le_ofReal (le_max_right _ _))

#print axioms energy_le_real_quotient_of_product_bound
#print axioms ceil_scale_volume_lower_bound
#print axioms OSS_original_energy_slow_local_L2_bound
end OAI.Falconer
