import Kakeya4.Hard.MultiplicativeConvolution.AllScaleSmoothing
import Kakeya4.Hard.MultiplicativeConvolution.SmallScalePowers
import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningDyadicEnergy

/-! Original finite-scale interval caps produce genuine nontruncated smooth energy.
Source: manuscript re:energy-bound. Reuses actual smoothing ball transport and
the audited OpenAI dyadic Riesz majorant/energy_scale_identity; no energy certificate.
The coefficient and smoothing radius occur after the constant. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

theorem probability_coarse_cap_all_radii (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {S r K : ℝ} (hS : 0 ≤ S) (hr : 0 < r) (hK : 0 ≤ K)
    (hcap : ∀ z R : ℝ, r ≤ R → R ≤ 1 → μ (closedBall z R) ≤ ENNReal.ofReal (K*R^S)) :
    ∀ z R : ℝ, r ≤ R → μ (closedBall z R) ≤ ENNReal.ofReal ((K+1)*R^S) := by
  intro z R hrR
  by_cases hR : R ≤ 1
  · apply (hcap z R hrR hR).trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith only [Real.rpow_nonneg (hr.trans_le hrR).le S]
  · have hR1 : 1 ≤ R := (lt_of_not_ge hR).le
    calc
      _ ≤ μ univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal ((K+1)*R^S) := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        have hp : 1 ≤ R^S := Real.one_le_rpow hR1 hS
        nlinarith only [hp, hK]

theorem pairMass_le_uniform_closedBallCap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R A : ℝ) (hcap : ∀ z, μ (closedBall z R) ≤ ENNReal.ofReal A) :
    pairMass R μ ≤ ENNReal.ofReal A := by
  unfold pairMass
  calc
    _ ≤ ∫⁻ _ : ℝ, ENNReal.ofReal A ∂μ := lintegral_mono hcap
    _ = _ := by simp

theorem exists_smoothEnergy_bound_of_coarseCap (kernel : SmoothKernel) {s S : ℝ}
    (hs : 0 < s) (hsS : s < S) (hS1 : S ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∀ (r K : ℝ), 0 < r → 0 ≤ K →
        (∀ z R : ℝ, r ≤ R → R ≤ 1 → μ (closedBall z R) ≤ ENNReal.ofReal (K*R^S)) →
        smoothEnergy kernel.law s r μ ≤ ENNReal.ofReal (C*(K+1)) := by
  obtain ⟨C₀, hC₀, hsmooth⟩ := exists_smoothLaw_all_scale_ball_bound kernel (hs.trans hsS).le hS1
  let q : ℝ≥0∞ := ENNReal.ofReal ((1/2:ℝ)^(S-s))
  have hq : q < 1 := ENNReal.ofReal_lt_one.mpr
    (Real.rpow_lt_one (by norm_num) (by norm_num) (sub_pos.mpr hsS))
  have hsum : (∑' n : ℕ, q^n) < ∞ := tsum_geometric_lt_top.mpr hq
  let L : ℝ := (∑' n : ℕ, q^n).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hsumEq : (∑' n : ℕ, q^n) = ENNReal.ofReal L := (ENNReal.ofReal_toReal hsum.ne).symm
  let A : ℝ := (1/2:ℝ)^(-s)*C₀*2^S
  have hA : 0 < A := by dsimp [A]; positivity
  let C : ℝ := 1+A*L
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro μ hμ r K hr hK hcap
  let : IsProbabilityMeasure μ := hμ
  have hb := hsmooth μ r (K+1) hr (by linarith)
    (probability_coarse_cap_all_radii μ (hs.trans hsS).le hr hK hcap)
  have hterm (n : ℕ) :
      ENNReal.ofReal ((OAI.PlanarFalconer.energyScale n/2)^(-s)) *
        pairMass (2*OAI.PlanarFalconer.energyScale n) (smoothLaw kernel.law r μ) ≤
      ENNReal.ofReal (A*(K+1))*q^n := by
    apply (mul_le_mul_right (pairMass_le_uniform_closedBallCap (smoothLaw kernel.law r μ) _ _
      (fun z ↦ hb z _ (by positivity [OAI.PlanarFalconer.energyScale_pos n]))) _).trans_eq
    rw [← ENNReal.ofReal_mul (by positivity [OAI.PlanarFalconer.energyScale_pos n]),
      OAI.PlanarFalconer.energy_scale_identity]
    rw [ENNReal.ofReal_mul' (by positivity), ENNReal.ofReal_pow (by positivity)]
    congr 1
    congr 1
    dsimp [A]
    ring
  apply (OAI.Falconer.smoothEnergy_le_dyadic_pairMass kernel μ hr.ne' hs).trans
  calc
    _ ≤ 1 + ∑' n : ℕ, ENNReal.ofReal (A*(K+1))*q^n :=
      add_le_add_right (ENNReal.tsum_le_tsum hterm) _
    _ = 1 + ENNReal.ofReal (A*(K+1))*ENNReal.ofReal L := by
      rw [ENNReal.tsum_mul_left, hsumEq]
    _ ≤ _ := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by norm_num) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      dsimp [C]
      nlinarith only [hK]

#print axioms probability_coarse_cap_all_radii
#print axioms pairMass_le_uniform_closedBallCap
#print axioms exists_smoothEnergy_bound_of_coarseCap

/-- General positive cap exponents are lowered only inside the input estimate;
the output remains the original s-energy with 0<s<min(S,1). -/
theorem exists_smoothEnergy_bound_of_coarseCap_general (kernel : SmoothKernel) {s S : ℝ}
    (hs : 0 < s) (hsS : s < S) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∀ (r K : ℝ), 0 < r → 0 ≤ K →
        (∀ z R : ℝ, r ≤ R → R ≤ 1 → μ (closedBall z R) ≤ ENNReal.ofReal (K*R^S)) →
        smoothEnergy kernel.law s r μ ≤ ENNReal.ofReal (C*(K+1)) := by
  obtain ⟨C, hC, henergy⟩ := exists_smoothEnergy_bound_of_coarseCap kernel hs
    (lt_min hsS hs1) (min_le_right S 1)
  refine ⟨C, hC, ?_⟩
  intro μ hμ r K hr hK hcap
  apply henergy μ hμ r K hr hK
  intro z R hrR hR1
  apply (hcap z R hrR hR1).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (hr.trans_le hrR) hR1 (min_le_left S 1)) hK

/-- A finite-scale ball cap with a small power loss produces every original
energy input on the entire h..h^e window, with the threshold uniform in the law. -/
theorem exists_smoothEnergy_window_cap_of_coarseCap (kernel : SmoothKernel) {s S ε e : ℝ}
    (hs : 0 < s) (hsS : s < S) (hs1 : s < 1) (hε : 0 < ε) (he : 0 < e) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∀ (h K : ℝ), 0 < h → h ≤ h₀ → 0 ≤ K → K ≤ h^(-(e*ε/2)) →
        (∀ z R : ℝ, h ≤ R → R ≤ 1 → μ (closedBall z R) ≤ ENNReal.ofReal (K*R^S)) →
        ∀ r : ℝ, h ≤ r → r ≤ h^e →
          smoothEnergy kernel.law s r μ ≤ ENNReal.ofReal (r^(-ε)) := by
  obtain ⟨C, hC, henergy⟩ := exists_smoothEnergy_bound_of_coarseCap_general kernel hs hsS hs1
  let q : ℝ := e*ε/2
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨h₀, hh₀, hh₀1, hsmall⟩ :=
    exists_small_scale_power_bound (C := 2*C) (a := q) (τ := 0) (by positivity) hq
  refine ⟨h₀, hh₀, hh₀1, ?_⟩
  intro μ hμ h K hh hhh hK hKq hcap r hrlo hrhi
  have hh1 : h ≤ 1 := hhh.trans hh₀1
  have hone : 1 ≤ h^(-q) := by
    have hp := Real.rpow_le_rpow_of_exponent_ge hh hh1 (show -q ≤ 0 by linarith)
    simpa using hp
  have hmul : h^q*h^(-q) = 1 := by rw [← Real.rpow_add hh]; simp
  have hpay : 2*C ≤ h^(-q) := by
    have hp : (2*C)*h^q ≤ 1 := by simpa using hsmall h hh hhh
    calc
      2*C = ((2*C)*h^q)*h^(-q) := by rw [mul_assoc, hmul, mul_one]
      _ ≤ 1*h^(-q) := mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := one_mul _
  have hKone : K+1 ≤ 2*h^(-q) := by
    change K ≤ h^(-q) at hKq
    linarith only [hKq, hone]
  have hcoef : C*(K+1) ≤ h^(-2*q) := by
    calc
      _ ≤ C*(2*h^(-q)) := mul_le_mul_of_nonneg_left hKone hC.le
      _ = (2*C)*h^(-q) := by ring
      _ ≤ h^(-q)*h^(-q) := mul_le_mul_of_nonneg_right hpay (by positivity)
      _ = _ := by rw [← Real.rpow_add hh]; congr 1; ring
  have heq : h^(-2*q) = (h^e)^(-ε) := by
    rw [← Real.rpow_mul hh.le]
    dsimp [q]
    congr 1
    ring
  have hlast : h^(-2*q) ≤ r^(-ε) := by
    rw [heq]
    exact Real.rpow_le_rpow_of_nonpos (hh.trans_le hrlo) hrhi (by linarith)
  exact (henergy μ hμ r K (hh.trans_le hrlo) hK
    (fun z R hrR hR1 ↦ hcap z R (hrlo.trans hrR) hR1)).trans
      (ENNReal.ofReal_le_ofReal (hcoef.trans hlast))

#print axioms exists_smoothEnergy_bound_of_coarseCap_general
#print axioms exists_smoothEnergy_window_cap_of_coarseCap
end Kakeya4.Hard.MultiplicativeConvolution
