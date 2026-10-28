import OAI.MeasureTheory.Falconer.FlatteningPairMass

/-! Directly consume the bundled Euclidean dyadic kernel bound on an isometric real line. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set Metric
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem real_riesz_kernel_dyadic_majorant {u : ℝ} (hu : 0 < u) (x y : ℝ) (hxy : x ≠ y) :
    rieszKernel u x y ≤ 1 + ∑' n : ℕ,
      (closedBall x (2*OAI.PlanarFalconer.energyScale n)).indicator
        (fun _ ↦ ENNReal.ofReal ((OAI.PlanarFalconer.energyScale n/2)^(-u))) y := by
  let X : Space 1 := EuclideanSpace.single 0 x
  let Y : Space 1 := EuclideanSpace.single 0 y
  have hXY : X ≠ Y := by
    intro h
    apply hxy
    have hh := congrArg (fun z : Space 1 ↦ z 0) h
    simpa [X,Y] using hh
  have h := euclidean_riesz_kernel_majorant X Y hu hXY
  have hleft : (edist X Y)^(-u) = rieszKernel u x y := by
    simp [X,Y,edist_dist,Real.dist_eq,rieszKernel]
  rw [hleft] at h
  apply h.trans
  apply add_le_add_right
  apply ENNReal.tsum_le_tsum
  intro n
  unfold euclideanEnergyMajorant
  by_cases hmem : Y∈ball X (2*OAI.PlanarFalconer.energyScale n)
  · have hreal : y∈closedBall x (2*OAI.PlanarFalconer.energyScale n) := by
      have hh := mem_ball.mp hmem
      have heq : dist Y X = dist y x := by simp [X,Y]
      exact mem_closedBall.mpr (by simpa only [heq] using hh.le)
    simp only [indicator_of_mem hmem,indicator_of_mem hreal,le_refl]
  · rw [indicator_of_notMem hmem]
    exact bot_le

theorem real_rieszEnergy_le_dyadic_pairMass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {u : ℝ} (hu : 0 < u) :
    rieszEnergy u μ ≤ 1 + ∑' n : ℕ,
      ENNReal.ofReal ((OAI.PlanarFalconer.energyScale n/2)^(-u)) *
        pairMass (2*OAI.PlanarFalconer.energyScale n) μ := by
  have hpot (x : ℝ) : (∫⁻ y, rieszKernel u x y ∂μ) ≤
      1 + ∑' n : ℕ, ENNReal.ofReal ((OAI.PlanarFalconer.energyScale n/2)^(-u)) *
        μ (closedBall x (2*OAI.PlanarFalconer.energyScale n)) := by
    have hxy : ∀ᵐ y ∂μ, x ≠ y := by
      rw [ae_iff]
      simp
    calc
      _ ≤ ∫⁻ y, 1 + ∑' n : ℕ,
          (closedBall x (2*OAI.PlanarFalconer.energyScale n)).indicator
            (fun _ ↦ ENNReal.ofReal ((OAI.PlanarFalconer.energyScale n/2)^(-u))) y ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hxy] with y hy
        exact real_riesz_kernel_dyadic_majorant hu x y hy
      _ = _ := by
        rw [lintegral_add_left measurable_const,
          lintegral_tsum (fun _ ↦ (measurable_const.indicator measurableSet_closedBall).aemeasurable)]
        simp only [lintegral_const,measure_univ,mul_one]
        congr 1
        apply tsum_congr
        intro n
        rw [lintegral_indicator measurableSet_closedBall,setLIntegral_const]
  calc
    _ ≤ ∫⁻ x, 1 + ∑' n : ℕ, ENNReal.ofReal ((OAI.PlanarFalconer.energyScale n/2)^(-u)) *
        μ (closedBall x (2*OAI.PlanarFalconer.energyScale n)) ∂μ := lintegral_mono hpot
    _ = _ := by
      rw [lintegral_add_left measurable_const,lintegral_tsum]
      · simp only [lintegral_const,measure_univ,mul_one]
        congr 1
        apply tsum_congr
        intro n
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rfl
      · intro n
        apply Measurable.aemeasurable
        apply Measurable.const_mul
        exact measurable_measure_prodMk_left (ν := μ)
          ((isClosed_le (by fun_prop : Continuous (fun p : ℝ×ℝ ↦ dist p.2 p.1))
            continuous_const).measurableSet)

theorem smoothEnergy_le_dyadic_pairMass (kernel : SmoothKernel) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {δ u : ℝ} (hδ : δ ≠ 0) (hu : 0 < u) :
    smoothEnergy kernel.law u δ μ ≤ 1 + ∑' n : ℕ,
      ENNReal.ofReal ((OAI.PlanarFalconer.energyScale n/2)^(-u)) *
        pairMass (2*OAI.PlanarFalconer.energyScale n) (smoothLaw kernel.law δ μ) := by
  have : IsProbabilityMeasure (smoothLaw kernel.law δ μ) := by unfold smoothLaw; infer_instance
  have : NullSingletonClass (smoothLaw kernel.law δ μ) := by
    rw [smoothLaw_eq_withDensity kernel μ hδ]
    infer_instance
  exact real_rieszEnergy_le_dyadic_pairMass _ hu

#print axioms real_riesz_kernel_dyadic_majorant
#print axioms real_rieszEnergy_le_dyadic_pairMass
#print axioms smoothEnergy_le_dyadic_pairMass
end OAI.Falconer
