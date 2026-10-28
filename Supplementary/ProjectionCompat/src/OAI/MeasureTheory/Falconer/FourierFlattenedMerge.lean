import OAI.MeasureTheory.Falconer.FourierPowerSupport
import OAI.MeasureTheory.Falconer.FourierScaledCaps

/-! A genuine unit-supported, energy-capped producer for the induction's merged factor. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem exists_uniform_normalized_flattening_packet (kernel : SmoothKernel) {α ε : ℝ}
    (hα : 0 < α) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∀ s t : ℝ, α ≤ s → α ≤ t → s+t < 1 →
      ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        UnitSupported μ → UnitSupported ν →
        smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-ε₀)) →
        smoothEnergy kernel.law t δ ν ≤ ENNReal.ofReal (δ^(-ε₀)) →
        let ρ := additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) (2^n)
        let R : ℝ := 4*((2^n:ℕ):ℝ)
        UnitSupported (ρ.map (fun x : ℝ ↦ x/R)) ∧
          smoothEnergy kernel.law (s+t) (δ/R) (ρ.map (fun x : ℝ ↦ x/R)) ≤
            ENNReal.ofReal ((δ/R)^(-ε)) := by
  obtain ⟨K,hK,hflat⟩ := OSS_original_energy_interior_flattening_uniform_K kernel hα
    (by positivity : 0 < ε/2)
  have hpower : ∀ m : ℕ, m ≤ (2:ℕ)^m := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [pow_succ]
      have hp : 0 < (2:ℕ)^m := by positivity
      omega
  let R : ℝ := 4*((2^K:ℕ):ℝ)
  have hR : 1 ≤ R := by
    have hp : 0 < (2:ℕ)^K := by positivity
    have hp' : (1:ℝ) ≤ ((2^K:ℕ):ℝ) := by exact_mod_cast hp
    calc
      (1:ℝ) ≤ 4*1 := by norm_num
      _ ≤ 4*((2^K:ℕ):ℝ) := mul_le_mul_of_nonneg_left hp' (by norm_num)
  obtain ⟨δp,hδp,hδp1,hpay⟩ := exists_normalized_input_energy_cap kernel hR hε
  refine ⟨K,by omega,?_⟩
  intro s t hαs hαt hst
  obtain ⟨ε₀,δ₁,hε₀,hδ₁,hδ₁1,henergy⟩ := hflat s t hαs hαt hst
  refine ⟨ε₀,min δ₁ δp,hε₀,lt_min hδ₁ hδp,(min_le_left _ _).trans hδ₁1,?_⟩
  intro δ hδ hδsmall μ ν _ _ hμU hνU hμE hνE ρ R'
  have : IsProbabilityMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  refine ⟨normalized_difference_product_power_unitSupported μ ν hμU hνU
    (k := (2:ℕ)^K) (by positivity),?_⟩
  exact hpay δ hδ (hδsmall.trans (min_le_right _ _)) ρ (s+t) hst.le
    (henergy δ hδ (hδsmall.trans (min_le_left _ _)) μ ν hμU hνU hμE hνE (2^K) (hpower K))

theorem norm_fourier_three_product_le_normalized_flattened_power (μ ν lawL : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure lawL]
    (ξ : ℝ) (n : ℕ) :
    let R : ℝ := 4*((2^n:ℕ):ℝ)
    ‖fourier ((μ ∗ₘ ν) ∗ₘ lawL) ξ‖^((2:ℕ)^(n+2)) ≤
      ‖fourier (((additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) (2^n)).map
        (fun x : ℝ ↦ x/R)) ∗ₘ lawL) (R*ξ)‖ := by
  intro R
  have : IsProbabilityMeasure (differenceLaw μ) := by unfold differenceLaw; infer_instance
  have : IsProbabilityMeasure (differenceLaw ν) := by unfold differenceLaw; infer_instance
  rw [fourier_mconv_normalization _ _ (by positivity : R ≠ 0)]
  exact norm_fourier_three_product_le_flattened_power μ ν lawL ξ n

#print axioms exists_uniform_normalized_flattening_packet
#print axioms norm_fourier_three_product_le_normalized_flattened_power
end OAI.Falconer

