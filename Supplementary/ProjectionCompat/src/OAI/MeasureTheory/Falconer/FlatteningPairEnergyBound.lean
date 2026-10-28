import OAI.MeasureTheory.Falconer.FlatteningDyadicEnergy

/-! Integrated pair nonconcentration suffices; no pointwise Frostman certificate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem exists_rieszEnergy_bound_of_pairMass_power {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ],
      ∀ D : ℝ, 0 ≤ D → (∀ r : ℝ, 0 < r → pairMass r μ ≤ ENNReal.ofReal (D*r^v)) →
      rieszEnergy u μ ≤ ENNReal.ofReal (1+C*D) := by
  let q : ℝ≥0∞ := ENNReal.ofReal ((1/2:ℝ)^(v-u))
  let A : ℝ≥0∞ := ENNReal.ofReal ((1/2:ℝ)^(-u)*2^v)*∑' n : ℕ, q^n
  have hq : q < 1 := ENNReal.ofReal_lt_one.mpr
    (Real.rpow_lt_one (by norm_num) (by norm_num) (sub_pos.mpr huv))
  have hA : A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (tsum_geometric_lt_top.mpr hq).ne
  let C : ℝ := A.toReal+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal hA]
    exact ENNReal.ofReal_le_ofReal (by dsimp [C]; linarith)
  refine ⟨C,hC,?_⟩
  intro μ _ _ D hD hpair
  have ht (n : ℕ) : ENNReal.ofReal ((OAI.PlanarFalconer.energyScale n/2)^(-u))*
      pairMass (2*OAI.PlanarFalconer.energyScale n) μ ≤ ENNReal.ofReal D *
        (ENNReal.ofReal ((1/2:ℝ)^(-u)*2^v) * q^n) := by
    calc
      _ ≤ ENNReal.ofReal ((OAI.PlanarFalconer.energyScale n/2)^(-u))*
          ENNReal.ofReal (D*(2*OAI.PlanarFalconer.energyScale n)^v) :=
        mul_le_mul_right (hpair _ (mul_pos (by norm_num) (OAI.PlanarFalconer.energyScale_pos n))) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg
          (div_nonneg (OAI.PlanarFalconer.energyScale_pos n).le (by norm_num)) _),
          OAI.PlanarFalconer.energy_scale_identity n u v D]
        dsimp [q]
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (1/2:ℝ)^(-u)*D*2^v),
          ENNReal.ofReal_pow (by positivity : 0 ≤ (1/2:ℝ)^(v-u)),
          ENNReal.ofReal_mul (by positivity : 0 ≤ (1/2:ℝ)^(-u)*D),
          ENNReal.ofReal_mul (by positivity : 0 ≤ (1/2:ℝ)^(-u)),
          ENNReal.ofReal_mul (by positivity : 0 ≤ (1/2:ℝ)^(-u))]
        ring
  calc
    rieszEnergy u μ ≤ 1 + ∑' n : ℕ, ENNReal.ofReal D *
        (ENNReal.ofReal ((1/2:ℝ)^(-u)*2^v)*q^n) :=
      (real_rieszEnergy_le_dyadic_pairMass μ hu).trans (add_le_add_right (ENNReal.tsum_le_tsum ht) 1)
    _ = 1 + ENNReal.ofReal D*A := by dsimp [A]; rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_left]
    _ ≤ 1 + ENNReal.ofReal D*ENNReal.ofReal C := add_le_add_right (mul_le_mul_right hAC _) _
    _ = _ := by rw [← ENNReal.ofReal_mul hD,← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1) (mul_nonneg hD hC.le)]; congr 1; ring

#print axioms exists_rieszEnergy_bound_of_pairMass_power
end OAI.Falconer
