import Kakeya4.Hard.AlgebraicGeometry.HiddenQuadratic
import Kakeya4.Hard.Analysis.PlanarRegionVolume
import Kakeya4.Hard.Analysis.QuadraticSliceVolume

/-! Tonelli and the quadratic hidden-coordinate estimate for the actual allowed region. -/

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace Kakeya4.Hard.EligibleFormula

def baseRegion (p : Parameters) (t : ℝ) : Set (Fin 2 → ℝ) :=
  {y | spatialEnergyValue p t (Fin.snoc y 0) ≤ p .K ^ 2}

theorem spatialEnergyValue_snoc (p : Parameters) (t : ℝ) (y : Fin 2 → ℝ) (w : ℝ) :
    spatialEnergyValue p t (Fin.snoc y w) = spatialEnergyValue p t (Fin.snoc y 0) := by
  simp only [spatialEnergyValue,Fin.snoc_castSucc]

theorem continuous_snoc : Continuous (fun z : (Fin 2 → ℝ) × ℝ => (Fin.snoc z.1 z.2 : Point)) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using continuous_snd
  · simpa only [Fin.snoc_castSucc,Function.comp_def] using (continuous_apply j).comp continuous_fst

theorem measurePreserving_snoc :
    MeasurePreserving (fun z : (Fin 2 → ℝ) × ℝ => (Fin.snoc z.1 z.2 : Point)) := by
  have hh := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)).symm _
  have hs := hh.comp (Measure.measurePreserving_swap (μ := (volume : Measure (Fin 2 → ℝ)))
    (ν := (volume : Measure ℝ)))
  convert hs using 1
  funext z
  change (Fin.snoc z.1 z.2 : Point) =
    (Fin.insertNth (α := fun _ : Fin 3 => ℝ) (Fin.last 2) z.2 z.1 : Point)
  simp only [Fin.insertNth_last]
  rfl

theorem measurableSet_baseRegion (p : Parameters) (t : ℝ) : MeasurableSet (baseRegion p t) := by
  have hh : Continuous (fun y : Fin 2 → ℝ => spatialEnergyValue p t (Fin.snoc y 0)) := by
    unfold spatialEnergyValue
    simp only [Fin.snoc_castSucc]
    fun_prop
  exact (isClosed_le hh continuous_const).measurableSet

theorem volume_allowedRegion_le_base (p : Parameters) (t : ℝ)
    (hε : 0 < p .K * p .thickness) (hB : 0 < p .invK) :
    volume (allowedRegion p t) ≤
      ENNReal.ofReal (4 * (p .K * p .thickness) / (p .invK / 32)) * volume (baseRegion p t) := by
  let A := {z : (Fin 2 → ℝ) × ℝ | Fin.snoc z.1 z.2 ∈ allowedRegion p t}
  have hA : MeasurableSet A := (measurableSet_allowedRegion p t).preimage continuous_snoc.measurable
  rw [← measurePreserving_snoc.measure_preimage (measurableSet_allowedRegion p t).nullMeasurableSet]
  change (volume.prod volume) A ≤ _
  rw [Measure.prod_apply hA]
  calc
    (∫⁻ y, volume (Prod.mk y ⁻¹' A)) ≤
        ∫⁻ y, (baseRegion p t).indicator
          (fun _ => ENNReal.ofReal (4 * (p .K * p .thickness) / (p .invK / 32))) y := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ baseRegion p t
      · rw [Set.indicator_of_mem hy]
        have hsub : Prod.mk y ⁻¹' A ⊆
            {w : ℝ | |(hiddenPolynomial p t y).coeff 2*w^2 +
              (hiddenPolynomial p t y).coeff 1*w + (hiddenPolynomial p t y).coeff 0| ≤ p .K*p .thickness ∧
              p .invK/32 ≤ |2*(hiddenPolynomial p t y).coeff 2*w + (hiddenPolynomial p t y).coeff 1|} := by
          intro w hw
          exact ⟨by simpa only [← hiddenPolynomial_eval_quadratic] using hw.2.1,
            by simpa only [← hiddenPolynomial_derivative_affine] using hw.2.2⟩
        exact (measure_mono hsub).trans (Kakeya4.quadratic_sublevel_volume_explicit _ _ _ _ _ hε (by positivity))
      · rw [Set.indicator_of_notMem hy]
        have he : Prod.mk y ⁻¹' A = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro w hw
          exact hy (by simpa only [baseRegion,mem_ofPred_eq,spatialEnergyValue_snoc] using hw.1)
        change volume (Prod.mk y ⁻¹' A) ≤ 0
        rw [he,measure_empty]
    _ = _ := lintegral_indicator_const (measurableSet_baseRegion p t) _

end Kakeya4.Hard.EligibleFormula
