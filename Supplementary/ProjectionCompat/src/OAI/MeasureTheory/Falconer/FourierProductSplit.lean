import OAI.MeasureTheory.Falconer.FourierFlattenedMerge

/-! Actual independent product laws under the coordinate split used in induction. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped BigOperators

theorem productLaw_finSucc {n : ℕ} (μ : Fin (n+1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)] :
    productLaw μ = (μ 0) ∗ₘ productLaw (fun j : Fin n ↦ μ j.succ) := by
  let S : (Fin (n+1) → ℝ) → ℝ×(Fin n → ℝ) := fun x ↦ (x 0,fun j ↦ x j.succ)
  have hS : Measurable S := by fun_prop
  have hp : (Measure.pi μ).map S = (μ 0).prod (Measure.pi (fun j : Fin n ↦ μ j.succ)) := by
    have h := (measurePreserving_piFinSuccAbove μ 0).map_eq
    have he : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ ℝ) 0 :
        (Fin (n+1) → ℝ) → ℝ×(Fin n → ℝ)) = S := by
      funext x
      apply Prod.ext
      · rfl
      · funext j
        rfl
    rw [he] at h
    simpa using h
  have hright : (μ 0).prod (productLaw (fun j : Fin n ↦ μ j.succ)) =
      ((μ 0).prod (Measure.pi (fun j : Fin n ↦ μ j.succ))).map
        (fun p : ℝ×(Fin n → ℝ) ↦ (p.1,∏ j, p.2 j)) := by
    have hm := Measure.map_prod_map (μ 0) (Measure.pi (fun j : Fin n ↦ μ j.succ))
      measurable_id (show Measurable (fun x : Fin n → ℝ ↦ ∏ j, x j) by fun_prop)
    rw [Measure.map_id] at hm
    convert hm using 1
    · rfl
    · congr 1
  rw [Measure.mconv,hright,← hp,Measure.map_map (by fun_prop) hS,
    Measure.map_map (by fun_prop) (by fun_prop)]
  unfold productLaw
  congr 1
  funext x
  simp [S,Function.comp_def,Fin.prod_univ_succ]

theorem productLaw_first_two {n : ℕ} (μ : Fin (n+2) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)] :
    productLaw μ = ((μ 0) ∗ₘ (μ 1)) ∗ₘ productLaw (fun j : Fin n ↦ μ j.succ.succ) := by
  rw [productLaw_finSucc,productLaw_finSucc,← Measure.mconv_assoc]
  rfl

#print axioms productLaw_finSucc
#print axioms productLaw_first_two
end OAI.Falconer
