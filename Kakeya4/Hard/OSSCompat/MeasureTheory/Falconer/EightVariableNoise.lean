






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.EightVariableFrostmanLargeImage

/-! Actual eight-coordinate smoothing error, reusing the proved six-variable
projection error twice with the same four noisy parameters. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

def eightAnchorTuple (w : Fin 8 → ℝ) : Fin 6 → ℝ := ![w 0,w 1,w 2,w 3,w 4,w 5]
def eightTargetTuple (w : Fin 8 → ℝ) : Fin 6 → ℝ := ![w 0,w 1,w 2,w 3,w 6,w 7]

theorem eight_bilinear_anchor_target (w : Fin 8 → ℝ) :
    eightBilinearValue w = projectionValue (eightAnchorTuple w)-projectionValue (eightTargetTuple w) := by
  simp [eightBilinearValue,projectionValue,eightAnchorTuple,eightTargetTuple]
  ring

theorem eight_bilinear_noisyHalf_error (w u : Fin 8 → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hw : ∀ i, |w i| ≤ 1) (hu : ∀ i, |u i| ≤ 1) :
    |eightBilinearValue (fun i ↦ noisyHalf r (w i) (u i))-eightBilinearValue w/4| ≤ 8*r := by
  have hwA : ∀ i, |eightAnchorTuple w i| ≤ 1 := by intro i; fin_cases i <;> exact hw _
  have hwT : ∀ i, |eightTargetTuple w i| ≤ 1 := by intro i; fin_cases i <;> exact hw _
  have huA : ∀ i, |eightAnchorTuple u i| ≤ 1 := by intro i; fin_cases i <;> exact hu _
  have huT : ∀ i, |eightTargetTuple u i| ≤ 1 := by intro i; fin_cases i <;> exact hu _
  have heA : eightAnchorTuple (fun i ↦ noisyHalf r (w i) (u i)) =
      (fun i ↦ noisyHalf r (eightAnchorTuple w i) (eightAnchorTuple u i)) := by
    funext i; fin_cases i <;> rfl
  have heT : eightTargetTuple (fun i ↦ noisyHalf r (w i) (u i)) =
      (fun i ↦ noisyHalf r (eightTargetTuple w i) (eightTargetTuple u i)) := by
    funext i; fin_cases i <;> rfl
  have hA := projectionValue_noisyHalf_error (eightAnchorTuple w) (eightAnchorTuple u) hr hr1 hwA huA
  have hT := projectionValue_noisyHalf_error (eightTargetTuple w) (eightTargetTuple u) hr hr1 hwT huT
  rw [← heA] at hA
  rw [← heT] at hT
  rw [eight_bilinear_anchor_target,eight_bilinear_anchor_target]
  have he : projectionValue (eightAnchorTuple (fun i ↦ noisyHalf r (w i) (u i)))-
      projectionValue (eightTargetTuple (fun i ↦ noisyHalf r (w i) (u i)))-
      (projectionValue (eightAnchorTuple w)-projectionValue (eightTargetTuple w))/4 =
      (projectionValue (eightAnchorTuple (fun i ↦ noisyHalf r (w i) (u i)))-projectionValue (eightAnchorTuple w)/4)-
      (projectionValue (eightTargetTuple (fun i ↦ noisyHalf r (w i) (u i)))-projectionValue (eightTargetTuple w)/4) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

#print axioms eight_bilinear_anchor_target
#print axioms eight_bilinear_noisyHalf_error
end OAI.Falconer
