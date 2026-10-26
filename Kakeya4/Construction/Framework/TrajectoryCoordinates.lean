import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Kakeya4.Construction.Framework.Trajectory

/-!
# Finite real coordinates for the two trajectory models

The scalar record has five real coefficients. The planar record has four two-dimensional
coefficient blocks, flattened in the order `(y₀₁,y₀₂,V₁,V₂,w₀₁,w₀₂,W₁,W₂)`. These are
measurable equivalences; transport of the canonical coefficient reference measure is handled
separately.
-/

set_option autoImplicit false

namespace Kakeya4.Framework

/-- Read scalar trajectory coefficients in the order `(y₀,V,w₀,w₁,w₂)`. -/
def scalarTrajectoryCoords (l : ScalarTrajectory) : Fin 5 → ℝ := fun i =>
  if i = 0 then l.y0 else if i = 1 then l.velocity else if i = 2 then l.w0
    else if i = 3 then l.w1 else l.w2

/-- Reconstruct a scalar trajectory from its five real coefficients. -/
def scalarTrajectoryOfCoords (x : Fin 5 → ℝ) : ScalarTrajectory :=
  { y0 := x 0, velocity := x 1, w0 := x 2, w1 := x 3, w2 := x 4 }

/-- The canonical scalar trajectory coefficient chart in `Fin 5 → ℝ`. -/
def scalarTrajectoryFinMeasurableEquiv : ScalarTrajectory ≃ᵐ (Fin 5 → ℝ) where
  toFun := scalarTrajectoryCoords
  invFun := scalarTrajectoryOfCoords
  left_inv := by intro l; cases l; rfl
  right_inv := by intro x; funext i; fin_cases i <;> simp [scalarTrajectoryCoords, scalarTrajectoryOfCoords]
  measurable_toFun := by
    have hc : Measurable ScalarTrajectory.coefficientEquiv := comap_measurable _
    have h0 : Measurable (fun l : ScalarTrajectory => l.y0) := by
      change Measurable (fun l => (ScalarTrajectory.coefficientEquiv l).1)
      exact measurable_fst.comp hc
    have h1 : Measurable (fun l : ScalarTrajectory => l.velocity) := by
      change Measurable (fun l => (ScalarTrajectory.coefficientEquiv l).2.1)
      exact measurable_fst.comp (measurable_snd.comp hc)
    have h2 : Measurable (fun l : ScalarTrajectory => l.w0) := by
      change Measurable (fun l => (ScalarTrajectory.coefficientEquiv l).2.2.1)
      exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hc))
    have h3 : Measurable (fun l : ScalarTrajectory => l.w1) := by
      change Measurable (fun l => (ScalarTrajectory.coefficientEquiv l).2.2.2.1)
      exact measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hc)))
    have h4 : Measurable (fun l : ScalarTrajectory => l.w2) := by
      change Measurable (fun l => (ScalarTrajectory.coefficientEquiv l).2.2.2.2)
      exact measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hc)))
    apply measurable_pi_iff.mpr
    intro i
    fin_cases i <;> simp [scalarTrajectoryCoords] <;> first
      | exact h0
      | exact h1
      | exact h2
      | exact h3
      | exact h4
  measurable_invFun := by
    rw [measurable_comap_iff]
    change Measurable (fun x : Fin 5 → ℝ => (x 0, (x 1, (x 2, (x 3, x 4)))))
    fun_prop

/-- Read planar trajectory coefficients in the manuscript's eight-coordinate order. -/
def planarTrajectoryCoords (l : PlanarTrajectory) : Fin 8 → ℝ := fun i =>
  match i.val with
  | 0 => l.y0 0
  | 1 => l.y0 1
  | 2 => l.velocity 0
  | 3 => l.velocity 1
  | 4 => l.w0 0
  | 5 => l.w0 1
  | 6 => l.wVelocity 0
  | _ => l.wVelocity 1

/-- Reconstruct the four planar coefficient vectors from eight real coordinates. -/
def planarTrajectoryOfCoords (x : Fin 8 → ℝ) : PlanarTrajectory :=
  { y0 := !₂[x 0, x 1]
    velocity := !₂[x 2, x 3]
    w0 := !₂[x 4, x 5]
    wVelocity := !₂[x 6, x 7] }

/-- The canonical planar trajectory coefficient chart in `Fin 8 → ℝ`. -/
def planarTrajectoryFinMeasurableEquiv : PlanarTrajectory ≃ᵐ (Fin 8 → ℝ) where
  toFun := planarTrajectoryCoords
  invFun := planarTrajectoryOfCoords
  left_inv := by
    intro l
    cases l with
    | mk y v w wv =>
        simp [planarTrajectoryCoords, planarTrajectoryOfCoords, PlanarTrajectory.mk.injEq]
        constructor
        · apply (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2)).injective
          funext j
          fin_cases j <;> simp [planarTrajectoryCoords, planarTrajectoryOfCoords]
        constructor
        · apply (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2)).injective
          funext j
          fin_cases j <;> simp [planarTrajectoryCoords, planarTrajectoryOfCoords]
        constructor
        · apply (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2)).injective
          funext j
          fin_cases j <;> simp [planarTrajectoryCoords, planarTrajectoryOfCoords]
        · apply (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2)).injective
          funext j
          fin_cases j <;> simp [planarTrajectoryCoords, planarTrajectoryOfCoords]
  right_inv := by
    intro x
    funext i
    fin_cases i <;> simp [planarTrajectoryCoords, planarTrajectoryOfCoords]
  measurable_toFun := by
    have hc : Measurable PlanarTrajectory.coefficientEquiv := comap_measurable _
    have hY : Measurable (fun l : PlanarTrajectory => l.y0) := by
      change Measurable (fun l => (PlanarTrajectory.coefficientEquiv l).1)
      exact measurable_fst.comp hc
    have hV : Measurable (fun l : PlanarTrajectory => l.velocity) := by
      change Measurable (fun l => (PlanarTrajectory.coefficientEquiv l).2.1)
      exact measurable_fst.comp (measurable_snd.comp hc)
    have hW : Measurable (fun l : PlanarTrajectory => l.w0) := by
      change Measurable (fun l => (PlanarTrajectory.coefficientEquiv l).2.2.1)
      exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hc))
    have hWV : Measurable (fun l : PlanarTrajectory => l.wVelocity) := by
      change Measurable (fun l => (PlanarTrajectory.coefficientEquiv l).2.2.2)
      exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hc))
    apply measurable_pi_iff.mpr
    intro i
    fin_cases i <;> simp [planarTrajectoryCoords] <;>
      first
      | exact Measurable.eval ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2)).continuous.measurable.comp hY)
      | exact Measurable.eval ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2)).continuous.measurable.comp hV)
      | exact Measurable.eval ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2)).continuous.measurable.comp hW)
      | exact Measurable.eval ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2)).continuous.measurable.comp hWV)
  measurable_invFun := by
    rw [measurable_comap_iff]
    change Measurable (fun x : Fin 8 → ℝ =>
      (!₂[x 0, x 1], (!₂[x 2, x 3], (!₂[x 4, x 5], !₂[x 6, x 7]))))
    fun_prop

/-- Version-indexed dimension of the finite real trajectory coefficient chart. -/
def trajectoryCoefficientDimension : ModelVersion → ℕ
  | .scalar => 5
  | .planar => 8

/-- The finite real coefficient chart for either manuscript model. -/
def trajectoryCoefficientFinMeasurableEquiv (v : ModelVersion) :
    Trajectory v ≃ᵐ (Fin (trajectoryCoefficientDimension v) → ℝ) := by
  cases v with
  | scalar => exact scalarTrajectoryFinMeasurableEquiv
  | planar => exact planarTrajectoryFinMeasurableEquiv

end Kakeya4.Framework
