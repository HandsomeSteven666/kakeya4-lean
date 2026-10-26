import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Kakeya4.Construction.Framework.Trajectory

/-!
# Translation in the observed spatial coordinate

For fixed time and velocity, the change from the trajectory base point `y₀` to `y(t)` is a
translation. This module isolates that measure-preserving step. It does not yet prove the joint
change of variables in all trajectory coefficients or the observation density decomposition.
-/

set_option autoImplicit false

namespace Kakeya4.Framework

open MeasureTheory

/-- Translation preserves any measure already known to be right-translation invariant. -/
theorem measurePreserving_add_const_of_isAddRightInvariant
    {α : Type*} [MeasurableSpace α] [Add α] [MeasurableAdd₂ α]
    (μ : Measure α) [Measure.IsAddRightInvariant μ] (c : α) :
    MeasurePreserving (fun x : α => x + c) μ μ := by
  exact ⟨Measurable.add measurable_id measurable_const,
    Measure.IsAddRightInvariant.map_add_right_eq_self c⟩

/-- In the scalar model, at fixed time and velocity the base-point coordinate change
`y₀ ↦ y₀ + tV` preserves Lebesgue measure. -/
theorem scalar_spatialCoordinate_change_measurePreserving (t velocity : ℝ) :
    MeasurePreserving (fun y₀ : ℝ => y₀ + t * velocity) volume volume := by
  exact measurePreserving_add_const_of_isAddRightInvariant volume (t * velocity)

/-- In the planar model, at fixed time and velocity the two-dimensional base-point coordinate
change `y₀ ↦ y₀ + t • V` preserves Euclidean Lebesgue measure. -/
theorem planar_spatialCoordinate_change_measurePreserving (t : ℝ) (velocity : E2) :
    MeasurePreserving (fun y₀ : E2 => y₀ + t • velocity) volume volume := by
  exact measurePreserving_add_const_of_isAddRightInvariant volume (t • velocity)

/-- A coordinate shear of finite-dimensional coefficient space preserves product Lebesgue
measure. This is the full-coefficient analogue of translating `y₀` after freezing velocity:
the velocity coordinate remains variable and is sheared into the base coordinate. -/
theorem coordinateShear_measurePreserving {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (c : ℝ) :
    MeasurePreserving (fun x : ι → ℝ => Function.update x i (x i + c * x j)) volume volume := by
  let shear : Matrix.TransvectionStruct ι ℝ := ⟨i, j, hij, c⟩
  have hfun :
      (fun x : ι → ℝ => Function.update x i (x i + c * x j)) =
        Matrix.toLin' shear.toMatrix := by
    funext x
    ext k
    by_cases hki : k = i
    · subst k
      simp [shear, Matrix.toLin'_apply, Matrix.TransvectionStruct.toMatrix,
        Matrix.transvection, Matrix.single_mulVec]
    · simp [shear, hki, Matrix.toLin'_apply, Matrix.TransvectionStruct.toMatrix,
        Matrix.transvection, Matrix.single_mulVec]
  rw [hfun]
  exact Real.volume_preserving_transvectionStruct shear

/-- The full five-coordinate scalar trajectory shear preserves coefficient-space Lebesgue
measure. Coordinates are ordered `(y₀, V, w₀, w₁, w₂)` as in
`ScalarTrajectory.coefficientEquiv`. -/
theorem scalarTrajectoryCoefficientShear_measurePreserving (t : ℝ) :
    MeasurePreserving
      (fun coeff : Fin 5 → ℝ => Function.update coeff 0 (coeff 0 + t * coeff 1)) volume volume := by
  exact coordinateShear_measurePreserving 0 1 (by decide) t

/-- The full eight-coordinate planar trajectory shear preserves coefficient-space Lebesgue
measure. Coordinates are ordered `(y₀₁,y₀₂,V₁,V₂,w₀₁,w₀₂,W₁,W₂)`; the two spatial
coordinates are updated by two commuting transvections. -/
theorem planarTrajectoryCoefficientShear_measurePreserving (t : ℝ) :
    MeasurePreserving
      (fun coeff : Fin 8 → ℝ =>
        Function.update (Function.update coeff 0 (coeff 0 + t * coeff 2))
          1 (coeff 1 + t * coeff 3)) volume volume := by
  let shear₀ : (Fin 8 → ℝ) → (Fin 8 → ℝ) :=
    fun coeff => Function.update coeff 0 (coeff 0 + t * coeff 2)
  let shear₁ : (Fin 8 → ℝ) → (Fin 8 → ℝ) :=
    fun coeff => Function.update coeff 1 (coeff 1 + t * coeff 3)
  have h₀ := coordinateShear_measurePreserving (i := (0 : Fin 8)) (j := 2) (by decide) t
  have h₁ := coordinateShear_measurePreserving (i := (1 : Fin 8)) (j := 3) (by decide) t
  have hcomp := h₁.comp h₀
  have heq :
      (fun coeff : Fin 8 → ℝ =>
        Function.update (Function.update coeff 0 (coeff 0 + t * coeff 2))
          1 (coeff 1 + t * coeff 3)) = shear₁ ∘ shear₀ := by
    funext coeff i
    fin_cases i <;> simp [shear₀, shear₁]
  rw [heq]
  exact hcomp

/-- If each fiber map is a translation, translating the first coordinate by an amount
depending measurably on the second coordinate preserves the product measure. -/
theorem measurePreserving_fiberwise_add_shift_prod
    {α Y : Type*} [MeasurableSpace α] [MeasurableSpace Y] [Add Y]
    [MeasurableAdd₂ Y] (μ : Measure α) (ν : Measure Y) [SFinite μ] [SFinite ν]
    [Measure.IsAddRightInvariant ν] (shift : α → Y) (hshift : Measurable shift) :
    MeasurePreserving (fun z : Y × α => (z.1 + shift z.2, z.2)) (ν.prod μ) (ν.prod μ) := by
  have hskew : MeasurePreserving
      (fun z : α × Y => (z.1, z.2 + shift z.1)) (μ.prod ν) (μ.prod ν) := by
    refine MeasurePreserving.skew_product (μa := μ) (μb := μ) (μc := ν)
      (μd := ν) (f := id) (g := fun a y => y + shift a)
      (MeasurePreserving.id μ) ?_ ?_
    · exact (measurable_snd.add (hshift.comp measurable_fst))
    · filter_upwards with a
      exact (measurePreserving_add_const_of_isAddRightInvariant ν (shift a)).map_eq
  have hswap := (Measure.measurePreserving_swap (μ := ν) (ν := μ))
  have hswapBack := (Measure.measurePreserving_swap (μ := μ) (ν := ν))
  have h := hswapBack.comp (hskew.comp hswap)
  have heq : (fun z : Y × α => (z.1 + shift z.2, z.2)) =
      fun z => Prod.swap ((Prod.swap z).1, (Prod.swap z).2 + shift (Prod.swap z).1) := by
    funext z
    rfl
  rw [heq]
  exact h

/-- Product Lebesgue measure in the nested scalar coefficient order. -/
noncomputable def scalarNestedCoefficientMeasure :
    Measure (ℝ × (ℝ × (ℝ × (ℝ × ℝ)))) := by
  let μ : Measure ℝ := volume
  exact μ.prod (μ.prod (μ.prod (μ.prod μ)))

/-- Product Euclidean volume in the nested planar coefficient order. -/
noncomputable def planarNestedCoefficientMeasure :
    Measure (E2 × (E2 × (E2 × E2))) := by
  let μ : Measure E2 := volume
  exact μ.prod (μ.prod (μ.prod μ))

/-- The canonical product-Lebesgue measure on scalar records, transported through
`ScalarTrajectory.coefficientEquiv`. -/
noncomputable def ScalarTrajectory.coefficientProductMeasure : Measure ScalarTrajectory :=
  scalarNestedCoefficientMeasure.map ScalarTrajectory.coefficientEquiv.symm

/-- The canonical product-Euclidean measure on planar records, transported through
`PlanarTrajectory.coefficientEquiv`. -/
noncomputable def PlanarTrajectory.coefficientProductMeasure : Measure PlanarTrajectory :=
  planarNestedCoefficientMeasure.map PlanarTrajectory.coefficientEquiv.symm

/-- The scalar coefficient shear in the exact nested product order used by
`ScalarTrajectory.coefficientEquiv`. -/
theorem scalarNestedTrajectoryCoefficientShear_measurePreserving (t : ℝ) :
    MeasurePreserving
      (fun coeff : ℝ × (ℝ × (ℝ × (ℝ × ℝ))) =>
        (coeff.1 + t * coeff.2.1, coeff.2))
      (scalarNestedCoefficientMeasure) (scalarNestedCoefficientMeasure) := by
  exact measurePreserving_fiberwise_add_shift_prod
    ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))))
    (volume : Measure ℝ)
    (fun coeff : ℝ × (ℝ × (ℝ × ℝ)) => t * coeff.1) (by fun_prop)

/-- The planar coefficient shear in the exact nested product order used by
`PlanarTrajectory.coefficientEquiv`. -/
theorem planarNestedTrajectoryCoefficientShear_measurePreserving (t : ℝ) :
    MeasurePreserving
      (fun coeff : E2 × (E2 × (E2 × E2)) =>
        (coeff.1 + t • coeff.2.1, coeff.2))
      (planarNestedCoefficientMeasure) (planarNestedCoefficientMeasure) := by
  exact measurePreserving_fiberwise_add_shift_prod
    ((volume : Measure E2).prod ((volume : Measure E2).prod (volume : Measure E2)))
    (volume : Measure E2)
    (fun coeff : E2 × (E2 × E2) => t • coeff.1) (by fun_prop)

/-- The scalar trajectory base-point shear preserves the canonical product measure on records. -/
theorem scalarTrajectoryRecordShear_measurePreserving (t : ℝ) :
    MeasurePreserving
      (fun l : ScalarTrajectory => { l with y0 := l.y0 + t * l.velocity })
      ScalarTrajectory.coefficientProductMeasure ScalarTrajectory.coefficientProductMeasure := by
  let e : ScalarTrajectory ≃ᵐ ℝ × (ℝ × (ℝ × (ℝ × ℝ))) :=
    { toEquiv := ScalarTrajectory.coefficientEquiv
      measurable_toFun := comap_measurable _
      measurable_invFun := by
        rw [measurable_comap_iff]
        simpa using (measurable_id : Measurable (id : ℝ × (ℝ × (ℝ × (ℝ × ℝ))) → _)) }
  have hcoord : MeasurePreserving e.symm
      scalarNestedCoefficientMeasure ScalarTrajectory.coefficientProductMeasure := by
    exact ⟨e.symm.measurable, rfl⟩
  have hcoordBack : MeasurePreserving e
      ScalarTrajectory.coefficientProductMeasure scalarNestedCoefficientMeasure :=
    MeasurePreserving.symm e.symm hcoord
  have hcompose := hcoord.comp
    (scalarNestedTrajectoryCoefficientShear_measurePreserving t |>.comp hcoordBack)
  have hfun :
      (e.symm ∘
        (fun coeff : ℝ × (ℝ × (ℝ × (ℝ × ℝ))) =>
          (coeff.1 + t * coeff.2.1, coeff.2)) ∘ e) =
        (fun l : ScalarTrajectory => { l with y0 := l.y0 + t * l.velocity }) := by
    funext l
    cases l
    rfl
  rw [hfun] at hcompose
  exact hcompose

/-- The planar trajectory base-point shear preserves the canonical product measure on records. -/
theorem planarTrajectoryRecordShear_measurePreserving (t : ℝ) :
    MeasurePreserving
      (fun l : PlanarTrajectory => { l with y0 := l.y0 + t • l.velocity })
      PlanarTrajectory.coefficientProductMeasure PlanarTrajectory.coefficientProductMeasure := by
  let e : PlanarTrajectory ≃ᵐ E2 × (E2 × (E2 × E2)) :=
    { toEquiv := PlanarTrajectory.coefficientEquiv
      measurable_toFun := comap_measurable _
      measurable_invFun := by
        rw [measurable_comap_iff]
        simpa using (measurable_id : Measurable (id : E2 × (E2 × (E2 × E2)) → _)) }
  have hcoord : MeasurePreserving e.symm
      planarNestedCoefficientMeasure PlanarTrajectory.coefficientProductMeasure := by
    exact ⟨e.symm.measurable, rfl⟩
  have hcoordBack : MeasurePreserving e
      PlanarTrajectory.coefficientProductMeasure planarNestedCoefficientMeasure :=
    MeasurePreserving.symm e.symm hcoord
  have hcompose := hcoord.comp
    (planarNestedTrajectoryCoefficientShear_measurePreserving t |>.comp hcoordBack)
  have hfun :
      (e.symm ∘
        (fun coeff : E2 × (E2 × (E2 × E2)) =>
          (coeff.1 + t • coeff.2.1, coeff.2)) ∘ e) =
        (fun l : PlanarTrajectory => { l with y0 := l.y0 + t • l.velocity }) := by
    funext l
    cases l
    rfl
  rw [hfun] at hcompose
  exact hcompose

end Kakeya4.Framework
