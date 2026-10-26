import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Kakeya4.Construction.Framework.ExactSequence
import Kakeya4.Construction.Framework.Trajectory

/-!
# Discrete hidden-coordinate observations in §2

This file formalizes the hidden-bin payload at a fixed world, depth, and resolution. Requested
widths are rounded upward to origin-centered dyadic widths, with nesting proved through integer
quotients. It uses the half-open convention encoded by `Int.floor`. Density disintegration and
temperedness remain separate later interfaces.
-/

set_option autoImplicit false

namespace Kakeya4.Framework

/-- The integer exponent of the smallest power-of-two grid width not below a request. -/
noncomputable def dyadicWidthExponent (requestedWidth : ℝ) : ℤ :=
  Int.ceil (Real.logb 2 requestedWidth)

/-- The origin-centered dyadic grid width obtained by rounding a positive requested width up. -/
noncomputable def dyadicRoundedWidth (requestedWidth : ℝ) : ℝ :=
  Real.rpow 2 (dyadicWidthExponent requestedWidth : ℝ)

theorem requested_le_dyadicRoundedWidth (requestedWidth : ℝ) (hwidth : 0 < requestedWidth) :
    requestedWidth ≤ dyadicRoundedWidth requestedWidth := by
  have hrepr : Real.rpow 2 (Real.logb 2 requestedWidth) = requestedWidth :=
    Real.rpow_logb (by norm_num) (by norm_num) hwidth
  unfold dyadicRoundedWidth dyadicWidthExponent
  calc
    requestedWidth = Real.rpow 2 (Real.logb 2 requestedWidth) := hrepr.symm
    _ ≤ Real.rpow 2 (Int.ceil (Real.logb 2 requestedWidth) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.le_ceil _)

theorem dyadicRoundedWidth_le_two_mul_requested (requestedWidth : ℝ)
    (hwidth : 0 < requestedWidth) :
    dyadicRoundedWidth requestedWidth ≤ 2 * requestedWidth := by
  unfold dyadicRoundedWidth dyadicWidthExponent
  have hexp : (Int.ceil (Real.logb 2 requestedWidth) : ℝ) ≤ Real.logb 2 requestedWidth + 1 := by
    calc
      (Int.ceil (Real.logb 2 requestedWidth) : ℝ) ≤
          (Int.floor (Real.logb 2 requestedWidth) : ℝ) + 1 := by
            have hcast : (Int.ceil (Real.logb 2 requestedWidth) : ℝ) ≤
                ((Int.floor (Real.logb 2 requestedWidth) + 1 : ℤ) : ℝ) := by
              exact_mod_cast (Int.ceil_le_floor_add_one (Real.logb 2 requestedWidth))
            simpa [add_comm] using hcast
      _ ≤ Real.logb 2 requestedWidth + 1 := by
            have hfloor : (Int.floor (Real.logb 2 requestedWidth) : ℝ) ≤
                Real.logb 2 requestedWidth := Int.floor_le _
            linarith
  calc
    Real.rpow 2 (Int.ceil (Real.logb 2 requestedWidth) : ℝ) ≤
        Real.rpow 2 (Real.logb 2 requestedWidth + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = 2 * requestedWidth := by
      calc
        Real.rpow 2 (Real.logb 2 requestedWidth + 1) =
            Real.rpow 2 (Real.logb 2 requestedWidth) * Real.rpow 2 1 :=
          Real.rpow_add (by norm_num) _ _
        _ = 2 * requestedWidth := by
          change 2 ^ Real.logb 2 requestedWidth * 2 ^ (1 : ℝ) = 2 * requestedWidth
          rw [Real.rpow_one, Real.rpow_logb (by norm_num) (by norm_num) hwidth]
          ring

theorem dyadicRoundedWidth_mono {x y : ℝ} (hxy : x ≤ y) (hx : 0 < x) :
    dyadicRoundedWidth x ≤ dyadicRoundedWidth y := by
  unfold dyadicRoundedWidth dyadicWidthExponent
  have hlog : Real.logb 2 x ≤ Real.logb 2 y :=
    Real.logb_le_logb_of_le (by norm_num) hx hxy
  have hceil : Int.ceil (Real.logb 2 x) ≤ Int.ceil (Real.logb 2 y) := Int.ceil_mono hlog
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact_mod_cast hceil

theorem dyadicWidthExponent_mono {x y : ℝ} (hxy : x ≤ y) (hx : 0 < x) :
    dyadicWidthExponent x ≤ dyadicWidthExponent y := by
  unfold dyadicWidthExponent
  apply Int.ceil_mono
  exact Real.logb_le_logb_of_le (by norm_num) hx hxy

/-- Integer label of the half-open origin-centered cell of a dyadic grid. -/
noncomputable def dyadicGridBin (x : ℝ) (exponent : ℤ) : ℤ :=
  Int.floor (x / Real.rpow 2 (exponent : ℝ))

/-- A coarser dyadic grid label is the Euclidean quotient of the finer label. -/
theorem dyadicGridBin_coarsen {fine coarse : ℤ} (hlevel : fine ≤ coarse) (x : ℝ) :
    dyadicGridBin x coarse =
      dyadicGridBin x fine / (2 ^ (coarse - fine).toNat) := by
  let levelsApart : ℕ := (coarse - fine).toNat
  have hnonneg : 0 ≤ coarse - fine := sub_nonneg.mpr hlevel
  have hcastApart : (levelsApart : ℝ) = ((coarse - fine : ℤ) : ℝ) := by
    dsimp [levelsApart]
    exact_mod_cast (Int.toNat_of_nonneg hnonneg)
  have hexponent : (coarse : ℝ) = (fine : ℝ) + (levelsApart : ℝ) := by
    have hInt : fine + (coarse - fine) = coarse := by omega
    have hReal : (fine : ℝ) + ((coarse - fine : ℤ) : ℝ) = (coarse : ℝ) := by
      exact_mod_cast hInt
    rw [← hcastApart] at hReal
    linarith
  have hwidth : Real.rpow 2 (coarse : ℝ) =
      Real.rpow 2 (fine : ℝ) * ((2 ^ levelsApart : ℕ) : ℝ) := by
    have hnatPow : Real.rpow 2 (levelsApart : ℝ) = ((2 ^ levelsApart : ℕ) : ℝ) := by
      change (2 : ℝ) ^ (levelsApart : ℝ) = ((2 ^ levelsApart : ℕ) : ℝ)
      rw [Real.rpow_natCast]
      norm_cast
    calc
      Real.rpow 2 (coarse : ℝ) =
          Real.rpow 2 ((fine : ℝ) + (levelsApart : ℝ)) := by rw [hexponent]
      _ = Real.rpow 2 (fine : ℝ) * Real.rpow 2 (levelsApart : ℝ) :=
        Real.rpow_add (by norm_num) _ _
      _ = Real.rpow 2 (fine : ℝ) * ((2 ^ levelsApart : ℕ) : ℝ) := by rw [hnatPow]
  have hdenom : 0 < (2 ^ levelsApart : ℕ) := by positivity
  unfold dyadicGridBin
  rw [show x / Real.rpow 2 (coarse : ℝ) =
        (x / Real.rpow 2 (fine : ℝ)) / ((2 ^ levelsApart : ℕ) : ℝ) by
      rw [hwidth]
      field_simp]
  rw [Int.floor_div_natCast]
  rfl

/-- The rounded requested-width grids are nested: coarsening the request takes an integer
quotient of the finer cell label. -/
theorem dyadicGridBin_coarsen_of_requested {fineRequest coarseRequest : ℝ}
    (hrequest : fineRequest ≤ coarseRequest) (hfine : 0 < fineRequest) (x : ℝ) :
    dyadicGridBin x (dyadicWidthExponent coarseRequest) =
      dyadicGridBin x (dyadicWidthExponent fineRequest) /
        (2 ^ (dyadicWidthExponent coarseRequest -
          dyadicWidthExponent fineRequest).toNat) := by
  exact dyadicGridBin_coarsen
    (dyadicWidthExponent_mono hrequest hfine) x

/-- The hidden-bin label has one integer coordinate in v1 and two in v2. -/
def HiddenBin : ModelVersion → Type
  | .scalar => ℤ
  | .planar => Fin 2 → ℤ

instance instMeasurableSpaceCoordinate (v : ModelVersion) : MeasurableSpace (Coordinate v) := by
  cases v with
  | scalar => exact (inferInstance : MeasurableSpace ℝ)
  | planar => exact (inferInstance : MeasurableSpace E2)

instance instMeasurableSpaceHiddenBin (v : ModelVersion) : MeasurableSpace (HiddenBin v) := by
  cases v with
  | scalar => exact (inferInstance : MeasurableSpace ℤ)
  | planar => exact (inferInstance : MeasurableSpace (Fin 2 → ℤ))

private theorem measurable_scalar_y0 : Measurable (fun l : ScalarTrajectory => l.y0) := by
  have hcoeff : Measurable ScalarTrajectory.coefficientEquiv := comap_measurable _
  change Measurable (fun l => (ScalarTrajectory.coefficientEquiv l).1)
  exact measurable_fst.comp hcoeff

private theorem measurable_scalar_velocity :
    Measurable (fun l : ScalarTrajectory => l.velocity) := by
  have hcoeff : Measurable ScalarTrajectory.coefficientEquiv :=
    comap_measurable _
  change Measurable (fun l => (ScalarTrajectory.coefficientEquiv l).2.1)
  exact measurable_fst.comp (measurable_snd.comp hcoeff)

private theorem measurable_scalar_w0 : Measurable (fun l : ScalarTrajectory => l.w0) := by
  have hcoeff : Measurable ScalarTrajectory.coefficientEquiv :=
    comap_measurable _
  change Measurable (fun l => (ScalarTrajectory.coefficientEquiv l).2.2.1)
  exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hcoeff))

private theorem measurable_scalar_w1 : Measurable (fun l : ScalarTrajectory => l.w1) := by
  have hcoeff : Measurable ScalarTrajectory.coefficientEquiv :=
    comap_measurable _
  change Measurable (fun l => (ScalarTrajectory.coefficientEquiv l).2.2.2.1)
  exact measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hcoeff)))

private theorem measurable_scalar_w2 : Measurable (fun l : ScalarTrajectory => l.w2) := by
  have hcoeff : Measurable ScalarTrajectory.coefficientEquiv :=
    comap_measurable _
  change Measurable (fun l => (ScalarTrajectory.coefficientEquiv l).2.2.2.2)
  exact measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hcoeff)))

private theorem measurable_planar_y0 : Measurable (fun l : PlanarTrajectory => l.y0) := by
  have hcoeff : Measurable PlanarTrajectory.coefficientEquiv := comap_measurable _
  change Measurable (fun l => (PlanarTrajectory.coefficientEquiv l).1)
  exact measurable_fst.comp hcoeff

private theorem measurable_planar_velocity :
    Measurable (fun l : PlanarTrajectory => l.velocity) := by
  have hcoeff : Measurable PlanarTrajectory.coefficientEquiv := comap_measurable _
  change Measurable (fun l => (PlanarTrajectory.coefficientEquiv l).2.1)
  exact measurable_fst.comp (measurable_snd.comp hcoeff)

private theorem measurable_planar_w0 : Measurable (fun l : PlanarTrajectory => l.w0) :=
  by
    have hcoeff : Measurable PlanarTrajectory.coefficientEquiv := comap_measurable _
    change Measurable (fun l => (PlanarTrajectory.coefficientEquiv l).2.2.1)
    exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hcoeff))

private theorem measurable_planar_wVelocity :
    Measurable (fun l : PlanarTrajectory => l.wVelocity) := by
  have hcoeff : Measurable PlanarTrajectory.coefficientEquiv := comap_measurable _
  change Measurable (fun l => (PlanarTrajectory.coefficientEquiv l).2.2.2)
  exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hcoeff))

theorem spatialAt_joint_measurable (v : ModelVersion) :
    Measurable (fun p : Trajectory v × ℝ => spatialAt v p.1 p.2) := by
  cases v with
  | scalar =>
      change Measurable (fun p : ScalarTrajectory × ℝ => p.1.y0 + p.2 * p.1.velocity)
      exact Measurable.add
        (measurable_scalar_y0.comp measurable_fst)
        (Measurable.mul measurable_snd (measurable_scalar_velocity.comp measurable_fst))
  | planar =>
      change Measurable (fun p : PlanarTrajectory × ℝ => p.1.y0 + p.2 • p.1.velocity)
      exact Measurable.add
        (measurable_planar_y0.comp measurable_fst)
        (Measurable.smul measurable_snd (measurable_planar_velocity.comp measurable_fst))

theorem hiddenAt_joint_measurable (v : ModelVersion) :
    Measurable (fun p : Trajectory v × ℝ => hiddenAt v p.1 p.2) := by
  cases v with
  | scalar =>
      change Measurable (fun p : ScalarTrajectory × ℝ =>
        p.1.w0 + p.2 * p.1.w1 + p.2 ^ 2 * p.1.w2)
      exact Measurable.add
        (Measurable.add
          (measurable_scalar_w0.comp measurable_fst)
          (Measurable.mul measurable_snd (measurable_scalar_w1.comp measurable_fst)))
        (Measurable.mul (measurable_snd.pow_const 2)
          (measurable_scalar_w2.comp measurable_fst))
  | planar =>
      change Measurable (fun p : PlanarTrajectory × ℝ => p.1.w0 + p.2 • p.1.wVelocity)
      exact Measurable.add
        (measurable_planar_w0.comp measurable_fst)
        (Measurable.smul measurable_snd (measurable_planar_wVelocity.comp measurable_fst))

/-- The hidden-coordinate bin of width `width`, using half-open unit intervals after scaling. -/
noncomputable def hiddenBin : (v : ModelVersion) → Coordinate v → ℝ → HiddenBin v
  | .scalar, (x : ℝ), width => Int.floor (x / width)
  | .planar, (x : E2), width => fun i => Int.floor (x.ofLp i / width)

theorem hiddenBin_measurable (v : ModelVersion) (width : ℝ) :
    Measurable (fun x => hiddenBin v x width) := by
  cases v with
  | scalar =>
      change Measurable (fun x : ℝ => Int.floor (x / (width : ℝ)))
      exact Int.measurable_floor.comp (measurable_id.div_const width)
  | planar =>
      change Measurable (fun x : E2 => fun i => Int.floor (x.ofLp i / width))
      apply Measurable.of_eval
      intro i
      have hcoord : Measurable (fun x : E2 => x.ofLp i) :=
        (measurable_pi_apply i).comp
          (WithLp.measurable_ofLp 2 (Fin 2 → ℝ))
      exact Int.measurable_floor.comp (hcoord.div_const width)

/-- Complete discrete observation payload at one fixed world, depth, and resolution. -/
def ObservationData (v : ModelVersion) (worldCount : ℕ) :=
  Fin worldCount × ℝ × Coordinate v × HiddenBin v

instance instMeasurableSpaceObservationData (v : ModelVersion) (worldCount : ℕ) :
    MeasurableSpace (ObservationData v worldCount) := by
  letI : MeasurableSpace (Fin worldCount) := ⊤
  cases v with
  | scalar =>
      change MeasurableSpace (Fin worldCount × ℝ × ℝ × ℤ)
      infer_instance
  | planar =>
      change MeasurableSpace (Fin worldCount × ℝ × E2 × (Fin 2 → ℤ))
      infer_instance

/-- The observation payload from manuscript label `a01:observation`: world, time, spatial point,
and the hidden-coordinate bin at the requested width `a_r / B_γ`, rounded upward to its nested
dyadic grid within a factor of two. -/
noncomputable def observationAt (v : ModelVersion) {worldCount : ℕ}
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin worldCount → VersionWorldData v)
    (γ : Fin worldCount) (trajectory : Trajectory v) (t : ℝ) : ObservationData v worldCount :=
  (γ, t, spatialAt v trajectory t,
    hiddenBin v (hiddenAt v trajectory t)
      (dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale v (worldData γ))))

theorem observationAt_measurable (v : ModelVersion) {worldCount : ℕ}
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin worldCount → VersionWorldData v) (γ : Fin worldCount) :
    Measurable (fun p : Trajectory v × ℝ =>
      observationAt v seq depth n worldData γ p.1 p.2) := by
  letI : MeasurableSpace (Fin worldCount) := ⊤
  cases v with
  | scalar =>
      let width := dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale .scalar (worldData γ))
      change Measurable (fun p : ScalarTrajectory × ℝ =>
        (γ, p.2, spatialAt .scalar p.1 p.2,
          hiddenBin .scalar (hiddenAt .scalar p.1 p.2) width))
      exact Measurable.prodMk measurable_const
        (Measurable.prodMk measurable_snd
          (Measurable.prodMk (spatialAt_joint_measurable .scalar)
            ((hiddenBin_measurable .scalar width).comp
              (hiddenAt_joint_measurable .scalar))))
  | planar =>
      let width := dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale .planar (worldData γ))
      change Measurable (fun p : PlanarTrajectory × ℝ =>
        (γ, p.2, spatialAt .planar p.1 p.2,
          hiddenBin .planar (hiddenAt .planar p.1 p.2) width))
      exact Measurable.prodMk measurable_const
        (Measurable.prodMk measurable_snd
          (Measurable.prodMk (spatialAt_joint_measurable .planar)
            ((hiddenBin_measurable .planar width).comp
              (hiddenAt_joint_measurable .planar))))

theorem observation_requested_width_pos (v : ModelVersion) {worldCount : ℕ}
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin worldCount → VersionWorldData v) (γ : Fin worldCount) :
    0 < seq.depthScale depth n / worldDerivativeScale v (worldData γ) := by
  apply div_pos (seq.depthScale_pos depth n)
  cases v with
  | scalar => norm_num [worldDerivativeScale]
  | planar => exact (worldData γ).derivativeScale_pos

theorem observation_bin_width_pos (v : ModelVersion) {worldCount : ℕ}
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin worldCount → VersionWorldData v) (γ : Fin worldCount) :
    0 < dyadicRoundedWidth
      (seq.depthScale depth n / worldDerivativeScale v (worldData γ)) := by
  exact lt_of_lt_of_le (observation_requested_width_pos v seq depth n worldData γ)
    (requested_le_dyadicRoundedWidth _ (observation_requested_width_pos v seq depth n worldData γ))

theorem observation_dyadic_bin_width_bounds (v : ModelVersion) {worldCount : ℕ}
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin worldCount → VersionWorldData v) (γ : Fin worldCount) :
    seq.depthScale depth n / worldDerivativeScale v (worldData γ) ≤
        dyadicRoundedWidth
          (seq.depthScale depth n / worldDerivativeScale v (worldData γ)) ∧
      dyadicRoundedWidth
          (seq.depthScale depth n / worldDerivativeScale v (worldData γ)) ≤
        2 * (seq.depthScale depth n / worldDerivativeScale v (worldData γ)) := by
  have hpos := observation_requested_width_pos v seq depth n worldData γ
  exact ⟨requested_le_dyadicRoundedWidth _ hpos,
    dyadicRoundedWidth_le_two_mul_requested _ hpos⟩

end Kakeya4.Framework
