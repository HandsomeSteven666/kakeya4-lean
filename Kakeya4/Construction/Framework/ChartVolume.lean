import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Kakeya4.Construction.Framework.CoordinateChange
import Kakeya4.Construction.Framework.PriorDensity
import Kakeya4.Construction.Framework.TrajectoryCoordinates

/-!
# Measure transport for finite trajectory coefficient charts

The finite-coordinate charts are measurable equivalences by themselves. This file records the
additional measure-preserving proofs for the scalar and planar charts; mere measurability is not
used as a substitute for a Jacobian calculation.
-/

set_option autoImplicit false

namespace Kakeya4.Framework

open MeasureTheory

/-- The first step of the right-associated finite-Pi decomposition. -/
private theorem piFinSuccAbove_zero_measurePreserving {n : ℕ} :
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
      (volume : Measure (Fin (n + 1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
  have h := MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))
  simpa only [Measure.volume_eq_prod] using h

/-- Split the first coordinate and recursively flatten the remaining finite Pi; all stages retain
the explicit product measure and hence compose without guessing a Jacobian. -/
private theorem piFinSuccAbove_zero_trans_measurePreserving
    {n : ℕ} {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (e : (Fin n → ℝ) ≃ᵐ α)
    (he : MeasurePreserving e (volume : Measure (Fin n → ℝ)) μ) :
    MeasurePreserving
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) e))
      (volume : Measure (Fin (n + 1) → ℝ)) ((volume : Measure ℝ).prod μ) := by
  let split : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hsplit := piFinSuccAbove_zero_measurePreserving (n := n)
  have hprod : MeasurePreserving
      (Prod.map id e)
      (volume : Measure (ℝ × (Fin n → ℝ))) ((volume : Measure ℝ).prod μ) := by
    have h := MeasurePreserving.prod
      (MeasureTheory.MeasurePreserving.id (volume : Measure ℝ)) he
    simpa only [Measure.volume_eq_prod] using h
  have hcomp := hprod.comp hsplit
  have hfun :
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) e) :
          (Fin (n + 1) → ℝ) → ℝ × α) = Prod.map id e ∘ split := by
    funext x
    rfl
  rw [hfun]
  exact hcomp

/-- Coordinates `(x₀,x₁)` in right-associated product order. -/
private def finTwoRealPiEquiv : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)))

/-- Coordinates `(x₀,(x₁,x₂))` in right-associated product order. -/
private def finThreeRealPiEquiv : (Fin 3 → ℝ) ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) finTwoRealPiEquiv)

/-- Coordinates `(x₀,(x₁,(x₂,x₃)))` in right-associated product order. -/
private def finFourRealPiEquiv : (Fin 4 → ℝ) ≃ᵐ ℝ × (ℝ × (ℝ × ℝ)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) finThreeRealPiEquiv)

/-- The manuscript order `(y₀,V,w₀,w₁,w₂)` as a right-associated product. -/
private def finFiveRealPiEquiv : (Fin 5 → ℝ) ≃ᵐ ℝ × (ℝ × (ℝ × (ℝ × ℝ))) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) finFourRealPiEquiv)

private theorem finOneRealPiEquiv_measurePreserving :
    MeasurePreserving (MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ))
      (volume : Measure (Fin 1 → ℝ)) (volume : Measure ℝ) :=
  MeasureTheory.volume_preserving_piUnique (fun _ : Fin 1 => ℝ)

private theorem finTwoRealPiEquiv_measurePreserving :
    MeasurePreserving finTwoRealPiEquiv (volume : Measure (Fin 2 → ℝ))
      ((volume : Measure ℝ).prod volume) :=
  piFinSuccAbove_zero_trans_measurePreserving (μ := volume)
    (MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ))
    finOneRealPiEquiv_measurePreserving

private theorem finThreeRealPiEquiv_measurePreserving :
    MeasurePreserving finThreeRealPiEquiv (volume : Measure (Fin 3 → ℝ))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)) :=
  piFinSuccAbove_zero_trans_measurePreserving (μ := (volume : Measure (ℝ × ℝ)))
    finTwoRealPiEquiv finTwoRealPiEquiv_measurePreserving

private theorem finFourRealPiEquiv_measurePreserving :
    MeasurePreserving finFourRealPiEquiv (volume : Measure (Fin 4 → ℝ))
      ((volume : Measure ℝ).prod
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume))) :=
  piFinSuccAbove_zero_trans_measurePreserving
    (μ := (volume : Measure (ℝ × (ℝ × ℝ))))
    finThreeRealPiEquiv finThreeRealPiEquiv_measurePreserving

/-- The canonical `Fin 5` chart pushes standard Pi volume to the nested scalar product measure. -/
private theorem finFiveRealPiEquiv_measurePreserving :
    MeasurePreserving finFiveRealPiEquiv (volume : Measure (Fin 5 → ℝ))
      scalarNestedCoefficientMeasure := by
  have h := piFinSuccAbove_zero_trans_measurePreserving
    (μ := (volume : Measure (ℝ × (ℝ × (ℝ × ℝ)))))
    finFourRealPiEquiv finFourRealPiEquiv_measurePreserving
  simpa [finFiveRealPiEquiv, finFourRealPiEquiv, finThreeRealPiEquiv,
    finTwoRealPiEquiv, scalarNestedCoefficientMeasure, Measure.volume_eq_prod] using h

/-- Coordinates `(x₀,…,x₅)` in right-associated product order. -/
private abbrev RealNested4 := ℝ × (ℝ × (ℝ × ℝ))
private abbrev RealNested5 := ℝ × (ℝ × (ℝ × (ℝ × ℝ)))
private abbrev RealNested6 := ℝ × (ℝ × (ℝ × (ℝ × (ℝ × ℝ))))
private abbrev RealNested7 := ℝ × (ℝ × (ℝ × (ℝ × (ℝ × (ℝ × ℝ)))))
private abbrev RealNested8 := ℝ × (ℝ × (ℝ × (ℝ × (ℝ × (ℝ × (ℝ × ℝ))))))

private def finSixRealPiEquiv :
    (Fin 6 → ℝ) ≃ᵐ RealNested6 :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 6 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) finFiveRealPiEquiv)

/-- Coordinates `(x₀,…,x₆)` in right-associated product order. -/
private def finSevenRealPiEquiv :
    (Fin 7 → ℝ) ≃ᵐ RealNested7 :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 7 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) finSixRealPiEquiv)

/-- Coordinates `(x₀,…,x₇)` in right-associated product order. -/
private def finEightRealPiEquiv :
    (Fin 8 → ℝ) ≃ᵐ RealNested8 :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 8 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) finSevenRealPiEquiv)

private theorem finSixRealPiEquiv_measurePreserving :
    MeasurePreserving finSixRealPiEquiv (volume : Measure (Fin 6 → ℝ))
      (volume : Measure RealNested6) := by
  have hFive : MeasurePreserving finFiveRealPiEquiv (volume : Measure (Fin 5 → ℝ))
      (volume : Measure RealNested5) := by
    simpa [scalarNestedCoefficientMeasure, Measure.volume_eq_prod] using
      finFiveRealPiEquiv_measurePreserving
  let μ : Measure RealNested5 := volume
  have h := piFinSuccAbove_zero_trans_measurePreserving
    (μ := μ) finFiveRealPiEquiv hFive
  simpa [finSixRealPiEquiv, μ, RealNested6, Measure.volume_eq_prod] using h

private theorem finSevenRealPiEquiv_measurePreserving :
    MeasurePreserving finSevenRealPiEquiv (volume : Measure (Fin 7 → ℝ))
      (volume : Measure RealNested7) := by
  let μ : Measure RealNested6 := volume
  have h := piFinSuccAbove_zero_trans_measurePreserving
    (μ := μ)
    finSixRealPiEquiv finSixRealPiEquiv_measurePreserving
  simpa [finSevenRealPiEquiv, finSixRealPiEquiv, μ, RealNested6, RealNested7,
    Measure.volume_eq_prod] using h

private theorem finEightRealPiEquiv_measurePreserving :
    MeasurePreserving finEightRealPiEquiv (volume : Measure (Fin 8 → ℝ))
      (volume : Measure RealNested8) := by
  let μ : Measure RealNested7 := volume
  have h := piFinSuccAbove_zero_trans_measurePreserving
    (μ := μ)
    finSevenRealPiEquiv finSevenRealPiEquiv_measurePreserving
  simpa [finEightRealPiEquiv, finSevenRealPiEquiv, finSixRealPiEquiv,
    μ, RealNested6, RealNested7, RealNested8, Measure.volume_eq_prod] using h

/-- Reassociate two real coordinate pairs without changing their product volume. -/
private def realPairPairAssocEquiv :
    (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ RealNested4 :=
  MeasurableEquiv.prodAssoc

/-- Reassociate three real coordinate pairs without changing their product volume. -/
private def realThreePairAssocEquiv :
    (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) ≃ᵐ
      RealNested6 :=
  MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) realPairPairAssocEquiv))

/-- Reassociate four real coordinate pairs in manuscript order. -/
private def realFourPairAssocEquiv :
    (ℝ × ℝ) × ((ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) ≃ᵐ
      RealNested8 :=
  MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) realThreePairAssocEquiv))

private theorem realPairPairAssocEquiv_measurePreserving :
    MeasurePreserving realPairPairAssocEquiv (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ)))
      (volume : Measure RealNested4) := by
  exact MeasureTheory.volume_preserving_prodAssoc

private theorem realThreePairAssocEquiv_measurePreserving :
    MeasurePreserving realThreePairAssocEquiv
      (volume : Measure ((ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))))
      (volume : Measure RealNested6) := by
  have hAssoc := MeasureTheory.volume_preserving_prodAssoc
    (α₁ := ℝ) (β₁ := ℝ) (γ₁ := (ℝ × ℝ) × (ℝ × ℝ))
  have hTail : MeasurePreserving (Prod.map id (Prod.map id realPairPairAssocEquiv))
      (volume : Measure (ℝ × (ℝ × ((ℝ × ℝ) × (ℝ × ℝ)))))
      (volume : Measure RealNested6) := by
    have h := MeasurePreserving.prod
      (MeasureTheory.MeasurePreserving.id (volume : Measure ℝ))
      (MeasurePreserving.prod
        (MeasureTheory.MeasurePreserving.id (volume : Measure ℝ))
        realPairPairAssocEquiv_measurePreserving)
    simpa only [Measure.volume_eq_prod] using h
  change MeasurePreserving
    (Prod.map id (Prod.map id realPairPairAssocEquiv) ∘ MeasurableEquiv.prodAssoc) _ _
  exact hTail.comp hAssoc

private theorem realFourPairAssocEquiv_measurePreserving :
    MeasurePreserving realFourPairAssocEquiv
      (volume : Measure ((ℝ × ℝ) × ((ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)))))
      (volume : Measure RealNested8) := by
  have hAssoc := MeasureTheory.volume_preserving_prodAssoc
    (α₁ := ℝ) (β₁ := ℝ)
    (γ₁ := (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)))
  have hTail : MeasurePreserving (Prod.map id (Prod.map id realThreePairAssocEquiv))
      (volume : Measure (ℝ × (ℝ × ((ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))))))
      (volume : Measure RealNested8) := by
    have h := MeasurePreserving.prod
      (MeasureTheory.MeasurePreserving.id (volume : Measure ℝ))
      (MeasurePreserving.prod
        (MeasureTheory.MeasurePreserving.id (volume : Measure ℝ))
        realThreePairAssocEquiv_measurePreserving)
    simpa only [Measure.volume_eq_prod] using h
  change MeasurePreserving
    (Prod.map id (Prod.map id realThreePairAssocEquiv) ∘ MeasurableEquiv.prodAssoc) _ _
  exact hTail.comp hAssoc

/-- Flatten four `Fin 2` real coordinate blocks into eight nested real coordinates. -/
private def planarPiBlocksToNestedRealEquiv :
    (Fin 2 → ℝ) × ((Fin 2 → ℝ) × ((Fin 2 → ℝ) × (Fin 2 → ℝ))) ≃ᵐ
      RealNested8 :=
  (MeasurableEquiv.prodCongr finTwoRealPiEquiv
    (MeasurableEquiv.prodCongr finTwoRealPiEquiv
      (MeasurableEquiv.prodCongr finTwoRealPiEquiv finTwoRealPiEquiv))).trans
    realFourPairAssocEquiv

private theorem planarPiBlocksToNestedRealEquiv_measurePreserving :
    MeasurePreserving planarPiBlocksToNestedRealEquiv
      ((volume : Measure (Fin 2 → ℝ)).prod
        ((volume : Measure (Fin 2 → ℝ)).prod
          ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure (Fin 2 → ℝ)))))
      (volume : Measure RealNested8) := by
  have hPairs := MeasurePreserving.prod finTwoRealPiEquiv_measurePreserving
    (MeasurePreserving.prod finTwoRealPiEquiv_measurePreserving
      (MeasurePreserving.prod finTwoRealPiEquiv_measurePreserving
        finTwoRealPiEquiv_measurePreserving))
  have h := realFourPairAssocEquiv_measurePreserving.comp hPairs
  change MeasurePreserving
    (realFourPairAssocEquiv ∘ Prod.map finTwoRealPiEquiv
      (Prod.map finTwoRealPiEquiv (Prod.map finTwoRealPiEquiv finTwoRealPiEquiv))) _ _
  exact h

/-- The four Euclidean coefficient blocks in the actual planar reference measure, expressed as
four finite real Pi blocks. -/
private def planarEuclideanBlocksToPiEquiv :
    E2 × (E2 × (E2 × E2)) ≃ᵐ
      (Fin 2 → ℝ) × ((Fin 2 → ℝ) × ((Fin 2 → ℝ) × (Fin 2 → ℝ))) :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm
    (MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm
      (MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm))

private theorem planarEuclideanBlocksToPiEquiv_measurePreserving :
    MeasurePreserving planarEuclideanBlocksToPiEquiv
      planarNestedCoefficientMeasure
      ((volume : Measure (Fin 2 → ℝ)).prod
        ((volume : Measure (Fin 2 → ℝ)).prod
          ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure (Fin 2 → ℝ))))) := by
  have hE2 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm
      (volume : Measure E2) (volume : Measure (Fin 2 → ℝ)) := by
    exact EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)
  have h := MeasurePreserving.prod hE2
    (MeasurePreserving.prod hE2 (MeasurePreserving.prod hE2 hE2))
  change MeasurePreserving
    (Prod.map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm
      (Prod.map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm
        (Prod.map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm
          (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm))) _ _
  simpa [planarNestedCoefficientMeasure, Measure.volume_eq_prod] using h

/-- The actual planar coefficient block product is measure-preservingly flattened to its Fin 8
chart, in the manuscript order `(y₀₁,y₀₂,V₁,V₂,w₀₁,w₀₂,W₁,W₂)`. -/
private def planarCoefficientFinChartEquiv :
    E2 × (E2 × (E2 × E2)) ≃ᵐ (Fin 8 → ℝ) :=
  (planarEuclideanBlocksToPiEquiv.trans
    planarPiBlocksToNestedRealEquiv).trans finEightRealPiEquiv.symm

private theorem planarCoefficientFinChartEquiv_measurePreserving :
    MeasurePreserving planarCoefficientFinChartEquiv planarNestedCoefficientMeasure
      (volume : Measure (Fin 8 → ℝ)) := by
  have hBlocks := planarPiBlocksToNestedRealEquiv_measurePreserving.comp
    planarEuclideanBlocksToPiEquiv_measurePreserving
  have h := (MeasurePreserving.symm finEightRealPiEquiv
    finEightRealPiEquiv_measurePreserving).comp hBlocks
  change MeasurePreserving
    (finEightRealPiEquiv.symm ∘ planarPiBlocksToNestedRealEquiv ∘
      planarEuclideanBlocksToPiEquiv) planarNestedCoefficientMeasure
      (volume : Measure (Fin 8 → ℝ))
  exact h

/-- The scalar trajectory chart preserves the canonical nested product reference measure. -/
theorem scalarTrajectoryFinChart_measurePreserving :
    MeasurePreserving (trajectoryCoefficientFinMeasurableEquiv .scalar)
      (trajectoryCoefficientReferenceMeasure .scalar) (volume : Measure (Fin 5 → ℝ)) := by
  let e : ScalarTrajectory ≃ᵐ ℝ × (ℝ × (ℝ × (ℝ × ℝ))) :=
    { toEquiv := ScalarTrajectory.coefficientEquiv
      measurable_toFun := comap_measurable _
      measurable_invFun := by
        rw [measurable_comap_iff]
        simpa using
          (measurable_id : Measurable (id : ℝ × (ℝ × (ℝ × (ℝ × ℝ))) → _)) }
  have hcoord : MeasurePreserving e.symm
      scalarNestedCoefficientMeasure (trajectoryCoefficientReferenceMeasure .scalar) := by
    change MeasurePreserving e.symm scalarNestedCoefficientMeasure
      (scalarNestedCoefficientMeasure.map e.symm)
    exact ⟨e.symm.measurable, rfl⟩
  have hcoordBack : MeasurePreserving e
      (trajectoryCoefficientReferenceMeasure .scalar) scalarNestedCoefficientMeasure :=
    MeasureTheory.MeasurePreserving.symm e.symm hcoord
  have hflat := MeasureTheory.MeasurePreserving.symm finFiveRealPiEquiv
    finFiveRealPiEquiv_measurePreserving
  have hcomp := hflat.comp hcoordBack
  have hfun :
      ((finFiveRealPiEquiv).symm ∘ e : ScalarTrajectory → (Fin 5 → ℝ)) =
        scalarTrajectoryFinMeasurableEquiv := by
    funext l
    cases l with
    | mk y v w0 w1 w2 =>
        funext i
        fin_cases i <;> simp [scalarTrajectoryFinMeasurableEquiv, scalarTrajectoryCoords,
          e, finFiveRealPiEquiv, finFourRealPiEquiv, finThreeRealPiEquiv,
          finTwoRealPiEquiv, ScalarTrajectory.coefficientEquiv,
          MeasurableEquiv.trans_symm, MeasurableEquiv.prodCongr,
          Equiv.prodCongr_symm, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv] <;> rfl
  rw [hfun] at hcomp
  change MeasurePreserving scalarTrajectoryFinMeasurableEquiv
    (trajectoryCoefficientReferenceMeasure .scalar) (volume : Measure (Fin 5 → ℝ))
  exact hcomp

/-- Exact pushforward of the scalar coefficient reference measure to standard `Fin 5` volume. -/
theorem scalarTrajectoryReferenceMeasure_map_chart_eq_volume :
    (trajectoryCoefficientReferenceMeasure .scalar).map
      (trajectoryCoefficientFinMeasurableEquiv .scalar) = (volume : Measure (Fin 5 → ℝ)) :=
  scalarTrajectoryFinChart_measurePreserving.map_eq

/-- The planar trajectory chart preserves the canonical product Euclidean reference measure. -/
theorem planarTrajectoryFinChart_measurePreserving :
    MeasurePreserving (trajectoryCoefficientFinMeasurableEquiv .planar)
      (trajectoryCoefficientReferenceMeasure .planar) (volume : Measure (Fin 8 → ℝ)) := by
  let e : PlanarTrajectory ≃ᵐ E2 × (E2 × (E2 × E2)) :=
    { toEquiv := PlanarTrajectory.coefficientEquiv
      measurable_toFun := comap_measurable _
      measurable_invFun := by
        rw [measurable_comap_iff]
        simpa using
          (measurable_id : Measurable (id : E2 × (E2 × (E2 × E2)) → _)) }
  have hcoord : MeasurePreserving e.symm planarNestedCoefficientMeasure
      (trajectoryCoefficientReferenceMeasure .planar) := by
    change MeasurePreserving e.symm planarNestedCoefficientMeasure
      (planarNestedCoefficientMeasure.map e.symm)
    exact ⟨e.symm.measurable, rfl⟩
  have hcoordBack : MeasurePreserving e
      (trajectoryCoefficientReferenceMeasure .planar) planarNestedCoefficientMeasure :=
    MeasureTheory.MeasurePreserving.symm e.symm hcoord
  have hcomp := planarCoefficientFinChartEquiv_measurePreserving.comp hcoordBack
  have hfun : (planarCoefficientFinChartEquiv ∘ e :
      PlanarTrajectory → (Fin 8 → ℝ)) = planarTrajectoryFinMeasurableEquiv := by
    funext l
    cases l with
    | mk y v w wv =>
        funext i
        fin_cases i <;>
          simp [planarTrajectoryFinMeasurableEquiv, planarTrajectoryCoords,
            planarCoefficientFinChartEquiv, planarEuclideanBlocksToPiEquiv,
            planarPiBlocksToNestedRealEquiv, realFourPairAssocEquiv,
            realThreePairAssocEquiv, realPairPairAssocEquiv,
            finEightRealPiEquiv, finSevenRealPiEquiv, finSixRealPiEquiv,
            finFiveRealPiEquiv, finFourRealPiEquiv, finThreeRealPiEquiv,
            finTwoRealPiEquiv,
            MeasurableEquiv.trans_symm, MeasurableEquiv.prodCongr,
            MeasurableEquiv.piFinSuccAbove_symm_apply,
            MeasurableEquiv.prodAssoc, Equiv.prodCongr_symm, Fin.insertNthEquiv] <;> rfl
  rw [hfun] at hcomp
  change MeasurePreserving planarTrajectoryFinMeasurableEquiv
    (trajectoryCoefficientReferenceMeasure .planar) (volume : Measure (Fin 8 → ℝ))
  simpa [trajectoryCoefficientFinMeasurableEquiv] using hcomp

/-- Exact pushforward of the planar coefficient reference measure to standard `Fin 8` volume. -/
theorem planarTrajectoryReferenceMeasure_map_chart_eq_volume :
    (trajectoryCoefficientReferenceMeasure .planar).map
      (trajectoryCoefficientFinMeasurableEquiv .planar) = (volume : Measure (Fin 8 → ℝ)) :=
  planarTrajectoryFinChart_measurePreserving.map_eq

end Kakeya4.Framework
