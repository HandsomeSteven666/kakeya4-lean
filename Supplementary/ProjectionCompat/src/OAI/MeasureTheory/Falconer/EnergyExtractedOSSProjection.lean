import OAI.MeasureTheory.Falconer.OSSFrostmanProjection

/-! Six original smooth-energy caps supply the actual extracted/smoothed
probabilities and the OSS projection, retaining the joint outer-mass coupling. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

theorem energy_extracted_OSS_projection (κ : SmoothKernel) {s t σ : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hσ : 0 ≤ σ) (hσmax : σ < min (s+t) 1) :
    ∃ ε e r₀ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < e ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ r : ℝ, ∀ hr : 0 < r, r ≤ r₀ →
    ∀ μ : Fin 6 → Measure ℝ, ∀ [∀ i, IsProbabilityMeasure (μ i)],
      (∀ i, UnitSupported (μ i)) →
      (∀ i, smoothEnergy κ.law (if i.val < 2 ∨ i.val = 4 then s else t) r (μ i) ≤
        ENNReal.ofReal (r^(-ε))) →
      ∃ (A : Fin 6 → Set ℝ) (ν : Fin 6 → ProbabilityMeasure ℝ),
        (∀ i, MeasurableSet (A i)) ∧ (∀ i, μ i (A i) ≠ 0) ∧
        (∀ i, μ i (A i)ᶜ ≤ ENNReal.ofReal (r^ε)) ∧
        (∀ i, (ν i : Measure ℝ) = unitRescaledSmoothLaw κ r (normalizedRestriction (μ i) (A i))) ∧
        (∀ i, UnitSupported (ν i : Measure ℝ)) ∧
        (∀ E : Set (Fin 6 → ℝ), Measure.pi μ E ≤
          Measure.pi (fun i ↦ (ν i : Measure ℝ))
            (cthickening (r/2) ((fun x i ↦ x i/2) '' E)) + 6*ENNReal.ofReal (r^ε)) ∧
        ∃ Bad : Set (Fin 4 → ℝ), MeasurableSet Bad ∧
          Measure.pi (fun i : Fin 4 ↦ (ν i.castSucc.castSucc : Measure ℝ)) Bad ≤ ENNReal.ofReal (r^e) ∧
          ∀ w ∉ Bad, ∀ G : Set (Space 2),
            ENNReal.ofReal (r^e) ≤ planarProductLaw (ν 4) (ν 5) G →
            (Nat.ceil (r^(-σ)) : ℕ∞) ≤ externalCoveringNumber ⟨r,hr.le⟩
              ((fun x ↦ (w 2-w 3)*x 0+(w 0-w 1)*x 1) '' G) := by
  classical
  obtain ⟨e,δ₀,he,hδ₀,hδ₀1,hOSS⟩ := OSS_Frostman_projection hs hs1 ht ht1 hσ hσmax
  let η := min (e/4) 1
  have hη : 0 < η := lt_min (by positivity) zero_lt_one
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηe : η ≤ e/4 := min_le_left _ _
  let d : Fin 6 → ℝ := fun i ↦ if i.val < 2 ∨ i.val = 4 then s else t
  have hd (i : Fin 6) : 0 ≤ d i ∧ d i ≤ 1 := by
    dsimp [d]; split_ifs
    · exact ⟨hs.le,hs1⟩
    · exact ⟨ht.le,ht1⟩
  obtain ⟨ε,rE,hε,hε1,hrE,hrE1,hextract⟩ := exists_joint_Frostman_extraction κ d hd hη hη1
  refine ⟨ε,e,min rE δ₀,hε,hε1,he,lt_min hrE hδ₀,(min_le_left _ _).trans hrE1,?_⟩
  intro r hr hrr μ _ hμ henergy
  have hr1 : r ≤ 1 := (hrr.trans (min_le_left _ _)).trans hrE1
  obtain ⟨A,hA,hA0,hloss,hprob,hsupp,hball,htransport⟩ :=
    hextract μ hμ r hr (hrr.trans (min_le_left _ _)) henergy
  let ν : Fin 6 → ProbabilityMeasure ℝ := fun i ↦
    ⟨unitRescaledSmoothLaw κ r (normalizedRestriction (μ i) (A i)),hprob i⟩
  have hν (i : Fin 6) : UnitSupported (ν i : Measure ℝ) := hsupp i
  let C := r^(-η)
  have hC1 : 1 ≤ C := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (neg_nonpos.mpr hη.le)
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  have hCC1 : 1 ≤ C*C := by nlinarith
  have hCC : C*C ≤ r^(-e) := calc
    _ = r^(-2*η) := by dsimp [C]; rw [← Real.rpow_add hr]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have hb (i : Fin 6) (z R : ℝ) (hR : 0 < R) :
      (ν i : Measure ℝ) (closedBall z R) ≤ ENNReal.ofReal (C*R^(d i)) := by
    simpa only [ν,ProbabilityMeasure.coe_mk] using hball i z R hR
  let front : Fin 4 → Measure ℝ := fun i ↦ (ν i.castSucc.castSucc : Measure ℝ)
  let : ∀ i, IsProbabilityMeasure (front i) := fun i ↦ by dsimp [front]; infer_instance
  have hfront (i : Fin 4) : UnitSupported (front i) := hν i.castSucc.castSucc
  have hfrontball (i : Fin 4) (z R : ℝ) (hR : 0 < R) :
      front i (ball z R) ≤ ENNReal.ofReal ((C*C)*R^(if i.val < 2 then s else t)) := by
    have heq : d i.castSucc.castSucc = if i.val < 2 then s else t := by
      have hne : i.val ≠ 4 := by omega
      simp only [d,Fin.val_castSucc,hne,or_false]
    have hh := (measure_mono ball_subset_closedBall).trans (hb i.castSucc.castSucc z R hR)
    rw [heq] at hh
    exact hh.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by nlinarith : C ≤ C*C) (by positivity)))
  have hρ : FrostmanBallBound (planarProductLaw (ν 4) (ν 5)) (s+t) (C*C) := by
    apply parameter_product_full_frostman (ν 4) (ν 5) hC0
    · simpa [d] using hb 4
    · simpa [d] using hb 5
  obtain ⟨Bad,hBad,hdel,hgood⟩ := hOSS r hr (hrr.trans (min_le_right _ _)) (C*C) hCC1 hCC
    front hfront hfrontball (planarProductLaw (ν 4) (ν 5)) hρ (planarProductLaw_unitCube (ν 4) (ν 5) (hν 4) (hν 5))
  refine ⟨A,ν,hA,hA0,hloss,fun _ ↦ rfl,hν,?_,Bad,hBad,hdel,hgood⟩
  intro E
  simpa only [ν,ProbabilityMeasure.coe_mk,Fintype.card_fin,Nat.cast_ofNat] using htransport E

#print axioms energy_extracted_OSS_projection
end OAI.Falconer
