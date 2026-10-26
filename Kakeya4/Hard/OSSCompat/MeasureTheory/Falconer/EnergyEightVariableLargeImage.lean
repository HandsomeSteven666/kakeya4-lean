






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.EnergyLargeImageBudgets

/-! Original smooth-energy caps imply a large image of the original pi8 law.
The conclusion uses the original radius r and permits nonmeasurable targets. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

theorem energy_eight_variable_large_image (κ : SmoothKernel) {s t σ : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hσ : 0 ≤ σ) (hσmax : σ < min (s+t) 1) :
    ∃ ε r₀ : ℝ, 0 < ε ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
    ∀ r : ℝ, ∀ hr : 0 < r, r ≤ r₀ →
    ∀ μ : Fin 8 → Measure ℝ, ∀ [∀ i, IsProbabilityMeasure (μ i)],
      (∀ i, UnitSupported (μ i)) →
      (∀ i, smoothEnergy κ.law (if i.val < 2 ∨ i.val = 4 ∨ i.val = 6 then s else t) r (μ i) ≤
        ENNReal.ofReal (r^(-ε))) →
      ∀ E : Set ℝ, ENNReal.ofReal (r^ε) ≤ (Measure.pi μ).map eightBilinearValue E →
        (Nat.ceil (r^(-σ)) : ℕ∞) ≤ externalCoveringNumber ⟨r,hr.le⟩ E := by
  classical
  let σ' := (σ+min (s+t) 1)/2
  have hσσ' : σ < σ' := by dsimp [σ']; linarith
  have hσ'max : σ' < min (s+t) 1 := by dsimp [σ']; linarith
  obtain ⟨e,δF,he,hδF,hδF1,himage⟩ := uniform_eight_variable_Frostman_large_image
    hs hs1 ht ht1 (hσ.trans hσσ'.le) hσ'max
  let η := min (e/4) 1
  have hη : 0 < η := lt_min (by positivity) zero_lt_one
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηe : η < e := by have hh := min_le_left (e/4) 1; dsimp [η]; linarith
  let d : Fin 8 → ℝ := fun i ↦ if i.val < 2 ∨ i.val = 4 ∨ i.val = 6 then s else t
  have hd (i : Fin 8) : 0 ≤ d i ∧ d i ≤ 1 := by
    dsimp [d]; split_ifs
    · exact ⟨hs.le,hs1⟩
    · exact ⟨ht.le,ht1⟩
  obtain ⟨eE,rE,heE,heE1,hrE,hrE1,hextract⟩ := exists_joint_Frostman_extraction κ d hd hη hη1
  let ε := min e eE/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεe : ε < e := by dsimp [ε]; linarith [min_le_left e eE]
  have hεE : ε < eE := by dsimp [ε]; linarith [min_le_right e eE]
  obtain ⟨rT,hrT,hrT1,hT⟩ := exists_small_scaled_rpow_budget hεe 9 (1/4) (by norm_num) (by norm_num)
  obtain ⟨rL,hrL,hrL1,hL⟩ := exists_small_scaled_rpow_budget hεE 1 (1/32) (by norm_num) (by norm_num)
  obtain ⟨rC,hrC,hrC1,hC⟩ := exists_small_scaled_rpow_budget hηe 9 1 (by norm_num) zero_lt_one
  obtain ⟨rK,hrK,hrK1,hK⟩ := exists_small_scaled_rpow_budget hσσ' 9 1 (by norm_num) zero_lt_one
  let r₀ := min rE (min (δF/9) (min rT (min rL (min rC rK))))
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  refine ⟨ε,r₀,hε,hr₀,(min_le_left _ _).trans hrE1,?_⟩
  intro r hr hrr μ _ hμ henergy E hE
  have hp : r ≤ rE ∧ r ≤ δF/9 ∧ r ≤ rT ∧ r ≤ rL ∧ r ≤ rC ∧ r ≤ rK := by
    simpa only [r₀,le_min_iff] using hrr
  obtain ⟨hrrE,hrrF,hrrT,hrrL,hrrC,hrrK⟩ := hp
  have hr1 : r ≤ 1 := hrrE.trans hrE1
  have h9 : 9*r ≤ δF := by have hh := (le_div_iff₀ (by norm_num : (0:ℝ) < 9)).mp hrrF; linarith
  have henergy' (i : Fin 8) : smoothEnergy κ.law (d i) r (μ i) ≤ ENNReal.ofReal (r^(-eE)) :=
    (henergy i).trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hr hr1 (neg_le_neg hεE.le)))
  obtain ⟨A,hA,hA0,hloss,hprob,hsupp,hball,hjoint⟩ := hextract μ hμ r hr hrrE henergy'
  let ν : Fin 8 → Measure ℝ := fun i ↦ unitRescaledSmoothLaw κ r (normalizedRestriction (μ i) (A i))
  let (i : Fin 8) : IsProbabilityMeasure (ν i) := hprob i
  have hν (i : Fin 8) : UnitSupported (ν i) := hsupp i
  let C := r^(-η)
  have hC1 : 1 ≤ C := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (neg_nonpos.mpr hη.le)
  have hCbudget : C ≤ (9*r)^(-e) := by
    have hh : (9*r)^e ≤ r^η := by simpa only [one_mul] using hC r hr hrrC
    change r^(-η) ≤ (9*r)^(-e)
    rw [Real.rpow_neg hr.le,Real.rpow_neg (by positivity)]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hr η) (Real.rpow_pos_of_pos (by positivity) e)).mpr hh
  have hνball (i : Fin 8) (z R : ℝ) (hR : 0 < R) :
      ν i (ball z R) ≤ ENNReal.ofReal (C*R^(if i.val < 2 ∨ i.val = 4 ∨ i.val = 6 then s else t)) :=
    (measure_mono ball_subset_closedBall).trans (hball i z R hR)
  have hnum : (9*r)^e+8*r^eE < r^ε := by
    have ht := hT r hr hrrT
    have hl : r^eE ≤ (1/32:ℝ)*r^ε := by simpa only [one_mul] using hL r hr hrrL
    nlinarith [Real.rpow_pos_of_pos hr ε]
  have hstrict : ENNReal.ofReal ((9*r)^e)+8*ENNReal.ofReal (r^eE) < ENNReal.ofReal (r^ε) := by
    rw [← ENNReal.ofReal_ofNat 8,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hnum
  simp only [externalCoveringNumber,le_iInf_iff]
  intro centers hcover
  by_cases hfin : centers.Finite
  · let : Fintype centers := hfin.fintype
    let V : Set ℝ := ⋃ c : centers, closedBall (c:ℝ) r
    let U : Set ℝ := ⋃ c : centers, closedBall ((c:ℝ)/4) (9*r)
    have hV : MeasurableSet V := MeasurableSet.iUnion (fun _ ↦ measurableSet_closedBall)
    have hU : MeasurableSet U := MeasurableSet.iUnion (fun _ ↦ measurableSet_closedBall)
    have hEV : E ⊆ V := by
      intro x hx
      obtain ⟨c,hc⟩ := mem_iUnion.mp (hcover.subset_iUnion_closedBall hx)
      obtain ⟨hcC,hxc⟩ := mem_iUnion.mp hc
      exact mem_iUnion.mpr ⟨⟨c,hcC⟩,hxc⟩
    have htransport := original_eight_value_mass_le_smoothed_add_loss κ μ hμ A hA hA0 r V U hV hU
      (fun w u hw hu hwV ↦ eight_noisy_cover_transfer (fun c : centers ↦ (c:ℝ)) hr.le hr1 w u hw hu hwV)
    have hsum : (∑ i, μ i (A i)ᶜ) ≤ 8*ENNReal.ofReal (r^eE) := by
      exact (Finset.sum_le_sum (fun i _ ↦ hloss i)).trans_eq (by simp)
    have hνmass : ENNReal.ofReal ((9*r)^e) < (Measure.pi ν).map eightBilinearValue U := by
      by_contra hn
      have hle := le_of_not_gt hn
      have hh := htransport.trans (add_le_add hle hsum)
      exact (not_lt_of_ge hh) (hstrict.trans_le (hE.trans (measure_mono hEV)))
    have hlarge := himage (9*r) (by positivity) h9 C hC1 hCbudget ν hν hνball U hνmass.le
    let D : Set ℝ := (fun c : ℝ ↦ c/4) '' centers
    have hD : IsCover ⟨9*r,by positivity⟩ U D := by
      apply IsCover.of_subset_iUnion_closedBall
      intro x hx
      obtain ⟨c,hc⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨(c:ℝ)/4,mem_iUnion.mpr ⟨mem_image_of_mem _ c.property,hc⟩⟩
    have hexp : r^(-σ) ≤ (9*r)^(-σ') := by
      have hh : (9*r)^σ' ≤ r^σ := by simpa only [one_mul] using hK r hr hrrK
      rw [Real.rpow_neg hr.le,Real.rpow_neg (by positivity)]
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos hr σ) (Real.rpow_pos_of_pos (by positivity) σ')).mpr hh
    have hn : Nat.ceil (r^(-σ)) ≤ Nat.ceil ((9*r)^(-σ')) := Nat.ceil_mono hexp
    exact (show (Nat.ceil (r^(-σ)) : ℕ∞) ≤ Nat.ceil ((9*r)^(-σ')) by exact_mod_cast hn).trans
      (hlarge.trans (hD.externalCoveringNumber_le_encard.trans (encard_image_le _ centers)))
  · rw [Set.encard_eq_top hfin]
    exact le_top

#print axioms energy_eight_variable_large_image
end OAI.Falconer
