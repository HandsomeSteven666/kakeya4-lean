






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.ConditionalSupportCore

/-! Concrete far-cell consumption of the actual fixed-root finite bootstrap.
All constants precede the original laws, the retained cells and their centers.
No local gain certificate or law-dependent normalization constant is supplied. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal

theorem normalized_restriction_map_carried {d : ℕ}
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (A : Set (Space d)) (hA : MeasurableSet A) (hpos : (μ.restrict A) univ ≠ 0)
    (f : Space d ≃ₜ Space d) :
    ((normalizedSliceLaw (μ.restrict A) hpos).map f : Measure (Space d)) (f '' A)ᶜ = 0 := by
  change (Measure.map f (normalizedSliceLaw (μ.restrict A) hpos : Measure (Space d))) _ = 0
  rw [f.measurableEmbedding.map_apply,preimage_compl,f.injective.preimage_image,
    normalizedSliceLaw_apply]
  simp only [Measure.restrict_apply' hA,compl_inter_self,measure_empty,mul_zero]

namespace Regularization

theorem uniform_far_cell_bootstrap
    {a b α t : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbt : b < t)
    (ht : t < 1) (htα : t < α) (hα1 : α ≤ 1) (η : ℝ) (hη : 0 < η) :
    ∃ ε κ c : ℝ, 0 < ε ∧ 0 < κ ∧ 0 < c ∧ ∃ N₀ : ℕ,
    ∀ p ∈ Icc a b, ∀ N ≥ N₀, ∀ C : ℝ, 0 ≤ C → C ≤ ((2:ℝ)^N)^ε →
    ∀ μ ν : ProbabilityMeasure (Space 2),
      FrostmanBallBound (μ : Measure (Space 2)) α C →
      FrostmanBallBound (ν : Measure (Space 2)) α C →
    ∀ (A B : Set (Space 2)) (hA : MeasurableSet A) (hB : MeasurableSet B)
      (hμ : ((μ : Measure (Space 2)).restrict A) univ ≠ 0)
      (hν : ((ν : Measure (Space 2)).restrict B) univ ≠ 0),
      ENNReal.ofReal (((2:ℝ)^N)^(-κ)) ≤ (μ : Measure (Space 2)) A →
      ENNReal.ofReal (((2:ℝ)^N)^(-κ)) ≤ (ν : Measure (Space 2)) B →
    ∀ u v : Space 2, 0 < dist u v → dist u v ≤ 4 →
      (∀ z ∈ A, dist z u ≤ dist u v/8) →
      (∀ x ∈ B, dist x v ≤ dist u v/8) →
    ∀ G : Set (Space 2 × Space 2), MeasurableSet G → RadialCapBound μ ν G N ε p →
    ∃ H : Set (Space 2 × Space 2), MeasurableSet H ∧ H ⊆ G ∩ (A ×ˢ B) ∧
      H ⊆ (normalizedSliceLaw ((μ : Measure (Space 2)).restrict A) hμ : Measure (Space 2)).support ×ˢ
        (normalizedSliceLaw ((ν : Measure (Space 2)).restrict B) hν : Measure (Space 2)).support ∧
      ((normalizedSliceLaw ((μ : Measure (Space 2)).restrict A) hμ : Measure (Space 2)).prod
        (normalizedSliceLaw ((ν : Measure (Space 2)).restrict B) hν)) ((G ∩ (A ×ˢ B)) \ H) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
      RadialCapBound (normalizedSliceLaw ((μ : Measure (Space 2)).restrict A) hμ)
        (normalizedSliceLaw ((ν : Measure (Space 2)).restrict B) hν) H N η b := by
  classical
  have hdim : Real.sqrt (2:ℕ) ≤ (2:ℝ) := by
    norm_num only [Nat.cast_ofNat]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
  obtain ⟨e0,c,he0,hc,Nb,hNb⟩ := uniform_radial_bootstrap_power_cost ha hab hbt ht htα
    (centeredUnitCube 2) rfl (by norm_num : (1:ℝ) ≤ 2) hdim (by norm_num : (0:ℝ) < 1/8) η hη
  let ε := e0/4
  let κ := e0/4
  let ζ := e0/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  obtain ⟨Nf,hNf⟩ := normalized_cell_zoom_uniform_budget ζ hζ
  refine ⟨ε,κ,c,hε,hκ,hc,max Nb Nf,?_⟩
  intro p hp N hN C hC hCbudget μ ν hμfrost hνfrost A B hA hB hμ hν hμmass hνmass u v hd hdiam hAcell hBcell G hG hcap
  let μA := normalizedSliceLaw ((μ : Measure (Space 2)).restrict A) hμ
  let νB := normalizedSliceLaw ((ν : Measure (Space 2)).restrict B) hν
  obtain ⟨scale,hscale,hscaleLower,center,hAroot,hBroot,hsep⟩ := separated_cell_pair_normalization u v hd hdiam
  let f := radialZoom scale hscale.ne' center
  let A' := f '' A
  let B' := f '' B
  have hA' : MeasurableSet A' := f.measurableEmbedding.measurableSet_image.mpr hA
  have hB' : MeasurableSet B' := f.measurableEmbedding.measurableSet_image.mpr hB
  have hAroot' : A' ⊆ (centeredUnitCube 2).carrier := by
    rintro z ⟨x,hx,rfl⟩
    exact hAroot x (hAcell x hx)
  have hBroot' : B' ⊆ (centeredUnitCube 2).carrier := by
    rintro z ⟨x,hx,rfl⟩
    exact hBroot x (hBcell x hx)
  have hAfull : (μA.map f : Measure (Space 2)) A'ᶜ = 0 :=
    normalized_restriction_map_carried (μ : Measure (Space 2)) A hA hμ f
  have hBfull : (νB.map f : Measure (Space 2)) B'ᶜ = 0 :=
    normalized_restriction_map_carried (ν : Measure (Space 2)) B hB hν f
  have hμroot : (μA.map f : Measure (Space 2)) (centeredUnitCube 2).carrierᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hAroot') hAfull
  have hνroot : (νB.map f : Measure (Space 2)) (centeredUnitCube 2).carrierᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hBroot') hBfull
  have hα : 0 ≤ α := by have := hp.1; linarith
  have hL : 0 < ((2:ℝ)^N)^(-κ) := Real.rpow_pos_of_pos (by positivity) _
  have hfmA := hNf N ((le_max_right _ _).trans hN) 2 ε κ α (((2:ℝ)^N)^(-κ)) C scale
    hα hα1 hC hL hscale hscaleLower hCbudget le_rfl (μ : Measure (Space 2)) A hA hμ hμmass center hμfrost
  have hfmB := hNf N ((le_max_right _ _).trans hN) 2 ε κ α (((2:ℝ)^N)^(-κ)) C scale
    hα hα1 hC hL hscale hscaleLower hCbudget le_rfl (ν : Measure (Space 2)) B hB hν hνmass center hνfrost
  have hbudget : ε+κ+ζ ≤ e0 := by dsimp [ε,κ,ζ]; linarith
  have hraise (ξ : Measure (Space 2)) (hξ : FrostmanBallBound ξ α (((2:ℝ)^N)^(ε+κ+ζ))) :
      FrostmanBallBound ξ α (((2:ℝ)^N)^e0) := by
    intro x r hr
    exact (hξ x r hr).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le
        (one_le_pow₀ (by norm_num)) hbudget) (Real.rpow_nonneg hr.le _)))
  have hsep' : ∀ z ∈ A', ∀ x ∈ B', (1:ℝ)/8 ≤ ‖z-x‖ := by
    rintro z ⟨z,hz,rfl⟩ x ⟨x,hx,rfl⟩
    exact hsep z (hAcell z hz) x (hBcell x hx)
  have hpin : ∀ y ∈ (centeredUnitCube 2).carrier, ∀ x ∈ A' ∪ B', ‖y-x‖ ≤ 2 := by
    intro y hy x hx
    have hxroot := hx.elim (fun hx => hAroot' hx) (fun hx => hBroot' hx)
    have hb := (centeredUnitCube 2).dist_le (by norm_num [centeredUnitCube]) hy hxroot
    rw [show (centeredUnitCube 2).side = 1 from rfl,mul_one] at hb
    exact hb.trans hdim
  let Gc := G ∩ (A ×ˢ B)
  have hGc : MeasurableSet Gc := hG.inter (hA.prod hB)
  have hcond : RadialCapBound μA νB Gc N e0 p :=
    ((hcap.normalized_restrictions A B hμ hν hμmass hνmass).mono inter_subset_left).enlarge_loss
      (by dsimp [ε,κ]; linarith)
  have hzoomCap := hcond.radialZoom hscale center
  obtain ⟨H',hH',hHsub,hHdel,hHcap⟩ := hNb p hp N ((le_max_left _ _).trans hN)
    (((2:ℝ)^N)^e0) (by positivity) le_rfl (μA.map f) (νB.map f) hμroot hνroot
    (hraise _ hfmA) (hraise _ hfmB) A' B' hA' hB' hAfull hBfull hsep' hpin
    (zoomPairSet f Gc) (zoomPairSet_measurable f hGc) hzoomCap
  let H := (Prod.map f f) ⁻¹' H'
  have hH : MeasurableSet H := hH'.preimage (f.measurable.prodMap f.measurable)
  have hHsub' : H ⊆ Gc := by
    intro z hz
    exact (mem_zoomPairSet f Gc z.1 z.2).mp (hHsub hz)
  have hzoomH : zoomPairSet f H = H' := by
    ext z
    change (f (f.symm z.1),f (f.symm z.2)) ∈ H' ↔ z ∈ H'
    rw [f.apply_symm_apply,f.apply_symm_apply]
  have hcapH : RadialCapBound μA νB H N η b := by
    apply (RadialCapBound.radialZoom_iff hscale center).mp
    change RadialCapBound (μA.map f) (νB.map f) (zoomPairSet f H) N η b
    rw [hzoomH]
    exact hHcap
  have hdiff : zoomPairSet f (Gc \ H) = zoomPairSet f Gc \ H' := by
    rw [← hzoomH]
    rfl
  have hmassEq := zoom_pair_mass f (μA : Measure (Space 2)) (νB : Measure (Space 2))
    (Gc \ H) (hGc.diff hH)
  rw [hdiff] at hmassEq
  have hdelH : ((μA : Measure (Space 2)).prod νB) (Gc \ H) ≤
      ENNReal.ofReal (((2:ℝ)^N)^(-c)) := hmassEq.symm.trans_le hHdel
  obtain ⟨K,hK,hKH,hKS,hzero,hKcap⟩ := exists_radial_support_core μA νB H hH hcapH
  refine ⟨K,hK,hKH.trans hHsub',hKS,?_,hKcap⟩
  have htotal := relative_pruning_cost_trans ((μA : Measure (Space 2)).prod νB) Gc H K hdelH hzero.le
  simpa only [add_zero] using htotal

#print axioms OAI.Falconer.normalized_restriction_map_carried
#print axioms uniform_far_cell_bootstrap
end Regularization
end OAI.Falconer
