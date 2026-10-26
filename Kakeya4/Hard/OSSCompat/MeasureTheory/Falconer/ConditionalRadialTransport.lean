






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.SeparatedCellNormalization

/-! Actual original-law radial transport through conditional restrictions and
common positive similarities, including support-point quantifiers.
The homeomorph support lemma adapts Measures/SimilarityMeasures.lean from
OpenAI math, Apache-2.0, commit1581d4cbdd69a0faf34b2089614fe2a814316a6a.
COPYING preserves the original license. No upstream source is modified. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal

theorem normalized_restriction_absolutelyContinuous {d : ℕ}
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Set (Space d))
    (hA : (μ.restrict A) univ ≠ 0) :
    (normalizedSliceLaw (μ.restrict A) hA : Measure (Space d)) ≪ μ := by
  intro S hS
  rw [normalizedSliceLaw_apply]
  have hzero : (μ.restrict A) S = 0 := le_antisymm
    ((Measure.restrict_le_self S).trans_eq hS) zero_le
  rw [hzero,mul_zero]

theorem normalized_restriction_scale_bound {d : ℕ}
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Set (Space d))
    (hA : (μ.restrict A) univ ≠ 0) {R κ : ℝ} (hR : 1 ≤ R)
    (hmass : ENNReal.ofReal (R^(-κ)) ≤ μ A) (S : Set (Space d)) :
    (normalizedSliceLaw (μ.restrict A) hA : Measure (Space d)) S ≤
      ENNReal.ofReal (R^κ)*μ S := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hmass' : ENNReal.ofReal (R^(-κ)) ≤ (μ.restrict A) univ := by simpa using hmass
  apply (normalizedSliceLaw_bound (μ.restrict A) hA S hmass' (Measure.restrict_le_self S)).trans_eq
  rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hR0 _),Real.rpow_neg hR0.le,inv_inv]

theorem RadialCapBound.normalized_restrictions {d N : ℕ}
    {μ ν : ProbabilityMeasure (Space d)} {G : Set (Space d × Space d)} {e p κ : ℝ}
    (h : RadialCapBound μ ν G N e p)
    (A B : Set (Space d))
    (hA : ((μ : Measure (Space d)).restrict A) univ ≠ 0)
    (hB : ((ν : Measure (Space d)).restrict B) univ ≠ 0)
    (hμmass : ENNReal.ofReal (((2:ℝ)^N)^(-κ)) ≤ (μ : Measure (Space d)) A)
    (hνmass : ENNReal.ofReal (((2:ℝ)^N)^(-κ)) ≤ (ν : Measure (Space d)) B) :
    RadialCapBound (normalizedSliceLaw ((μ : Measure (Space d)).restrict A) hA)
      (normalizedSliceLaw ((ν : Measure (Space d)).restrict B) hB) G N (e+κ) p := by
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have heq (r : ℝ) : ENNReal.ofReal (((2:ℝ)^N)^κ) *
      ENNReal.ofReal (((2:ℝ)^N)^e*r^p) = ENNReal.ofReal (((2:ℝ)^N)^(e+κ)*r^p) := by
    rw [← ENNReal.ofReal_mul (by positivity),Real.rpow_add (by positivity)]
    congr 1
    ring
  constructor
  · intro x hx w hw r hr hr1
    have hx' := (normalized_restriction_absolutelyContinuous (μ : Measure (Space d)) A hA).support_mono hx
    exact (normalized_restriction_scale_bound (ν : Measure (Space d)) B hB hR hνmass _).trans
      ((mul_le_mul' le_rfl (h.1 x hx' w hw r hr hr1)).trans_eq (heq r))
  · intro y hy w hw r hr hr1
    have hy' := (normalized_restriction_absolutelyContinuous (ν : Measure (Space d)) B hB).support_mono hy
    exact (normalized_restriction_scale_bound (μ : Measure (Space d)) A hA hR hμmass _).trans
      ((mul_le_mul' le_rfl (h.2 y hy' w hw r hr hr1)).trans_eq (heq r))

theorem radialTransport_support_map_subset {d : ℕ} (f : Space d ≃ₜ Space d)
    (μ : Measure (Space d)) : (μ.map f).support ⊆ f '' μ.support := by
  apply Measure.support_subset_of_isClosed (f.isClosedMap _ Measure.isClosed_support)
  change (μ.map f) (f '' μ.support)ᶜ = 0
  rw [f.measurableEmbedding.map_apply]
  simpa only [preimage_compl,f.injective.preimage_image] using μ.measure_compl_support

theorem radialTransport_support_map_eq {d : ℕ} (f : Space d ≃ₜ Space d)
    (μ : Measure (Space d)) : (μ.map f).support = f '' μ.support := by
  apply Subset.antisymm (radialTransport_support_map_subset f μ)
  have hinv : (μ.map f).map f.symm = μ := by
    rw [Measure.map_map f.symm.measurable f.measurable]
    have hcomp : f.symm ∘ f = _root_.id := by funext x; exact f.symm_apply_apply x
    rw [hcomp]
    exact Measure.map_id
  have hback := radialTransport_support_map_subset f.symm (μ.map f)
  rw [hinv] at hback
  rintro y ⟨x,hx,rfl⟩
  obtain ⟨z,hz,hzx⟩ := hback hx
  have hfx : f x = z := by rw [← hzx,f.apply_symm_apply]
  rwa [hfx]

theorem radialZoom_radialDirection {d : ℕ} {a : ℝ} (ha : 0 < a)
    (c x y : Space d) :
    radialDirection (_root_.OAI.Falconer.radialZoom a ha.ne' c x) (_root_.OAI.Falconer.radialZoom a ha.ne' c y) = radialDirection x y := by
  change normalize (_root_.OAI.Falconer.radialZoom a ha.ne' c y-_root_.OAI.Falconer.radialZoom a ha.ne' c x) = normalize (y-x)
  rw [radialZoom_sub,normalize_smul_of_pos ha]

theorem RadialCapBound.radialZoom {d N : ℕ} {μ ν : ProbabilityMeasure (Space d)}
    {G : Set (Space d × Space d)} {e p a : ℝ}
    (h : RadialCapBound μ ν G N e p) (ha : 0 < a) (c : Space d) :
    RadialCapBound (μ.map (_root_.OAI.Falconer.radialZoom a ha.ne' c)) (ν.map (_root_.OAI.Falconer.radialZoom a ha.ne' c))
      (zoomPairSet (_root_.OAI.Falconer.radialZoom a ha.ne' c) G) N e p := by
  let f := _root_.OAI.Falconer.radialZoom a ha.ne' c
  constructor
  · intro x hx w hw r hr hr1
    obtain ⟨x,hxs,rfl⟩ := radialTransport_support_map_subset f (μ : Measure (Space d)) hx
    change ((ν : Measure (Space d)).map f) _ ≤ _
    rw [f.measurableEmbedding.map_apply]
    have he : f ⁻¹' {y | (f x,y) ∈ zoomPairSet f G ∧ dist (radialDirection (f x) y) w < r} =
        {y | (x,y) ∈ G ∧ dist (radialDirection x y) w < r} := by
      ext y
      simp only [mem_preimage,mem_ofPred_eq,mem_zoomPairSet]
      rw [radialZoom_radialDirection ha]
    rw [he]
    exact h.1 x hxs w hw r hr hr1
  · intro y hy w hw r hr hr1
    obtain ⟨y,hys,rfl⟩ := radialTransport_support_map_subset f (ν : Measure (Space d)) hy
    change ((μ : Measure (Space d)).map f) _ ≤ _
    rw [f.measurableEmbedding.map_apply]
    have he : f ⁻¹' {x | (x,f y) ∈ zoomPairSet f G ∧ dist (radialDirection (f y) x) w < r} =
        {x | (x,y) ∈ G ∧ dist (radialDirection y x) w < r} := by
      ext x
      simp only [mem_preimage,mem_ofPred_eq,mem_zoomPairSet]
      rw [radialZoom_radialDirection ha]
    rw [he]
    exact h.2 y hys w hw r hr hr1

theorem RadialCapBound.radialZoom_iff {d N : ℕ} {μ ν : ProbabilityMeasure (Space d)}
    {G : Set (Space d × Space d)} {e p a : ℝ} (ha : 0 < a) (c : Space d) :
    RadialCapBound (μ.map (_root_.OAI.Falconer.radialZoom a ha.ne' c)) (ν.map (_root_.OAI.Falconer.radialZoom a ha.ne' c))
      (zoomPairSet (_root_.OAI.Falconer.radialZoom a ha.ne' c) G) N e p ↔ RadialCapBound μ ν G N e p := by
  constructor
  · intro h
    let f := _root_.OAI.Falconer.radialZoom a ha.ne' c
    constructor
    · intro x hx w hw r hr hr1
      have hx' : f x ∈ ((μ : Measure (Space d)).map f).support := by
        rw [radialTransport_support_map_eq]; exact mem_image_of_mem f hx
      have hb := h.1 (f x) hx' w hw r hr hr1
      change ((ν : Measure (Space d)).map f) _ ≤ _ at hb
      rw [f.measurableEmbedding.map_apply] at hb
      have he : f ⁻¹' {y | (f x,y) ∈ zoomPairSet f G ∧ dist (radialDirection (f x) y) w < r} =
          {y | (x,y) ∈ G ∧ dist (radialDirection x y) w < r} := by
        ext y
        simp only [mem_preimage,mem_ofPred_eq,mem_zoomPairSet]
        rw [radialZoom_radialDirection ha]
      rw [he] at hb
      exact hb
    · intro y hy w hw r hr hr1
      have hy' : f y ∈ ((ν : Measure (Space d)).map f).support := by
        rw [radialTransport_support_map_eq]; exact mem_image_of_mem f hy
      have hb := h.2 (f y) hy' w hw r hr hr1
      change ((μ : Measure (Space d)).map f) _ ≤ _ at hb
      rw [f.measurableEmbedding.map_apply] at hb
      have he : f ⁻¹' {x | (x,f y) ∈ zoomPairSet f G ∧ dist (radialDirection (f y) x) w < r} =
          {x | (x,y) ∈ G ∧ dist (radialDirection y x) w < r} := by
        ext x
        simp only [mem_preimage,mem_ofPred_eq,mem_zoomPairSet]
        rw [radialZoom_radialDirection ha]
      rw [he] at hb
      exact hb
  · intro h
    exact h.radialZoom ha c

#print axioms normalized_restriction_absolutelyContinuous
#print axioms normalized_restriction_scale_bound
#print axioms RadialCapBound.normalized_restrictions
#print axioms radialTransport_support_map_subset
#print axioms radialTransport_support_map_eq
#print axioms radialZoom_radialDirection
#print axioms RadialCapBound.radialZoom
#print axioms RadialCapBound.radialZoom_iff
end OAI.Falconer
