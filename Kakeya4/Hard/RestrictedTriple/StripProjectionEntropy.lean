import Kakeya4.Hard.RestrictedTriple.StripProjection

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal Classical

namespace Kakeya4.Hard.RestrictedTriple

theorem strip_projection_separated_pair {t : ℝ} (ht : 0 < t) (L : AffineLine) (a b x y : Plane)
    (ha : ‖a‖ ≤ 1) (hA : 0 < |inner ℝ a L.direction|)
    (hx : x ∈ lineNeighborhood t L) (hy : y ∈ lineNeighborhood t L)
    (hsep : 8*t/|inner ℝ a L.direction| < dist x y) :
    4*t < dist (inner ℝ a (x-b)) (inner ℝ a (y-b)) := by
  have hlow := strip_projection_colipschitz ht.le L a x y ha hA hx hy hsep.le
  have hmul := mul_lt_mul_of_pos_left hsep (show 0 < |inner ℝ a L.direction|/2 by positivity)
  have heq : (|inner ℝ a L.direction|/2)*(8*t/|inner ℝ a L.direction|) = 4*t := by field_simp <;> norm_num
  rw [heq] at hmul
  have hdist : dist (inner ℝ a (x-b)) (inner ℝ a (y-b)) = |inner ℝ a (x-y)| := by
    rw [Real.dist_eq,← inner_sub_right]
    congr 2
    module
  rw [hdist]
  exact hmul.trans_le hlow

/-- An actual separated finite subset in a strip supplies a true projection entropy lower bound. -/
theorem strip_projection_image_card_le_cover {t : ℝ} (ht : 0 < t) (L : AffineLine) (a b : Plane)
    (ha : ‖a‖ ≤ 1) (hA : 0 < |inner ℝ a L.direction|) (P : Finset Plane) (E : Set Plane)
    (hPE : (P : Set Plane) ⊆ E) (hstrip : ∀ x ∈ P, x ∈ lineNeighborhood t L)
    (hsep : IsSeparated (Real.toNNReal (8*t/|inner ℝ a L.direction|)) (P : Set Plane)) :
    (P.card : ℝ≥0∞) ≤ intervalCover (2*t) ((fun x : Plane ↦ inner ℝ a (x-b)) '' E) := by
  classical
  let f : Plane → ℝ := fun x ↦ inner ℝ a (x-b)
  have hpair (x : Plane) (hx : x ∈ P) (y : Plane) (hy : y ∈ P) (hne : x ≠ y) :
      4*t < dist (f x) (f y) := by
    have hs := hsep hx hy hne
    have hsreal : 8*t/|inner ℝ a L.direction| < dist x y := by
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (show 0 ≤ 8*t/|inner ℝ a L.direction| by positivity)).mp
      simpa only [ENNReal.coe_nnreal_eq,Real.coe_toNNReal _ (show 0 ≤ 8*t/|inner ℝ a L.direction| by positivity),edist_dist] using hs
    exact strip_projection_separated_pair ht L a b x y ha hA (hstrip x hx) (hstrip y hy) hsreal
  have hinj : Set.InjOn f (P : Set Plane) := by
    intro x hx y hy heq
    by_contra hne
    have hh := hpair x hx y hy hne
    rw [heq,dist_self] at hh
    linarith
  have hsepImage : IsSeparated (Real.toNNReal (2*t)) (f '' (P : Set Plane)) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hne
    have hxy : x ≠ y := fun heq ↦ hne (congrArg f heq)
    have hh : 2*t < dist (f x) (f y) := by linarith [hpair x hx y hy hxy]
    have he := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (show 0 ≤ 2*t by positivity)).mpr hh
    simpa only [ENNReal.coe_nnreal_eq,Real.coe_toNNReal _ (show 0 ≤ 2*t by positivity),edist_dist] using he
  have hrad : 2*Real.toNNReal t = Real.toNNReal (2*t) := by
    apply NNReal.coe_injective
    simp [Real.toNNReal_of_nonneg ht.le,Real.toNNReal_of_nonneg (show 0 ≤ 2*t by positivity)]
  have hpack := hsepImage.encard_le_packingNumber (image_mono hPE)
  have hcover := packingNumber_two_mul_le_externalCoveringNumber (Real.toNNReal t) (f '' E)
  rw [hrad] at hcover
  have hh := ENat.toENNReal_mono (hpack.trans hcover)
  rw [hinj.encard_image,Set.encard_coe_eq_coe_finsetCard,ENat.toENNReal_coe] at hh
  simpa only [intervalCover,show (2*t)/2 = t by ring] using hh

end Kakeya4.Hard.RestrictedTriple
