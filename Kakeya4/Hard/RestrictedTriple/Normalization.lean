import Kakeya4.Hard.RestrictedTriple.MetricAdapters

/-! Exact cardinality, image and interval-scale normalization for actual triples.
No finite dichotomy is asserted or assumed proved by these adapters. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem halfTriple_injective : Function.Injective halfTriple := by
  intro t u h
  apply Prod.ext
  · exact halfPlane_injective (congrArg (fun v : Triple ↦ v.1) h)
  · apply Prod.ext
    · exact halfPlane_injective (congrArg (fun v : Triple ↦ v.2.1) h)
    · exact halfPlane_injective (congrArg (fun v : Triple ↦ v.2.2) h)

theorem halfTriple_encard (Q : Set Triple) : (halfTriple '' Q).encard = Q.encard :=
  halfTriple_injective.encard_image Q

theorem halfTriple_image_subset_carrier {Q : Set Triple} {A B : Set Plane}
    (hQ : Q ⊆ tripleCarrier A B) :
    halfTriple '' Q ⊆ tripleCarrier (halfPlane '' A) (halfPlane '' B) := by
  rintro _ ⟨t,ht,rfl⟩
  exact ⟨⟨t.1,(hQ ht).1,rfl⟩,⟨t.2.1,(hQ ht).2.1,rfl⟩,⟨t.2.2,(hQ ht).2.2,rfl⟩⟩

theorem dotDifferenceImage_halfTriple (Q : Set Triple) :
    dotDifferenceImage (halfTriple '' Q) = (fun x : ℝ ↦ x/4) '' dotDifferenceImage Q := by
  simp only [dotDifferenceImage, image_image, Function.comp_def, dotDifference_halfTriple]

theorem intervalCover_mul_image_le {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (E : Set ℝ) :
    intervalCover (c*r) ((fun x : ℝ ↦ c*x) '' E) ≤ intervalCover r E := by
  classical
  obtain ⟨Q,hQ,hcard⟩ := exists_external_optimal_cover (Real.toNNReal (r/2)) E
  have hcover : IsCover (Real.toNNReal ((c*r)/2)) ((fun x : ℝ ↦ c*x) '' E)
      ((fun x : ℝ ↦ c*x) '' Q) := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hd⟩ := hQ hx
    change edist x y ≤ (Real.toNNReal (r/2) : ℝ≥0∞) at hd
    have hd' : dist x y ≤ r/2 := (edist_le_ofReal (by positivity)).mp (by
      simpa only [ENNReal.coe_nnreal_eq,
        Real.coe_toNNReal _ (show 0 ≤ r/2 by positivity)] using hd)
    refine ⟨c*y,⟨y,hy,rfl⟩,?_⟩
    change edist (c*x) (c*y) ≤ (Real.toNNReal ((c*r)/2) : ℝ≥0∞)
    have hdscale : dist (c*x) (c*y) = c*dist x y := by
      simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hc]
    have hh : dist (c*x) (c*y) ≤ (c*r)/2 := by
      rw [hdscale]
      nlinarith
    have he := (edist_le_ofReal (show 0 ≤ (c*r)/2 by positivity)).mpr hh
    simpa only [ENNReal.coe_nnreal_eq,
      Real.coe_toNNReal _ (show 0 ≤ (c*r)/2 by positivity)] using he
  have hh := hcover.externalCoveringNumber_le_encard.trans (encard_image_le (fun x : ℝ ↦ c*x) Q)
  rw [hcard] at hh
  exact ENat.toENNReal_mono hh

theorem intervalCover_mul_image {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (E : Set ℝ) :
    intervalCover (c*r) ((fun x : ℝ ↦ c*x) '' E) = intervalCover r E := by
  apply le_antisymm (intervalCover_mul_image_le hc hr E)
  have hh := intervalCover_mul_image_le (inv_pos.mpr hc) (mul_nonneg hc.le hr)
    ((fun x : ℝ ↦ c*x) '' E)
  simpa [image_image, Function.comp_def, ← mul_assoc, hc.ne'] using hh

theorem mul_image_Icc_inter {c : ℝ} (hc : 0 < c) (a b : ℝ) (E : Set ℝ) :
    (fun x : ℝ ↦ c*x) '' (Icc a b ∩ E) = Icc (c*a) (c*b) ∩ (fun x : ℝ ↦ c*x) '' E := by
  ext y
  constructor
  · rintro ⟨x,⟨hx,hxE⟩,rfl⟩
    exact ⟨⟨by nlinarith [hx.1],by nlinarith [hx.2]⟩,⟨x,hxE,rfl⟩⟩
  · rintro ⟨hy,x,hxE,rfl⟩
    exact ⟨x,⟨⟨by nlinarith [hy.1],by nlinarith [hy.2]⟩,hxE⟩,rfl⟩

theorem intervalCover_mul_Icc_inter {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r)
    (a b : ℝ) (E : Set ℝ) :
    intervalCover (c*r) (Icc (c*a) (c*b) ∩ (fun x : ℝ ↦ c*x) '' E) =
      intervalCover r (Icc a b ∩ E) := by
  rw [← mul_image_Icc_inter hc]
  exact intervalCover_mul_image hc hr _

theorem intervalCover_halfTriple (r : ℝ) (hr : 0 ≤ r) (a b : ℝ) (Q : Set Triple) :
    intervalCover (r/4) (Icc (a/4) (b/4) ∩ dotDifferenceImage (halfTriple '' Q)) =
      intervalCover r (Icc a b ∩ dotDifferenceImage Q) := by
  rw [dotDifferenceImage_halfTriple]
  convert intervalCover_mul_Icc_inter (by norm_num : (0:ℝ) < 1/4) hr a b (dotDifferenceImage Q) using 1 <;>
    simp only [div_eq_mul_inv, mul_comm, one_mul]

/-- The finite normalized scale is p/2, while the actual dot image is scaled by 1/4.
The resulting original interval scale is 4s >= 2p and hence meets the original p cutoff. -/
theorem longIntervalExpansion_of_halfTriple {p ε η : ℝ} {Q : Set Triple}
    (hp : 0 < p) (hη : 0 ≤ η)
    (h : LongIntervalExpansion (p/2) ε η (halfTriple '' Q)) :
    LongIntervalExpansion p ε η Q := by
  obtain ⟨s,a,b,hs,hab,hwidth,hlower⟩ := h
  have hspos : 0 < s := (show 0 < p/2 by positivity).trans_le hs
  have hpower : p^(-η) ≤ (p/2)^(-η) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have hwidth' : p^(-η)*(4*s) ≤ 4*b-4*a := by
    have hh := mul_le_mul_of_nonneg_right hpower hspos.le
    nlinarith
  refine ⟨4*s,4*a,4*b,by linarith,by linarith,hwidth',?_⟩
  have hcover := intervalCover_halfTriple (4*s) (by positivity) (4*a) (4*b) Q
  have hsimpl : (4*s)/4 = s ∧ (4*a)/4 = a ∧ (4*b)/4 = b := ⟨by ring,by ring,by ring⟩
  rcases hsimpl with ⟨hss,haa,hbb⟩
  rw [hss,haa,hbb] at hcover
  rw [← hcover]
  have hratio : (4*b-4*a)/(4*s) = (b-a)/s := by ring
  rwa [hratio]

end Kakeya4.Hard.RestrictedTriple
