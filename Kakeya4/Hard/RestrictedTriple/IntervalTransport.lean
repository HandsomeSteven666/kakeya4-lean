import Kakeya4.Hard.RestrictedTriple.CubeScaling

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem intervalCover_mono {E F : Set ℝ} {r : ℝ} (h : E ⊆ F) :
    intervalCover r E ≤ intervalCover r F :=
  ENat.toENNReal_mono (externalCoveringNumber_mono_set h)

theorem intervalCover_anti {E : Set ℝ} {r s : ℝ} (h : r ≤ s) :
    intervalCover s E ≤ intervalCover r E :=
  ENat.toENNReal_mono (externalCoveringNumber_anti (Real.toNNReal_mono (by linarith)))

theorem intervalCover_le_four_mul_four_scale {r : ℝ} (hr : 0 ≤ r) (E : Set ℝ) :
    intervalCover r E ≤ 4*intervalCover (4*r) E := by
  classical
  obtain ⟨Q, hQ, hcard⟩ := exists_external_optimal_cover (Real.toNNReal ((4*r)/2)) E
  let f : ℝ × Fin 4 → ℝ := fun q ↦ q.1+((q.2:ℝ)-3/2)*r
  let R : Set ℝ := f '' (Q ×ˢ (univ : Set (Fin 4)))
  have hcover : IsCover (Real.toNNReal (r/2)) E R := by
    intro x hx
    obtain ⟨q, hq, hd⟩ := hQ hx
    change edist x q ≤ (Real.toNNReal ((4*r)/2) : ℝ≥0∞) at hd
    have hd' : |x-q| ≤ 2*r := by
      have hh : dist x q ≤ (4*r)/2 := (edist_le_ofReal (by positivity)).mp (by
        simpa only [ENNReal.coe_nnreal_eq,
          Real.coe_toNNReal _ (show 0 ≤ (4*r)/2 by positivity)] using hd)
      rw [Real.dist_eq] at hh
      linarith
    obtain ⟨j, hj⟩ := exists_quarter_interval_center hr hd'
    refine ⟨f (q,j), ⟨(q,j), ⟨hq, mem_univ _⟩, rfl⟩, ?_⟩
    change edist x (f (q,j)) ≤ (Real.toNNReal (r/2) : ℝ≥0∞)
    have heq : x-f (q,j) = (x-q)-((j:ℝ)-3/2)*r := by dsimp [f]; ring
    have hh : dist x (f (q,j)) ≤ r/2 := by simpa only [Real.dist_eq, heq] using hj
    have hh' := (edist_le_ofReal (show 0 ≤ r/2 by positivity)).mpr hh
    simpa only [ENNReal.coe_nnreal_eq,
      Real.coe_toNNReal _ (show 0 ≤ r/2 by positivity)] using hh'
  have hR : R.encard ≤ Q.encard*4 := by
    have hh := encard_image_le f (Q ×ˢ (univ : Set (Fin 4)))
    simpa [R, encard_prod, encard_univ, ENat.card_eq_coe_fintype_card] using hh
  have hh := ENat.toENNReal_mono (hcover.externalCoveringNumber_le_encard.trans hR)
  simpa only [intervalCover, ENat.toENNReal_mul, ENat.toENNReal_ofNat, hcard, mul_comm] using hh

theorem intervalCover_le_sixteen_mul_sixteen_scale {r : ℝ} (hr : 0 ≤ r) (E : Set ℝ) :
    intervalCover r E ≤ 16*intervalCover (16*r) E := by
  calc
    _ ≤ 4*intervalCover (4*r) E := intervalCover_le_four_mul_four_scale hr E
    _ ≤ 4*(4*intervalCover (4*(4*r)) E) := by
      gcongr
      exact intervalCover_le_four_mul_four_scale (by positivity) E
    _ = 16*intervalCover (16*r) E := by ring_nf

/-- A local approximation enlarges the interval as well as the covering scale. -/
theorem intervalCover_local_le_of_approximation {E F : Set ℝ} {s δ a b : ℝ}
    (hs : 0 ≤ s) (hδ : 0 ≤ δ)
    (happrox : ∀ x ∈ E, ∃ y ∈ F, |x-y| ≤ δ) :
    intervalCover (s+2*δ) (Icc a b ∩ E) ≤
      intervalCover s (Icc (a-δ) (b+δ) ∩ F) := by
  apply intervalCover_le_of_approximation hs hδ
  rintro x ⟨hx, hxE⟩
  obtain ⟨y, hy, hdist⟩ := happrox x hxE
  have hh := abs_le.mp hdist
  exact ⟨y, ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hy⟩, hdist⟩

/-- At scales dominating the perturbation, the original covering scale is retained
at the cost of a fixed factor 16, with the interval enlargement still explicit. -/
theorem intervalCover_local_le_sixteen_mul_of_approximation {E F : Set ℝ} {s δ a b : ℝ}
    (hs : 0 ≤ s) (hδ : 0 ≤ δ) (hsmall : δ ≤ 6*s)
    (happrox : ∀ x ∈ E, ∃ y ∈ F, |x-y| ≤ δ) :
    intervalCover s (Icc a b ∩ E) ≤
      16*intervalCover s (Icc (a-δ) (b+δ) ∩ F) := by
  calc
    _ ≤ 16*intervalCover (16*s) (Icc a b ∩ E) :=
      intervalCover_le_sixteen_mul_sixteen_scale hs _
    _ ≤ 16*intervalCover (s+2*δ) (Icc a b ∩ E) := by
      gcongr
      exact intervalCover_anti (by linarith)
    _ ≤ _ := by
      gcongr
      exact intervalCover_local_le_of_approximation hs hδ happrox

end Kakeya4.Hard.RestrictedTriple
