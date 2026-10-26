import Kakeya4.Hard.RestrictedTriple.FiniteModel

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

/-- The actual dot-difference map is 6-Lipschitz on the unit cube in coordinate sup distance. -/
theorem abs_dotDifference_sub_le {t u : Triple} {δ : ℝ} (hδ : 0 ≤ δ)
    (ht : t ∈ tripleCarrier unitSquare unitSquare)
    (hu : u ∈ tripleCarrier unitSquare unitSquare)
    (hclose : dist (tripleCoordinates t) (tripleCoordinates u) ≤ δ) :
    |dotDifference t-dotDifference u| ≤ 6*δ := by
  have hcoord (j : Fin 3) (i : Fin 2) :
      |tripleCoordinates t (j,i)-tripleCoordinates u (j,i)| ≤ δ := by
    simpa [Real.dist_eq] using (dist_le_pi_dist (tripleCoordinates t) (tripleCoordinates u) (j,i)).trans hclose
  have hterm (i : Fin 2) :
      |t.1 i*(t.2.1 i-t.2.2 i)-u.1 i*(u.2.1 i-u.2.2 i)| ≤ 3*δ := by
    have ha : |t.1 i-u.1 i| ≤ δ := by simpa [tripleCoordinates] using hcoord 0 i
    have hb : |t.2.1 i-u.2.1 i| ≤ δ := by simpa [tripleCoordinates] using hcoord 1 i
    have hc : |t.2.2 i-u.2.2 i| ≤ δ := by simpa [tripleCoordinates] using hcoord 2 i
    have hbc : |t.2.1 i-t.2.2 i| ≤ 1 := abs_le.mpr
      ⟨by linarith [(ht.2.1 i).1, (ht.2.2 i).2], by linarith [(ht.2.1 i).2, (ht.2.2 i).1]⟩
    have hau : |u.1 i| ≤ 1 := abs_le.mpr ⟨by linarith [(hu.1 i).1], (hu.1 i).2⟩
    have hdiff : |(t.2.1 i-t.2.2 i)-(u.2.1 i-u.2.2 i)| ≤ 2*δ := by
      have heq : (t.2.1 i-t.2.2 i)-(u.2.1 i-u.2.2 i) =
          (t.2.1 i-u.2.1 i)-(t.2.2 i-u.2.2 i) := by ring
      rw [heq]
      exact (abs_sub _ _).trans (by linarith)
    calc
      _ = |(t.1 i-u.1 i)*(t.2.1 i-t.2.2 i) +
          u.1 i*((t.2.1 i-t.2.2 i)-(u.2.1 i-u.2.2 i))| := by congr 1; ring
      _ ≤ |t.1 i-u.1 i| * |t.2.1 i-t.2.2 i| +
          |u.1 i| * |(t.2.1 i-t.2.2 i)-(u.2.1 i-u.2.2 i)| := by
        simpa only [abs_mul] using abs_add_le
          ((t.1 i-u.1 i)*(t.2.1 i-t.2.2 i))
          (u.1 i*((t.2.1 i-t.2.2 i)-(u.2.1 i-u.2.2 i)))
      _ ≤ 3*δ := by
        have h1 := mul_le_mul ha hbc (abs_nonneg _) hδ
        have h2 := mul_le_mul hau hdiff (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
        nlinarith
  have hexpand (v : Triple) : dotDifference v =
      v.1 0*(v.2.1 0-v.2.2 0) + v.1 1*(v.2.1 1-v.2.2 1) := by
    simp [dotDifference, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
    ring
  rw [hexpand t, hexpand u]
  have heq : (t.1 0*(t.2.1 0-t.2.2 0) + t.1 1*(t.2.1 1-t.2.2 1)) -
      (u.1 0*(u.2.1 0-u.2.2 0) + u.1 1*(u.2.1 1-u.2.2 1)) =
      (t.1 0*(t.2.1 0-t.2.2 0)-u.1 0*(u.2.1 0-u.2.2 0)) +
      (t.1 1*(t.2.1 1-t.2.2 1)-u.1 1*(u.2.1 1-u.2.2 1)) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith [hterm 0, hterm 1])

/-- Coordinate nets transport the actual image, with the explicit error 6δ. -/
theorem dotDifferenceImage_approximation {A B : Set Plane}
    (hA : A ⊆ unitSquare) (hB : B ⊆ unitSquare) {H P : Set Triple}
    (hH : H ⊆ tripleCarrier A B) (hPH : P ⊆ H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcover : IsCover (Real.toNNReal δ) (tripleCoordinates '' H) (tripleCoordinates '' P)) :
    ∀ x ∈ dotDifferenceImage H, ∃ y ∈ dotDifferenceImage P, |x-y| ≤ 6*δ := by
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨_, ⟨u, hu, rfl⟩, hdist⟩ := hcover ⟨t, ht, rfl⟩
  change edist (tripleCoordinates t) (tripleCoordinates u) ≤ (Real.toNNReal δ : ℝ≥0∞) at hdist
  have hd : dist (tripleCoordinates t) (tripleCoordinates u) ≤ δ := by
    apply (edist_le_ofReal hδ).mp
    simpa only [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hδ] using hdist
  have htu : t ∈ tripleCarrier unitSquare unitSquare :=
    ⟨hA (hH ht).1, hB (hH ht).2.1, hB (hH ht).2.2⟩
  have huu : u ∈ tripleCarrier unitSquare unitSquare :=
    ⟨hA (hH (hPH hu)).1, hB (hH (hPH hu)).2.1, hB (hH (hPH hu)).2.2⟩
  exact ⟨dotDifference u, ⟨u, hu, rfl⟩, abs_dotDifference_sub_le hδ htu huu hd⟩

/-- Approximation transfers external interval entropy with the exact additive scale cost. -/
theorem intervalCover_le_of_approximation {E F : Set ℝ} {s δ : ℝ}
    (hs : 0 ≤ s) (hδ : 0 ≤ δ)
    (happrox : ∀ x ∈ E, ∃ y ∈ F, |x-y| ≤ δ) :
    intervalCover (s+2*δ) E ≤ intervalCover s F := by
  apply ENat.toENNReal_mono
  simp only [externalCoveringNumber, le_iInf_iff]
  intro Q hQ
  apply IsCover.externalCoveringNumber_le_encard
  intro x hx
  obtain ⟨y, hy, hxy⟩ := happrox x hx
  obtain ⟨z, hz, hyz⟩ := hQ hy
  change edist y z ≤ (Real.toNNReal (s/2) : ℝ≥0∞) at hyz
  refine ⟨z, hz, ?_⟩
  change edist x z ≤ (Real.toNNReal ((s+2*δ)/2) : ℝ≥0∞)
  have hyz' : dist y z ≤ s/2 := by
    apply (edist_le_ofReal (by positivity)).mp
    simpa only [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ (show 0 ≤ s/2 by positivity)] using hyz
  have hxz : dist x z ≤ (s+2*δ)/2 := by
    have hxy' : dist x y ≤ δ := by simpa only [Real.dist_eq] using hxy
    linarith [dist_triangle x y z]
  have hh := (edist_le_ofReal (show 0 ≤ (s+2*δ)/2 by positivity)).mpr hxz
  simpa only [ENNReal.coe_nnreal_eq,
    Real.coe_toNNReal _ (show 0 ≤ (s+2*δ)/2 by positivity)] using hh

/-- A finite subset of the original restricted H preserves its large entropy and actual image. -/
theorem exists_finite_restricted_triple_model {A B : Set Plane}
    (hA : A ⊆ unitSquare) (hB : B ⊆ unitSquare) {H : Set Triple}
    (hH : H ⊆ tripleCarrier A B) {r : ℝ} (hr : 0 < r) :
    ∃ P : Set Triple, P ⊆ H ∧ P.Finite ∧
      IsSeparated (Real.toNNReal (r/2)) (tripleCoordinates '' P) ∧
      tripleCover r H ≤ (P.encard : ℝ≥0∞) ∧
      (P.encard : ℝ≥0∞) ≤ tripleCover (r/2) H ∧
      dotDifferenceImage P ⊆ dotDifferenceImage H ∧
      (∀ x ∈ dotDifferenceImage H, ∃ y ∈ dotDifferenceImage P, |x-y| ≤ 3*r) ∧
      (∀ s : ℝ, 0 ≤ s → intervalCover (s+6*r) (dotDifferenceImage H) ≤
        intervalCover s (dotDifferenceImage P)) := by
  obtain ⟨P, hPH, hP, hsep, hcover, hlo, hhi⟩ :=
    exists_finite_restricted_triple_representatives hA hB hH hr
  have happ : ∀ x ∈ dotDifferenceImage H, ∃ y ∈ dotDifferenceImage P, |x-y| ≤ 3*r := by
    intro x hx
    obtain ⟨y, hy, hh⟩ := dotDifferenceImage_approximation hA hB hH hPH
      (show 0 ≤ r/2 by positivity) hcover x hx
    exact ⟨y, hy, by linarith⟩
  refine ⟨P, hPH, hP, hsep, hlo, hhi, image_mono hPH, happ, ?_⟩
  intro s hs
  have hh := intervalCover_le_of_approximation hs (show 0 ≤ 3*r by positivity) happ
  have heq : s+2*(3*r) = s+6*r := by ring
  rwa [heq] at hh

end Kakeya4.Hard.RestrictedTriple
