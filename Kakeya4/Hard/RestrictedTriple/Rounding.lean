import Kakeya4.Hard.RestrictedTriple.ImageTransport

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

/-- Rounding by δ is injective on a 2δ-separated set. The strict separation
convention is essential; the original restricted triples need not form a product. -/
theorem rounding_injOn_of_separated {X Y ι : Type*} [Fintype ι]
    {E : Set X} (f : X → ι → ℝ) (g : X → Y) (j : Y → ι → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hf : Function.Injective f)
    (hsep : IsSeparated (Real.toNNReal (2*δ)) (f '' E))
    (hclose : ∀ x ∈ E, dist (f x) (j (g x)) ≤ δ) : Set.InjOn g E := by
  intro x hx y hy hxy
  by_contra hne
  have hstrict := hsep (show f x ∈ f '' E from ⟨x, hx, rfl⟩)
    (show f y ∈ f '' E from ⟨y, hy, rfl⟩) (fun h ↦ hne (hf h))
  have hdist : dist (f x) (f y) ≤ 2*δ := by
    have h1 := hclose x hx
    have h2 := hclose y hy
    rw [hxy] at h1
    have hh := dist_triangle (f x) (j (g y)) (f y)
    rw [dist_comm (j (g y)) (f y)] at hh
    linarith
  have he : edist (f x) (f y) ≤ (Real.toNNReal (2*δ) : ℝ≥0∞) := by
    have hh := (edist_le_ofReal (show 0 ≤ 2*δ by positivity)).mpr hdist
    simpa only [ENNReal.coe_nnreal_eq,
      Real.coe_toNNReal _ (show 0 ≤ 2*δ by positivity)] using hh
  exact (not_lt_of_ge he) hstrict

theorem exists_finite_plane_net {A : Set Plane} (hA : A ⊆ unitSquare)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ P : Set Plane, P ⊆ A ∧ P.Finite ∧
      IsSeparated (Real.toNNReal δ) (planeCoordinates '' P) ∧
      ∀ x ∈ A, ∃ y ∈ P, dist (planeCoordinates x) (planeCoordinates y) ≤ δ := by
  have hsub : planeCoordinates '' A ⊆ Icc (0 : Fin 2 → ℝ) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨fun i ↦ (hA hx i).1, fun i ↦ (hA hx i).2⟩
  obtain ⟨P, hPA, hP, hsep, hcover, _hlo, _hhi⟩ :=
    exists_finite_representatives_under_injection planeCoordinates planeCoordinates_injective
      (isCompact_Icc.totallyBounded.subset hsub) (show 0 < 2*δ by positivity)
  have heq : (2*δ)/2 = δ := by ring
  rw [heq] at hsep hcover
  refine ⟨P, hPA, hP, hsep, ?_⟩
  intro x hx
  obtain ⟨_, ⟨y, hy, rfl⟩, hdist⟩ := hcover ⟨x, hx, rfl⟩
  change edist (planeCoordinates x) (planeCoordinates y) ≤ (Real.toNNReal δ : ℝ≥0∞) at hdist
  refine ⟨y, hy, (edist_le_ofReal hδ.le).mp ?_⟩
  simpa only [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hδ.le] using hdist

/-- A large restricted H has a finite rounded model in independently separated marginals.
The model is built from H, rather than the full product; cardinality is preserved at scale 4δ. -/
theorem exists_separated_marginal_restricted_model {A B : Set Plane}
    (hA : A ⊆ unitSquare) (hB : B ⊆ unitSquare) {H : Set Triple}
    (hH : H ⊆ tripleCarrier A B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ PA PB : Set Plane, ∃ Q : Set Triple,
      PA ⊆ A ∧ PB ⊆ B ∧ PA.Finite ∧ PB.Finite ∧ Q.Finite ∧
      IsSeparated (Real.toNNReal δ) (planeCoordinates '' PA) ∧
      IsSeparated (Real.toNNReal δ) (planeCoordinates '' PB) ∧
      Q ⊆ tripleCarrier PA PB ∧ tripleCover (4*δ) H ≤ (Q.encard : ℝ≥0∞) ∧
      (∀ u ∈ Q, ∃ t ∈ H, dist (tripleCoordinates t) (tripleCoordinates u) ≤ δ) ∧
      (∀ t ∈ H, ∃ u ∈ Q, dist (tripleCoordinates t) (tripleCoordinates u) ≤ 3*δ) := by
  classical
  obtain ⟨PA, hPA, hPAfin, hPAsep, hna⟩ := exists_finite_plane_net hA hδ
  obtain ⟨PB, hPB, hPBfin, hPBsep, hnb⟩ := exists_finite_plane_net hB hδ
  let ra : Plane → Plane := fun x ↦ if hx : x ∈ A then (hna x hx).choose else x
  let rb : Plane → Plane := fun x ↦ if hx : x ∈ B then (hnb x hx).choose else x
  have hra : ∀ x ∈ A, ra x ∈ PA ∧ dist (planeCoordinates x) (planeCoordinates (ra x)) ≤ δ := by
    intro x hx
    simpa only [ra, dite_eq_left hx] using (hna x hx).choose_spec
  have hrb : ∀ x ∈ B, rb x ∈ PB ∧ dist (planeCoordinates x) (planeCoordinates (rb x)) ≤ δ := by
    intro x hx
    simpa only [rb, dite_eq_left hx] using (hnb x hx).choose_spec
  let g : Triple → Triple := fun t ↦ (ra t.1, rb t.2.1, rb t.2.2)
  have hgmem : ∀ t ∈ H, g t ∈ tripleCarrier PA PB := by
    intro t ht
    exact ⟨(hra _ (hH ht).1).1, (hrb _ (hH ht).2.1).1, (hrb _ (hH ht).2.2).1⟩
  have hgclose : ∀ t ∈ H, dist (tripleCoordinates t) (tripleCoordinates (g t)) ≤ δ := by
    intro t ht
    apply (dist_pi_le_iff hδ.le).mpr
    intro ji
    rcases ji with ⟨j,i⟩
    fin_cases j
    · exact (dist_le_pi_dist _ _ i).trans (hra _ (hH ht).1).2
    · exact (dist_le_pi_dist _ _ i).trans (hrb _ (hH ht).2.1).2
    · exact (dist_le_pi_dist _ _ i).trans (hrb _ (hH ht).2.2).2
  obtain ⟨P, hPH, hPfin, hPsep, hPcover, hlarge, _hupper⟩ :=
    exists_finite_restricted_triple_representatives hA hB hH (show 0 < 4*δ by positivity)
  have hhalf : (4*δ)/2 = 2*δ := by ring
  rw [hhalf] at hPsep hPcover
  have hinj : Set.InjOn g P := rounding_injOn_of_separated tripleCoordinates g tripleCoordinates
    hδ.le tripleCoordinates_injective hPsep (fun t ht ↦ hgclose t (hPH ht))
  refine ⟨PA, PB, g '' P, hPA, hPB, hPAfin, hPBfin, hPfin.image g, hPAsep, hPBsep,
    ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hgmem t (hPH ht)
  · rwa [hinj.encard_image]
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, hPH ht, hgclose t (hPH ht)⟩
  · intro t ht
    obtain ⟨_, ⟨v, hv, rfl⟩, hdist⟩ := hPcover ⟨t, ht, rfl⟩
    change edist (tripleCoordinates t) (tripleCoordinates v) ≤ (Real.toNNReal (2*δ) : ℝ≥0∞) at hdist
    have htv : dist (tripleCoordinates t) (tripleCoordinates v) ≤ 2*δ := by
      apply (edist_le_ofReal (show 0 ≤ 2*δ by positivity)).mp
      simpa only [ENNReal.coe_nnreal_eq,
        Real.coe_toNNReal _ (show 0 ≤ 2*δ by positivity)] using hdist
    refine ⟨g v, ⟨v, hv, rfl⟩, ?_⟩
    have hvg := hgclose v (hPH hv)
    have hh := dist_triangle (tripleCoordinates t) (tripleCoordinates v) (tripleCoordinates (g v))
    linarith

/-- Approximation need not select a subset: both actual triple sets may be different. -/
theorem dotImage_approximation_of_nearby_triples {H Q : Set Triple} {δ : ℝ}
    (hδ : 0 ≤ δ) (hH : H ⊆ tripleCarrier unitSquare unitSquare)
    (hQ : Q ⊆ tripleCarrier unitSquare unitSquare)
    (hclose : ∀ t ∈ H, ∃ u ∈ Q, dist (tripleCoordinates t) (tripleCoordinates u) ≤ δ) :
    ∀ x ∈ dotDifferenceImage H, ∃ y ∈ dotDifferenceImage Q, |x-y| ≤ 6*δ := by
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨u, hu, hd⟩ := hclose t ht
  exact ⟨dotDifference u, ⟨u, hu, rfl⟩, abs_dotDifference_sub_le hδ (hH ht) (hQ hu) hd⟩

/-- Finite separated marginals, restricted cardinality, and the original dot image
are transported together, with every scale loss visible. -/
theorem exists_separated_marginal_dot_model {A B : Set Plane}
    (hA : A ⊆ unitSquare) (hB : B ⊆ unitSquare) {H : Set Triple}
    (hH : H ⊆ tripleCarrier A B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ PA PB : Set Plane, ∃ Q : Set Triple,
      PA ⊆ A ∧ PB ⊆ B ∧ PA.Finite ∧ PB.Finite ∧ Q.Finite ∧
      IsSeparated (Real.toNNReal δ) (planeCoordinates '' PA) ∧
      IsSeparated (Real.toNNReal δ) (planeCoordinates '' PB) ∧
      Q ⊆ tripleCarrier PA PB ∧ tripleCover (4*δ) H ≤ (Q.encard : ℝ≥0∞) ∧
      (∀ x ∈ dotDifferenceImage H, ∃ y ∈ dotDifferenceImage Q, |x-y| ≤ 18*δ) ∧
      (∀ y ∈ dotDifferenceImage Q, ∃ x ∈ dotDifferenceImage H, |y-x| ≤ 6*δ) ∧
      (∀ s : ℝ, 0 ≤ s → intervalCover (s+36*δ) (dotDifferenceImage H) ≤
        intervalCover s (dotDifferenceImage Q)) := by
  obtain ⟨PA, PB, Q, hPA, hPB, hPAfin, hPBfin, hQfin, hPAsep, hPBsep,
    hQ, hlarge, hQnear, hHnear⟩ := exists_separated_marginal_restricted_model hA hB hH hδ
  have hHu : H ⊆ tripleCarrier unitSquare unitSquare := by
    intro t ht
    exact ⟨hA (hH ht).1, hB (hH ht).2.1, hB (hH ht).2.2⟩
  have hQu : Q ⊆ tripleCarrier unitSquare unitSquare := by
    intro t ht
    exact ⟨hA (hPA (hQ ht).1), hB (hPB (hQ ht).2.1), hB (hPB (hQ ht).2.2)⟩
  have hforward : ∀ x ∈ dotDifferenceImage H, ∃ y ∈ dotDifferenceImage Q, |x-y| ≤ 18*δ := by
    intro x hx
    obtain ⟨y, hy, hh⟩ := dotImage_approximation_of_nearby_triples
      (show 0 ≤ 3*δ by positivity) hHu hQu hHnear x hx
    exact ⟨y, hy, by linarith⟩
  have hbackward : ∀ y ∈ dotDifferenceImage Q, ∃ x ∈ dotDifferenceImage H, |y-x| ≤ 6*δ := by
    apply dotImage_approximation_of_nearby_triples hδ.le hQu hHu
    intro u hu
    obtain ⟨t, ht, hd⟩ := hQnear u hu
    exact ⟨t, ht, by rwa [dist_comm]⟩
  refine ⟨PA, PB, Q, hPA, hPB, hPAfin, hPBfin, hQfin, hPAsep, hPBsep,
    hQ, hlarge, hforward, hbackward, ?_⟩
  intro s hs
  have hh := intervalCover_le_of_approximation hs (show 0 ≤ 18*δ by positivity) hforward
  have heq : s+2*(18*δ) = s+36*δ := by ring
  rwa [heq] at hh

end Kakeya4.Hard.RestrictedTriple
