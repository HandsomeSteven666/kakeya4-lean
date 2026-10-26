import Kakeya4.Hard.RestrictedTriple.Covering

/-! Finite representatives selected inside the original arbitrary sets.
The large-H premise is transported to cardinality without replacing H by a product.
All radius losses are explicit. This does not prove the H-003 dichotomy. -/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem exists_finite_cube_representatives {ι : Type*} [Fintype ι]
    {E : Set (ι → ℝ)} (hE : TotallyBounded E) {r : ℝ} (hr : 0 < r) :
    ∃ P : Set (ι → ℝ), P ⊆ E ∧ P.Finite ∧
      IsSeparated (Real.toNNReal (r/2)) P ∧ IsCover (Real.toNNReal (r/2)) E P ∧
      cubeCover r E ≤ (P.encard : ℝ≥0∞) ∧
      (P.encard : ℝ≥0∞) ≤ cubeCover (r/2) E := by
  let e := Real.toNNReal (r/2/2)
  have he : 2*e = Real.toNNReal (r/2) := by
    apply NNReal.coe_injective
    simp [e, Real.toNNReal_of_nonneg (show 0 ≤ r/2/2 by positivity),
      Real.toNNReal_of_nonneg (show 0 ≤ r/2 by positivity)]
    ring
  have hfinite : externalCoveringNumber e E < ⊤ := by
    have hh := cubeCover_lt_top_of_totallyBounded (show 0 < r/2 by positivity) hE
    exact ENat.toENNReal_lt_top.mp hh
  have hpack : packingNumber (Real.toNNReal (r/2)) E ≠ ⊤ := by
    rw [← he]
    exact ne_top_of_le_ne_top hfinite.ne (packingNumber_two_mul_le_externalCoveringNumber e E)
  let P := maximalSeparatedSet (Real.toNNReal (r/2)) E
  have hcard : P.encard = packingNumber (Real.toNNReal (r/2)) E :=
    encard_maximalSeparatedSet hpack
  have hP : P.Finite := Set.encard_ne_top_iff.mp (hcard ▸ hpack)
  have hcover : IsCover (Real.toNNReal (r/2)) E P := isCover_maximalSeparatedSet hpack
  refine ⟨P, maximalSeparatedSet_subset, hP, isSeparated_maximalSeparatedSet, hcover,
    ENat.toENNReal_mono hcover.externalCoveringNumber_le_encard, ?_⟩
  apply ENat.toENNReal_mono
  rw [hcard, ← he]
  exact packingNumber_two_mul_le_externalCoveringNumber e E

/-- Injective coordinate embeddings allow the finite representatives to remain original points. -/
theorem exists_finite_representatives_under_injection {X ι : Type*} [Fintype ι]
    (f : X → ι → ℝ) (hf : Function.Injective f) {E : Set X}
    (hE : TotallyBounded (f '' E)) {r : ℝ} (hr : 0 < r) :
    ∃ P : Set X, P ⊆ E ∧ P.Finite ∧
      IsSeparated (Real.toNNReal (r/2)) (f '' P) ∧
      IsCover (Real.toNNReal (r/2)) (f '' E) (f '' P) ∧
      cubeCover r (f '' E) ≤ (P.encard : ℝ≥0∞) ∧
      (P.encard : ℝ≥0∞) ≤ cubeCover (r/2) (f '' E) := by
  obtain ⟨Q, hQE, hQ, hsep, hcover, hlo, hhi⟩ := exists_finite_cube_representatives hE hr
  let P := E ∩ f ⁻¹' Q
  have himg : f '' P = Q := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx.2
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hQE hy
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  have hP : P.Finite := (himg ▸ hQ).of_finite_image hf.injOn
  have hcard : P.encard = Q.encard := by rw [← himg, hf.encard_image]
  refine ⟨P, inter_subset_left, hP, ?_, ?_, ?_, ?_⟩
  · rwa [himg]
  · rwa [himg]
  · rwa [hcard]
  · rwa [hcard]

theorem exists_finite_restricted_triple_representatives {A B : Set Plane}
    (hA : A ⊆ unitSquare) (hB : B ⊆ unitSquare) {H : Set Triple}
    (hH : H ⊆ tripleCarrier A B) {r : ℝ} (hr : 0 < r) :
    ∃ P : Set Triple, P ⊆ H ∧ P.Finite ∧
      IsSeparated (Real.toNNReal (r/2)) (tripleCoordinates '' P) ∧
      IsCover (Real.toNNReal (r/2)) (tripleCoordinates '' H) (tripleCoordinates '' P) ∧
      tripleCover r H ≤ (P.encard : ℝ≥0∞) ∧
      (P.encard : ℝ≥0∞) ≤ tripleCover (r/2) H := by
  have hsub : tripleCoordinates '' H ⊆ Icc (0 : (Fin 3 × Fin 2) → ℝ) 1 := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' := hH ht
    have hc : ∀ j : Fin 3, (![t.1, t.2.1, t.2.2] j) ∈ unitSquare := by
      intro j
      fin_cases j
      · exact hA ht'.1
      · exact hB ht'.2.1
      · exact hB ht'.2.2
    exact ⟨fun ji ↦ (hc ji.1 ji.2).1, fun ji ↦ (hc ji.1 ji.2).2⟩
  exact exists_finite_representatives_under_injection tripleCoordinates tripleCoordinates_injective
    (isCompact_Icc.totallyBounded.subset hsub) hr

/-- A separated set has local cardinality bounded by the original cube entropy. -/
theorem separated_local_encard_le_planeCover {A P : Set Plane} {r : ℝ}
    (hr : 0 ≤ r) (hPA : P ⊆ A)
    (hsep : IsSeparated (Real.toNNReal r) (planeCoordinates '' P)) (D : Set Plane) :
    ((P ∩ D).encard : ℝ≥0∞) ≤ planeCover r (A ∩ D) := by
  have he : 2*Real.toNNReal (r/2) = Real.toNNReal r := by
    apply NNReal.coe_injective
    simp [Real.toNNReal_of_nonneg hr,
      Real.toNNReal_of_nonneg (show 0 ≤ r/2 by positivity)]
    ring
  have hsub : planeCoordinates '' (P ∩ D) ⊆ planeCoordinates '' (A ∩ D) :=
    image_mono (inter_subset_inter_left _ hPA)
  have hsep' : IsSeparated (Real.toNNReal r) (planeCoordinates '' (P ∩ D)) :=
    hsep.subset (image_mono inter_subset_left)
  have hc := hsep'.encard_le_packingNumber hsub
  have hh := hc.trans (he ▸ packingNumber_two_mul_le_externalCoveringNumber (Real.toNNReal (r/2))
    (planeCoordinates '' (A ∩ D)))
  rw [planeCoordinates_injective.encard_image] at hh
  exact ENat.toENNReal_mono hh

/-- Upper AD alone gives the finite separated local-count bound, with no lower regularity. -/
theorem separated_local_count_of_ADUpperBound {A P : Set Plane} {p C : ℝ}
    (hp : 0 < p) (hAD : ADUpperBound p C A) (hPA : P ⊆ A)
    (hsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' P))
    (z : Plane) {w : ℝ} (hw : p ≤ w) :
    ((P ∩ ball z w).encard : ℝ≥0∞) ≤ ENNReal.ofReal (C*w/p) :=
  (separated_local_encard_le_planeCover hp.le hPA hsep (ball z w)).trans
    (hAD z p w le_rfl hw)

end Kakeya4.Hard.RestrictedTriple
