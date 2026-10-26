import Kakeya4.Hard.RestrictedTriple.Statement
import Mathlib.Tactic

/-! Concrete semantic and finite-cover tools for the full H-003 target.
These do not prove ManuscriptDotProductAlternative. -/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem cubeCover_empty {ι : Type*} [Fintype ι] (r : ℝ) :
    cubeCover r (∅ : Set (ι → ℝ)) = 0 := by simp [cubeCover]

theorem cubeCover_mono {ι : Type*} [Fintype ι] {E F : Set (ι → ℝ)} {r : ℝ}
    (h : E ⊆ F) : cubeCover r E ≤ cubeCover r F :=
  ENat.toENNReal_mono (Metric.externalCoveringNumber_mono_set h)

theorem cubeCover_pos_iff {ι : Type*} [Fintype ι] (r : ℝ) (E : Set (ι → ℝ)) :
    0 < cubeCover r E ↔ E.Nonempty := by
  rw [cubeCover, ← ENat.toENNReal_zero, ENat.toENNReal_lt,
    Metric.externalCoveringNumber_pos_iff]

theorem cubeCover_lt_top_of_totallyBounded {ι : Type*} [Fintype ι] {r : ℝ}
    (hr : 0 < r) {E : Set (ι → ℝ)} (hE : TotallyBounded E) : cubeCover r E < ∞ := by
  have he : Real.toNNReal (r/2) ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr (by positivity))
  obtain ⟨C, _hCE, hC, hcover⟩ := Metric.exists_finite_isCover_of_totallyBounded he hE
  apply ENat.toENNReal_lt_top.mpr
  exact lt_of_le_of_lt hcover.externalCoveringNumber_le_encard hC.encard_lt_top

theorem planeCoordinates_injective : Function.Injective planeCoordinates := by
  intro x y h
  exact PiLp.ext (fun i ↦ congrFun h i)

theorem tripleCoordinates_injective : Function.Injective tripleCoordinates := by
  intro x y h
  apply Prod.ext
  · apply PiLp.ext
    intro i
    simpa [tripleCoordinates] using congrFun h ((0 : Fin 3), i)
  · apply Prod.ext
    · apply PiLp.ext
      intro i
      simpa [tripleCoordinates] using congrFun h ((1 : Fin 3), i)
    · apply PiLp.ext
      intro i
      simpa [tripleCoordinates] using congrFun h ((2 : Fin 3), i)

theorem planeCover_mono {A B : Set Plane} {r : ℝ} (h : A ⊆ B) :
    planeCover r A ≤ planeCover r B := cubeCover_mono (image_mono h)

theorem planeCover_lt_top_of_subset_unitSquare {A : Set Plane} (hA : A ⊆ unitSquare)
    {r : ℝ} (hr : 0 < r) : planeCover r A < ∞ := by
  have hsub : planeCoordinates '' A ⊆ Icc (0 : Fin 2 → ℝ) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨fun i ↦ (hA hx i).1, fun i ↦ (hA hx i).2⟩
  exact cubeCover_lt_top_of_totallyBounded hr (isCompact_Icc.totallyBounded.subset hsub)

theorem tripleCover_lt_top_of_unitSquare {A B : Set Plane} (hA : A ⊆ unitSquare)
    (hB : B ⊆ unitSquare) {H : Set Triple} (hH : H ⊆ tripleCarrier A B)
    {r : ℝ} (hr : 0 < r) : tripleCover r H < ∞ := by
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
  exact cubeCover_lt_top_of_totallyBounded hr (isCompact_Icc.totallyBounded.subset hsub)

theorem ADUpperBound_mono {A B : Set Plane} {p C : ℝ}
    (hB : ADUpperBound p C B) (hAB : A ⊆ B) : ADUpperBound p C A := by
  intro z s w hps hsw
  exact (planeCover_mono (inter_subset_inter_left _ hAB)).trans (hB z s w hps hsw)

theorem continuous_dotDifference : Continuous dotDifference := by unfold dotDifference; fun_prop

theorem abs_dotDifference_le_two {A B : Set Plane} (hA : A ⊆ unitSquare)
    (hB : B ⊆ unitSquare) {t : Triple} (ht : t ∈ tripleCarrier A B) :
    |dotDifference t| ≤ 2 := by
  have ha := hA ht.1
  have hb := hB ht.2.1
  have hc := hB ht.2.2
  have hterm (i : Fin 2) : |t.1 i * (t.2.1 i-t.2.2 i)| ≤ 1 := by
    have hai : |t.1 i| ≤ 1 := abs_le.mpr ⟨by linarith [(ha i).1], (ha i).2⟩
    have hdi : |t.2.1 i-t.2.2 i| ≤ 1 := abs_le.mpr
      ⟨by linarith [(hb i).1, (hc i).2], by linarith [(hb i).2, (hc i).1]⟩
    rw [abs_mul]
    nlinarith [abs_nonneg (t.1 i), abs_nonneg (t.2.1 i-t.2.2 i)]
  have heq : dotDifference t =
      t.1 0 * (t.2.1 0-t.2.2 0) + t.1 1 * (t.2.1 1-t.2.2 1) := by
    simp [dotDifference, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith [hterm 0, hterm 1])

theorem intervalCover_lt_top_of_dotDifferenceImage {A B : Set Plane} (hA : A ⊆ unitSquare)
    (hB : B ⊆ unitSquare) {H : Set Triple} (hH : H ⊆ tripleCarrier A B)
    {r : ℝ} (hr : 0 < r) (J : Set ℝ) :
    intervalCover r (J ∩ dotDifferenceImage H) < ∞ := by
  have hsub : J ∩ dotDifferenceImage H ⊆ Icc (-2:ℝ) 2 := by
    rintro _ ⟨_hxJ, t, ht, rfl⟩
    exact abs_le.mp (abs_dotDifference_le_two hA hB (hH ht))
  have he : Real.toNNReal (r/2) ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr (by positivity))
  obtain ⟨C, _hCE, hC, hcover⟩ := Metric.exists_finite_isCover_of_totallyBounded he
    (isCompact_Icc.totallyBounded.subset hsub)
  apply ENat.toENNReal_lt_top.mpr
  exact lt_of_le_of_lt hcover.externalCoveringNumber_le_encard hC.encard_lt_top

def horizontalLine (a : Plane) : AffineLine where
  anchor := a
  direction := EuclideanSpace.single 0 1
  direction_unit := by simp

theorem lineCarrier_nonempty (L : AffineLine) : (lineCarrier L).Nonempty := by
  refine ⟨L.anchor, 0, ?_⟩
  simp

#print axioms cubeCover_empty
#print axioms cubeCover_mono
#print axioms cubeCover_pos_iff
#print axioms cubeCover_lt_top_of_totallyBounded
#print axioms planeCoordinates_injective
#print axioms tripleCoordinates_injective
#print axioms planeCover_mono
#print axioms planeCover_lt_top_of_subset_unitSquare
#print axioms tripleCover_lt_top_of_unitSquare
#print axioms ADUpperBound_mono
#print axioms continuous_dotDifference
#print axioms abs_dotDifference_le_two
#print axioms intervalCover_lt_top_of_dotDifferenceImage
#print axioms horizontalLine
#print axioms lineCarrier_nonempty
end Kakeya4.Hard.RestrictedTriple
