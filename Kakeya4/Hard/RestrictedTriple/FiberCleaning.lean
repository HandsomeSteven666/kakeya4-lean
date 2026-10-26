import Kakeya4.Hard.RestrictedTriple.EndpointNormalization

/-! Simultaneous fiber cleaning by finite optimization of a projection-cost potential.
The selected graph is an actual subset of the original edge set. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Kakeya4.Hard.RestrictedTriple

def fiberPotential {α β ι : Type*} [DecidableEq β]
    (I : Finset ι) (f : ι → α → β) (w : ι → ℝ) (S : Finset α) : ℝ :=
  (S.card : ℝ)-∑ i ∈ I, w i*((S.image (f i)).card : ℝ)

/-- Clean all specified partitions at once. The exact loss is the total original
projection cost, and each surviving fiber has the prescribed absolute lower bound. -/
theorem exists_simultaneous_fiber_cleaning {α β ι : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (I : Finset ι) (f : ι → α → β) (w : ι → ℝ) (H : Finset α)
    (hw : ∀ i ∈ I, 0 ≤ w i) :
    ∃ T : Finset α, T ⊆ H ∧
      (H.card : ℝ)-(∑ i ∈ I, w i*((H.image (f i)).card : ℝ)) ≤ T.card ∧
      ∀ i ∈ I, ∀ x ∈ T, w i ≤ ((T.filter (fun y ↦ f i y = f i x)).card : ℝ) := by
  classical
  obtain ⟨T,hTp,hmax⟩ := Finset.exists_max_image H.powerset (fiberPotential I f w)
    (Finset.powerset_nonempty H)
  have hTH : T ⊆ H := Finset.mem_powerset.mp hTp
  have hcost0 : 0 ≤ ∑ i ∈ I, w i*((T.image (f i)).card : ℝ) :=
    Finset.sum_nonneg (fun i hi ↦ mul_nonneg (hw i hi) (Nat.cast_nonneg _))
  have hmaxH := hmax H (Finset.mem_powerset.mpr (Finset.Subset.refl H))
  refine ⟨T,hTH,?_,?_⟩
  · unfold fiberPotential at hmaxH
    linarith
  · intro i hi x hx
    by_contra hbad
    let D := T.filter (fun y ↦ f i y = f i x)
    let S := T \ D
    have hbad' : (D.card : ℝ) < w i := lt_of_not_ge hbad
    have hDT : D ⊆ T := Finset.filter_subset _ _
    have hST : S ⊆ T := Finset.sdiff_subset
    have hSH : S ⊆ H := hST.trans hTH
    have hmaxS := hmax S (Finset.mem_powerset.mpr hSH)
    have hcards : (S.card : ℝ)+(D.card : ℝ) = T.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hDT
    have hproj (j : ι) : ((S.image (f j)).card : ℝ) ≤ (T.image (f j)).card := by
      exact_mod_cast Finset.card_le_card (Finset.image_subset_image hST)
    have hremoved : S.image (f i) ⊆ (T.image (f i)).erase (f i x) := by
      intro z hz
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hyT,hyD⟩ := Finset.mem_sdiff.mp hy
      apply Finset.mem_erase.mpr
      refine ⟨?_,Finset.mem_image_of_mem _ hyT⟩
      intro heq
      exact hyD (Finset.mem_filter.mpr ⟨hyT,heq⟩)
    have hcardI : ((S.image (f i)).card : ℝ)+1 ≤ (T.image (f i)).card := by
      have hle := Finset.card_le_card hremoved
      have hmem : f i x ∈ T.image (f i) := Finset.mem_image_of_mem _ hx
      have heq := Finset.card_erase_add_one hmem
      exact_mod_cast (by omega : (S.image (f i)).card+1 ≤ (T.image (f i)).card)
    have hcostI : w i*((S.image (f i)).card : ℝ)+w i ≤
        w i*((T.image (f i)).card : ℝ) := by
      nlinarith [hw i hi]
    have hother : (∑ j ∈ I.erase i, w j*((S.image (f j)).card : ℝ)) ≤
        ∑ j ∈ I.erase i, w j*((T.image (f j)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hproj j) (hw j (Finset.mem_of_mem_erase hj))
    have hsumS := Finset.sum_erase_add I (fun j ↦ w j*((S.image (f j)).card : ℝ)) hi
    have hsumT := Finset.sum_erase_add I (fun j ↦ w j*((T.image (f j)).card : ℝ)) hi
    have hcost : (∑ j ∈ I, w j*((S.image (f j)).card : ℝ))+w i ≤
        ∑ j ∈ I, w j*((T.image (f j)).card : ℝ) := by linarith
    unfold fiberPotential at hmaxS
    linarith

theorem exists_simultaneous_fiber_cleaning_of_budget {α β ι : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (I : Finset ι) (f : ι → α → β) (w : ι → ℝ) (H : Finset α)
    (hw : ∀ i ∈ I, 0 ≤ w i) {ε : ℝ}
    (hbudget : (∑ i ∈ I, w i*((H.image (f i)).card : ℝ)) ≤ ε*(H.card : ℝ)) :
    ∃ T : Finset α, T ⊆ H ∧ (1-ε)*(H.card : ℝ) ≤ T.card ∧
      ∀ i ∈ I, ∀ x ∈ T, w i ≤ ((T.filter (fun y ↦ f i y = f i x)).card : ℝ) := by
  obtain ⟨T,hTH,hcard,hdense⟩ := exists_simultaneous_fiber_cleaning I f w H hw
  exact ⟨T,hTH,by nlinarith,hdense⟩

end Kakeya4.Hard.RestrictedTriple
