import Kakeya4.Hard.RestrictedTriple.FiberCleaning

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Kakeya4.Hard.RestrictedTriple

def coordinateMask {ι α : Type*} [DecidableEq ι] (I : Finset ι) (x : ι → α) : ι → Option α :=
  fun j ↦ if j ∈ I then some (x j) else none

theorem coordinateMask_eq_iff {ι α : Type*} [DecidableEq ι] (I : Finset ι) (x y : ι → α) :
    coordinateMask I x = coordinateMask I y ↔ ∀ j ∈ I, x j = y j := by
  constructor
  · intro h j hj
    simpa [coordinateMask,hj] using congrFun h j
  · intro h
    funext j
    by_cases hj : j ∈ I
    · simp [coordinateMask,hj,h j hj]
    · simp [coordinateMask,hj]

/-- Count coordinate restrictions by the finite type of assignments in the vertex classes. -/
theorem card_coordinateMask_image_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) (H : Finset (ι → α))
    (hsupport : ∀ x ∈ H, ∀ j, x j ∈ A j) (I : Finset ι) :
    (H.image (coordinateMask I)).card ≤ ∏ j ∈ I, (A j).card := by
  classical
  let Assign := (j : I) → {a : α // a ∈ A j}
  let encode : Assign → ι → Option α := fun v j ↦ if hj : j ∈ I then some (v ⟨j,hj⟩).val else none
  have hsub : H.image (coordinateMask I) ⊆ (Finset.univ : Finset Assign).image encode := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    let v : Assign := fun j ↦ ⟨x j,hsupport x hx j⟩
    refine Finset.mem_image.mpr ⟨v,Finset.mem_univ _,?_⟩
    funext j
    by_cases hj : j ∈ I <;> simp [encode,coordinateMask,v,hj]
  have hh := (Finset.card_le_card hsub).trans (Finset.card_image_le (f := encode) (s := Finset.univ))
  have hfinite : (Finset.univ : Finset Assign).card = ∏ j ∈ I, (A j).card := by
    simp only [Finset.card_univ,Assign,Fintype.card_pi,Fintype.card_coe]
    exact Finset.prod_coe_sort I (fun j ↦ (A j).card)
  exact hh.trans_eq hfinite

def coordinateDensity {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (c : ℝ) (A : ι → Finset α) (H : Finset (ι → α)) : Prop :=
  (∀ x ∈ H, ∀ j, x j ∈ A j) ∧
    ∀ x ∈ H, ∀ I : Finset ι,
      c*(∏ j ∈ Iᶜ, ((A j).card : ℝ)) ≤
        ((H.filter (fun y ↦ ∀ j ∈ I, y j = x j)).card : ℝ)

/-- Simultaneous density for all coordinate subsets with exactly the paper's 2^-dimension loss. -/
theorem exists_coordinate_refinement {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) (hA : ∀ j, (A j).Nonempty) (H : Finset (ι → α))
    (hsupport : ∀ x ∈ H, ∀ j, x j ∈ A j) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ T : Finset (ι → α), T ⊆ H ∧ (1-ε)*(H.card : ℝ) ≤ T.card ∧
      coordinateDensity ((ε*(H.card : ℝ))/((2:ℝ)^(Fintype.card ι)*(∏ j, ((A j).card : ℝ)))) A T := by
  classical
  let P : ℝ := ∏ j, ((A j).card : ℝ)
  let c : ℝ := (ε*(H.card : ℝ))/((2:ℝ)^(Fintype.card ι)*P)
  have hP : 0 < P := Finset.prod_pos (fun j _ ↦ by exact_mod_cast Finset.card_pos.mpr (hA j))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let w : Finset ι → ℝ := fun I ↦ c*(∏ j ∈ Iᶜ, ((A j).card : ℝ))
  have hw (I : Finset ι) : 0 ≤ w I := by
    exact mul_nonneg hc (Finset.prod_nonneg (fun j _ ↦ Nat.cast_nonneg _))
  have hbudget : (∑ I : Finset ι, w I*((H.image (coordinateMask I)).card : ℝ)) ≤ ε*(H.card : ℝ) := by
    calc
      _ ≤ ∑ I : Finset ι, w I*(∏ j ∈ I, ((A j).card : ℝ)) := by
        apply Finset.sum_le_sum
        intro I _hI
        apply mul_le_mul_of_nonneg_left _ (hw I)
        exact_mod_cast card_coordinateMask_image_le A H hsupport I
      _ = ∑ _I : Finset ι, c*P := by
        apply Finset.sum_congr rfl
        intro I _hI
        dsimp [w]
        rw [mul_assoc,Finset.prod_compl_mul_prod]
      _ = (2:ℝ)^(Fintype.card ι)*(c*P) := by simp [Fintype.card_finset]
      _ = ε*(H.card : ℝ) := by dsimp [c]; field_simp
  obtain ⟨T,hTH,hcard,hdense⟩ := exists_simultaneous_fiber_cleaning_of_budget
    (Finset.univ : Finset (Finset ι)) coordinateMask w H (fun I _ ↦ hw I) hbudget
  refine ⟨T,hTH,hcard,?_,?_⟩
  · intro x hx j
    exact hsupport x (hTH hx) j
  · intro x hx I
    have hh := hdense I (Finset.mem_univ _) x hx
    simpa only [w,coordinateMask_eq_iff] using hh

/-- Full finite-set version, including empty edge or vertex classes. -/
theorem exists_coordinate_refinement_of_support {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) (H : Finset (ι → α))
    (hsupport : ∀ x ∈ H, ∀ j, x j ∈ A j) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ T : Finset (ι → α), T ⊆ H ∧ (1-ε)*(H.card : ℝ) ≤ T.card ∧
      coordinateDensity ((ε*(H.card : ℝ))/((2:ℝ)^(Fintype.card ι)*(∏ j, ((A j).card : ℝ)))) A T := by
  classical
  by_cases hH : H.Nonempty
  · have hA : ∀ j, (A j).Nonempty := by
      intro j
      obtain ⟨x,hx⟩ := hH
      exact ⟨x j,hsupport x hx j⟩
    exact exists_coordinate_refinement A hA H hsupport hε
  · have hH0 : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    subst H
    refine ⟨∅,Finset.Subset.refl _,by simp,?_⟩
    simp [coordinateDensity]

theorem coordinateDensity_mono {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    {c d : ℝ} {A : ι → Finset α} {H : Finset (ι → α)} (hcd : c ≤ d)
    (h : coordinateDensity d A H) : coordinateDensity c A H := by
  refine ⟨h.1,?_⟩
  intro x hx I
  exact (mul_le_mul_of_nonneg_right hcd (Finset.prod_nonneg (fun j _ ↦ Nat.cast_nonneg _))).trans
    (h.2 x hx I)

end Kakeya4.Hard.RestrictedTriple
