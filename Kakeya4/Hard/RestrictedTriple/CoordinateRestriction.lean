import Kakeya4.Hard.RestrictedTriple.TwoEndsFrostman

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace Kakeya4.Hard.RestrictedTriple

def restrictCoordinate {ι α : Type*} [DecidableEq α] (H : Finset (ι → α)) (i : ι) (P : Finset α) : Finset (ι → α) :=
  H.filter (fun x ↦ x i ∈ P)

theorem restrictCoordinate_subset {ι α : Type*} [DecidableEq α] (H : Finset (ι → α)) (i : ι) (P : Finset α) :
    restrictCoordinate H i P ⊆ H := Finset.filter_subset _ _

theorem restrictCoordinate_image {ι α : Type*} [DecidableEq α] (H : Finset (ι → α)) (i : ι) (P : Finset α)
    (hP : P ⊆ H.image (fun x ↦ x i)) :
    (restrictCoordinate H i P).image (fun x ↦ x i) = P := by
  ext v
  constructor
  · intro hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hx).2
  · intro hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (hP hv)
    exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hv⟩,rfl⟩

theorem restrictCoordinate_card_eq_sum {ι α : Type*} [DecidableEq α] (H : Finset (ι → α)) (i : ι) (P : Finset α)
    (hP : P ⊆ H.image (fun x ↦ x i)) :
    (restrictCoordinate H i P).card = ∑ v ∈ P, (H.filter (fun x ↦ x i = v)).card := by
  calc
    _ = ∑ v ∈ (restrictCoordinate H i P).image (fun x ↦ x i),
        ((restrictCoordinate H i P).filter (fun x ↦ x i = v)).card :=
      Finset.card_eq_sum_card_image (fun x : ι → α ↦ x i) (restrictCoordinate H i P)
    _ = _ := by
      rw [restrictCoordinate_image H i P hP]
      apply Finset.sum_congr rfl
      intro v hv
      congr 1
      ext x
      simp only [restrictCoordinate,Finset.mem_filter]
      constructor
      · exact fun h ↦ ⟨h.1.1,h.2⟩
      · rintro ⟨hx,hvEq⟩
        exact ⟨⟨hx,hvEq ▸ hv⟩,hvEq⟩

theorem coordinate_card_le_product {ι α : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (A : ι → Finset α) (H : Finset (ι → α)) (hsup : ∀ x ∈ H, ∀ i, x i ∈ A i) :
    (H.card : ℝ) ≤ ∏ i, ((A i).card : ℝ) := by
  have hinj : Function.Injective (coordinateMask (Finset.univ : Finset ι) : (ι → α) → ι → Option α) := by
    intro x y h
    funext i
    exact (coordinateMask_eq_iff _ _ _).mp h i (Finset.mem_univ _)
  have hh := card_coordinateMask_image_le A H hsup (Finset.univ : Finset ι)
  rw [Finset.card_image_of_injective _ hinj] at hh
  exact_mod_cast hh

/-- Restrict a genuinely active coordinate to any selected vertex subset.
The lower fiber density is summed over every selected vertex, producing actual retained edges. -/
theorem restrictCoordinate_card_lower {ι α : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]
    {c : ℝ} {A : ι → Finset α} {H : Finset (ι → α)}
    (h : coordinateDensity c A H) (i : ι) (P : Finset α)
    (hP : P ⊆ H.image (fun x ↦ x i)) :
    c*(P.card : ℝ)*(∏ j ∈ ({i} : Finset ι)ᶜ, ((A j).card : ℝ)) ≤
      ((restrictCoordinate H i P).card : ℝ) := by
  have hfiber (v : α) (hv : v ∈ P) :
      c*(∏ j ∈ ({i} : Finset ι)ᶜ, ((A j).card : ℝ)) ≤
        ((H.filter (fun x ↦ x i = v)).card : ℝ) := by
    obtain ⟨x,hx,hxi⟩ := Finset.mem_image.mp (hP hv)
    have hh := h.2 x hx ({i} : Finset ι)
    simpa only [Finset.mem_singleton,forall_eq,hxi] using hh
  have hsum : ((restrictCoordinate H i P).card : ℝ) =
      ∑ v ∈ P, ((H.filter (fun x ↦ x i = v)).card : ℝ) := by
    exact_mod_cast restrictCoordinate_card_eq_sum H i P hP
  calc
    _ = ∑ _v ∈ P, c*(∏ j ∈ ({i} : Finset ι)ᶜ, ((A j).card : ℝ)) := by simp; ring
    _ ≤ _ := Finset.sum_le_sum hfiber
    _ = _ := hsum.symm

theorem restrictCoordinate_retains_fraction {ι α : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]
    {c θ : ℝ} (hc : 0 ≤ c) (hθ : 0 ≤ θ) {A : ι → Finset α} {H : Finset (ι → α)}
    (h : coordinateDensity c A H) (i : ι) (P : Finset α)
    (hP : P ⊆ H.image (fun x ↦ x i)) (hmass : θ*((A i).card : ℝ) ≤ P.card) :
    c*θ*(H.card : ℝ) ≤ ((restrictCoordinate H i P).card : ℝ) := by
  have hprod : ((A i).card : ℝ)*(∏ j ∈ ({i} : Finset ι)ᶜ, ((A j).card : ℝ)) =
      ∏ j, ((A j).card : ℝ) := by
    have heq : ({i} : Finset ι)ᶜ = Finset.univ.erase i := by ext j; simp
    rw [heq]
    exact Finset.mul_prod_erase (Finset.univ : Finset ι) (fun j ↦ ((A j).card : ℝ)) (Finset.mem_univ i)
  calc
    _ ≤ c*θ*(∏ j, ((A j).card : ℝ)) :=
      mul_le_mul_of_nonneg_left (coordinate_card_le_product A H h.1) (mul_nonneg hc hθ)
    _ = c*(θ*((A i).card : ℝ))*(∏ j ∈ ({i} : Finset ι)ᶜ, ((A j).card : ℝ)) := by rw [← hprod]; ring
    _ ≤ c*(P.card : ℝ)*(∏ j ∈ ({i} : Finset ι)ᶜ, ((A j).card : ℝ)) := by
      gcongr
    _ ≤ _ := restrictCoordinate_card_lower h i P hP

end Kakeya4.Hard.RestrictedTriple
