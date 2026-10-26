import Kakeya4.Hard.RestrictedTriple.MarginalFrostman

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace Kakeya4.Hard.RestrictedTriple

/-- Independent injective changes of the vertex coordinates preserve all fiber densities exactly. -/
theorem coordinateDensity_map {ι α β : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq α] [DecidableEq β]
    (g : ι → α → β) (hg : ∀ i, Function.Injective (g i))
    {c : ℝ} {A : ι → Finset α} {H : Finset (ι → α)} (h : coordinateDensity c A H) :
    coordinateDensity c (fun i ↦ (A i).image (g i))
      (H.image (fun x i ↦ g i (x i))) := by
  classical
  let G : (ι → α) → ι → β := fun x i ↦ g i (x i)
  have hG : Function.Injective G := by
    intro x y hxy
    funext i
    exact hg i (congrFun hxy i)
  refine ⟨?_,?_⟩
  · intro z hz i
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨x i,h.1 x hx i,rfl⟩
  · intro z hz I
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    have hfilter : (H.image G).filter (fun y ↦ ∀ i ∈ I, y i = G x i) =
        (H.filter (fun y ↦ ∀ i ∈ I, y i = x i)).image G := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyH,hyI⟩ := Finset.mem_filter.mp hy
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hyH
        apply Finset.mem_image.mpr
        refine ⟨v,Finset.mem_filter.mpr ⟨hv,?_⟩,rfl⟩
        intro i hi
        exact hg i (hyI i hi)
      · intro hy
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨hvH,hvI⟩ := Finset.mem_filter.mp hv
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_image.mpr ⟨v,hvH,rfl⟩,?_⟩
        intro i hi
        exact congrArg (g i) (hvI i hi)
    change c*(∏ i ∈ Iᶜ, (((A i).image (g i)).card : ℝ)) ≤
      (((H.image G).filter (fun y ↦ ∀ i ∈ I, y i = G x i)).card : ℝ)
    rw [hfilter,Finset.card_image_of_injective _ hG]
    simpa only [Finset.card_image_of_injective _ (hg _)] using h.2 x hx I

theorem coordinateDensity_halfTriple {c : ℝ} {F G : Finset Plane} {Q : Finset Triple}
    (h : coordinateDensity c (tripleClasses F G) (Q.image tripleVertexMap)) :
    coordinateDensity c (tripleClasses (F.image halfPlane) (G.image halfPlane))
      ((Q.image halfTriple).image tripleVertexMap) := by
  classical
  have hh := coordinateDensity_map (fun _ ↦ halfPlane) (fun _ ↦ halfPlane_injective) h
  have hclasses : (fun i ↦ ((tripleClasses F G) i).image halfPlane) =
      tripleClasses (F.image halfPlane) (G.image halfPlane) := by
    funext i
    fin_cases i <;> rfl
  have himage : (Q.image tripleVertexMap).image (fun x i ↦ halfPlane (x i)) =
      (Q.image halfTriple).image tripleVertexMap := by
    simp only [Finset.image_image]
    congr 1
    funext t i
    fin_cases i <;> rfl
  rwa [hclasses,himage] at hh

/-- The exact source-style ENNReal fiber inequalities, with all finite products retained. -/
theorem coordinateDensity_enn {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    {c : ℝ} {A : ι → Finset α} {H : Finset (ι → α)} (hc : 0 ≤ c)
    (h : coordinateDensity c A H) :
    (∀ x ∈ H, ∀ i, x i ∈ A i) ∧
      ∀ x ∈ H, ∀ I : Finset ι,
        ENNReal.ofReal c*(∏ i ∈ Iᶜ, ((A i).card : ℝ≥0∞)) ≤
          ((H.filter (fun y ↦ ∀ i ∈ I, y i = x i)).card : ℝ≥0∞) := by
  refine ⟨h.1,?_⟩
  intro x hx I
  have hh := ENNReal.ofReal_le_ofReal (h.2 x hx I)
  rw [ENNReal.ofReal_mul hc,ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ Nat.cast_nonneg _)] at hh
  simpa only [ENNReal.ofReal_natCast] using hh

end Kakeya4.Hard.RestrictedTriple
