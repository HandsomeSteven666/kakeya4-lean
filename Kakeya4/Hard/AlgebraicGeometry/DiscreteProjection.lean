import Kakeya4.Hard.AlgebraicGeometry.PolynomialNull

/-! Coordinate projections of discrete semialgebraic sets have empty interior. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical
open OAI.Release061 OAI.Release061.SignElimination

namespace Kakeya4.Hard

/-- An interval in a coordinate projection would admit a locally analytic section.
Isolation forces that section to be locally constant, contradicting its coordinate. -/
theorem discrete_semialgebraic_projection_empty_interior {κ : Type*} [Fintype κ]
    {R : Set (κ → ℝ)} (hR : PolynomialSignSet id R)
    (hdiscrete : ∀ v ∈ R, ∃ U : Set (κ → ℝ), IsOpen U ∧ v ∈ U ∧
      ∀ w ∈ R, w ∈ U → w = v) (j : κ) :
    interior {t : Fin 1 → ℝ | ∃ v ∈ R, v j = t 0} = ∅ := by
  let A : Set ((Fin 1 → ℝ) × (κ → ℝ)) := {z | z.2 ∈ R ∧ z.2 j = z.1 0}
  have hA : PolynomialSignSet
      (fun z : (Fin 1 → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2) A := by
    have hr := hR.coordinate_preimage Prod.snd Sum.inr
      (d := fun z : (Fin 1 → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2) (by intros; rfl)
    have he : PolynomialSignSet
        (fun z : (Fin 1 → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2)
        {z | z.2 j = z.1 0} := by
      convert PolynomialSignSet.zero (c := fun z : (Fin 1 → ℝ) × (κ → ℝ) =>
        Sum.elim z.1 z.2) (MvPolynomial.X (Sum.inr j) - MvPolynomial.X (Sum.inl 0)) using 1
      ext z
      simp [sub_eq_zero]
    exact hr.inter he
  obtain ⟨f,D,hD,hf,_,ha⟩ := semialgebraic_analytic_selector hA
  let B : Set (Fin 1 → ℝ) := {t | ∃ v ∈ R, v j = t 0}
  have hdom (t : Fin 1 → ℝ) : (∃ v, (t,v) ∈ A) ↔ t ∈ B := Iff.rfl
  have hfR (t : Fin 1 → ℝ) (ht : t ∈ B) : f t ∈ R ∧ f t j = t 0 :=
    hf t ((hdom t).mpr ht)
  have hzero : interior {t : Fin 1 → ℝ | MvPolynomial.eval t D = 0} = ∅ :=
    volume.interior_eq_empty_of_null (real_polynomial_zero_volume D hD)
  by_contra hB
  have hnot : ¬ interior B ⊆ {t | MvPolynomial.eval t D = 0} := by
    intro hsub
    have hh := interior_maximal hsub isOpen_interior
    rw [hzero] at hh
    exact hB (subset_empty_iff.mp hh)
  obtain ⟨a,haB,haD⟩ := Set.not_subset.mp hnot
  have haB' : a ∈ B := interior_subset haB
  obtain ⟨U,hU,haU,hiso⟩ := hdiscrete (f a) (hfR a haB').1
  have hcont := (ha a ((hdom a).mpr haB') haD).continuousAt
  have hevent : ∀ᶠ t in 𝓝 a, t = a := by
    filter_upwards [mem_interior_iff_mem_nhds.mp haB,
      hcont (hU.mem_nhds haU)] with t ht htU
    have hfa := hiso (f t) (hfR t ht).1 htU
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (hfR t ht).2.symm.trans ((congrArg (fun v => v j) hfa).trans (hfR a haB').2)
  have hopen : IsOpen ({a} : Set (Fin 1 → ℝ)) := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have ht' : t = a := ht
    subst t
    exact hevent
  exact not_isOpen_singleton a hopen

/-- Scalar-coordinate version of the projection conclusion. -/
theorem discrete_semialgebraic_scalar_projection_empty_interior {κ : Type*} [Fintype κ]
    {R : Set (κ → ℝ)} (hR : PolynomialSignSet id R)
    (hdiscrete : ∀ v ∈ R, ∃ U : Set (κ → ℝ), IsOpen U ∧ v ∈ U ∧
      ∀ w ∈ R, w ∈ U → w = v) (j : κ) :
    interior {t : ℝ | ∃ v ∈ R, v j = t} = ∅ := by
  let e : (Fin 1 → ℝ) ≃ₜ ℝ := Homeomorph.piUnique (fun _ : Fin 1 => ℝ)
  have hh := discrete_semialgebraic_projection_empty_interior hR hdiscrete j
  have he : e ⁻¹' interior {t : ℝ | ∃ v ∈ R, v j = t} = ∅ := by
    rw [e.preimage_interior]
    exact hh
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hm : e.symm t ∈ e ⁻¹' interior {t : ℝ | ∃ v ∈ R, v j = t} := by
    simpa using ht
  simpa only [he, mem_empty_iff_false] using hm

end Kakeya4.Hard
