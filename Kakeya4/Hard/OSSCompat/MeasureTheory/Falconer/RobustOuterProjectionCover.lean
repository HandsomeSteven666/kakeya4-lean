






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.OuterMassCollisionCover
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-! Actual external covering numbers of projections of arbitrary sets.
One collision bound works simultaneously for every later large outer-mass G. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal NNReal BigOperators

theorem finite_projection_cover_card_lower {α : Type*} [MeasurableSpace α]
    (ρ : Measure α) [IsFiniteMeasure ρ] (f : α → ℝ) (hf : Measurable f)
    {m T δ r : ℝ} (hm : 0 ≤ m) (hT : 0 < T) (hδr : 2*δ < r)
    (hcollision : ((ρ.prod ρ) {z | |f z.1-f z.2| < r}).toReal ≤ T)
    (G : Set α) (hG : m ≤ (ρ G).toReal) {M : ℕ} (c : Fin M → ℝ)
    (hcover : ∀ x ∈ G, ∃ i, |f x-c i| ≤ δ) : m^2/T ≤ (M:ℝ) := by
  apply (div_le_iff₀ hT).mpr
  have hm2 := pow_le_pow_left₀ hm hG 2
  have hc := finite_projection_cover_collision ρ f hf G c hδr hcover
  exact hm2.trans (hc.trans (mul_le_mul_of_nonneg_left hcollision (Nat.cast_nonneg _)))

theorem external_projection_cover_card_lower {α : Type*} [MeasurableSpace α]
    (ρ : Measure α) [IsFiniteMeasure ρ] (f : α → ℝ) (hf : Measurable f)
    {m T r : ℝ} (hm : 0 ≤ m) (hT : 0 < T) (δ : ℝ≥0) (hδr : 2*(δ:ℝ) < r)
    (hcollision : ((ρ.prod ρ) {z | |f z.1-f z.2| < r}).toReal ≤ T) :
    ∀ G : Set α, m ≤ (ρ G).toReal →
      (Nat.ceil (m^2/T) : ℕ∞) ≤ externalCoveringNumber δ (f '' G) := by
  classical
  intro G hG
  simp only [externalCoveringNumber,le_iInf_iff]
  intro C hC
  by_cases hfin : C.Finite
  · let : Fintype C := hfin.fintype
    let c : Fin (Fintype.card C) → ℝ := fun i ↦ ((Fintype.equivFin C).symm i : C)
    have hcover : ∀ x ∈ G, ∃ i, |f x-c i| ≤ (δ:ℝ) := by
      intro x hx
      obtain ⟨z,hz⟩ := mem_iUnion.mp (hC.subset_iUnion_closedBall (mem_image_of_mem f hx))
      obtain ⟨hzC,hxz⟩ := mem_iUnion.mp hz
      refine ⟨Fintype.equivFin C ⟨z,hzC⟩,?_⟩
      simpa only [c,Equiv.symm_apply_apply,mem_closedBall,Real.dist_eq] using hxz
    have hc := finite_projection_cover_card_lower ρ f hf hm hT hδr hcollision G hG c hcover
    have hn : Nat.ceil (m^2/T) ≤ Fintype.card C := Nat.ceil_le.mpr hc
    rw [← Set.coe_fintypeCard C]
    exact_mod_cast hn
  · rw [Set.encard_eq_top hfin]
    exact le_top

theorem direction_collision_robust_outer_cover (ρ : Measure (Space 2)) [IsFiniteMeasure ρ]
    (u : Space 2) {m T r : ℝ} (hm : 0 ≤ m) (hT : 0 < T)
    (δ : ℝ≥0) (hδr : 2*(δ:ℝ) < r)
    (hc : (directionProjectionCollision ρ u r).toReal ≤ T) :
    ∀ G : Set (Space 2), m ≤ (ρ G).toReal →
      (Nat.ceil (m^2/T) : ℕ∞) ≤ externalCoveringNumber δ ((fun x ↦ u 0*x 1-u 1*x 0) '' G) := by
  have he : {z : Space 2 × Space 2 |
      |(u 0*z.1 1-u 1*z.1 0)-(u 0*z.2 1-u 1*z.2 0)| < r} =
      {z | |u 0*(z.1-z.2) 1-u 1*(z.1-z.2) 0| < r} := by
    ext z
    simp only [mem_setOf_eq,PiLp.sub_apply]
    have hh : (u 0*z.1 1-u 1*z.1 0)-(u 0*z.2 1-u 1*z.2 0) =
        u 0*(z.1 1-z.2 1)-u 1*(z.1 0-z.2 0) := by ring
    rw [hh]
  apply external_projection_cover_card_lower ρ _ (by fun_prop) hm hT δ hδr
  rw [he]
  exact hc

#print axioms finite_projection_cover_card_lower
#print axioms external_projection_cover_card_lower
#print axioms direction_collision_robust_outer_cover
end OAI.Falconer
