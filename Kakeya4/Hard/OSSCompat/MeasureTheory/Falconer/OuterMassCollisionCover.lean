






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FiniteScaleKaufmanAverage
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Order.Disjointed

/-! Outer mass, finite covers and actual collisions. The set G is arbitrary;
only the covering bins are measurable. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal BigOperators

theorem finite_disjoint_self_pairs_le {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (ρ : Measure α) [SFinite ρ] (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hdis : Pairwise fun i j ↦ Disjoint (A i) (A j))
    (R : Set (α × α)) (hR : ∀ i, A i ×ˢ A i ⊆ R) :
    ∑ i, (ρ (A i))^2 ≤ (ρ.prod ρ) R := by
  have hpair : Pairwise fun i j ↦ Disjoint (A i ×ˢ A i) (A j ×ˢ A j) := by
    intro i j hij
    apply disjoint_left.mpr
    intro z hz hz'
    exact disjoint_left.mp (hdis hij) hz.1 hz'.1
  calc
    _ = ∑ i, (ρ.prod ρ) (A i ×ˢ A i) := by simp only [Measure.prod_prod,pow_two]
    _ = (ρ.prod ρ) (⋃ i, A i ×ˢ A i) := by
      rw [measure_iUnion hpair (fun i ↦ (hA i).prod (hA i)),tsum_fintype]
    _ ≤ _ := measure_mono (iUnion_subset hR)

theorem finite_partition_outer_mass_collision {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (ρ : Measure α) [IsFiniteMeasure ρ] (G : Set α)
    (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hdis : Pairwise fun i j ↦ Disjoint (A i) (A j)) (hcover : G ⊆ ⋃ i, A i)
    (R : Set (α × α)) (hR : ∀ i, A i ×ˢ A i ⊆ R) :
    (ρ G).toReal^2 ≤ (Fintype.card ι : ℝ)*((ρ.prod ρ) R).toReal := by
  classical
  have hmass : (ρ G).toReal ≤ ∑ i, (ρ (A i)).toReal := by
    have hh := ENNReal.toReal_mono (measure_ne_top ρ (⋃ i, A i)) (measure_mono hcover)
    rw [measure_iUnion hdis hA,tsum_fintype,
      ENNReal.toReal_sum (fun i _ ↦ measure_ne_top ρ (A i))] at hh
    exact hh
  have hsquares : ∑ i, (ρ (A i)).toReal^2 ≤ ((ρ.prod ρ) R).toReal := by
    have hh := ENNReal.toReal_mono (measure_ne_top (ρ.prod ρ) R)
      (finite_disjoint_self_pairs_le ρ A hA hdis R hR)
    rw [ENNReal.toReal_sum (fun i _ ↦ by finiteness)] at hh
    simpa only [ENNReal.toReal_pow] using hh
  calc
    _ ≤ (∑ i, (ρ (A i)).toReal)^2 := pow_le_pow_left₀ ENNReal.toReal_nonneg hmass 2
    _ ≤ (Fintype.card ι : ℝ)*(∑ i, (ρ (A i)).toReal^2) := by
      simpa only [Finset.card_univ] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i ↦ (ρ (A i)).toReal))
    _ ≤ _ := mul_le_mul_of_nonneg_left hsquares (Nat.cast_nonneg _)

theorem finite_projection_cover_collision {α : Type*} [MeasurableSpace α]
    (ρ : Measure α) [IsFiniteMeasure ρ] (f : α → ℝ) (hf : Measurable f)
    (G : Set α) {M : ℕ} (c : Fin M → ℝ) {δ r : ℝ} (hδr : 2*δ < r)
    (hcover : ∀ x ∈ G, ∃ i, |f x-c i| ≤ δ) :
    (ρ G).toReal^2 ≤ (M:ℝ)*
      ((ρ.prod ρ) {z | |f z.1-f z.2| < r}).toReal := by
  classical
  let B : Fin M → Set α := fun i ↦ {x | |f x-c i| ≤ δ}
  let A := disjointed B
  have hB (i : Fin M) : MeasurableSet (B i) :=
    measurableSet_le (hf.sub_const (c i)).abs measurable_const
  have hA (i : Fin M) : MeasurableSet (A i) := by
    change MeasurableSet (disjointed B i)
    rw [disjointed_eq_inter_compl]
    exact (hB i).inter (MeasurableSet.iInter (fun j ↦ MeasurableSet.iInter (fun _ ↦ (hB j).compl)))
  have hcov : G ⊆ ⋃ i, A i := by
    rw [show (⋃ i, A i) = ⋃ i, B i from iUnion_disjointed]
    intro x hx
    obtain ⟨i,hi⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨i,hi⟩
  have hR (i : Fin M) : A i ×ˢ A i ⊆ {z | |f z.1-f z.2| < r} := by
    intro z hz
    have h1 : |f z.1-c i| ≤ δ := disjointed_subset B i hz.1
    have h2 : |f z.2-c i| ≤ δ := disjointed_subset B i hz.2
    have hh := abs_sub_le (f z.1) (c i) (f z.2)
    rw [abs_sub_comm (c i) (f z.2)] at hh
    exact lt_of_le_of_lt (hh.trans (add_le_add h1 h2)) (by linarith)
  simpa only [Fintype.card_fin] using finite_partition_outer_mass_collision ρ G A hA
    (disjoint_disjointed B) hcov _ hR

#print axioms finite_disjoint_self_pairs_le
#print axioms finite_partition_outer_mass_collision
#print axioms finite_projection_cover_collision
end OAI.Falconer
