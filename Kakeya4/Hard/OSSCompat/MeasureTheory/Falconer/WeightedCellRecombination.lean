






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.ConditionalRadialTransport
import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FineDyadicSeparation

/-! Recombination with original marginal masses. The finite matrix of real
pair relations is assembled by union. No factor equal to its number of cells
is paid in the fiber bound or the product deletion bound. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal

theorem finite_disjoint_probability_masses_le_one {X ι : Type*}
    [MeasurableSpace X] [Fintype ι] (μ : Measure X) [IsProbabilityMeasure μ]
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hdis : Pairwise fun i j => Disjoint (A i) (A j)) :
    ∑ i, μ (A i) ≤ 1 := by
  have hsum := measure_biUnion_finset
    (fun i (_ : i ∈ Finset.univ) j (_ : j ∈ Finset.univ) hij => hdis hij)
    (fun i (_ : i ∈ Finset.univ) => hA i) (μ := μ)
  have hb : μ (⋃ i ∈ Finset.univ, A i) ≤ 1 :=
    (measure_mono (subset_univ _)).trans_eq measure_univ
  rw [hsum] at hb
  simpa using hb

theorem original_restriction_denormalize {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (A : Set X) (hA : MeasurableSet A)
    (hpos : (μ.restrict A) univ ≠ 0) (S : Set X) (hS : S ⊆ A) :
    μ S = μ A*(normalizedSliceLaw (μ.restrict A) hpos : Measure X) S := by
  have hmass : μ A ≠ 0 := by simpa using hpos
  rw [normalizedSliceLaw_apply,Measure.restrict_apply_univ,
    Measure.restrict_apply' hA,inter_eq_left.mpr hS,← mul_assoc,
    ENNReal.mul_inv_cancel hmass (measure_ne_top _ _),one_mul]

theorem original_product_restriction_denormalize {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμ : (μ.restrict A) univ ≠ 0) (hν : (ν.restrict B) univ ≠ 0)
    (E : Set (X × Y)) (hE : E ⊆ A ×ˢ B) :
    (μ.prod ν) E = (μ A*ν B)*
      ((normalizedSliceLaw (μ.restrict A) hμ : Measure X).prod
        (normalizedSliceLaw (ν.restrict B) hν)) E := by
  have hμ' : μ A ≠ 0 := by simpa using hμ
  have hν' : ν B ≠ 0 := by simpa using hν
  rw [normalizedSliceLaw_incidence,Measure.restrict_apply_univ,Measure.restrict_apply_univ,
    Measure.prod_restrict,Measure.restrict_apply' (hA.prod hB),inter_eq_left.mpr hE,
    ← mul_assoc,ENNReal.mul_inv_cancel (mul_ne_zero hμ' hν')
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),one_mul]

theorem finite_relation_fiber_weighted_bound {X Y ι κ : Type*}
    [MeasurableSpace X] [Fintype ι] [Fintype κ]
    (μ : Measure X) [IsProbabilityMeasure μ] (A : ι → Set X) (B : κ → Set Y)
    (hA : ∀ i, MeasurableSet (A i)) (hAdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (F : ι → κ → Set (X × Y)) (hF : ∀ i j, F i j ⊆ A i ×ˢ B j)
    (P : X → Y → Prop) (K : ℝ≥0∞)
    (hlocal : ∀ i j x, x ∈ B j → μ {z | (z,x) ∈ F i j ∧ P z x} ≤ μ (A i)*K) :
    ∀ x, μ {z | (z,x) ∈ ⋃ i, ⋃ j, F i j ∧ P z x} ≤ K := by
  classical
  intro x
  by_cases hx : ∃ j, x ∈ B j
  · obtain ⟨j,hxj⟩ := hx
    have hsub : {z | (z,x) ∈ ⋃ i, ⋃ k, F i k ∧ P z x} ⊆
        ⋃ i, {z | (z,x) ∈ F i j ∧ P z x} := by
      rintro z ⟨hz,hP⟩
      obtain ⟨i,k,hzik⟩ := mem_iUnion₂.mp hz
      have hxk : x ∈ B k := (hF i k hzik).2
      have hkj : k = j := by
        by_contra hn
        exact Set.disjoint_left.mp (hBdis hn) hxk hxj
      subst k
      exact mem_iUnion.mpr ⟨i,hzik,hP⟩
    calc
      _ ≤ μ (⋃ i, {z | (z,x) ∈ F i j ∧ P z x}) := measure_mono hsub
      _ ≤ ∑ i, μ {z | (z,x) ∈ F i j ∧ P z x} := measure_iUnion_fintype_le μ _
      _ ≤ ∑ i, μ (A i)*K := Finset.sum_le_sum (fun i _ => hlocal i j x hxj)
      _ = (∑ i, μ (A i))*K := (Finset.sum_mul _ _ _).symm
      _ ≤ 1*K := mul_le_mul' (finite_disjoint_probability_masses_le_one μ A hA hAdis) le_rfl
      _ = _ := one_mul K
  · have hzero : {z | (z,x) ∈ ⋃ i, ⋃ j, F i j ∧ P z x} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro z ⟨hz,_⟩
      obtain ⟨i,j,hzij⟩ := mem_iUnion₂.mp hz
      exact hx ⟨j,(hF i j hzij).2⟩
    rw [hzero,measure_empty]
    exact zero_le

theorem finite_product_relation_weighted_deletion {X Y ι κ : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [Fintype ι] [Fintype κ]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : ι → Set X) (B : κ → Set Y)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ j, MeasurableSet (B j))
    (hAdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hμ : ∀ i, (μ.restrict (A i)) univ ≠ 0) (hν : ∀ j, (ν.restrict (B j)) univ ≠ 0)
    (F H : ι → κ → Set (X × Y)) (hF : ∀ i j, F i j ⊆ A i ×ˢ B j)
    (K : ℝ≥0∞)
    (hlocal : ∀ i j, ((normalizedSliceLaw (μ.restrict (A i)) (hμ i) : Measure X).prod
      (normalizedSliceLaw (ν.restrict (B j)) (hν j))) (F i j \ H i j) ≤ K) :
    (μ.prod ν) ((⋃ i, ⋃ j, F i j) \ (⋃ i, ⋃ j, H i j)) ≤ K := by
  have hsub : (⋃ i, ⋃ j, F i j) \ (⋃ i, ⋃ j, H i j) ⊆ ⋃ i, ⋃ j, F i j \ H i j := by
    rintro z ⟨hz,hn⟩
    obtain ⟨i,j,hzij⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨i,j,hzij,fun hh => hn (mem_iUnion₂.mpr ⟨i,j,hh⟩)⟩
  have hsum : ∑ i, ∑ j, (μ (A i)*ν (B j))*K =
      (∑ i, μ (A i))*(∑ j, ν (B j))*K := by
    calc
      _ = ∑ i, μ (A i)*(∑ j, ν (B j)*K) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        exact mul_assoc _ _ _
      _ = (∑ i, μ (A i))*(∑ j, ν (B j)*K) := (Finset.sum_mul _ _ _).symm
      _ = _ := by rw [← Finset.sum_mul,mul_assoc]
  calc
    _ ≤ (μ.prod ν) (⋃ i, ⋃ j, F i j \ H i j) := measure_mono hsub
    _ ≤ ∑ i, (μ.prod ν) (⋃ j, F i j \ H i j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ∑ j, (μ.prod ν) (F i j \ H i j) :=
      Finset.sum_le_sum (fun i _ => measure_iUnion_fintype_le _ _)
    _ ≤ ∑ i, ∑ j, (μ (A i)*ν (B j))*K := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [original_product_restriction_denormalize μ ν (A i) (B j) (hA i) (hB j) (hμ i) (hν j)
        (F i j \ H i j) (sdiff_subset.trans (hF i j))]
      exact mul_le_mul' le_rfl (hlocal i j)
    _ = (∑ i, μ (A i))*(∑ j, ν (B j))*K := hsum
    _ ≤ (1*1)*K := mul_le_mul' (mul_le_mul'
      (finite_disjoint_probability_masses_le_one μ A hA hAdis)
      (finite_disjoint_probability_masses_le_one ν B hB hBdis)) le_rfl
    _ = K := by simp

#print axioms finite_disjoint_probability_masses_le_one
#print axioms original_restriction_denormalize
#print axioms original_product_restriction_denormalize
#print axioms finite_relation_fiber_weighted_bound
#print axioms finite_product_relation_weighted_deletion
end OAI.Falconer
