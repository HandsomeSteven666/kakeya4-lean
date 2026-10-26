import Kakeya4.Hard.MultilinearKakeya.DirectionalFactors
import Kakeya4.Hard.MultilinearKakeya.Imported.NuminaBoundedOverlap.BoundedOverlap

/-! Reuse of Numina's exact bounded-overlap measure theorem on the actual
directional derivative density. It pays finite regional energies by the whole
affine-line tube degree budget, including the exact amplification cancellation. -/

noncomputable section
open Set MeasureTheory Classical
open scoped Topology BigOperators ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem sum_directionalEnergy_le_boundedOverlap_tube {n : ℕ} (hn : 2 ≤ n)
    (L : Line n) (P : MvPolynomial (Fin n) ℝ) {ε : ℝ} (hε : ε ≠ 0) (r : ℝ)
    {ι : Type*} (s : Finset ι) (A : ι → Set (E n)) (hA : ∀ i ∈ s, IsCompact (A i))
    (hsub : ∀ i ∈ s, A i ⊆ L.tube r) {C : ℕ}
    (hoverlap : ∀ x, (s.filter (fun i => x ∈ A i)).card ≤ C) :
    ∑ i ∈ s, directionalEnergy P ε (A i) L.direction ≤
      (C : ℝ)*(localDegreeBudget n r P.totalDegree).toReal := by
  classical
  let μ := volume.withDensity (fun x => ENNReal.ofReal ‖fderiv ℝ (smoothPolynomial P ε) x L.direction‖)
  have he (i : ι) (hi : i ∈ s) : μ (A i) = ENNReal.ofReal (directionalEnergy P ε (A i) L.direction) := by
    rw [withDensity_apply _ (hA i hi).measurableSet]
    exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_smoothPolynomial_direction P ε (hA i hi) _)
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).symm
  have hsum := MeasureTheory.sum_measure_le_mul_measure_biUnion_of_card_filter_le (μ := μ) s
    (fun i hi => (hA i hi).measurableSet) hoverlap
  have hUnion : (⋃ i ∈ s, A i) ⊆ L.tube r := iUnion₂_subset hsub
  have hmono := measure_mono (μ := μ) hUnion
  have htube : μ (L.tube r) ≤ localDegreeBudget n r P.totalDegree := by
    rw [withDensity_apply _ (L.measurableSet_tube r)]
    exact lintegral_smoothPolynomial_tube_le_degree hn L P hε r
  have htotal : ∑ i ∈ s, ENNReal.ofReal (directionalEnergy P ε (A i) L.direction) ≤
      (C : ℝ≥0∞)*localDegreeBudget n r P.totalDegree := by
    calc
      _ = ∑ i ∈ s, μ (A i) := Finset.sum_congr rfl (fun i hi => (he i hi).symm)
      _ ≤ _ := hsum.trans (mul_le_mul_of_nonneg_left (hmono.trans htube) (by simp))
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top C) (localDegreeBudget_ne_top n r P.totalDegree)) htotal
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top)] at hreal
  simpa only [ENNReal.toReal_ofReal (directionalEnergy_nonneg P ε _ _),ENNReal.toReal_mul,
    ENNReal.toReal_natCast] using hreal

theorem sum_directionalFactor_le_of_degree_bound {n : ℕ} (hn : 2 ≤ n)
    (L : Line n) (P : MvPolynomial (Fin n) ℝ) {ε : ℝ} (hε : ε ≠ 0) (r : ℝ)
    {ι : Type*} (s : Finset ι) (A : ι → Set (E n)) (hA : ∀ i ∈ s, IsCompact (A i))
    (hsub : ∀ i ∈ s, A i ⊆ L.tube r) {C : ℕ}
    (hoverlap : ∀ x, (s.filter (fun i => x ∈ A i)).card ≤ C)
    {t D : ℝ} (ht : 0 < t) (hdegree : (P.totalDegree : ℝ) ≤ t*D) :
    ∑ i ∈ s, directionalFactor P ε t (A i) L.direction ≤
      (C : ℝ)*((ENNReal.ofReal r)^(n-1)*transverseUnitVolume n).toReal*Real.pi*D := by
  have h := sum_directionalEnergy_le_boundedOverlap_tube hn L P hε r s A hA hsub hoverlap
  have hbudget : (localDegreeBudget n r P.totalDegree).toReal =
      ((ENNReal.ofReal r)^(n-1)*transverseUnitVolume n).toReal * Real.pi * (P.totalDegree : ℝ) := by
    simp only [localDegreeBudget,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (P.totalDegree : ℝ)*Real.pi)]
    ring
  unfold directionalFactor
  rw [← Finset.sum_div]
  apply (div_le_iff₀ ht).mpr
  rw [hbudget] at h
  have hpay := mul_le_mul_of_nonneg_left hdegree
    (by positivity : 0 ≤ (C : ℝ)*((ENNReal.ofReal r)^(n-1)*transverseUnitVolume n).toReal*Real.pi)
  nlinarith

end Kakeya4.Hard.MultilinearKakeya
