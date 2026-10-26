import Kakeya4.Hard.MultilinearKakeya.BoundedSpatialPacking

/-! One smoothing parameter for a finite family of actual spatial tests, and
the obstruction to bisecting all disjoint tests of a low-energy shape class. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

def polynomialBisects {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (A : Set (E n)) : Prop :=
  (volume.restrict A) {x | MvPolynomial.eval (WithLp.ofLp x) P ≤ 0} = volume A / 2 ∧
    (volume.restrict A) {x | 0 ≤ MvPolynomial.eval (WithLp.ofLp x) P} = volume A / 2

theorem exists_common_spatialTest_bisection_energy_fraction {n k : ℕ} [NeZero n]
    {ι : Type*} [Fintype ι]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (L : ι → (Fin n → ℝ) ≃L[ℝ] E n) (c : ι → E n) {r : ℝ} (hr : 0 < r)
    {S : Set (E k)} (hS : IsCompact S) (hzero : ∀ u ∈ S, u ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ∀ u ∈ S,
      polynomialBisects (coefficientPolynomial B u) (spatialTestCell (L i) (c i) r) →
      (Real.pi/10)*(volume (spatialTestCell (L i) (c i) r)).toReal ≤
        referencePoincareConstant n * ∑ j, directionalEnergy (coefficientPolynomial B u) ε
          (spatialTestCell (L i) (c i) r) (r • L i (Pi.single j 1)) := by
  obtain ⟨ε,hε,h⟩ := exists_common_euclidean_bisection_energy_fraction B hB
    (fun i => WithLp.ofLp (c i)) (fun i => nativeSpatialShape (L i) r hr.ne') hS hzero
  refine ⟨ε,hε,fun i u hu hb => ?_⟩
  have heq := spatialTestCell_eq_euclideanAffineRegion (L i) (c i) hr
  have hb' : polynomialBisects (coefficientPolynomial B u)
      (euclideanAffineRegion (WithLp.ofLp (c i)) (nativeSpatialShape (L i) r hr.ne')) := by
    rwa [← heq]
  have he := h i u hu hb'.1 hb'.2
  rw [← heq] at he
  simpa only [← spatialReferenceChart_apply, nativeSpatialShape_toEuclidean] using he

theorem spatialTest_energy_budget_of_local_bounds {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (ε : ℝ)
    (L : (Fin n → ℝ) ≃L[ℝ] E n) (r : ℝ) (s : Finset (E n))
    {Q : Set (E n)} (hQ : IsCompact Q)
    (hd : Set.Pairwise (s : Set (E n)) (fun c d =>
      Disjoint (spatialTestCell L c r) (spatialTestCell L d r)))
    (hsub : ∀ c ∈ s, spatialTestCell L c r ⊆ Q)
    (hlocal : ∀ c ∈ s, (Real.pi/10)*(volume (spatialTestCell L c r)).toReal ≤
      referencePoincareConstant n * ∑ j, directionalEnergy P ε (spatialTestCell L c r)
        (r • L (Pi.single j 1))) :
    (Real.pi/10)*(s.card : ℝ)*(volume (spatialTestCell L 0 r)).toReal ≤
      referencePoincareConstant n * ∑ j, directionalEnergy P ε Q (r • L (Pi.single j 1)) := by
  have hs := Finset.sum_le_sum (fun c (hc : c ∈ s) => hlocal c hc)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm] at hs
  simp only [volume_spatialTestCell_translation, Finset.sum_const, nsmul_eq_mul] at hs
  rw [← mul_assoc] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (referencePoincareConstant_pos n).le
  apply Finset.sum_le_sum
  intro j _
  exact sum_directionalEnergy_finset_disjoint_le P ε hQ _ s
    (fun c _ => (isOpen_spatialTestCell L c r).measurableSet) hd hsub _

theorem exists_common_shapeClass_bisection_obstruction {n k : ℕ} [NeZero n]
    {σ : Type*} [Fintype σ]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (T : σ → E n ≃L[ℝ] E n) (s : σ → Finset (E n))
    {S : Set (E k)} (hS : IsCompact S) (hzero : ∀ u ∈ S, u ≠ 0)
    (Q : σ → Set (E n)) (hQ : ∀ a, IsCompact (Q a))
    (hd : ∀ a, Set.Pairwise (s a : Set (E n)) (fun c d =>
      Disjoint (spatialTestCell (chartOfShape (T a)) c (spatialTestScale n))
        (spatialTestCell (chartOfShape (T a)) d (spatialTestScale n))))
    (hsub : ∀ a, ∀ c ∈ s a, spatialTestCell (chartOfShape (T a)) c (spatialTestScale n) ⊆ Q a)
    (hmass : ∀ a, spatialTestMass n ≤ (s a |>.card : ℝ) *
      (volume (spatialTestCell (chartOfShape (T a)) 0 (spatialTestScale n))).toReal) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a, ∀ u ∈ S, u ∈ coefficientShapeClass B ε (Q a) (T a) →
      ∃ c ∈ s a, ¬ polynomialBisects (coefficientPolynomial B u)
        (spatialTestCell (chartOfShape (T a)) c (spatialTestScale n)) := by
  classical
  let ι := Σ a : σ, ↥(s a)
  obtain ⟨ε,hε,h⟩ := exists_common_spatialTest_bisection_energy_fraction B hB
    (fun i : ι => chartOfShape (T i.1)) (fun i : ι => (i.2 : E n))
    (spatialTestScale_spec n).1 hS hzero
  refine ⟨ε,hε,fun a u hu hclass => ?_⟩
  by_contra hall
  push Not at hall
  have hlocal (c : E n) (hc : c ∈ s a) := h ⟨a,⟨c,hc⟩⟩ u hu (hall c hc)
  have hb := spatialTest_energy_budget_of_local_bounds (coefficientPolynomial B u) ε
    (chartOfShape (T a)) (spatialTestScale n) (s a) (hQ a) (hd a) (hsub a) hlocal
  have hsum : (∑ j, directionalEnergy (coefficientPolynomial B u) ε (Q a)
      (spatialTestScale n • chartOfShape (T a) (Pi.single j 1))) ≤ (n : ℝ)*(2*spatialTestScale n) := by
    calc
      _ ≤ ∑ _j : Fin n, (2*spatialTestScale n) := Finset.sum_le_sum (fun j _ =>
        directionalEnergy_scaled_axis_le_of_shapeClass B ε (Q a) (T a) hclass (spatialTestScale_spec n).1.le j)
      _ = _ := by simp
  have hupper := mul_le_mul_of_nonneg_left hsum (referencePoincareConstant_pos n).le
  have hlower := mul_le_mul_of_nonneg_left (hmass a) (by positivity : 0 ≤ Real.pi/10)
  rw [← mul_assoc] at hlower hupper
  exact (not_lt_of_ge (hlower.trans (hb.trans hupper))) (spatialTestScale_spec n).2.2

theorem exists_finite_shapeClass_test_obstruction {n k : ℕ} [NeZero n]
    {σ : Type*} [Fintype σ]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (T : σ → E n ≃L[ℝ] E n) (hT : ∀ a, ‖(T a).toContinuousLinearMap‖ ≤ 1)
    (b : σ → E n)
    {S : Set (E k)} (hS : IsCompact S) (hzero : ∀ u ∈ S, u ≠ 0) :
    ∃ s : σ → Finset (E n),
      (∀ a, (s a).Nonempty) ∧
      (∀ a, Set.Pairwise (s a : Set (E n)) (fun c d =>
        Disjoint (spatialTestCell (chartOfShape (T a)) c (spatialTestScale n))
          (spatialTestCell (chartOfShape (T a)) d (spatialTestScale n)))) ∧
      (∀ a, ∀ c ∈ s a, spatialTestCell (chartOfShape (T a)) c (spatialTestScale n) ⊆ Metric.closedBall (b a) 1) ∧
      (∀ a, spatialTestMass n ≤ ((s a).card : ℝ) *
        (volume (spatialTestCell (chartOfShape (T a)) 0 (spatialTestScale n))).toReal) ∧
      (∀ a, ((s a).card : ℝ) * (volume (spatialTestCell (chartOfShape (T a)) 0 (spatialTestScale n))).toReal ≤
        (volume (Metric.closedBall (0 : E n) 1)).toReal) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ a, ∀ u ∈ S,
        u ∈ coefficientShapeClass B ε (Metric.closedBall (b a) 1) (T a) →
        ∃ c ∈ s a, ¬ polynomialBisects (coefficientPolynomial B u)
          (spatialTestCell (chartOfShape (T a)) c (spatialTestScale n)) := by
  classical
  choose s hne hcentres hd hsub hlower hupper using
    (fun a => exists_unitBall_spatialTest_packing (T a) (hT a) (b a))
  obtain ⟨ε,hε,h⟩ := exists_common_shapeClass_bisection_obstruction B hB T s hS hzero
    (fun a => Metric.closedBall (b a) 1) (fun a => isCompact_closedBall (b a) 1) hd hsub hlower
  exact ⟨s,hne,hd,hsub,hlower,hupper,ε,hε,h⟩

end Kakeya4.Hard.MultilinearKakeya
