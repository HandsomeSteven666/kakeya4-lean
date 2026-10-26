import Kakeya4.Hard.MultilinearKakeya.ThresholdVisibility
import Kakeya4.Hard.MultilinearKakeya.MonomialBisection

/-! A genuine simultaneous small-visibility-body polynomial on finitely many
arbitrary unit balls. The common smoothing parameter, finite coloured shape
classes and spatial tests are constructed, with an explicit total index budget. -/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

namespace Kakeya4.Hard.MultilinearKakeya

theorem exists_polynomial_simultaneous_small_visibilityBody {n m d : ℕ} (hn : 2 ≤ n)
    {κ : Type*} [Fintype κ]
    (B : Fin (m+1) → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (hdeg : ∀ i, (B i).totalDegree ≤ d) (b : κ → E n) (ρ : κ → ℝ) (hρ : ∀ q, 0 < ρ q)
    (hbudget : ∑ q, ⌈(volume (Metric.closedBall (0 : E n) 1)).toReal /
      (spatialTestVolumeFactor n*ρ q)⌉₊ * shapeColourCount n ≤ m) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ P.totalDegree ≤ d ∧
      ∀ q, (volume (visibilityBody (smoothDirectionalSeminorm P ε (Metric.closedBall (b q) 1)
        (isCompact_closedBall (b q) 1)))).toReal < (2*Real.sqrt n)^n * ρ q := by
  classical
  letI : NeZero n := ⟨by omega⟩
  choose s colour hbounded hclasses using (fun q => exists_uniform_closed_shape_classes hn B hdeg
    (isCompact_closedBall (b q) 1) (Subset.refl (Metric.closedBall (b q) 1)))
  let σ := Σ q : κ, ↥(s q)
  let T (i : σ) := i.2.val
  have hz (u : E (m+1)) (hu : u ∈ Metric.sphere 0 1) : u ≠ 0 := by
    intro he
    have hn : ‖u‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hu
    rw [he,norm_zero] at hn
    norm_num at hn
  obtain ⟨tests,hne,htestdisjoint,hsub,hlower,hupper,ε,hε,hnot⟩ :=
    exists_finite_shapeClass_test_obstruction B hB T
      (fun i => hbounded i.1 i.2.val i.2.property) (fun i => b i.1) (isCompact_sphere 0 1) hz
  have hd (q : κ) (i j : s q) (hij : i ≠ j) (hc : colour q i = colour q j) :
      Disjoint (coefficientShapeClass B ε (Metric.closedBall (b q) 1) i.val)
        (coefficientShapeClass B ε (Metric.closedBall (b q) 1) j.val) :=
    (hclasses q ε hε.ne').2.2.1 i j hij hc
  have hc (q : κ) : (⋃ i : s q, coefficientShapeClass B ε (Metric.closedBall (b q) 1) i.val) = univ :=
    (hclasses q ε hε.ne').2.2.2
  obtain ⟨u,hu⟩ := exists_small_visibilityBodies_of_actual_tests (by omega : 0 < n) B hB ε
    (fun q => Metric.closedBall (b q) 1) (fun q => isCompact_closedBall (b q) 1)
    (fun q (i : s q) => i.val) colour (fun q i => tests ⟨q,i⟩) hd hc
    (fun u q i hi => hnot ⟨q,i⟩ u u.property hi) ρ
    (fun _ => (volume (Metric.closedBall (0 : E n) 1)).toReal) hρ
    (fun q i => hupper ⟨q,i⟩) hbudget
  exact ⟨ε,hε,coefficientPolynomial B u,coefficientPolynomial_sphere_ne_zero B hB u,
    totalDegree_coefficientPolynomial_le B hdeg u,hu⟩

def visibilityIndexBudget (n : ℕ) {κ : Type*} [Fintype κ] (ρ : κ → ℝ) : ℕ :=
  ∑ q, ⌈(volume (Metric.closedBall (0 : E n) 1)).toReal /
    (spatialTestVolumeFactor n*ρ q)⌉₊ * shapeColourCount n

theorem exists_polynomial_simultaneous_small_visibilityBody_nthRoot {n : ℕ} (hn : 2 ≤ n)
    {κ : Type*} [Fintype κ] (b : κ → E n) (ρ : κ → ℝ) (hρ : ∀ q, 0 < ρ q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧
      P.totalDegree ≤ n * Nat.nthRoot n (visibilityIndexBudget n ρ) ∧
      ∀ q, (volume (visibilityBody (smoothDirectionalSeminorm P ε (Metric.closedBall (b q) 1)
        (isCompact_closedBall (b q) 1)))).toReal < (2*Real.sqrt n)^n * ρ q := by
  let m := visibilityIndexBudget n ρ
  let d := Nat.nthRoot n m
  have hcard : m+1 ≤ (d+1)^n := Nat.lt_pow_nthRoot_add_one (by omega : n ≠ 0) m
  have hle : Fintype.card (Fin (m+1)) ≤ Fintype.card (Fin n → Fin (d+1)) := by simpa using hcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
  let f : Fin (m+1) ↪ (Fin n →₀ ℕ) := e.trans (exponentBoxEmbedding n d)
  let B : Fin (m+1) → MvPolynomial (Fin n) ℝ := fun i => MvPolynomial.basisMonomials _ _ (f i)
  have hB : LinearIndependent ℝ B :=
    (MvPolynomial.basisMonomials (Fin n) ℝ).linearIndependent.comp f f.injective
  have hD (i : Fin (m+1)) : (B i).totalDegree ≤ n*d := totalDegree_box_monomial_le n d (e i)
  exact exists_polynomial_simultaneous_small_visibilityBody hn B hB hD b ρ hρ (le_refl m)

theorem exists_polynomial_simultaneous_small_visibilityBody_quantitative {n : ℕ} (hn : 2 ≤ n)
    {κ : Type*} [Fintype κ] (b : κ → E n) (ρ : κ → ℝ) (hρ : ∀ q, 0 < ρ q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧
      (P.totalDegree : ℝ) ≤ (n : ℝ)*(visibilityIndexBudget n ρ : ℝ)^((n : ℝ)⁻¹) ∧
      ∀ q, (volume (visibilityBody (smoothDirectionalSeminorm P ε (Metric.closedBall (b q) 1)
        (isCompact_closedBall (b q) 1)))).toReal < (2*Real.sqrt n)^n * ρ q := by
  obtain ⟨ε,hε,P,hP,hD,hV⟩ := exists_polynomial_simultaneous_small_visibilityBody_nthRoot hn b ρ hρ
  refine ⟨ε,hε,P,hP,?_,hV⟩
  calc
    (P.totalDegree : ℝ) ≤ (n : ℝ)*(Nat.nthRoot n (visibilityIndexBudget n ρ) : ℝ) := by exact_mod_cast hD
    _ ≤ _ := mul_le_mul_of_nonneg_left (cast_nthRoot_le_rpow (by omega : 0 < n) _) (Nat.cast_nonneg n)

end Kakeya4.Hard.MultilinearKakeya
