import Kakeya4.Hard.MultilinearKakeya.LineMeasureGeometry
import Kakeya4.Hard.MultilinearKakeya.BallTubeFactors

/-! The existing geometric factors are Borel functions of unrestricted line
parameters. This retains the actual common polynomial rather than adding a
measurable-selection hypothesis to the factor existence statement. -/

noncomputable section
open Set MeasureTheory Classical
open scoped Topology ENNReal BigOperators

namespace Kakeya4.Hard.MultilinearKakeya

theorem measurable_ballTubeFactor_parameter {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (ε t R : ℝ) (b : E n) :
    Measurable (fun p : LineParameter n => ballTubeFactor P ε t R b p.toLine) := by
  have hd : Measurable (fun p : LineParameter n =>
      directionalFactor P ε t (Metric.closedBall b 1) p.2.val) :=
    (((continuous_smoothDirectionalSeminorm P ε (isCompact_closedBall b 1)).measurable.comp
      measurable_snd.subtype_coe).div_const t)
  have he : {p : LineParameter n | b ∈ p.toLine.tube R} =
      (fun p : LineParameter n => (p,b)) ⁻¹' parameterTubeIncidence n R := by
    ext p
    exact (mem_parameterTubeIncidence R p b).symm
  have hs : MeasurableSet {p : LineParameter n | b ∈ p.toLine.tube R} := by
    rw [he]
    exact (measurableSet_parameterTubeIncidence n R).preimage (measurable_id.prodMk measurable_const)
  exact hd.ite hs measurable_const

theorem exists_measurable_geometric_ballTube_factors {n : ℕ} (hn : 2 ≤ n)
    {κ : Type*} [Fintype κ] (b : κ → E n) (w : κ → ℝ) (hw : ∀ q, 1 ≤ w q)
    {C : ℕ} (hoverlap : ∀ x, (Finset.univ.filter (fun q => x ∈ Metric.closedBall (b q) 1)).card ≤ C)
    (R : ℝ) :
    ∃ S : LineParameter n → κ → ℝ,
      (∀ q, Measurable (fun p => S p q)) ∧
      (∀ p q, 0 ≤ S p q) ∧
      (∀ q, ∀ p : Fin n → LineParameter n, (∀ i, b q ∈ (p i).toLine.tube R) →
        directionalDeterminantConstant n*w q*|Matrix.det (fun i j => (p j).2.val i)| ≤
          ∏ i, S (p i) q) ∧
      (∀ p, ∑ q, S p q ≤
        (C : ℝ)*((ENNReal.ofReal (R+1))^(n-1)*transverseUnitVolume n).toReal*Real.pi*
          weightedVisibilityDegreeBound n w) := by
  classical
  obtain ⟨t,ht,ε,hε,P,hP,hD,hdir,hdet⟩ := exists_weighted_directional_factor_polynomial hn b w hw
  refine ⟨fun p q => ballTubeFactor P ε t R (b q) p.toLine,
    fun q => measurable_ballTubeFactor_parameter P ε t R (b q),
    fun p q => ballTubeFactor_nonneg P ε R (by linarith) (b q) p.toLine,?_,?_⟩
  · intro q p hp
    calc
      _ ≤ ∏ i, directionalFactor P ε t (Metric.closedBall (b q) 1) (p i).toLine.direction :=
        hdet q (fun i => (p i).toLine.direction) (fun i => (p i).toLine.norm_direction)
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        simp only [ballTubeFactor,if_pos (hp i)]
  · intro p
    exact sum_ballTubeFactor_le_of_degree_bound hn b hoverlap p.toLine P hε.ne' R (by linarith) hD

end Kakeya4.Hard.MultilinearKakeya
