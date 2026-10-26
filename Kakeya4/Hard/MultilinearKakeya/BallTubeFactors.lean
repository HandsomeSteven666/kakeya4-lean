import Kakeya4.Hard.MultilinearKakeya.TubeFactorBudget

/-! Genuine geometric factors indexed by every full affine line and every
prescribed spatial ball. Centre incidence supplies the enclosing whole tube;
the same polynomial works for all lines, including repeated input indices. -/

noncomputable section
open Set MeasureTheory Classical
open scoped Topology BigOperators ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

theorem center_mem_tube_of_mem_closedBall {n : ℕ} (L : Line n) (b x : E n) {a r : ℝ}
    (hx : x ∈ Metric.closedBall b a) (hL : x ∈ L.tube r) : b ∈ L.tube (r+a) := by
  change Metric.infDist b L.carrier ≤ r+a
  apply Metric.infDist_le_infDist_add_dist.trans
  exact add_le_add hL (by simpa only [Metric.mem_closedBall,dist_comm] using hx)

theorem closedBall_subset_tube_of_center_mem {n : ℕ} (L : Line n) (b : E n) {R : ℝ}
    (hb : b ∈ L.tube R) : Metric.closedBall b 1 ⊆ L.tube (R+1) := by
  intro x hx
  change Metric.infDist x L.carrier ≤ R+1
  exact Metric.infDist_le_infDist_add_dist.trans
    (add_le_add hb (by simpa only [Metric.mem_closedBall] using hx))

def ballTubeFactor {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε t R : ℝ) (b : E n) (L : Line n) : ℝ :=
  if b ∈ L.tube R then directionalFactor P ε t (Metric.closedBall b 1) L.direction else 0

theorem ballTubeFactor_nonneg {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (ε R : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (b : E n) (L : Line n) : 0 ≤ ballTubeFactor P ε t R b L := by
  unfold ballTubeFactor
  split_ifs
  · exact directionalFactor_nonneg P ε ht _ _
  · exact le_rfl

theorem sum_ballTubeFactor_le_of_degree_bound {n : ℕ} (hn : 2 ≤ n)
    {κ : Type*} [Fintype κ] (b : κ → E n) {C : ℕ}
    (hoverlap : ∀ x, (Finset.univ.filter (fun q => x ∈ Metric.closedBall (b q) 1)).card ≤ C)
    (L : Line n) (P : MvPolynomial (Fin n) ℝ) {ε : ℝ} (hε : ε ≠ 0) (R : ℝ)
    {t D : ℝ} (ht : 0 < t) (hdegree : (P.totalDegree : ℝ) ≤ t*D) :
    ∑ q, ballTubeFactor P ε t R (b q) L ≤
      (C : ℝ)*((ENNReal.ofReal (R+1))^(n-1)*transverseUnitVolume n).toReal*Real.pi*D := by
  let s := Finset.univ.filter (fun q => b q ∈ L.tube R)
  have hsub (q : κ) (hq : q ∈ s) : Metric.closedBall (b q) 1 ⊆ L.tube (R+1) :=
    closedBall_subset_tube_of_center_mem L (b q) (Finset.mem_filter.mp hq).2
  have hov (x : E n) : (s.filter (fun q => x ∈ Metric.closedBall (b q) 1)).card ≤ C := by
    apply (Finset.card_le_card ?_).trans (hoverlap x)
    intro q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ q,(Finset.mem_filter.mp hq).2⟩
  have h := sum_directionalFactor_le_of_degree_bound hn L P hε (R+1) s
    (fun q => Metric.closedBall (b q) 1) (fun q _ => isCompact_closedBall (b q) 1) hsub hov ht hdegree
  simpa only [ballTubeFactor,← Finset.sum_filter] using h

theorem exists_geometric_ballTube_factors {n : ℕ} (hn : 2 ≤ n)
    {κ : Type*} [Fintype κ] (b : κ → E n) (w : κ → ℝ) (hw : ∀ q, 1 ≤ w q)
    {C : ℕ} (hoverlap : ∀ x, (Finset.univ.filter (fun q => x ∈ Metric.closedBall (b q) 1)).card ≤ C)
    (R : ℝ) :
    ∃ S : Line n → κ → ℝ,
      (∀ L q, 0 ≤ S L q) ∧
      (∀ q, ∀ L : Fin n → Line n, (∀ i, b q ∈ (L i).tube R) →
        directionalDeterminantConstant n*w q*|Matrix.det (fun i j => (L j).direction i)| ≤ ∏ i, S (L i) q) ∧
      (∀ L, ∑ q, S L q ≤
        (C : ℝ)*((ENNReal.ofReal (R+1))^(n-1)*transverseUnitVolume n).toReal*Real.pi*weightedVisibilityDegreeBound n w) := by
  obtain ⟨t,ht,ε,hε,P,hP,hD,hdir,hdet⟩ := exists_weighted_directional_factor_polynomial hn b w hw
  refine ⟨fun L q => ballTubeFactor P ε t R (b q) L,
    (fun L q => ballTubeFactor_nonneg P ε R (by linarith) (b q) L),?_,?_⟩
  · intro q L hL
    simpa only [ballTubeFactor,if_pos (hL _)] using hdet q (fun i => (L i).direction) (fun i => (L i).norm_direction)
  · intro L
    exact sum_ballTubeFactor_le_of_degree_bound hn b hoverlap L P hε.ne' R (by linarith) hD

end Kakeya4.Hard.MultilinearKakeya
