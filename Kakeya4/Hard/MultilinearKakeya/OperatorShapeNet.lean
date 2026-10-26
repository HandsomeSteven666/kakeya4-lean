import Kakeya4.Hard.MultilinearKakeya.OperatorCandidates
import Kakeya4.Hard.MultilinearKakeya.OperatorPacking
import Kakeya4.Hard.MultilinearKakeya.FiniteNeighbourColouring

/-! A finite relative shape net with a palette independent of the compact
candidate bounds. No continuous choice of John ellipsoids is assumed. -/

noncomputable section
open Set
open scoped BigOperators Topology

namespace Kakeya4.Hard.MultilinearKakeya

def operatorColourCount (n : ℕ) (C δ : ℝ) : ℕ :=
  ⌈(C*(1+δ)/(δ/C))^(n*n)⌉₊ + 1

theorem exists_relativeOperator_colouring {n : ℕ} {ι : Type*} [Fintype ι]
    (T : ι → E n ≃L[ℝ] E n) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hd : Pairwise (fun i j => Disjoint (relativeOperatorBall (T i) δ) (relativeOperatorBall (T j) δ))) :
    ∃ colour : ι → Fin (operatorColourCount n C δ), ∀ i j, i ≠ j → colour i = colour j →
      C < ‖(T i).symm.toContinuousLinearMap.comp (T j).toContinuousLinearMap‖ ∨
        C < ‖(T j).symm.toContinuousLinearMap.comp (T i).toContinuousLinearMap‖ := by
  classical
  let R := fun i j => i ≠ j ∧
    ‖(T i).symm.toContinuousLinearMap.comp (T j).toContinuousLinearMap‖ ≤ C ∧
    ‖(T j).symm.toContinuousLinearMap.comp (T i).toContinuousLinearMap‖ ≤ C
  let b := (C*(1+δ)/(δ/C))^(n*n)
  have hdegree (i : ι) : Fintype.card {j | R i j} ≤ ⌈b⌉₊ := by
    have hbound := relativeOperator_neighbour_card_bound (T i)
      (fun j : {j | R i j} => T j.val) hC hδ
      (fun j => j.property.2.1) (fun j => j.property.2.2)
      (fun j k hjk => hd (fun he => hjk (Subtype.ext he)))
    exact_mod_cast hbound.trans (Nat.le_ceil b)
  obtain ⟨colour, hc⟩ := finite_neighbour_colouring R (fun i h => h.1 rfl)
    (fun i j h => ⟨h.1.symm,h.2.2,h.2.1⟩) ⌈b⌉₊ hdegree
  refine ⟨colour, fun i j hij hcol => ?_⟩
  by_contra hnot
  push Not at hnot
  exact (hc i j ⟨hij,hnot.1,hnot.2⟩) hcol

theorem exists_disjoint_relativeOperator_cover (n : ℕ) {c R δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ s : Finset (E n ≃L[ℝ] E n),
      (∀ T ∈ s, T.toContinuousLinearMap ∈ operatorCandidateSet n c R) ∧
      Set.Pairwise (s : Set (E n ≃L[ℝ] E n))
        (fun T S => Disjoint (relativeOperatorBall T δ) (relativeOperatorBall S δ)) ∧
      ∀ T : E n ≃L[ℝ] E n, T.toContinuousLinearMap ∈ operatorCandidateSet n c R →
        ∃ S ∈ s,
          ‖S.symm.toContinuousLinearMap.comp T.toContinuousLinearMap‖ ≤ ((1+δ)/(1-δ))^2 ∧
          ‖T.symm.toContinuousLinearMap.comp S.toContinuousLinearMap‖ ≤ ((1+δ)/(1-δ))^2 := by
  classical
  obtain ⟨t, ht, hcover⟩ := exists_finite_relativeOperator_cover n hc hδ
  obtain ⟨s, hst, hd, hmeet⟩ := relativeOperator_disjoint_refinement t hδ
  refine ⟨s, fun T hT => ht T (hst hT), hd, ?_⟩
  let γ := (1+δ)/(1-δ)
  have hγ : 0 ≤ γ := div_nonneg (by linarith) (by linarith)
  have htrans (A B D : E n ≃L[ℝ] E n)
      (hab : ‖A.symm.toContinuousLinearMap.comp B.toContinuousLinearMap‖ ≤ γ)
      (hbd : ‖B.symm.toContinuousLinearMap.comp D.toContinuousLinearMap‖ ≤ γ) :
      ‖A.symm.toContinuousLinearMap.comp D.toContinuousLinearMap‖ ≤ γ^2 := by
    have he : A.symm.toContinuousLinearMap.comp D.toContinuousLinearMap =
        (A.symm.toContinuousLinearMap.comp B.toContinuousLinearMap).comp
          (B.symm.toContinuousLinearMap.comp D.toContinuousLinearMap) := by
      ext x
      simp
    rw [he]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hab hbd (norm_nonneg _) hγ).trans_eq (pow_two γ).symm)
  intro T hT
  obtain ⟨A, hAt, hTA⟩ := hcover T.toContinuousLinearMap hT
  obtain ⟨S, hSs, hAS⟩ := hmeet A hAt
  have hAT := relativeOperatorBall_intersection_bounds A T hδ.le hδ1
    ⟨T.toContinuousLinearMap,hTA,center_mem_relativeOperatorBall T hδ⟩
  have hSA := relativeOperatorBall_intersection_bounds S A hδ.le hδ1
    (by simpa only [inter_comm] using hAS)
  exact ⟨S,hSs,htrans S A T hSA.1 hAT.1,htrans T A S hAT.2 hSA.2⟩

def shapeColourCount (n : ℕ) : ℕ := operatorColourCount n (4*(1+Real.sqrt n)) (1/100)

theorem exists_coloured_operator_shape_net (n : ℕ) {c R : ℝ} (hc : 0 < c) :
    ∃ s : Finset (E n ≃L[ℝ] E n), ∃ colour : s → Fin (shapeColourCount n),
      (∀ T ∈ s, T.toContinuousLinearMap ∈ operatorCandidateSet n c R) ∧
      (∀ T : E n ≃L[ℝ] E n, T.toContinuousLinearMap ∈ operatorCandidateSet n c R →
        ∃ S ∈ s, ‖S.symm.toContinuousLinearMap.comp T.toContinuousLinearMap‖ ≤ 2 ∧
          ‖T.symm.toContinuousLinearMap.comp S.toContinuousLinearMap‖ ≤ 2) ∧
      (∀ T S : s, T ≠ S → colour T = colour S →
        4*(1+Real.sqrt n) < ‖T.val.symm.toContinuousLinearMap.comp S.val.toContinuousLinearMap‖ ∨
          4*(1+Real.sqrt n) < ‖S.val.symm.toContinuousLinearMap.comp T.val.toContinuousLinearMap‖) := by
  classical
  obtain ⟨s, hs, hd, hcover⟩ := exists_disjoint_relativeOperator_cover n hc
    (δ := 1/100) (by norm_num) (by norm_num)
  obtain ⟨colour, hcolour⟩ := exists_relativeOperator_colouring (fun T : s => T.val)
    (C := 4*(1+Real.sqrt n)) (by positivity) (by norm_num : (0 : ℝ) < 1/100)
    (fun T S hTS => hd T.property S.property (fun he => hTS (Subtype.ext he)))
  refine ⟨s,colour,hs,?_,hcolour⟩
  intro T hT
  obtain ⟨S,hS,hfor,hback⟩ := hcover T hT
  have hsmall : ((1+(1/100 : ℝ))/(1-1/100))^2 ≤ 2 := by norm_num
  exact ⟨S,hS,hfor.trans hsmall,hback.trans hsmall⟩

theorem exists_uniform_smoothVisibility_shape_net {n : ℕ} (hn : 2 ≤ n)
    {Q : Set (E n)} (hQ : IsCompact Q) {c : E n} {R : ℝ}
    (hQR : Q ⊆ Metric.closedBall c R) (d : ℕ) :
    ∃ s : Finset (E n ≃L[ℝ] E n), ∃ colour : s → Fin (shapeColourCount n),
      (∀ S ∈ s, ‖S.toContinuousLinearMap‖ ≤ 1) ∧
      (∀ T S : s, T ≠ S → colour T = colour S →
        4*(1+Real.sqrt n) < ‖T.val.symm.toContinuousLinearMap.comp S.val.toContinuousLinearMap‖ ∨
          4*(1+Real.sqrt n) < ‖S.val.symm.toContinuousLinearMap.comp T.val.toContinuousLinearMap‖) ∧
      ∀ (P : MvPolynomial (Fin n) ℝ) (ε : ℝ), ε ≠ 0 → P.totalDegree ≤ d →
        ∃ T : E n ≃L[ℝ] E n,
          T '' Metric.closedBall 0 1 ⊆ visibilityBody (smoothDirectionalSeminorm P ε Q hQ) ∧
          visibilityBody (smoothDirectionalSeminorm P ε Q hQ) ⊆ T '' Metric.closedBall 0 (Real.sqrt n) ∧
          ∃ S ∈ s, ‖S.symm.toContinuousLinearMap.comp T.toContinuousLinearMap‖ ≤ 2 ∧
            ‖T.symm.toContinuousLinearMap.comp S.toContinuousLinearMap‖ ≤ 2 := by
  let c₀ := (((1+Real.sqrt n)*max 1 (localDegreeBudget n R d).toReal)⁻¹)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  obtain ⟨s,colour,hs,hcover,hcolour⟩ := exists_coloured_operator_shape_net n (R := 1) hc₀
  refine ⟨s,colour,fun S hS => (hs S hS).1,hcolour,fun P ε hε hd => ?_⟩
  obtain ⟨T,hinner,houter,hT⟩ := exists_smoothVisibility_johnOperator_in_candidates hn P hε hQ hQR hd
  exact ⟨T,hinner,houter,hcover T hT⟩

end Kakeya4.Hard.MultilinearKakeya
