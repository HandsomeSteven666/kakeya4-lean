import Kakeya4.Construction.Combinatorics.BoxPerturbation
import Kakeya4.Construction.Combinatorics.ParameterNet

/-!
# Finite nets for bounded families of orthogonal-box parameters

Encode a center, an orthonormal frame, and coordinate half-widths in one finite-dimensional
Euclidean parameter space. A net in this code space, together with the perturbation lemma,
produces a finite family of enlarged orthogonal boxes covering every box in a bounded family.
-/

set_option autoImplicit false

open Metric
noncomputable section

namespace Kakeya4.Construction

abbrev BoxParameterIndex (n : ℕ) := Fin n ⊕ ((Fin n × Fin n) ⊕ Fin n)

abbrev BoxParameterSpace (n : ℕ) := EuclideanSpace ℝ (BoxParameterIndex n)

abbrev BoxAmbient (n : ℕ) := EuclideanSpace ℝ (Fin n)

structure OrthogonalBoxData (n : ℕ) where
  center : BoxAmbient n
  frame : OrthonormalBasis (Fin n) ℝ (BoxAmbient n)
  halfWidth : Fin n → ℝ

/-- Store a center, all frame-vector coordinates, and the half-widths in one Euclidean vector. -/
def orthogonalBoxParameterCode {n : ℕ} (d : OrthogonalBoxData n) :
    BoxParameterSpace n :=
  WithLp.toLp 2 fun k =>
    match k with
    | Sum.inl i => d.center i
    | Sum.inr (Sum.inl (i, j)) => d.frame i j
    | Sum.inr (Sum.inr i) => d.halfWidth i

private theorem euclidean_norm_le_sqrt_card_mul_of_coordinate_bound
    {ι : Type*} [Fintype ι] {x : EuclideanSpace ℝ ι} {r : ℝ}
    (hr : 0 ≤ r) (hcoord : ∀ i, |x i| ≤ r) :
    ‖x‖ ≤ √(Fintype.card ι : ℝ) * r := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖x i‖ ^ 2 ≤ (√(Fintype.card ι : ℝ) * r) ^ 2 := by
    calc
      ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : ι, r ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi : ‖x i‖ ≤ r := by simpa [Real.norm_eq_abs] using hcoord i
        have hprod : 0 ≤ (r - ‖x i‖) * (r + ‖x i‖) :=
          mul_nonneg (sub_nonneg.mpr hi) (add_nonneg hr (norm_nonneg _))
        nlinarith
      _ = (Fintype.card ι : ℝ) * r ^ 2 := by simp
      _ = (√(Fintype.card ι : ℝ) * r) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    √(∑ i, ‖x i‖ ^ 2) ≤ √((√(Fintype.card ι : ℝ) * r) ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = √(Fintype.card ι : ℝ) * r := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hr)]

/-- Every coordinate of a Euclidean vector is bounded by its Euclidean norm. -/
private theorem euclidean_coordinate_abs_le_norm
    {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) (i : ι) :
    |x i| ≤ ‖x‖ := by
  have h := PiLp.norm_apply_le x i
  simpa [Real.norm_eq_abs] using h

/-- If center and width coordinates are bounded by `C`, the encoded parameter family lies in
the Euclidean ball of radius `sqrt(card(index)) * (C+1)`. The `+1` pays for the unit frame
vectors. -/
private theorem orthogonalBoxParameterCode_norm_le
    {n : ℕ} (d : OrthogonalBoxData n) {C : ℝ} (hC : 0 ≤ C)
    (hcenter : ‖d.center‖ ≤ C)
    (hwidth : ∀ i, |d.halfWidth i| ≤ C) :
    ‖orthogonalBoxParameterCode d‖ ≤
      √(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1) := by
  apply euclidean_norm_le_sqrt_card_mul_of_coordinate_bound (by positivity)
  intro k
  have hCplus : C ≤ C + 1 := by linarith
  have honeC : (1 : ℝ) ≤ C + 1 := by linarith
  cases k with
  | inl i =>
      have hi := euclidean_coordinate_abs_le_norm d.center i
      have hi' : |d.center i| ≤ C := hi.trans hcenter
      have hk : orthogonalBoxParameterCode d (Sum.inl i) = d.center i := by
        simp [orthogonalBoxParameterCode]
      simpa [hk] using hi'.trans hCplus
  | inr k =>
      cases k with
      | inl ij =>
          rcases ij with ⟨i, j⟩
          have hi := euclidean_coordinate_abs_le_norm (d.frame i) j
          have hunit : ‖d.frame i‖ = 1 := d.frame.norm_eq_one i
          have hi' : |d.frame i j| ≤ 1 := by simpa [hunit] using hi
          have hk : orthogonalBoxParameterCode d (Sum.inr (Sum.inl (i, j))) =
              d.frame i j := by simp [orthogonalBoxParameterCode]
          simpa [hk] using hi'.trans honeC
      | inr i =>
          have hk : orthogonalBoxParameterCode d (Sum.inr (Sum.inr i)) =
              d.halfWidth i := by simp [orthogonalBoxParameterCode]
          simpa [hk] using (hwidth i).trans hCplus

/-- A coordinate of the difference between two parameter codes is at most their full
Euclidean distance. -/
private theorem orthogonalBoxParameterCode_coordinate_le_dist
    {n : ℕ} (d d' : OrthogonalBoxData n) (k : BoxParameterIndex n) :
    |orthogonalBoxParameterCode d k - orthogonalBoxParameterCode d' k| ≤
      dist (orthogonalBoxParameterCode d) (orthogonalBoxParameterCode d') := by
  rw [dist_eq_norm]
  have h := PiLp.norm_apply_le (orthogonalBoxParameterCode d -
    orthogonalBoxParameterCode d') k
  simpa [orthogonalBoxParameterCode, Pi.sub_apply, Real.norm_eq_abs] using h

/-- A bounded family of orthogonal boxes has a finite family of enlarged representative boxes.
The parameter count is the ambient Euclidean packing bound for center, frame, and width data;
the enlargement is the explicit cost from `orthogonalBox_subset_of_parameter_perturbation`.

The bounds on centers and half-widths are explicit inputs. In a John-box application they must
be proved from the truncation radius and the lower/upper axis-length bounds. -/
theorem exists_finite_orthogonalBox_cover
    {n : ℕ} [NeZero n] (S : Set (OrthogonalBoxData n)) {C ε : ℝ}
    (hC : 0 ≤ C)
    (hcenter : ∀ d ∈ S, ‖d.center‖ ≤ C)
    (hwidth : ∀ d ∈ S, ∀ i, |d.halfWidth i| ≤ C)
    (hε : 0 < ε)
    (hεR : ε ≤ √(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1)) :
    ∃ N : Finset (BoxParameterSpace n),
      (N : Set (BoxParameterSpace n)) ⊆ orthogonalBoxParameterCode '' S ∧
      (∀ p ∈ orthogonalBoxParameterCode '' S, ∃ q ∈ N, dist p q ≤ ε) ∧
      (N.card : ℝ) ≤
        4 ^ Module.finrank ℝ (BoxParameterSpace n) *
          ((√(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1)) / ε) ^
            Module.finrank ℝ (BoxParameterSpace n) ∧
      (∀ d ∈ S, ∃ q ∈ N, ∃ d' ∈ S,
        orthogonalBoxParameterCode d' = q ∧
        orthogonalBox d.frame d.center d.halfWidth ⊆
          orthogonalBox d'.frame d'.center
            (fun i => d'.halfWidth i + 2 * (√(n : ℝ) * ε) +
              (n : ℝ) * C * (√(n : ℝ) * ε))) := by
  classical
  let P : Set (BoxParameterSpace n) := orthogonalBoxParameterCode '' S
  let ρ : ℝ := √(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1)
  have hcodeSub : P ⊆ closedBall (0 : BoxParameterSpace n) ρ := by
    rintro p ⟨d, hd, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa [ρ] using orthogonalBoxParameterCode_norm_le d hC (hcenter d hd) (hwidth d hd)
  have hP : Bornology.IsBounded P :=
    (Metric.isBounded_iff_subset_closedBall (0 : BoxParameterSpace n)).2 ⟨ρ, hcodeSub⟩
  obtain ⟨N, hNsub, hNcover, _hNsep, hNcard⟩ :=
    exists_local_net_subset hP hε (by simpa [ρ] using hεR) hcodeSub
  refine ⟨N, ?_, ?_, ?_, ?_⟩
  · simpa [P] using hNsub
  · simpa [P] using hNcover
  · simpa [ρ] using hNcard
  · intro d hd
    have hdp : orthogonalBoxParameterCode d ∈ P := ⟨d, hd, rfl⟩
    obtain ⟨q, hq, hdist⟩ := hNcover (orthogonalBoxParameterCode d) hdp
    obtain ⟨d', hd', hencode⟩ := by simpa [P] using hNsub hq
    refine ⟨q, hq, d', hd', hencode, ?_⟩
    let η : ℝ := √(Fintype.card (Fin n) : ℝ) * ε
    have hη_nonneg : 0 ≤ η := by positivity
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hn : (1 : ℝ) ≤ n := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
    have hn_one : (1 : ℝ) ≤ √(n : ℝ) := by
      calc
        1 = √(1 : ℝ) := by norm_num
        _ ≤ √(n : ℝ) := Real.sqrt_le_sqrt hn
    have hεη : ε ≤ η := by
      dsimp [η]
      simpa only [Fintype.card_fin] using
        (show ε ≤ √(n : ℝ) * ε from by
          calc
            ε = 1 * ε := by ring
            _ ≤ √(n : ℝ) * ε := mul_le_mul_of_nonneg_right hn_one hε.le)
    have hcodeDist :
        dist (orthogonalBoxParameterCode d) (orthogonalBoxParameterCode d') ≤ ε := by
      simpa [hencode] using hdist
    have hcenterCoord : ∀ i : Fin n, |d.center i - d'.center i| ≤ ε := by
      intro i
      have h := orthogonalBoxParameterCode_coordinate_le_dist d d' (Sum.inl i)
      simpa [orthogonalBoxParameterCode] using h.trans hcodeDist
    have hframeCoord : ∀ i j : Fin n, |(d.frame i) j - (d'.frame i) j| ≤ ε := by
      intro i j
      have h := orthogonalBoxParameterCode_coordinate_le_dist d d'
        (Sum.inr (Sum.inl (i, j)))
      simpa [orthogonalBoxParameterCode] using h.trans hcodeDist
    have hcenterNorm : ‖d.center - d'.center‖ ≤ η := by
      have h := euclidean_norm_le_sqrt_card_mul_of_coordinate_bound (by positivity)
        (x := d.center - d'.center) (r := ε) (by
          intro i
          simpa [Pi.sub_apply] using hcenterCoord i)
      simpa [η] using h
    have hframeNorm : ∀ i : Fin n, ‖d.frame i - d'.frame i‖ ≤ η := by
      intro i
      have h := euclidean_norm_le_sqrt_card_mul_of_coordinate_bound (by positivity)
        (x := d.frame i - d'.frame i) (r := ε) (by
          intro j
          simpa [Pi.sub_apply] using hframeCoord i j)
      simpa [η] using h
    have hwidthError : ∀ i : Fin n, |d.halfWidth i - d'.halfWidth i| ≤ η := by
      intro i
      have h := orthogonalBoxParameterCode_coordinate_le_dist d d'
        (Sum.inr (Sum.inr i))
      have h' : |d.halfWidth i - d'.halfWidth i| ≤ ε := by
        simpa [orthogonalBoxParameterCode] using h.trans hcodeDist
      exact h'.trans hεη
    have hframeDist : ∀ i : Fin n, dist (d.frame i) (d'.frame i) ≤ η := by
      intro i
      rw [dist_eq_norm]
      simpa [norm_sub_rev] using hframeNorm i
    have hcenterDist : dist d.center d'.center ≤ η := by
      rw [dist_eq_norm]
      exact hcenterNorm
    have hwidthBound : ∀ i : Fin n, d.halfWidth i ≤ C := by
      intro i
      exact (le_abs_self _).trans (hwidth d hd i)
    simpa [η, Fintype.card_fin] using orthogonalBox_subset_of_parameter_perturbation
      d.frame d'.frame d.center d'.center d.halfWidth d'.halfWidth
      hC hη_nonneg hcenterDist hframeDist hwidthError hwidthBound

end Kakeya4.Construction
