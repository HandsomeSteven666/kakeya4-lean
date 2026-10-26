import Kakeya4.Construction.Combinatorics.BoxParameterNet

/-!
# Quadratic-scale budgets for orthogonal-box parameter nets

This module packages the finite parameter net at precision `α * δ^2`. A lower bound on every
half-width controls the multiplicative cost of the additive `O(δ^2)` enlargement, while the
net cardinality becomes an explicit power of `δ⁻¹`.
-/

set_option autoImplicit false

open Finset
open MeasureTheory
open Metric
open scoped ENNReal
noncomputable section

namespace Kakeya4.Construction

/-- Adding a quadratic error to widths bounded below at scale `δ` changes their product by at
most a dimension-dependent multiplicative factor. -/
private theorem finset_prod_add_quadratic_le
    {ι : Type*} [Fintype ι] (a : ι → ℝ) {δ κ D : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 < κ) (hD : 0 ≤ D)
    (ha : ∀ i, κ * δ ≤ a i) :
    (∏ i, (a i + D * δ ^ 2)) ≤
      (∏ i, a i) * (1 + D / κ) ^ Fintype.card ι := by
  have hcoef : 0 ≤ D / κ := div_nonneg hD hκ.le
  have hδsq : δ ^ 2 ≤ δ := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ1)]
  have hpert : ∀ i, D * δ ^ 2 ≤ (D / κ) * a i := by
    intro i
    have hscaled := mul_le_mul_of_nonneg_left (ha i) hcoef
    have hcancel : (D / κ) * (κ * δ) = D * δ := by
      field_simp
    calc
      D * δ ^ 2 ≤ D * δ := mul_le_mul_of_nonneg_left hδsq hD
      _ = (D / κ) * (κ * δ) := hcancel.symm
      _ ≤ (D / κ) * a i := hscaled
  have hfactor : 0 ≤ 1 + D / κ := by linarith
  calc
    (∏ i, (a i + D * δ ^ 2)) ≤ ∏ i, (a i * (1 + D / κ)) := by
      apply Finset.prod_le_prod₀
      · intro i _
        have hai : 0 ≤ a i := (mul_pos hκ hδ).le.trans (ha i)
        have herror : 0 ≤ D * δ ^ 2 := mul_nonneg hD (sq_nonneg δ)
        exact add_nonneg hai herror
      · intro i _
        calc
          a i + D * δ ^ 2 ≤ a i + (D / κ) * a i := by nlinarith [hpert i]
          _ = a i * (1 + D / κ) := by ring
    _ = (∏ i, a i) * (1 + D / κ) ^ Fintype.card ι := by simp [Finset.prod_mul_distrib]

/-- A finite cover of a bounded orthogonal-box family at parameter precision `α δ²`, with the
resulting polynomial net-size bound and a controlled product of the enlarged representative
half-widths.

The family itself is supplied by the caller. The hypotheses explicitly record center/width
bounds, the lower thickness `κ δ`, and the product-width budget `V`; this theorem does not
construct a John box or infer those geometric facts from convexity. -/
theorem exists_finite_orthogonalBox_cover_of_quadratic_budget
    {n : ℕ} [NeZero n] (S : Set (OrthogonalBoxData n))
    {C α κ δ V : ℝ}
    (hC : 0 ≤ C)
    (hcenter : ∀ d ∈ S, ‖d.center‖ ≤ C)
    (hwidth : ∀ d ∈ S, ∀ i, |d.halfWidth i| ≤ C)
    (hα : 0 < α) (hκ : 0 < κ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hthickness : ∀ d ∈ S, ∀ i, κ * δ ≤ d.halfWidth i)
    (hvolume : ∀ d ∈ S, (∏ i, d.halfWidth i) ≤ V)
    (hscale : α * δ ^ 2 ≤
      √(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1)) :
    ∃ N : Finset (BoxParameterSpace n),
      (N : Set (BoxParameterSpace n)) ⊆ orthogonalBoxParameterCode '' S ∧
      (∀ p ∈ orthogonalBoxParameterCode '' S, ∃ q ∈ N, dist p q ≤ α * δ ^ 2) ∧
      (N.card : ℝ) ≤
        4 ^ Module.finrank ℝ (BoxParameterSpace n) *
          ((√(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1)) / α) ^
            Module.finrank ℝ (BoxParameterSpace n) *
          (δ⁻¹) ^ (2 * Module.finrank ℝ (BoxParameterSpace n)) ∧
      (∀ d ∈ S, ∃ q ∈ N, ∃ d' ∈ S,
        orthogonalBoxParameterCode d' = q ∧
        orthogonalBox d.frame d.center d.halfWidth ⊆
          orthogonalBox d'.frame d'.center
            (fun i => (d'.halfWidth i +
              ((2 + (n : ℝ) * C) * √(n : ℝ) * α) * δ ^ 2)) ∧
        (∏ i, (d'.halfWidth i +
          ((2 + (n : ℝ) * C) * √(n : ℝ) * α) * δ ^ 2)) ≤
          (1 + (((2 + (n : ℝ) * C) * √(n : ℝ) * α) / κ)) ^ n * V) := by
  classical
  let ρ : ℝ := √(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1)
  let m : ℕ := Module.finrank ℝ (BoxParameterSpace n)
  let ε : ℝ := α * δ ^ 2
  let D : ℝ := (2 + (n : ℝ) * C) * √(n : ℝ) * α
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hscale' : ε ≤ ρ := by simpa [ε, ρ] using hscale
  obtain ⟨N, hNsub, hNcover, hNcard, hNboxes⟩ :=
    exists_finite_orthogonalBox_cover S hC hcenter hwidth hε hscale'
  have hratio : ρ / ε = (ρ / α) * (δ⁻¹) ^ 2 := by
    dsimp [ε]
    field_simp [ne_of_gt hα, ne_of_gt hδ]
  have hcard : (N.card : ℝ) ≤ 4 ^ m * (ρ / α) ^ m * (δ⁻¹) ^ (2 * m) := by
    calc
      (N.card : ℝ) ≤ 4 ^ m * (ρ / ε) ^ m := by
        simpa [m, ρ] using hNcard
      _ = 4 ^ m * (ρ / α) ^ m * (δ⁻¹) ^ (2 * m) := by
        rw [hratio, mul_pow, ← pow_mul]
        ring
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hfactor : 0 ≤ (1 + D / κ) ^ n := by positivity
  refine ⟨N, hNsub, ?_, ?_, ?_⟩
  · simpa [ε] using hNcover
  · simpa [m, ρ] using hcard
  · intro d hd
    obtain ⟨q, hq, d', hd', hencode, hsubset⟩ := hNboxes d hd
    refine ⟨q, hq, d', hd', hencode, ?_, ?_⟩
    · have hsubset' := hsubset
      simp only [ε] at hsubset'
      have hwidthEq :
          (fun i => d'.halfWidth i + D * δ ^ 2) =
            (fun i => d'.halfWidth i + 2 * (√(n : ℝ) * (α * δ ^ 2)) +
              (n : ℝ) * C * (√(n : ℝ) * (α * δ ^ 2))) := by
        funext i
        dsimp [D]
        ring
      rw [hwidthEq]
      exact hsubset'
    · have hprod := finset_prod_add_quadratic_le (a := d'.halfWidth)
        hδ hδ1 hκ hD (hthickness d' hd')
      have hprod' :
          (∏ i, (d'.halfWidth i + D * δ ^ 2)) ≤
            (∏ i, d'.halfWidth i) * (1 + D / κ) ^ n := by
        simpa using hprod
      calc
        (∏ i, (d'.halfWidth i + D * δ ^ 2)) ≤
            (∏ i, d'.halfWidth i) * (1 + D / κ) ^ n := hprod'
        _ ≤ V * (1 + D / κ) ^ n :=
          mul_le_mul_of_nonneg_right (hvolume d' hd') hfactor
        _ = (1 + D / κ) ^ n * V := mul_comm _ _

private theorem orthogonalBoxParameterCode_coordinate_dist
    {n : ℕ} (d d' : OrthogonalBoxData n) (k : BoxParameterIndex n) :
    |orthogonalBoxParameterCode d k - orthogonalBoxParameterCode d' k| ≤
      dist (orthogonalBoxParameterCode d) (orthogonalBoxParameterCode d') := by
  rw [dist_eq_norm]
  have h := PiLp.norm_apply_le
    (orthogonalBoxParameterCode d - orthogonalBoxParameterCode d')
    k
  simpa [orthogonalBoxParameterCode, Pi.sub_apply, Real.norm_eq_abs] using h

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

/-- The quadratic parameter net can be used with a *relative* box-volume estimate.

For each source box, a nearby representative box enlarged by the net error contains it, and the
product of the enlarged half-widths is bounded by a dimension-dependent factor times the product
of that source box's half-widths. The net still has polynomial cardinality in `δ⁻¹`.

This is the interface needed to pass from pointwise enclosing-box certificates for truncated
convex sets to one finite family of sampler tests. The caller must still supply the actual source
family, its center/width bounds, and the lower half-width bound; this theorem does not construct
those boxes from convexity. -/
theorem exists_finite_orthogonalBox_cover_with_relative_product_budget
    {n : ℕ} [NeZero n] (S : Set (OrthogonalBoxData n))
    {C α κ δ : ℝ}
    (hC : 0 ≤ C)
    (hcenter : ∀ d ∈ S, ‖d.center‖ ≤ C)
    (hwidth : ∀ d ∈ S, ∀ i, |d.halfWidth i| ≤ C)
    (hα : 0 < α) (hκ : 0 < κ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hthickness : ∀ d ∈ S, ∀ i, κ * δ ≤ d.halfWidth i)
    (hscale : α * δ ^ 2 ≤
      √(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1)) :
    ∃ N : Finset (BoxParameterSpace n),
      (N : Set (BoxParameterSpace n)) ⊆ orthogonalBoxParameterCode '' S ∧
      (∀ p ∈ orthogonalBoxParameterCode '' S, ∃ q ∈ N,
        dist p q ≤ α * δ ^ 2) ∧
      (N.card : ℝ) ≤
        4 ^ Module.finrank ℝ (BoxParameterSpace n) *
          ((√(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1)) / α) ^
            Module.finrank ℝ (BoxParameterSpace n) *
          (δ⁻¹) ^ (2 * Module.finrank ℝ (BoxParameterSpace n)) ∧
      (∀ d ∈ S, ∃ q ∈ N, ∃ d' ∈ S,
        orthogonalBoxParameterCode d' = q ∧
        orthogonalBox d.frame d.center d.halfWidth ⊆
          orthogonalBox d'.frame d'.center
            (fun i => d'.halfWidth i +
              ((2 + (n : ℝ) * C) * √(n : ℝ) * α) * δ ^ 2) ∧
        (∏ i, (d'.halfWidth i +
          ((2 + (n : ℝ) * C) * √(n : ℝ) * α) * δ ^ 2)) ≤
          (1 + ((α + (2 + (n : ℝ) * C) * √(n : ℝ) * α) / κ)) ^ n *
            (∏ i, d.halfWidth i)) := by
  classical
  let V : ℝ := C ^ n
  have hvolume : ∀ d ∈ S, (∏ i, d.halfWidth i) ≤ V := by
    intro d hd
    have hnonneg : ∀ i, 0 ≤ d.halfWidth i := fun i =>
      (mul_pos hκ hδ).le.trans (hthickness d hd i)
    have hupper : ∀ i, d.halfWidth i ≤ C := fun i =>
      (le_abs_self _).trans (hwidth d hd i)
    calc
      (∏ i, d.halfWidth i) ≤ ∏ _i : Fin n, C := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact hnonneg i
        · intro i hi
          exact hupper i
      _ = V := by simp [V]
  obtain ⟨N, hNsub, hNcover, hNcard, hNboxes⟩ :=
    exists_finite_orthogonalBox_cover_of_quadratic_budget S
      hC hcenter hwidth hα hκ hδ hδ1 hthickness hvolume hscale
  refine ⟨N, hNsub, ?_, ?_, ?_⟩
  · simpa using hNcover
  · simpa using hNcard
  · intro d hd
    have hdp : orthogonalBoxParameterCode d ∈ orthogonalBoxParameterCode '' S :=
      ⟨d, hd, rfl⟩
    obtain ⟨q, hq, hdist⟩ := hNcover (orthogonalBoxParameterCode d) hdp
    obtain ⟨d', hd', hencode⟩ := hNsub hq
    have hdist' :
        dist (orthogonalBoxParameterCode d) (orthogonalBoxParameterCode d') ≤
          α * δ ^ 2 := by
      simpa [hencode] using hdist
    let ε : ℝ := α * δ ^ 2
    let η : ℝ := √(n : ℝ) * ε
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hη_nonneg : 0 ≤ η := by positivity
    have hn : (1 : ℝ) ≤ n := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
    have hn_one : (1 : ℝ) ≤ √(n : ℝ) := by
      calc
        1 = √(1 : ℝ) := by norm_num
        _ ≤ √(n : ℝ) := Real.sqrt_le_sqrt hn
    have hεη : ε ≤ η := by
      dsimp [η]
      calc
        ε = 1 * ε := by ring
        _ ≤ √(n : ℝ) * ε := mul_le_mul_of_nonneg_right hn_one hε.le
    have hcenterCoord : ∀ i : Fin n, |d.center i - d'.center i| ≤ ε := by
      intro i
      have h := orthogonalBoxParameterCode_coordinate_dist d d' (Sum.inl i)
      have h' := h.trans hdist'
      simpa [orthogonalBoxParameterCode, ε] using h'
    have hframeCoord : ∀ i j : Fin n, |(d.frame i) j - (d'.frame i) j| ≤ ε := by
      intro i j
      have h := orthogonalBoxParameterCode_coordinate_dist d d'
        (Sum.inr (Sum.inl (i, j)))
      have h' := h.trans hdist'
      simpa [orthogonalBoxParameterCode, ε] using h'
    have hwidthError : ∀ i : Fin n, |d.halfWidth i - d'.halfWidth i| ≤ η := by
      intro i
      have h := orthogonalBoxParameterCode_coordinate_dist d d'
        (Sum.inr (Sum.inr i))
      have h' := h.trans hdist'
      have h'' : |d.halfWidth i - d'.halfWidth i| ≤ ε := by
        simpa [orthogonalBoxParameterCode, ε] using h'
      exact h''.trans hεη
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
    have hcenterDist : dist d.center d'.center ≤ η := by
      rw [dist_eq_norm]
      exact hcenterNorm
    have hframeDist : ∀ i : Fin n, dist (d.frame i) (d'.frame i) ≤ η := by
      intro i
      rw [dist_eq_norm]
      simpa [norm_sub_rev] using hframeNorm i
    have hwidthBound : ∀ i : Fin n, d.halfWidth i ≤ C := by
      intro i
      exact (le_abs_self _).trans (hwidth d hd i)
    have hsubset :
        orthogonalBox d.frame d.center d.halfWidth ⊆
          orthogonalBox d'.frame d'.center
            (fun i => d'.halfWidth i +
              ((2 + (n : ℝ) * C) * √(n : ℝ) * α) * δ ^ 2) := by
      have h := orthogonalBox_subset_of_parameter_perturbation
        d.frame d'.frame d.center d'.center d.halfWidth d'.halfWidth
        hC hη_nonneg hcenterDist hframeDist hwidthError hwidthBound
      have hwidthEq :
          (fun i => d'.halfWidth i +
            ((2 + (n : ℝ) * C) * √(n : ℝ) * α) * δ ^ 2) =
          (fun i => d'.halfWidth i + 2 * η +
            (n : ℝ) * C * η) := by
        funext i
        dsimp [η, ε]
        ring
      simpa [hwidthEq] using h
    have hD : 0 ≤ ((2 + (n : ℝ) * C) * √(n : ℝ) * α) := by positivity
    have hRel : 0 ≤ α + ((2 + (n : ℝ) * C) * √(n : ℝ) * α) := by positivity
    have hwidthCompare : ∀ i : Fin n,
        d'.halfWidth i + ((2 + (n : ℝ) * C) * √(n : ℝ) * α) * δ ^ 2 ≤
          d.halfWidth i +
            (α + (2 + (n : ℝ) * C) * √(n : ℝ) * α) * δ ^ 2 := by
      intro i
      have hcoord := orthogonalBoxParameterCode_coordinate_dist d d'
        (Sum.inr (Sum.inr i))
      have habs := hcoord.trans hdist'
      have hcoord' : d'.halfWidth i - d.halfWidth i ≤ α * δ ^ 2 := by
        have hleft := (abs_le.mp habs).1
        dsimp [orthogonalBoxParameterCode] at hleft
        nlinarith
      nlinarith [sq_nonneg δ]
    have hproducts :
        (∏ i, (d'.halfWidth i +
          ((2 + (n : ℝ) * C) * √(n : ℝ) * α) * δ ^ 2)) ≤
          (∏ i, (d.halfWidth i +
            (α + (2 + (n : ℝ) * C) * √(n : ℝ) * α) * δ ^ 2)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        have hi' : 0 ≤ d'.halfWidth i :=
          (mul_pos hκ hδ).le.trans (hthickness d' hd' i)
        exact add_nonneg hi' (mul_nonneg hD (sq_nonneg δ))
      · intro i hi
        exact hwidthCompare i
    have hpert := finset_prod_add_quadratic_le (a := d.halfWidth)
      hδ hδ1 hκ hRel (hthickness d hd)
    have hpert' :
        (∏ i, (d.halfWidth i +
          (α + (2 + (n : ℝ) * C) * √(n : ℝ) * α) * δ ^ 2)) ≤
          (∏ i, d.halfWidth i) *
            (1 + ((α + (2 + (n : ℝ) * C) * √(n : ℝ) * α) / κ)) ^ n := by
      simpa [Fintype.card_fin] using hpert
    refine ⟨q, hq, d', hd', hencode, hsubset, ?_⟩
    · calc
        (∏ i, (d'.halfWidth i +
          ((2 + (n : ℝ) * C) * √(n : ℝ) * α) * δ ^ 2)) ≤
            ∏ i, (d.halfWidth i +
              (α + (2 + (n : ℝ) * C) * √(n : ℝ) * α) * δ ^ 2) := hproducts
        _ ≤ (∏ i, d.halfWidth i) *
            (1 + ((α + (2 + (n : ℝ) * C) * √(n : ℝ) * α) / κ)) ^ n := hpert'
        _ = (1 + ((α + (2 + (n : ℝ) * C) * √(n : ℝ) * α) / κ)) ^ n *
            (∏ i, d.halfWidth i) := by ring

private theorem orthogonalBoxParameterCode_injective
    {n : ℕ} : Function.Injective (@orthogonalBoxParameterCode n) := by
  intro d d' h
  have hcenter : d.center = d'.center := by
    ext i
    have hi := congrArg (fun v : BoxParameterSpace n => v (Sum.inl i)) h
    simpa [orthogonalBoxParameterCode] using hi
  have hframe : d.frame = d'.frame := by
    apply DFunLike.coe_injective
    funext i
    ext j
    have hij := congrArg (fun v : BoxParameterSpace n =>
      v (Sum.inr (Sum.inl (i, j)))) h
    simpa [orthogonalBoxParameterCode] using hij
  have hwidth : d.halfWidth = d'.halfWidth := by
    funext i
    have hi := congrArg (fun v : BoxParameterSpace n => v (Sum.inr (Sum.inr i))) h
    simpa [orthogonalBoxParameterCode] using hi
  cases d
  cases d'
  simp_all

private theorem volume_orthogonalBox_eq_ofReal_twoPow_mul_prod
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ (BoxAmbient n))
    (c : BoxAmbient n) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    volume (orthogonalBox b c a) =
      ENNReal.ofReal ((2 : ℝ) ^ n * ∏ i, a i) := by
  rw [volume_orthogonalBox]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (by norm_num) (ha i))]
  congr 1
  simp [Finset.prod_mul_distrib]

/-- Enlarge an orthogonal box by the same additive amount on every half-width. -/
def orthogonalBox_enlargement {n : ℕ} (d : OrthogonalBoxData n) (ε : ℝ) : Set (BoxAmbient n) :=
  orthogonalBox d.frame d.center (fun i => d.halfWidth i + ε)

/-- The real volume represented by the exact orthogonal-box volume formula. -/
def orthogonalBox_enlargementVolume {n : ℕ} (d : OrthogonalBoxData n) (ε : ℝ) : ℝ :=
  (2 : ℝ) ^ n * ∏ i, (d.halfWidth i + ε)

/-- Additive width error used when the code space is netted at `α * δ ^ 2`. -/
def orthogonalBoxNetEnlargementError (n : ℕ) (C α δ : ℝ) : ℝ :=
  ((2 + (n : ℝ) * C) * √(n : ℝ) * α) * δ ^ 2

/-- Relative volume cost paid by the quadratic orthogonal-box parameter net. -/
def orthogonalBoxNetRelativeVolumeFactor (n : ℕ) (C α κ : ℝ) : ℝ :=
  (1 + ((α + (2 + (n : ℝ) * C) * √(n : ℝ) * α) / κ)) ^ n

private theorem volume_enlargement_le_of_product_bound
    {n : ℕ} (d d' : OrthogonalBoxData n) (ε F : ℝ)
    (hd : ∀ i, 0 ≤ d.halfWidth i)
    (hd' : ∀ i, 0 ≤ d'.halfWidth i + ε)
    (hF : 0 ≤ F)
    (hprod : (∏ i, (d'.halfWidth i + ε)) ≤ F * ∏ i, d.halfWidth i) :
    volume (orthogonalBox_enlargement d' ε) ≤
      ENNReal.ofReal F * volume (orthogonalBox d.frame d.center d.halfWidth) := by
  have hsourceVol := volume_orthogonalBox_eq_ofReal_twoPow_mul_prod
    d.frame d.center d.halfWidth hd
  have hexpandedVol := volume_orthogonalBox_eq_ofReal_twoPow_mul_prod
    d'.frame d'.center (fun i => d'.halfWidth i + ε) hd'
  have hscale :
      (2 : ℝ) ^ n * ∏ i, (d'.halfWidth i + ε) ≤
        F * ((2 : ℝ) ^ n * ∏ i, d.halfWidth i) := by
    have h := mul_le_mul_of_nonneg_left hprod (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
    calc
      (2 : ℝ) ^ n * ∏ i, (d'.halfWidth i + ε) ≤
          (2 : ℝ) ^ n * (F * ∏ i, d.halfWidth i) := h
      _ = F * ((2 : ℝ) ^ n * ∏ i, d.halfWidth i) := by ring
  calc
    volume (orthogonalBox_enlargement d' ε) =
        ENNReal.ofReal ((2 : ℝ) ^ n * ∏ i, (d'.halfWidth i + ε)) := by
      rw [orthogonalBox_enlargement]
      exact hexpandedVol
    _ ≤ ENNReal.ofReal (F * ((2 : ℝ) ^ n * ∏ i, d.halfWidth i)) :=
      ENNReal.ofReal_le_ofReal hscale
    _ = ENNReal.ofReal F * volume (orthogonalBox d.frame d.center d.halfWidth) := by
      rw [ENNReal.ofReal_mul hF, hsourceVol]

/-- Package the quadratic orthogonal-box net as the finite convex-box family required by the
sampler. Each relevant convex test is first truncated to the radius-`R` ball and covered by a
source box; the net then gives a finite representative box. The theorem proves the resulting
`hboxCover`, its volume comparison, finite box volumes, and the lower box-to-tube volume ratio.
The pointwise source-box certificates remain explicit caller inputs and are not proved here.
-/
theorem exists_finite_orthogonalBox_sampler_cover_of_source_certificates
    {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (indices : Finset ι) (tube : ι → Set (BoxAmbient n))
    (δ R C α κ : ℝ) (B : ℝ≥0∞)
    (hB : B < ⊤) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hTubeBall : ∀ i ∈ indices, tube i ⊆ closedBall (0 : BoxAmbient n) R)
    (tubeVolume : ℝ) (htube : 0 < tubeVolume)
    (hcommon : ∀ i ∈ indices, (volume (tube i)).toReal = tubeVolume)
    (S : Set (OrthogonalBoxData n))
    (hC : 0 ≤ C)
    (hcenter : ∀ d ∈ S, ‖d.center‖ ≤ C)
    (hwidth : ∀ d ∈ S, ∀ i, |d.halfWidth i| ≤ C)
    (hκ : 0 < κ) (hα : 0 < α)
    (hthickness : ∀ d ∈ S, ∀ i, κ * δ ≤ d.halfWidth i)
    (hscale : α * δ ^ 2 ≤
      √(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1))
    (hsource : ∀ K : Set (BoxAmbient n), Convex ℝ K →
      (∃ i ∈ indices, tube i ⊆ K) →
      ∃ d ∈ S,
        K ∩ closedBall (0 : BoxAmbient n) R ⊆
          orthogonalBox d.frame d.center d.halfWidth ∧
        volume (orthogonalBox d.frame d.center d.halfWidth) ≤
          B * volume (K ∩ closedBall (0 : BoxAmbient n) R))
    (hsourceRelevant : ∀ d ∈ S, ∃ K : Set (BoxAmbient n), Convex ℝ K ∧
      (∃ i ∈ indices, tube i ⊆ K) ∧
      K ∩ closedBall (0 : BoxAmbient n) R ⊆
        orthogonalBox d.frame d.center d.halfWidth) :
    ∃ N : Finset (BoxParameterSpace n),
      (N.card : ℝ) ≤
        4 ^ Module.finrank ℝ (BoxParameterSpace n) *
          ((√(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1)) / α) ^
            Module.finrank ℝ (BoxParameterSpace n) *
          (δ⁻¹) ^ (2 * Module.finrank ℝ (BoxParameterSpace n)) ∧
      ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) * B < ⊤ ∧
      ∃ rep : {q : BoxParameterSpace n // q ∈ N} → OrthogonalBoxData n,
        (∀ q, orthogonalBoxParameterCode (rep q) = q.1) ∧
        (∀ q, Convex ℝ (orthogonalBox_enlargement (rep q)
          (orthogonalBoxNetEnlargementError n C α δ))) ∧
        (∀ q, volume (orthogonalBox_enlargement (rep q)
          (orthogonalBoxNetEnlargementError n C α δ)) < ⊤) ∧
        (∀ q,
          (volume (orthogonalBox_enlargement (rep q)
            (orthogonalBoxNetEnlargementError n C α δ))).toReal =
            orthogonalBox_enlargementVolume (rep q)
              (orthogonalBoxNetEnlargementError n C α δ)) ∧
        (∀ q, 1 ≤ orthogonalBox_enlargementVolume (rep q)
          (orthogonalBoxNetEnlargementError n C α δ) / tubeVolume) ∧
        (∀ K : Set (BoxAmbient n), Convex ℝ K →
          (∃ i ∈ indices, tube i ⊆ K) →
          ∃ q : {q : BoxParameterSpace n // q ∈ N},
            (∀ i ∈ indices, tube i ⊆ K →
              tube i ⊆ orthogonalBox_enlargement (rep q)
                (orthogonalBoxNetEnlargementError n C α δ)) ∧
            volume (orthogonalBox_enlargement (rep q)
              (orthogonalBoxNetEnlargementError n C α δ)) ≤
              (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) * B) *
                volume K) := by
  classical
  obtain ⟨N, hNsub, _hNcover, hNcard, hNbox⟩ :=
    exists_finite_orthogonalBox_cover_with_relative_product_budget S
      hC hcenter hwidth hα hκ hδ hδ1 hthickness hscale
  have himage : ∀ q : {q : BoxParameterSpace n // q ∈ N},
      ∃ d, d ∈ S ∧ orthogonalBoxParameterCode d = q.1 := by
    intro q
    exact hNsub q.property
  let rep : {q : BoxParameterSpace n // q ∈ N} → OrthogonalBoxData n := fun q =>
    Classical.choose (himage q)
  have hrep : ∀ q, rep q ∈ S ∧ orthogonalBoxParameterCode (rep q) = q.1 := by
    intro q
    exact Classical.choose_spec (himage q)
  have hε : 0 ≤ orthogonalBoxNetEnlargementError n C α δ := by
    dsimp [orthogonalBoxNetEnlargementError]
    positivity
  have hF : 0 ≤ orthogonalBoxNetRelativeVolumeFactor n C α κ := by
    dsimp [orthogonalBoxNetRelativeVolumeFactor]
    positivity
  refine ⟨N, hNcard, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB, rep,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun q => (hrep q).2
  · intro q
    exact convex_orthogonalBox (rep q).frame (rep q).center
      (fun i => (rep q).halfWidth i + orthogonalBoxNetEnlargementError n C α δ)
  · intro q
    have hwidth' : ∀ i, 0 ≤ (rep q).halfWidth i +
        orthogonalBoxNetEnlargementError n C α δ := by
      intro i
      have hbase : 0 < (rep q).halfWidth i := by
        exact (mul_pos hκ hδ).trans_le (hthickness (rep q) (hrep q).1 i)
      positivity
    have hvol := volume_orthogonalBox_eq_ofReal_twoPow_mul_prod
      (rep q).frame (rep q).center
      (fun i => (rep q).halfWidth i + orthogonalBoxNetEnlargementError n C α δ) hwidth'
    rw [orthogonalBox_enlargement, hvol]
    exact ENNReal.ofReal_lt_top
  · intro q
    have hwidth' : ∀ i, 0 ≤ (rep q).halfWidth i +
        orthogonalBoxNetEnlargementError n C α δ := by
      intro i
      have hbase : 0 < (rep q).halfWidth i := by
        exact (mul_pos hκ hδ).trans_le (hthickness (rep q) (hrep q).1 i)
      positivity
    have hvol := volume_orthogonalBox_eq_ofReal_twoPow_mul_prod
      (rep q).frame (rep q).center
      (fun i => (rep q).halfWidth i + orthogonalBoxNetEnlargementError n C α δ) hwidth'
    rw [orthogonalBox_enlargement, orthogonalBox_enlargementVolume, hvol]
    exact ENNReal.toReal_ofReal (by
      exact mul_nonneg (pow_nonneg (by norm_num) _) (Finset.prod_nonneg fun i _ => hwidth' i))
  · intro q
    obtain ⟨K, hK, ⟨i, hi, hiTube⟩, hsourceBox⟩ := hsourceRelevant (rep q) (hrep q).1
    have htubeTrunc : tube i ⊆ K ∩ closedBall (0 : BoxAmbient n) R := by
      intro x hx
      exact ⟨hiTube hx, hTubeBall i hi hx⟩
    have hsourceTube : tube i ⊆ orthogonalBox (rep q).frame (rep q).center (rep q).halfWidth :=
      htubeTrunc.trans hsourceBox
    have hboxTube : tube i ⊆ orthogonalBox_enlargement (rep q)
        (orthogonalBoxNetEnlargementError n C α δ) := by
      intro x hx j
      have hbase := hsourceTube hx j
      exact hbase.trans (le_add_of_nonneg_right hε)
    have hwidth' : ∀ j, 0 ≤ (rep q).halfWidth j +
        orthogonalBoxNetEnlargementError n C α δ := by
      intro j
      have hj : 0 < (rep q).halfWidth j :=
        (mul_pos hκ hδ).trans_le (hthickness (rep q) (hrep q).1 j)
      positivity
    have hboxVolEq : volume (orthogonalBox_enlargement (rep q)
        (orthogonalBoxNetEnlargementError n C α δ)) =
        ENNReal.ofReal (orthogonalBox_enlargementVolume (rep q)
          (orthogonalBoxNetEnlargementError n C α δ)) := by
      rw [orthogonalBox_enlargement, orthogonalBox_enlargementVolume]
      exact volume_orthogonalBox_eq_ofReal_twoPow_mul_prod _ _ _ hwidth'
    have hboxFinite : volume (orthogonalBox_enlargement (rep q)
        (orthogonalBoxNetEnlargementError n C α δ)) ≠ ⊤ := by
      rw [hboxVolEq]
      exact ENNReal.ofReal_ne_top
    have hvolMono : volume (tube i) ≤
        volume (orthogonalBox_enlargement (rep q)
          (orthogonalBoxNetEnlargementError n C α δ)) := measure_mono hboxTube
    have hreal := ENNReal.toReal_mono hboxFinite hvolMono
    rw [hcommon i hi] at hreal
    rw [show (volume (orthogonalBox_enlargement (rep q)
      (orthogonalBoxNetEnlargementError n C α δ))).toReal =
        orthogonalBox_enlargementVolume (rep q)
          (orthogonalBoxNetEnlargementError n C α δ) by
        rw [hboxVolEq]
        exact ENNReal.toReal_ofReal (by
          exact mul_nonneg (pow_nonneg (by norm_num) _) (Finset.prod_nonneg fun j _ => hwidth' j))] at hreal
    exact (le_div_iff₀ htube).2 (by simpa using hreal)
  · intro K hK hRelevant
    have hRelevant' := hRelevant
    obtain ⟨i, hi, hiTube⟩ := hRelevant
    obtain ⟨d, hd, htruncate, hvolSource⟩ := hsource K hK hRelevant'
    obtain ⟨qcode, hqcode, d', hd', hcode, hcontain, hproduct⟩ := hNbox d hd
    let q : {q : BoxParameterSpace n // q ∈ N} := ⟨qcode, hqcode⟩
    have hrepEq : rep q = d' := by
      apply orthogonalBoxParameterCode_injective
      exact (hrep q).2.trans hcode.symm
    refine ⟨q, ?_, ?_⟩
    · intro j hj hjK
      have hjTruncate : tube j ⊆ K ∩ closedBall (0 : BoxAmbient n) R := by
        intro x hx
        exact ⟨hjK hx, hTubeBall j hj hx⟩
      have hjSource : tube j ⊆ orthogonalBox d.frame d.center d.halfWidth :=
        hjTruncate.trans htruncate
      have hjExpanded : tube j ⊆ orthogonalBox_enlargement d'
          (orthogonalBoxNetEnlargementError n C α δ) := by
        intro x hx
        exact hcontain (hjSource hx)
      simpa [hrepEq] using hjExpanded
    · have hsourceWidths : ∀ j, 0 ≤ d.halfWidth j := by
        intro j
        exact (mul_pos hκ hδ).le.trans (hthickness d hd j)
      have hexpandedWidths : ∀ j, 0 ≤ d'.halfWidth j +
          orthogonalBoxNetEnlargementError n C α δ := by
        intro j
        have hj : 0 < d'.halfWidth j := (mul_pos hκ hδ).trans_le (hthickness d' hd' j)
        positivity
      have hvolumeExpanded := volume_enlargement_le_of_product_bound d d'
        (orthogonalBoxNetEnlargementError n C α δ)
        (orthogonalBoxNetRelativeVolumeFactor n C α κ) hsourceWidths hexpandedWidths hF
        (by simpa [orthogonalBoxNetEnlargementError,
          orthogonalBoxNetRelativeVolumeFactor] using hproduct)
      calc
        volume (orthogonalBox_enlargement (rep q)
            (orthogonalBoxNetEnlargementError n C α δ)) ≤
            ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) *
              volume (orthogonalBox d.frame d.center d.halfWidth) := by
                simpa [hrepEq] using hvolumeExpanded
        _ ≤ ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) *
              (B * volume (K ∩ closedBall (0 : BoxAmbient n) R)) := by
                gcongr
        _ ≤ ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) *
              (B * volume K) := by
                gcongr
                exact Set.inter_subset_left
        _ = (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) * B) *
              volume K := by ac_rfl

/-- A source box certificate attached to one relevant convex test. The center, width, short-axis,
truncation-containment, and volume-comparison fields are kept together so a geometric theorem can
produce one certificate per test without separately constructing a global box family. -/
structure RelevantConvexTestSourceBox {n : ℕ} (K : Set (BoxAmbient n))
    (δ R C κ : ℝ) (B : ℝ≥0∞) where
  box : OrthogonalBoxData n
  center_bound : ‖box.center‖ ≤ C
  width_bound : ∀ j, |box.halfWidth j| ≤ C
  short_axis_bound : ∀ j, κ * δ ≤ box.halfWidth j
  truncation_subset : K ∩ closedBall (0 : BoxAmbient n) R ⊆
    orthogonalBox box.frame box.center box.halfWidth
  volume_bound : volume (orthogonalBox box.frame box.center box.halfWidth) ≤
    B * volume (K ∩ closedBall (0 : BoxAmbient n) R)

/-- The relevant convex tests are exactly those that contain at least one indexed tube. -/
abbrev RelevantConvexTubeTest {n : ℕ} {ι : Type*} [Fintype ι]
    (indices : Finset ι) (tube : ι → Set (BoxAmbient n)) :=
  {K : Set (BoxAmbient n) // Convex ℝ K ∧ ∃ i ∈ indices, tube i ⊆ K}

/-- Compile a per-test `K_R` source-box selector directly into the finite sampler family.

The output is the same finite net and `hboxCover` certificate as
`exists_finite_orthogonalBox_sampler_cover_of_source_certificates`. The source family is formed
as the range of the supplied selector, so every representative box is tied to a relevant convex
test and the lower box-to-tube volume payment is discharged from that test. The selector's
truncation inclusion, comparable-volume bound, center/width bounds, and short-axis bound remain
explicit caller evidence; this theorem does not prove the convex comparable-box result for `K_R`.
-/
theorem exists_finite_orthogonalBox_sampler_cover_of_relevant_source_box_selector
    {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (indices : Finset ι) (tube : ι → Set (BoxAmbient n))
    (δ R C α κ : ℝ) (B : ℝ≥0∞)
    (hB : B < ⊤) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hTubeBall : ∀ i ∈ indices, tube i ⊆ closedBall (0 : BoxAmbient n) R)
    (tubeVolume : ℝ) (htube : 0 < tubeVolume)
    (hcommon : ∀ i ∈ indices, (volume (tube i)).toReal = tubeVolume)
    (hC : 0 ≤ C) (hκ : 0 < κ) (hα : 0 < α)
    (hscale : α * δ ^ 2 ≤
      √(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1))
    (sourceBox : ∀ T : RelevantConvexTubeTest indices tube,
      RelevantConvexTestSourceBox T.1 δ R C κ B) :
    ∃ N : Finset (BoxParameterSpace n),
      (N.card : ℝ) ≤
        4 ^ Module.finrank ℝ (BoxParameterSpace n) *
          ((√(Fintype.card (BoxParameterIndex n) : ℝ) * (C + 1)) / α) ^
            Module.finrank ℝ (BoxParameterSpace n) *
          (δ⁻¹) ^ (2 * Module.finrank ℝ (BoxParameterSpace n)) ∧
      ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) * B < ⊤ ∧
      ∃ rep : {q : BoxParameterSpace n // q ∈ N} → OrthogonalBoxData n,
        (∀ q, orthogonalBoxParameterCode (rep q) = q.1) ∧
        (∀ q, Convex ℝ (orthogonalBox_enlargement (rep q)
          (orthogonalBoxNetEnlargementError n C α δ))) ∧
        (∀ q, volume (orthogonalBox_enlargement (rep q)
          (orthogonalBoxNetEnlargementError n C α δ)) < ⊤) ∧
        (∀ q,
          (volume (orthogonalBox_enlargement (rep q)
            (orthogonalBoxNetEnlargementError n C α δ))).toReal =
            orthogonalBox_enlargementVolume (rep q)
              (orthogonalBoxNetEnlargementError n C α δ)) ∧
        (∀ q, 1 ≤ orthogonalBox_enlargementVolume (rep q)
          (orthogonalBoxNetEnlargementError n C α δ) / tubeVolume) ∧
        (∀ K : Set (BoxAmbient n), Convex ℝ K →
          (∃ i ∈ indices, tube i ⊆ K) →
          ∃ q : {q : BoxParameterSpace n // q ∈ N},
            (∀ i ∈ indices, tube i ⊆ K →
              tube i ⊆ orthogonalBox_enlargement (rep q)
                (orthogonalBoxNetEnlargementError n C α δ)) ∧
            volume (orthogonalBox_enlargement (rep q)
              (orthogonalBoxNetEnlargementError n C α δ)) ≤
              (ENNReal.ofReal (orthogonalBoxNetRelativeVolumeFactor n C α κ) * B) *
                volume K) := by
  classical
  let S : Set (OrthogonalBoxData n) := Set.range (fun T => (sourceBox T).box)
  have hcenter : ∀ d ∈ S, ‖d.center‖ ≤ C := by
    rintro d ⟨T, rfl⟩
    exact (sourceBox T).center_bound
  have hwidth : ∀ d ∈ S, ∀ j, |d.halfWidth j| ≤ C := by
    rintro d ⟨T, rfl⟩ j
    exact (sourceBox T).width_bound j
  have hthickness : ∀ d ∈ S, ∀ j, κ * δ ≤ d.halfWidth j := by
    rintro d ⟨T, rfl⟩ j
    exact (sourceBox T).short_axis_bound j
  have hsource : ∀ K : Set (BoxAmbient n), Convex ℝ K →
      (∃ i ∈ indices, tube i ⊆ K) →
      ∃ d ∈ S,
        K ∩ closedBall (0 : BoxAmbient n) R ⊆
          orthogonalBox d.frame d.center d.halfWidth ∧
        volume (orthogonalBox d.frame d.center d.halfWidth) ≤
          B * volume (K ∩ closedBall (0 : BoxAmbient n) R) := by
    intro K hK hRelevant
    let T : RelevantConvexTubeTest indices tube := ⟨K, hK, hRelevant⟩
    exact ⟨(sourceBox T).box, Set.mem_range_self T,
      (sourceBox T).truncation_subset, (sourceBox T).volume_bound⟩
  have hsourceRelevant : ∀ d ∈ S, ∃ K : Set (BoxAmbient n), Convex ℝ K ∧
      (∃ i ∈ indices, tube i ⊆ K) ∧
      K ∩ closedBall (0 : BoxAmbient n) R ⊆
        orthogonalBox d.frame d.center d.halfWidth := by
    rintro d ⟨T, rfl⟩
    exact ⟨T.1, T.2.1, T.2.2, (sourceBox T).truncation_subset⟩
  exact exists_finite_orthogonalBox_sampler_cover_of_source_certificates
    indices tube δ R C α κ B hB hδ hδ1 hTubeBall tubeVolume htube hcommon S hC
    hcenter hwidth hκ hα hthickness hscale hsource hsourceRelevant

end Kakeya4.Construction
