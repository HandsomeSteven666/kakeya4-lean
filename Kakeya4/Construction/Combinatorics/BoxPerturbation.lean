import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Stability of orthogonal boxes under parameter perturbation

This lemma isolates the geometric continuity step used after discretizing a box center,
orthonormal frame, and half-widths. It makes the enlargement cost explicit and does not
assume anything about convex-clustering or the sampling certificate.
-/

set_option autoImplicit false

open scoped InnerProductSpace
open MeasureTheory

namespace Kakeya4.Construction

/-- The centered rectangular box with frame `b`, center `c`, and coordinate half-widths `a`. -/
def orthogonalBox {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E) (c : E) (a : ι → ℝ) : Set E :=
  {x | ∀ i, |b.repr (x - c) i| ≤ a i}

/-- Orthogonal boxes are convex, with no sign assumptions on their half-widths. -/
theorem convex_orthogonalBox {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E) (c : E) (a : ι → ℝ) :
    Convex ℝ (orthogonalBox b c a) := by
  intro x hx
  intro y hy u v hu hv huv
  intro i
  have hxI : -a i ≤ b.repr (x - c) i ∧ b.repr (x - c) i ≤ a i := (abs_le.mp (hx i))
  have hyI : -a i ≤ b.repr (y - c) i ∧ b.repr (y - c) i ≤ a i := (abs_le.mp (hy i))
  have hcoord :
      b.repr (u • x + v • y - c) i =
        u * b.repr (x - c) i + v * b.repr (y - c) i := by
    have hcoef : (u + v) • c = c := by rw [huv, one_smul]
    have hpoint : u • x + v • y - c = u • (x - c) + v • (y - c) := by
      calc
        u • x + v • y - c = u • x + v • y - (u + v) • c := by
          congr 2
          exact hcoef.symm
        _ = u • (x - c) + v • (y - c) := by
          rw [add_smul, smul_sub, smul_sub]
          abel
    rw [hpoint]
    simp [map_add, map_smul, PiLp.smul_apply, smul_eq_mul]
  rw [abs_le]
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hxI.1 hu
    have h2 := mul_le_mul_of_nonneg_left hyI.1 hv
    rw [hcoord]
    calc
      -a i = u * (-a i) + v * (-a i) := by rw [← add_mul, huv]; ring
      _ ≤ u * b.repr (x - c) i + v * b.repr (y - c) i := add_le_add h1 h2
  · have h1 := mul_le_mul_of_nonneg_left hxI.2 hu
    have h2 := mul_le_mul_of_nonneg_left hyI.2 hv
    rw [hcoord]
    calc
      a i = u * a i + v * a i := by rw [← add_mul, huv]; ring
      _ ≥ u * b.repr (x - c) i + v * b.repr (y - c) i := add_le_add h1 h2

/-- The volume of an orthogonal box is the product of its coordinate interval lengths.
This connects the parameter-net boxes to the volume data consumed by the sampler. -/
theorem volume_orthogonalBox {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (b : OrthonormalBasis ι ℝ E) (c : E) (a : ι → ℝ) :
    volume (orthogonalBox b c a) = ∏ i, ENNReal.ofReal (2 * a i) := by
  classical
  let f : E → EuclideanSpace ℝ ι := fun x => b.repr (x - c)
  let boxPi : Set (ι → ℝ) := Set.Icc (fun i => -a i) (fun i => a i)
  let coordBox : Set (EuclideanSpace ℝ ι) := WithLp.ofLp ⁻¹' boxPi
  have htranslate : MeasurePreserving (fun x : E => x - c) volume volume := by
    exact ⟨measurable_id.sub measurable_const,
      by simpa only [sub_eq_add_neg] using
        (Measure.IsAddRightInvariant.map_add_right_eq_self (-c) :
          Measure.map (fun x : E => x + -c) volume = volume)⟩
  have hrepr : MeasurePreserving b.repr volume volume := b.measurePreserving_repr
  have hf : MeasurePreserving f volume volume := by
    exact hrepr.comp htranslate
  have hset : orthogonalBox b c a = f ⁻¹' coordBox := by
    ext x
    simp only [orthogonalBox, Set.mem_ofPred_eq, Set.mem_preimage, f, coordBox,
      boxPi, Set.mem_Icc, abs_le, Pi.le_def]
    simp only [forall_and]
  have hofLp : MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ ι → (ι → ℝ)) :=
    PiLp.volume_preserving_ofLp ι
  have hcoordMeas : MeasurableSet coordBox := by
    exact measurableSet_Icc.preimage (WithLp.measurable_ofLp 2 (ι → ℝ))
  have hcoordVol : volume coordBox = ∏ i, ENNReal.ofReal (2 * a i) := by
    calc
      volume coordBox = volume (WithLp.ofLp ⁻¹' boxPi) := rfl
      _ = volume boxPi := hofLp.measure_preimage (s := boxPi)
        measurableSet_Icc.nullMeasurableSet
      _ = ∏ i, ENNReal.ofReal (a i - -a i) := by
        simpa [boxPi] using (Real.volume_Icc_pi (a := fun i : ι => -a i)
          (b := fun i => a i))
      _ = ∏ i, ENNReal.ofReal (2 * a i) := by
        apply Finset.prod_congr rfl
        intro i hi
        congr 1
        ring
  calc
    volume (orthogonalBox b c a) = volume (f ⁻¹' coordBox) := by rw [hset]
    _ = volume coordBox := hf.measure_preimage (s := coordBox) hcoordMeas.nullMeasurableSet
    _ = ∏ i, ENNReal.ofReal (2 * a i) := hcoordVol

/-- If the center, every frame vector, and every half-width move by at most `η`, then the
original box is contained in the perturbed frame box enlarged in each coordinate by
`2η + |ι| R η`. Here `R` bounds the original half-widths. -/
theorem orthogonalBox_subset_of_parameter_perturbation
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b b' : OrthonormalBasis ι ℝ E) (c c' : E) (a a' : ι → ℝ)
    {R η : ℝ} (hR : 0 ≤ R) (hη : 0 ≤ η)
    (hcenter : dist c c' ≤ η)
    (hframe : ∀ i, dist (b i) (b' i) ≤ η)
    (hwidth : ∀ i, |a i - a' i| ≤ η)
    (ha_le : ∀ i, a i ≤ R) :
    orthogonalBox b c a ⊆
      orthogonalBox b' c' (fun i => a' i + 2 * η + (Fintype.card ι : ℝ) * R * η) := by
  classical
  intro x hx j
  have hc_norm : ‖c - c'‖ ≤ η := by
    simpa [dist_eq_norm] using hcenter
  have hj_frame : ‖b' j - b j‖ ≤ η := by
    have h := hframe j
    simpa [dist_eq_norm, norm_sub_rev] using h
  have hrepr : b'.repr (x - c') j =
      (∑ i, b.repr (x - c) i * ⟪b' j, b i⟫_ℝ) + ⟪b' j, c - c'⟫_ℝ := by
    rw [b'.repr_apply_apply]
    have hdecomp : x - c' = (x - c) + (c - c') := by abel
    rw [hdecomp, inner_add_right]
    calc
      ⟪b' j, x - c⟫_ℝ + ⟪b' j, c - c'⟫_ℝ =
          ⟪b' j, ∑ i, b.repr (x - c) i • b i⟫_ℝ + ⟪b' j, c - c'⟫_ℝ := by
            rw [b.sum_repr (x - c)]
      _ = (∑ i, b.repr (x - c) i * ⟪b' j, b i⟫_ℝ) + ⟪b' j, c - c'⟫_ℝ := by
            simp [inner_sum, real_inner_smul_right]
  have hsum_split :
      (∑ i, b.repr (x - c) i * ⟪b' j, b i⟫_ℝ) =
        (∑ i ∈ Finset.univ.erase j,
          b.repr (x - c) i * ⟪b' j, b i⟫_ℝ) +
          b.repr (x - c) j * ⟪b' j, b j⟫_ℝ := by
    simpa using (Finset.sum_erase_add (Finset.univ)
      (fun i => b.repr (x - c) i * ⟪b' j, b i⟫_ℝ) (Finset.mem_univ j)).symm
  have hxj : |b.repr (x - c) j| ≤ a j := hx j
  have hdiag_inner : |⟪b' j, b j⟫_ℝ| ≤ 1 := by
    calc
      |⟪b' j, b j⟫_ℝ| ≤ ‖b' j‖ * ‖b j‖ := abs_real_inner_le_norm _ _
      _ = 1 := by simp
  have hdiag :
      |b.repr (x - c) j * ⟪b' j, b j⟫_ℝ| ≤ a j := by
    rw [abs_mul]
    calc
      |b.repr (x - c) j| * |⟪b' j, b j⟫_ℝ| ≤ |b.repr (x - c) j| * 1 :=
        mul_le_mul_of_nonneg_left hdiag_inner (abs_nonneg _)
      _ = |b.repr (x - c) j| := by ring
      _ ≤ a j := hxj
  have hoff : ∀ i ∈ Finset.univ.erase j,
      |b.repr (x - c) i * ⟪b' j, b i⟫_ℝ| ≤ R * η := by
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    have horth : ⟪b j, b i⟫_ℝ = 0 := by
      have h := (orthonormal_iff_ite.mp b.orthonormal) j i
      simpa [Ne.symm hij] using h
    have hinner_eq : ⟪b' j, b i⟫_ℝ = ⟪b' j - b j, b i⟫_ℝ := by
      have hsum : b' j = (b' j - b j) + b j := by abel
      have hinnerSum := congrArg (fun z : E => ⟪z, b i⟫_ℝ) hsum
      calc
        ⟪b' j, b i⟫_ℝ = ⟪(b' j - b j) + b j, b i⟫_ℝ := hinnerSum
        _ = ⟪b' j - b j, b i⟫_ℝ + ⟪b j, b i⟫_ℝ := inner_add_left _ _ _
        _ = ⟪b' j - b j, b i⟫_ℝ := by rw [horth, add_zero]
    have hinner : |⟪b' j, b i⟫_ℝ| ≤ η := by
      rw [hinner_eq]
      calc
        |⟪b' j - b j, b i⟫_ℝ| ≤ ‖b' j - b j‖ * ‖b i‖ := abs_real_inner_le_norm _ _
        _ ≤ η := by simpa using (mul_le_mul_of_nonneg_right hj_frame (norm_nonneg (b i)))
    have hxi : |b.repr (x - c) i| ≤ R := (hx i).trans (ha_le i)
    rw [abs_mul]
    calc
      |b.repr (x - c) i| * |⟪b' j, b i⟫_ℝ| ≤
          |b.repr (x - c) i| * η :=
        mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
      _ ≤ R * η := mul_le_mul_of_nonneg_right hxi hη
  have hoff_sum :
      |∑ i ∈ Finset.univ.erase j,
        b.repr (x - c) i * ⟪b' j, b i⟫_ℝ| ≤
        (Fintype.card ι : ℝ) * R * η := by
    calc
      |∑ i ∈ Finset.univ.erase j,
          b.repr (x - c) i * ⟪b' j, b i⟫_ℝ|
          ≤ ∑ i ∈ Finset.univ.erase j,
              |b.repr (x - c) i * ⟪b' j, b i⟫_ℝ| := by
                exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.univ.erase j, R * η := by
            apply Finset.sum_le_sum
            intro i hi
            exact hoff i hi
      _ ≤ (Fintype.card ι : ℝ) * R * η := by
            have hcard : ((Finset.univ.erase j).card : ℝ) ≤ Fintype.card ι := by
              exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
            calc
              ∑ i ∈ Finset.univ.erase j, R * η =
                  ((Finset.univ.erase j).card : ℝ) * (R * η) := by simp
              _ ≤ (Fintype.card ι : ℝ) * R * η := by
                  nlinarith [mul_nonneg hR hη]
  have hcenter_inner : |⟪b' j, c - c'⟫_ℝ| ≤ η := by
    calc
      |⟪b' j, c - c'⟫_ℝ| ≤ ‖b' j‖ * ‖c - c'‖ := abs_real_inner_le_norm _ _
      _ ≤ η := by simpa using (mul_le_mul_of_nonneg_left hc_norm (norm_nonneg (b' j)))
  have hcoord : |b'.repr (x - c') j| ≤
      a j + (Fintype.card ι : ℝ) * R * η + η := by
    rw [hrepr, hsum_split]
    calc
      |(∑ i ∈ Finset.univ.erase j,
          b.repr (x - c) i * ⟪b' j, b i⟫_ℝ) +
          b.repr (x - c) j * ⟪b' j, b j⟫_ℝ + ⟪b' j, c - c'⟫_ℝ|
          ≤ |∑ i ∈ Finset.univ.erase j,
              b.repr (x - c) i * ⟪b' j, b i⟫_ℝ| +
            |b.repr (x - c) j * ⟪b' j, b j⟫_ℝ| +
            |⟪b' j, c - c'⟫_ℝ| := by
              calc
                |(∑ i ∈ Finset.univ.erase j,
                    b.repr (x - c) i * ⟪b' j, b i⟫_ℝ) +
                    b.repr (x - c) j * ⟪b' j, b j⟫_ℝ + ⟪b' j, c - c'⟫_ℝ|
                    ≤ |(∑ i ∈ Finset.univ.erase j,
                        b.repr (x - c) i * ⟪b' j, b i⟫_ℝ) +
                        b.repr (x - c) j * ⟪b' j, b j⟫_ℝ| +
                        |⟪b' j, c - c'⟫_ℝ| := abs_add_le _ _
                _ ≤ |∑ i ∈ Finset.univ.erase j,
                      b.repr (x - c) i * ⟪b' j, b i⟫_ℝ| +
                    |b.repr (x - c) j * ⟪b' j, b j⟫_ℝ| +
                    |⟪b' j, c - c'⟫_ℝ| := by
                      gcongr
                      exact abs_add_le _ _
      _ ≤ (Fintype.card ι : ℝ) * R * η + a j + η := by
            gcongr
      _ = a j + (Fintype.card ι : ℝ) * R * η + η := by ring
  have hwidth' : a j ≤ a' j + η := by
    have h := hwidth j
    rw [abs_le] at h
    linarith
  linarith [hcoord]

end Kakeya4.Construction
