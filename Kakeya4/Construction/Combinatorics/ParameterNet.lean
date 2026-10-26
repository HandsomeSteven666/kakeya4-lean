import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Polynomial-size nets for bounded finite-dimensional parameter sets

This is the quantitative covering interface needed before encoding the John-ellipsoid box
parameters in the sampling argument. It gives a finite net for any bounded subset of a finite-
dimensional real inner-product space, with an explicit ambient-dimension power bound.
-/

set_option autoImplicit false

open MeasureTheory Metric
open scoped ENNReal NNReal

namespace Kakeya4.Construction

private theorem card_mul_closedBall_half_le_cthickening
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {r : ℝ≥0} {s : Set E} {T : Finset E}
    (hTs : (T : Set E) ⊆ s)
    (hTsep : Metric.IsSeparated (r : ℝ≥0∞) (T : Set E)) :
    (T.card : ℝ≥0∞) * volume (closedBall (0 : E) ((r : ℝ) / 2)) ≤
      volume (cthickening (r : ℝ) s) := by
  have hdisj : (T : Set E).PairwiseDisjoint
      (fun x => closedBall x ((r : ℝ) / 2)) := by
    intro x hx y hy hxy
    have hexy : (r : ℝ≥0∞) < edist x y := hTsep hx hy hxy
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal (p := r)] at hexy
    apply Metric.closedBall_disjoint_closedBall
    have hd : (r : ℝ) < dist x y :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg).mp hexy
    linarith
  have hsub : ∀ x ∈ T, closedBall x ((r : ℝ) / 2) ⊆ cthickening (r : ℝ) s := by
    intro x hx
    exact (Metric.closedBall_subset_closedBall (by linarith [r.coe_nonneg])).trans
      (Metric.closedBall_subset_cthickening (hTs hx) (r : ℝ))
  calc
    (T.card : ℝ≥0∞) * volume (closedBall (0 : E) ((r : ℝ) / 2)) =
        ∑ x ∈ T, volume (closedBall x ((r : ℝ) / 2)) := by
      simp [InnerProductSpace.volume_closedBall, Finset.sum_const, nsmul_eq_mul]
    _ = volume (⋃ x ∈ T, closedBall x ((r : ℝ) / 2)) :=
      (measure_biUnion_finset hdisj (fun _ _ => measurableSet_closedBall)).symm
    _ ≤ volume (cthickening (r : ℝ) s) := measure_mono (Set.iUnion₂_subset hsub)

private theorem card_le_of_separated_subset_closedBall_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {r : ℝ≥0} (hr : 0 < r) {x : E} {R : ℝ} (hR : 0 ≤ R) {T : Finset E}
    (hTsub : (T : Set E) ⊆ closedBall x R)
    (hTsep : Metric.IsSeparated (r : ℝ≥0∞) (T : Set E)) :
    (T.card : ℝ) ≤ (2 * (R + r) / (r : ℝ)) ^ Module.finrank ℝ E := by
  let n : ℕ := Module.finrank ℝ E
  let κ : ℝ := Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)
  have hκpos : 0 < κ := by
    dsimp [κ]
    exact div_pos (by positivity) (Real.Gamma_pos_of_pos (by positivity))
  have hpack := card_mul_closedBall_half_le_cthickening hTsub hTsep
  have hvolL : volume (closedBall (0 : E) ((r : ℝ) / 2)) =
      ENNReal.ofReal ((r : ℝ) / 2) ^ n * ENNReal.ofReal κ := by
    simpa [κ, n] using (InnerProductSpace.volume_closedBall (0 : E) ((r : ℝ) / 2))
  have hvolR : volume (cthickening (r : ℝ) (closedBall x R)) =
      ENNReal.ofReal ((r : ℝ) + R) ^ n * ENNReal.ofReal κ := by
    rw [cthickening_closedBall r.coe_nonneg hR x]
    simpa [κ, n, add_comm] using (InnerProductSpace.volume_closedBall x ((r : ℝ) + R))
  rw [hvolL] at hpack
  have hreal : (T.card : ℝ) * ((r : ℝ) / 2) ^ n * κ ≤ ((r : ℝ) + R) ^ n * κ := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    calc
      ENNReal.ofReal ((T.card : ℝ) * ((r : ℝ) / 2) ^ n * κ) =
          (T.card : ℝ≥0∞) *
            (ENNReal.ofReal ((r : ℝ) / 2) ^ n * ENNReal.ofReal κ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
        ring
      _ ≤ volume (cthickening (r : ℝ) (closedBall x R)) := hpack
      _ = ENNReal.ofReal (((r : ℝ) + R) ^ n * κ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
        exact hvolR
  have hpow : (T.card : ℝ) * ((r : ℝ) / 2) ^ n ≤ ((r : ℝ) + R) ^ n :=
    le_of_mul_le_mul_right hreal hκpos
  have hrpow : (0 : ℝ) < (r : ℝ) ^ n := by positivity
  rw [div_pow]
  apply (le_div_iff₀ hrpow).2
  calc
    (T.card : ℝ) * (r : ℝ) ^ n =
        ((T.card : ℝ) * ((r : ℝ) / 2) ^ n) * 2 ^ n := by
      rw [mul_assoc, ← mul_pow]
      ring
    _ ≤ ((r : ℝ) + R) ^ n * 2 ^ n := by gcongr
    _ = (2 * (R + r)) ^ n := by rw [← mul_pow]; congr 1 <;> ring

/-- A bounded subset of a finite-dimensional Euclidean space has an explicit finite `ε`-net.
The centers lie in the set, cover it by closed `ε`-balls, and their count is bounded by the
ambient-dimension packing power. -/
theorem exists_local_net_subset
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {s : Set E} (hs : Bornology.IsBounded s) {x : E} {R ε : ℝ}
    (hε : 0 < ε) (hεR : ε ≤ R) (hsub : s ⊆ closedBall x R) :
    ∃ N : Finset E,
      (N : Set E) ⊆ s ∧
      (∀ y ∈ s, ∃ c ∈ N, dist y c ≤ ε) ∧
      (∀ c ∈ N, ∀ c' ∈ N, c ≠ c' → ε ≤ dist c c') ∧
      (N.card : ℝ) ≤ 4 ^ Module.finrank ℝ E * (R / ε) ^ Module.finrank ℝ E := by
  classical
  let w : ℝ≥0 := ε.toNNReal
  have hw : (w : ℝ) = ε := Real.coe_toNNReal ε (le_of_lt hε)
  have hwpos : 0 < w := by rwa [← NNReal.coe_pos, hw]
  let _hproper : ProperSpace E := FiniteDimensional.proper_real E
  letI : ProperSpace E := _hproper
  have hcoverTop : coveringNumber (w / 2) s ≠ ⊤ := by
    obtain ⟨C, hCs, hCfinite, hCcover⟩ := Metric.exists_finite_isCover_of_totallyBounded
      (show w / 2 ≠ 0 by positivity)
      (hs.isCompact_closure.totallyBounded.subset subset_closure)
    exact ne_top_of_le_ne_top hCfinite.encard_lt_top.ne (hCcover.coveringNumber_le_encard hCs)
  have hpackTop : packingNumber w s ≠ ⊤ := by
    apply ne_top_of_le_ne_top hcoverTop
    calc
      packingNumber w s = packingNumber (2 * (w / 2)) s := by congr 1; ring
      _ ≤ externalCoveringNumber (w / 2) s := packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ coveringNumber (w / 2) s := externalCoveringNumber_le_coveringNumber _ _
  let A : Set E := maximalSeparatedSet w s
  have hAfin : A.Finite := by
    apply Set.encard_ne_top_iff.mp
    simpa [A] using (encard_maximalSeparatedSet (ε := w) (A := s) hpackTop).trans_ne hpackTop
  let N : Finset E := hAfin.toFinset
  have hNcoe : (N : Set E) = A := by ext z; simp [N]
  have hNsub : (N : Set E) ⊆ s := by
    rw [hNcoe]
    exact maximalSeparatedSet_subset
  have hNsep : Metric.IsSeparated (w : ℝ≥0∞) (N : Set E) := by
    rw [hNcoe]
    exact isSeparated_maximalSeparatedSet
  have hNcover : s ⊆ ⋃ c ∈ N, closedBall c (w : ℝ) := by
    change s ⊆ ⋃ c ∈ (N : Set E), closedBall c (w : ℝ)
    rw [hNcoe]
    simpa [A] using (isCover_iff_subset_iUnion_closedBall (ε := w)
      (N := maximalSeparatedSet w s) (s := s)).mp (isCover_maximalSeparatedSet hpackTop)
  refine ⟨N, hNsub, ?_, ?_, ?_⟩
  · intro y hy
    rcases Set.mem_iUnion₂.mp (hNcover hy) with ⟨c, hc, hcy⟩
    refine ⟨c, hc, ?_⟩
    have hdist : dist y c ≤ (w : ℝ) := by
      simpa [Metric.mem_closedBall, dist_comm] using hcy
    simpa [hw] using hdist
  · intro c hc c' hc' hne
    have hdist : (w : ℝ≥0∞) < edist c c' := hNsep (Finset.mem_coe.mpr hc)
      (Finset.mem_coe.mpr hc') hne
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal (p := w)] at hdist
    have hdist' : (w : ℝ) < dist c c' :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg w.coe_nonneg).mp hdist
    simpa [hw] using le_of_lt hdist'
  · have hNR : (N.card : ℝ) ≤ (2 * (R + w) / (w : ℝ)) ^ Module.finrank ℝ E :=
      card_le_of_separated_subset_closedBall_local hwpos (le_trans hε.le hεR)
        (hNsub.trans hsub) hNsep
    calc
      (N.card : ℝ) ≤ (2 * (R + w) / (w : ℝ)) ^ Module.finrank ℝ E := hNR
      _ ≤ (4 * (R / ε)) ^ Module.finrank ℝ E := by
        rw [hw]
        have hbase : 2 * (R + ε) / ε ≤ 4 * (R / ε) := by
          field_simp [ne_of_gt hε]
          nlinarith [hεR]
        have hRpos : 0 < R := lt_of_lt_of_le hε hεR
        exact pow_le_pow_left₀ (by positivity) hbase _
      _ = 4 ^ Module.finrank ℝ E * (R / ε) ^ Module.finrank ℝ E := by rw [mul_pow]

end Kakeya4.Construction
