import Kakeya4.Construction.Combinatorics.BoxParameterBudget
import Kakeya4.Construction.Combinatorics.BoxGeometry
import Kakeya4.Construction.Imported.NuminaThickness.Thickness.BoundingBox

/-!
# Geometry and volume of relevant truncated convex tests

For a convex test containing one indexed tube, the radius-`R` truncation is convex and has
positive finite volume once the indexed tube is contained in the ball and has a positive common
volume.  The module also adapts a licensed convex bounding-box theorem to return an actual
comparable-volume orthogonal box for this truncation.  Uniform center/width bounds, a short-axis
bound, and the weighted GWZ input remain separate obligations.
-/

set_option autoImplicit false

open MeasureTheory

namespace Kakeya4.Construction

/-- The truncation of a relevant convex test is convex, contains a relevant tube, and has positive
finite volume.  Positivity follows from the contained tube; finiteness follows because the
truncation is contained in a compact Euclidean ball.  No closedness assumption on the test is
needed (and compactness of the truncation is not asserted).
-/
theorem RelevantConvexTubeTest.truncatedRegion_geometry
    {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι]
    {indices : Finset ι} {tube : ι → Set (BoxAmbient n)}
    (T : RelevantConvexTubeTest indices tube) (R tubeVolume : ℝ)
    (hTubeBall : ∀ i ∈ indices, tube i ⊆ Metric.closedBall (0 : BoxAmbient n) R)
    (htubeVolume : 0 < tubeVolume)
    (hcommon : ∀ i ∈ indices, (volume (tube i)).toReal = tubeVolume) :
    Convex ℝ (T.1 ∩ Metric.closedBall (0 : BoxAmbient n) R) ∧
      (∃ i ∈ indices, tube i ⊆ T.1 ∩ Metric.closedBall (0 : BoxAmbient n) R) ∧
      0 < volume (T.1 ∩ Metric.closedBall (0 : BoxAmbient n) R) ∧
      volume (T.1 ∩ Metric.closedBall (0 : BoxAmbient n) R) < ⊤ := by
  rcases T.2 with ⟨hconvex, ⟨i, hi, htubeTest⟩⟩
  have hTubePos : 0 < volume (tube i) := by
    by_contra hnot
    have hle : volume (tube i) ≤ 0 := not_lt.mp hnot
    have hz : volume (tube i) = 0 := le_antisymm hle bot_le
    have hreal := hcommon i hi
    rw [hz, ENNReal.toReal_zero] at hreal
    linarith
  have hTubeTrunc : tube i ⊆ T.1 ∩ Metric.closedBall (0 : BoxAmbient n) R := by
    intro x hx
    exact ⟨htubeTest hx, hTubeBall i hi hx⟩
  have htruncPos : 0 < volume (T.1 ∩ Metric.closedBall (0 : BoxAmbient n) R) :=
    lt_of_lt_of_le hTubePos (measure_mono hTubeTrunc)
  have htruncFinite : volume (T.1 ∩ Metric.closedBall (0 : BoxAmbient n) R) < ⊤ := by
    have hsubset : T.1 ∩ Metric.closedBall (0 : BoxAmbient n) R ⊆
        Metric.closedBall (0 : BoxAmbient n) R := Set.inter_subset_right
    have hmono : volume (T.1 ∩ Metric.closedBall (0 : BoxAmbient n) R) ≤
        volume (Metric.closedBall (0 : BoxAmbient n) R) := measure_mono hsubset
    exact lt_of_le_of_lt hmono (isCompact_closedBall (0 : BoxAmbient n) R).measure_lt_top
  refine ⟨hconvex.inter (convex_closedBall (0 : BoxAmbient n) R), ?_, htruncPos, htruncFinite⟩
  exact ⟨i, hi, hTubeTrunc⟩

/-- A relevant truncated convex test has a positive, comparable-volume orthogonal source box.
The returned half-widths are the bounding-box producer's thicknesses, so containment of `K_R`
in the radius-`R` ball bounds every width by `R`. A point in the relevant tube bounds the box
center by `(n+1)R`; an actual radius-`δ` ball in that tube forces every half-width to be at least
`δ`. Thus all five fields of `RelevantConvexTestSourceBox` come from this one box.
-/
theorem RelevantConvexTubeTest.exists_truncatedRegion_comparableBox
    {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι]
    {indices : Finset ι} {tube : ι → Set (BoxAmbient n)}
    (T : RelevantConvexTubeTest indices tube) (R tubeVolume : ℝ)
    (hTubeBall : ∀ i ∈ indices, tube i ⊆ Metric.closedBall (0 : BoxAmbient n) R)
    (htubeVolume : 0 < tubeVolume)
    (hcommon : ∀ i ∈ indices, (volume (tube i)).toReal = tubeVolume) :
    ∃ d : OrthogonalBoxData n,
      T.1 ∩ Metric.closedBall (0 : BoxAmbient n) R ⊆
        orthogonalBox d.frame d.center d.halfWidth ∧
      volume (orthogonalBox d.frame d.center d.halfWidth) ≤
        ENNReal.ofReal ((2 : ℝ)^n * (n.factorial : ℝ)) *
          volume (T.1 ∩ Metric.closedBall (0 : BoxAmbient n) R) ∧
      (∀ i, 0 < d.halfWidth i) ∧
      (∀ i, d.halfWidth i = Metric.thickness ℝ
        (T.1 ∩ Metric.closedBall (0 : BoxAmbient n) R) i) := by
  rcases T.truncatedRegion_geometry R tubeVolume hTubeBall htubeVolume hcommon with
    ⟨hconvex, hrel, hpos, hfinite⟩
  let W := T.1 ∩ Metric.closedBall (0 : BoxAmbient n) R
  have h0 : volume W ≠ 0 := ne_of_gt (by simpa [W] using hpos)
  have htop : volume W ≠ ⊤ := ne_of_lt (by simpa [W] using hfinite)
  have hdim : Module.finrank ℝ (BoxAmbient n) = n := by
    dsimp [BoxAmbient]
    exact finrank_euclideanSpace_fin
  obtain ⟨c, b, len, hlen, hbox, hprod, hlenThickness⟩ :=
    Convex.exists_boundingBox hconvex h0 htop hdim
  let d : OrthogonalBoxData n := ⟨c, b, len⟩
  have hvolEq : volume (orthogonalBox b c len) =
      ENNReal.ofReal ((2 : ℝ)^n * ∏ i, len i) := by
    rw [volume_orthogonalBox]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (by norm_num) (hlen i).le)]
    congr 1
    simp [Finset.prod_mul_distrib]
  have hcoef : ENNReal.ofReal ((2 : ℝ)^n) *
      ((n.factorial : NNReal) : ENNReal) =
      ENNReal.ofReal ((2 : ℝ)^n * (n.factorial : ℝ)) := by
    rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · intro x hx i
    exact hbox x hx i
  · rw [hvolEq]
    calc
      ENNReal.ofReal ((2 : ℝ)^n * ∏ i, len i) =
          ENNReal.ofReal ((2 : ℝ)^n) * ENNReal.ofReal (∏ i, len i) :=
        ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal ((2 : ℝ)^n) *
          (((n.factorial : NNReal) : ENNReal) * volume W) := by gcongr
      _ = (ENNReal.ofReal ((2 : ℝ)^n) *
          ((n.factorial : NNReal) : ENNReal)) * volume W := by rw [← mul_assoc]
      _ = ENNReal.ofReal ((2 : ℝ)^n * (n.factorial : ℝ)) * volume W := by
        rw [hcoef]
  · exact hlen
  · exact hlenThickness

/-- Produce a `RelevantConvexTestSourceBox` for every relevant test with constants fixed before
the test is chosen. The only extra geometric tube input is an actual closed `δ`-ball contained
in each indexed tube; no center, width, or source-box certificate is assumed from the caller.
-/
theorem RelevantConvexTubeTest.exists_sourceBox
    {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι]
    {indices : Finset ι} {tube : ι → Set (BoxAmbient n)}
    (δ R tubeVolume : ℝ)
    (hδ : 0 < δ) (hR : 0 ≤ R)
    (hTubeBall : ∀ i ∈ indices,
      tube i ⊆ Metric.closedBall (0 : BoxAmbient n) R)
    (hTubeInnerBall : ∀ i ∈ indices, ∃ z : BoxAmbient n,
      Metric.closedBall z δ ⊆ tube i)
    (htubeVolume : 0 < tubeVolume)
    (hcommon : ∀ i ∈ indices, (volume (tube i)).toReal = tubeVolume)
    (T : RelevantConvexTubeTest indices tube) :
    Nonempty (RelevantConvexTestSourceBox T.1 δ R ((n : ℝ) * R + R) 1
      (ENNReal.ofReal ((2 : ℝ)^n * (n.factorial : ℝ)))) := by
  classical
  let W : Set (BoxAmbient n) := T.1 ∩ Metric.closedBall (0 : BoxAmbient n) R
  obtain ⟨d, hbox, hvolume, hhalfPositive, hhalfThickness⟩ :=
    T.exists_truncatedRegion_comparableBox R tubeVolume hTubeBall htubeVolume hcommon
  rcases T.2.2 with ⟨i, hi, htubeTest⟩
  rcases hTubeInnerBall i hi with ⟨z, hzTube⟩
  have hzTubeCenter : z ∈ tube i := hzTube (Metric.mem_closedBall_self hδ.le)
  have hzW : z ∈ W := by
    exact ⟨htubeTest hzTubeCenter, hTubeBall i hi hzTubeCenter⟩
  have hwidthUpper : ∀ j, d.halfWidth j ≤ R := by
    intro j
    rw [hhalfThickness j]
    exact Metric.thickness_le_of_subset_closedBall
      (s := W) (x := (0 : BoxAmbient n)) (r := R)
      (by intro x hx; exact hx.2) hR j
  have hcenterDistance : ‖z - d.center‖ ≤ (n : ℝ) * R := by
    have hboxz : z ∈ orthogonalBox d.frame d.center d.halfWidth := hbox hzW
    calc
      ‖z - d.center‖ =
          ‖∑ j : Fin n, d.frame.repr (z - d.center) j • d.frame j‖ := by
            congr 1
            exact (d.frame.sum_repr (z - d.center)).symm
      _ ≤ ∑ _j : Fin n, R := by
        refine norm_sum_le_of_le Finset.univ ?_
        intro j hj
        rw [norm_smul, Real.norm_eq_abs, d.frame.norm_eq_one, mul_one]
        exact (hboxz j).trans (hwidthUpper j)
      _ = (n : ℝ) * R := by simp
  have hzNorm : ‖z‖ ≤ R := by
    have hzBall := hzW.2
    rw [Metric.mem_closedBall, dist_zero_right] at hzBall
    exact hzBall
  have hcenterBound : ‖d.center‖ ≤ (n : ℝ) * R + R := by
    calc
      ‖d.center‖ = ‖z + (d.center - z)‖ := by congr 1; abel
      _ ≤ ‖z‖ + ‖d.center - z‖ := norm_add_le _ _
      _ = ‖z‖ + ‖z - d.center‖ := by rw [norm_sub_rev]
      _ ≤ R + (n : ℝ) * R := add_le_add hzNorm hcenterDistance
      _ = (n : ℝ) * R + R := by ring
  have hC : 0 ≤ (n : ℝ) * R + R := add_nonneg (mul_nonneg (Nat.cast_nonneg n) hR) hR
  have hCwidth : R ≤ (n : ℝ) * R + R := by
    have hn : 0 ≤ (n : ℝ) * R := mul_nonneg (Nat.cast_nonneg n) hR
    linarith
  have hshort := orthogonalBox_halfWidth_ge_of_closedBall_subset d hδ.le
    (by
      intro x hx
      rcases Metric.mem_closedBall.mp hx with hdist
      have hxtube : x ∈ tube i := hzTube hx
      exact ⟨htubeTest hxtube, hTubeBall i hi hxtube⟩)
    hbox
  refine ⟨⟨d, hcenterBound, ?_, ?_, ?_, ?_⟩⟩
  · intro j
    rw [abs_of_pos (hhalfPositive j)]
    exact (hwidthUpper j).trans hCwidth
  · intro j
    simpa using hshort j
  · simpa [W] using hbox
  · simpa [W] using hvolume

/-- A uniform selector produced from actual tube-ball, common-volume, and inner-ball data. The
constants `(n * R + R)`, `κ = 1`, and `B = 2^n n!` are fixed before any relevant convex test.
-/
noncomputable def RelevantConvexTubeTest.sourceBoxSelector
    {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι]
    {indices : Finset ι} {tube : ι → Set (BoxAmbient n)}
    (δ R tubeVolume : ℝ)
    (hδ : 0 < δ) (hR : 0 ≤ R)
    (hTubeBall : ∀ i ∈ indices,
      tube i ⊆ Metric.closedBall (0 : BoxAmbient n) R)
    (hTubeInnerBall : ∀ i ∈ indices, ∃ z : BoxAmbient n,
      Metric.closedBall z δ ⊆ tube i)
    (htubeVolume : 0 < tubeVolume)
    (hcommon : ∀ i ∈ indices, (volume (tube i)).toReal = tubeVolume) :
    ∀ T : RelevantConvexTubeTest indices tube,
      RelevantConvexTestSourceBox T.1 δ R ((n : ℝ) * R + R) 1
        (ENNReal.ofReal ((2 : ℝ)^n * (n.factorial : ℝ))) :=
  fun T => Classical.choice
    (T.exists_sourceBox δ R tubeVolume hδ hR hTubeBall hTubeInnerBall htubeVolume hcommon)
end Kakeya4.Construction
