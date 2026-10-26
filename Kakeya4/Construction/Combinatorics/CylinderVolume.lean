import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/-!
# Euclidean cylinder volume in dimension three

An axial cylinder is measured in orthogonal coordinates: an interval along a unit axis and a
closed ball in its orthogonal complement. The coordinate decomposition is assembled from
Mathlib's orthogonal decomposition and volume-preserving `WithLp` equivalence.
-/

set_option autoImplicit false

namespace Kakeya4.Construction

open MeasureTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Two carriers are essentially distinct when their overlap has at most half the larger
carrier volume. This is the volume predicate used by the licensed Numina tube development,
stated locally so this project can connect it to its own carrier geometry without importing
Numina's Tube hierarchy. -/
def IsCarrierEssentiallyDistinct (s t : Set E) : Prop :=
  volume (s ∩ t) ≤ (1 / 2 : ℝ≥0∞) * max (volume s) (volume t)

/-- For equal-volume carriers, failure of essential distinctness gives the strict half-volume
overlap required by a tube-overlap containment theorem. -/
theorem overlap_gt_half_of_not_carrierEssentiallyDistinct {s t : Set E}
    (hvol : volume s = volume t) (hnot : ¬ IsCarrierEssentiallyDistinct s t) :
    (1 / 2 : ℝ≥0∞) * volume s < volume (s ∩ t) := by
  have hoverlap := not_le.mp (show ¬ volume (s ∩ t) ≤
      (1 / 2 : ℝ≥0∞) * max (volume s) (volume t) from hnot)
  rw [hvol, max_self] at hoverlap
  calc
    (1 / 2 : ℝ≥0∞) * volume s = (1 / 2 : ℝ≥0∞) * volume t := by rw [hvol]
    _ < volume (s ∩ t) := hoverlap

/-- The orthogonal coordinates of a point, with its axial coordinate represented as a real. -/
noncomputable def axialCoordinates (d : E) (hd : ‖d‖ = 1) :
    E → ℝ × ((ℝ ∙ d)ᗮ : Submodule ℝ E) := by
  let K : Submodule ℝ E := ℝ ∙ d
  let φ : ℝ ≃ₗᵢ[ℝ] K := LinearIsometryEquiv.toSpanUnitSingleton d hd
  let e₁ : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (Kᗮ : Submodule ℝ E)) :=
    K.orthogonalDecomposition.trans
      (LinearIsometryEquiv.withLpProdCongr 2 φ.symm
        (LinearIsometryEquiv.refl ℝ (Kᗮ : Submodule ℝ E)))
  exact fun p => WithLp.ofLp (e₁ p)

/-- A cylinder described by its interval coordinate along a unit direction and a ball in the
orthogonal complement. -/
def axialCylinder (d : E) (hd : ‖d‖ = 1) (a b r : ℝ) : Set E :=
  {p | (axialCoordinates d hd p).1 ∈ Set.Icc a b ∧
    (axialCoordinates d hd p).2 ∈ Metric.closedBall 0 r}

/-- The orthogonal coordinate map preserves volume. -/
theorem measurePreserving_axialCoordinates (d : E) (hd : ‖d‖ = 1) :
    MeasurePreserving (axialCoordinates d hd) := by
  let K : Submodule ℝ E := ℝ ∙ d
  let φ : ℝ ≃ₗᵢ[ℝ] K := LinearIsometryEquiv.toSpanUnitSingleton d hd
  let e₁ : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (Kᗮ : Submodule ℝ E)) :=
    K.orthogonalDecomposition.trans
      (LinearIsometryEquiv.withLpProdCongr 2 φ.symm
        (LinearIsometryEquiv.refl ℝ (Kᗮ : Submodule ℝ E)))
  change MeasurePreserving (fun p : E => WithLp.ofLp (e₁ p))
  exact (WithLp.volume_preserving_ofLp ℝ (Kᗮ : Submodule ℝ E)).comp
    (e₁.measurePreserving)

/-- Cylinder volume factors into axial interval length and the cross-section ball volume. -/
theorem volume_axialCylinder (d : E) (hd : ‖d‖ = 1) (a b r : ℝ) :
    volume (axialCylinder d hd a b r) =
      ENNReal.ofReal (b - a) *
        volume (Metric.closedBall (0 : ((ℝ ∙ d)ᗮ : Submodule ℝ E)) r) := by
  let f := axialCoordinates d hd
  have hset : axialCylinder d hd a b r =
      f ⁻¹' (Set.Icc a b ×ˢ Metric.closedBall (0 : ((ℝ ∙ d)ᗮ : Submodule ℝ E)) r) := by
    ext p
    rfl
  rw [hset, (measurePreserving_axialCoordinates d hd).measure_preimage
    (measurableSet_Icc.prod measurableSet_closedBall).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]

/-- In dimension three, the cross-section of an axial cylinder is a two-dimensional disk. -/
theorem volume_axialCylinder_three (hdim : Module.finrank ℝ E = 3)
    (d : E) (hd : ‖d‖ = 1) (a b r : ℝ) :
    volume (axialCylinder d hd a b r) =
      ENNReal.ofReal (b - a) * (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) := by
  have hspan : Module.finrank ℝ (ℝ ∙ d : Submodule ℝ E) = 1 := by
    have hne : d ≠ 0 := by intro h; simp [h] at hd
    simpa using finrank_span_singleton hne
  have hperp : Module.finrank ℝ ((ℝ ∙ d)ᗮ : Submodule ℝ E) = 2 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ d : Submodule ℝ E)
    omega
  letI : Nontrivial ((ℝ ∙ d)ᗮ : Submodule ℝ E) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hperp]; decide)
  rw [volume_axialCylinder d hd a b r,
    InnerProductSpace.volume_closedBall_of_dim_even (k := 1) (by simpa using hperp)]
  simp only [hperp, pow_one, Nat.factorial_one, Nat.cast_one, div_one]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The first orthogonal coordinate is the inner product with the axis direction. -/
theorem axialCoordinates_fst (d : E) (hd : ‖d‖ = 1) (p : E) :
    (axialCoordinates d hd p).1 = inner ℝ p d := by
  let K : Submodule ℝ E := ℝ ∙ d
  let φ : ℝ ≃ₗᵢ[ℝ] K := LinearIsometryEquiv.toSpanUnitSingleton d hd
  let e₁ : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (Kᗮ : Submodule ℝ E)) :=
    K.orthogonalDecomposition.trans
      (LinearIsometryEquiv.withLpProdCongr 2 φ.symm
        (LinearIsometryEquiv.refl ℝ (Kᗮ : Submodule ℝ E)))
  have he : e₁ p = WithLp.toLp 2
      (φ.symm (K.orthogonalProjectionOnto p), Kᗮ.orthogonalProjectionOnto p) := by
    change LinearIsometryEquiv.withLpProdCongr 2 φ.symm
      (LinearIsometryEquiv.refl ℝ (Kᗮ : Submodule ℝ E))
      (K.orthogonalDecomposition p) = _
    rw [Submodule.orthogonalDecomposition_apply]
    simp [LinearIsometryEquiv.withLpProdCongr]
  have hproj : K.orthogonalProjectionOnto p = φ (inner ℝ p d) := by
    apply Subtype.ext
    change K.starProjection p = (inner ℝ p d : ℝ) • d
    rw [Submodule.starProjection_unit_singleton (𝕜 := ℝ) hd p, real_inner_comm]
  change (e₁ p).ofLp.1 = inner ℝ p d
  rw [he]
  change φ.symm (K.orthogonalProjectionOnto p) = inner ℝ p d
  rw [hproj, LinearIsometryEquiv.symm_apply_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The second orthogonal coordinate is the vector perpendicular to the axis. -/
theorem axialCoordinates_snd_norm (d : E) (hd : ‖d‖ = 1) (p : E) :
    ‖(axialCoordinates d hd p).2‖ =
      ‖p - (inner ℝ p d : ℝ) • d‖ := by
  let K : Submodule ℝ E := ℝ ∙ d
  let φ : ℝ ≃ₗᵢ[ℝ] K := LinearIsometryEquiv.toSpanUnitSingleton d hd
  let e₁ : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (Kᗮ : Submodule ℝ E)) :=
    K.orthogonalDecomposition.trans
      (LinearIsometryEquiv.withLpProdCongr 2 φ.symm
        (LinearIsometryEquiv.refl ℝ (Kᗮ : Submodule ℝ E)))
  have he : e₁ p = WithLp.toLp 2
      (φ.symm (K.orthogonalProjectionOnto p), Kᗮ.orthogonalProjectionOnto p) := by
    change LinearIsometryEquiv.withLpProdCongr 2 φ.symm
      (LinearIsometryEquiv.refl ℝ (Kᗮ : Submodule ℝ E))
      (K.orthogonalDecomposition p) = _
    rw [Submodule.orthogonalDecomposition_apply]
    simp [LinearIsometryEquiv.withLpProdCongr]
  change ‖(e₁ p).ofLp.2‖ = _
  rw [he]
  change ‖(Kᗮ.orthogonalProjectionOnto p : Kᗮ)‖ = _
  rw [show ‖(Kᗮ.orthogonalProjectionOnto p : Kᗮ)‖ =
      ‖((Kᗮ.orthogonalProjectionOnto p : Kᗮ) : E)‖ from rfl,
    Submodule.coe_orthogonalProjectionOnto_apply,
    Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton (𝕜 := ℝ) hd p, real_inner_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The coordinate definition agrees with the usual inner-product description of a cylinder. -/
theorem mem_axialCylinder_iff (d : E) (hd : ‖d‖ = 1) (a b r : ℝ) (p : E) :
    p ∈ axialCylinder d hd a b r ↔
      inner ℝ p d ∈ Set.Icc a b ∧
        ‖p - (inner ℝ p d : ℝ) • d‖ ≤ r := by
  rw [axialCylinder, Set.mem_ofPred_eq, axialCoordinates_fst,
    Metric.mem_closedBall, dist_zero_right, axialCoordinates_snd_norm]

/-- The point where the affine line through `o` in direction `d` meets the hyperplane
orthogonal to `d`. -/
def lineFootPoint (o d : E) : E := o - inner ℝ o d • d

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The intersection of a ball and a line neighborhood is a convex test set. -/
theorem convex_closedBall_inter_lineCthickening (o d : E) (R r : ℝ) :
    Convex ℝ (Metric.closedBall 0 R ∩ Metric.cthickening r
      (Set.range (fun t : ℝ => o + t • d))) := by
  have hline : Convex ℝ (Set.range (fun t : ℝ => o + t • d)) := by
    intro x hx
    obtain ⟨s, rfl⟩ := hx
    intro y hy a b ha hb hab
    obtain ⟨t, rfl⟩ := hy
    refine ⟨a * s + b * t, ?_⟩
    change o + (a * s + b * t) • d =
      a • (o + s • d) + b • (o + t • d)
    calc
      o + (a * s + b * t) • d =
          (a + b) • o + (a * s + b * t) • d := by rw [hab]; simp
      _ = a • (o + s • d) + b • (o + t • d) := by module
  exact (convex_closedBall (0 : E) R).inter (hline.cthickening r)

omit [MeasurableSpace E] [BorelSpace E] in
/-- In finite dimensions, the intersection of a closed ball and a line neighborhood is compact. -/
theorem isCompact_closedBall_inter_lineCthickening (o d : E) (R r : ℝ) :
    IsCompact (Metric.closedBall 0 R ∩ Metric.cthickening r
      (Set.range (fun t : ℝ => o + t • d))) := by
  have hclosed : IsClosed (Metric.closedBall (0 : E) R ∩ Metric.cthickening r
      (Set.range (fun t : ℝ => o + t • d))) :=
    Metric.isClosed_closedBall.inter Metric.isClosed_cthickening
  exact (isCompact_closedBall (0 : E) R).of_isClosed_subset hclosed Set.inter_subset_left

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For unit directions, the sine of their unoriented angle is bounded by the smaller of the
distances between the directions and between one direction and the negative of the other.
This elementary angular estimate is a reusable first step in converting tube-overlap estimates
into near-parallel direction bounds. -/
theorem unitDirections_sin_le_min_norm {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Real.sqrt (1 - (inner ℝ u v) ^ 2) ≤ min ‖u - v‖ ‖u + v‖ := by
  refine le_min ?_ ?_
  · exact (Real.sqrt_le_sqrt (by
      rw [norm_sub_sq_real, hu, hv]
      nlinarith [sq_nonneg (1 - inner ℝ u v)])).trans_eq
        (Real.sqrt_sq (norm_nonneg _))
  · exact (Real.sqrt_le_sqrt (by
      rw [norm_add_sq_real, hu, hv]
      nlinarith [sq_nonneg (1 + inner ℝ u v)])).trans_eq
        (Real.sqrt_sq (norm_nonneg _))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Thickening a compact set that already lies in a neighborhood increases the radius by at most
the sum of the two radii. -/
theorem cthickening_subset_cthickening_add_of_compact_subset {s t : Set E}
    (hs : IsCompact s) (hne : s.Nonempty) {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (hsub : s ⊆ Metric.cthickening ε t) :
    Metric.cthickening r s ⊆ Metric.cthickening (r + ε) t := by
  intro x hx
  rw [Metric.mem_cthickening_iff] at hx ⊢
  obtain ⟨y, hy, hnearest⟩ := hs.exists_infEDist_eq_edist hne x
  have hdist : edist x y ≤ ENNReal.ofReal r := by
    rw [← hnearest]
    exact hx
  have hy' : Metric.infEDist y t ≤ ENNReal.ofReal ε :=
    Metric.mem_cthickening_iff.mp (hsub hy)
  calc
    Metric.infEDist x t ≤ edist x y + Metric.infEDist y t :=
      Metric.infEDist_le_edist_add_infEDist
    _ ≤ ENNReal.ofReal r + ENNReal.ofReal ε := add_le_add hdist hy'
    _ = ENNReal.ofReal (r + ε) := (ENNReal.ofReal_add hr hε).symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The `C`-dilate of a segment, taken about its midpoint, remains on the affine line through
its endpoints. Consequently, if a set is contained in the `Cδ`-carrier of that dilated segment,
it is contained in the `Cδ`-neighborhood of the original core line. This is the final geometric
step needed after a tube-overlap theorem supplies containment in a dilated carrier; it does not
prove that overlap containment. -/
theorem carrier_subset_cthickening_line_of_subset_midpointDilate
    (x y : E) (C δ : ℝ) (S : Set E)
    (hS : S ⊆ Metric.cthickening (C * δ)
      (segment ℝ (AffineMap.homothety (midpoint ℝ x y) C x)
        (AffineMap.homothety (midpoint ℝ x y) C y))) :
    S ⊆ Metric.cthickening (C * δ) (Set.range (fun t : ℝ => x + t • (y - x))) := by
  apply hS.trans
  apply Metric.cthickening_subset_of_subset
  rw [← image_segment ℝ (AffineMap.homothety (midpoint ℝ x y) C) x y]
  rw [segment_eq_image_lineMap]
  rintro z ⟨w, hw, rfl⟩
  rcases hw with ⟨t, ht, rfl⟩
  rw [Set.mem_range]
  refine ⟨(1 / 2 : ℝ) + C * (t - 1 / 2), ?_⟩
  simp only [AffineMap.homothety_apply, AffineMap.lineMap_apply_module]
  rw [midpoint_eq_smul_add, invOf_eq_inv, one_div]
  simp only [vsub_eq_sub, vadd_eq_add]
  module

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A carrier around a compact core lies in the truncated ball-line test whenever the core is
within `4δ` of the line and the carrier stays in the ball. -/
theorem cthickening_subset_truncatedBallLineTest_of_core_subset
    {s : Set E} (o d : E) (R δ : ℝ) (hs : IsCompact s) (hne : s.Nonempty)
    (hδ : 0 ≤ δ)
    (hcore : s ⊆ Metric.cthickening (4 * δ)
      (Set.range (fun t : ℝ => o + t • d)))
    (hball : Metric.cthickening δ s ⊆ Metric.closedBall 0 R) :
    Metric.cthickening δ s ⊆
      Metric.closedBall 0 R ∩ Metric.cthickening (5 * δ)
        (Set.range (fun t : ℝ => o + t • d)) := by
  intro x hx
  refine ⟨hball hx, ?_⟩
  have hline := cthickening_subset_cthickening_add_of_compact_subset
    hs hne hδ (show 0 ≤ 4 * δ by positivity) hcore hx
  simpa only [show δ + 4 * δ = 5 * δ by ring] using hline

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem lineFootPoint_orthogonal (d o : E) (hd : ‖d‖ = 1) :
    inner ℝ (lineFootPoint o d) d = 0 := by
  simp only [lineFootPoint, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hd]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The component perpendicular to an affine line has norm at most the distance to any point
on that line. -/
theorem lineFootPoint_perpNorm_le_dist
    (d o x y : E) (hd : ‖d‖ = 1)
    (hy : y ∈ Set.range (fun t : ℝ => o + t • d)) :
    ‖(x - lineFootPoint o d) -
        (inner ℝ (x - lineFootPoint o d) d : ℝ) • d‖ ≤ dist x y := by
  obtain ⟨t, rfl⟩ := hy
  let f := lineFootPoint o d
  let a := inner ℝ (x - f) d
  let z := (x - f) - a • d
  have hfd : inner ℝ f d = 0 := lineFootPoint_orthogonal d o hd
  have hz : inner ℝ z d = 0 := by
    dsimp [z, a]
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hd]
    ring
  have hrepr : x - (o + t • d) = z + (a - t - inner ℝ o d) • d := by
    dsimp [z, a, f, lineFootPoint]
    module
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    z ((a - t - inner ℝ o d) • d) (by
      rw [real_inner_smul_right]
      simp [hz])
  change ‖z‖ ≤ dist x (o + t • d)
  rw [dist_eq_norm, hrepr]
  have hsum0 : 0 ≤ ‖z + (a - t - inner ℝ o d) • d‖ := norm_nonneg _
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hcoeff0 : 0 ≤ ‖(a - t - inner ℝ o d) • d‖ := norm_nonneg _
  nlinarith [hpyth, hsum0, hz0, hcoeff0]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A bounded part of an affine line neighborhood is contained in the corresponding translated
axial cylinder. -/
theorem boundedBall_lineCthickening_subset_translated_axialCylinder
    (d o x : E) (hd : ‖d‖ = 1) {R r : ℝ} (hr : 0 ≤ r)
    (hball : x ∈ Metric.closedBall 0 R)
    (hline : x ∈ Metric.cthickening r
      (Set.range (fun t : ℝ => o + t • d))) :
    x - lineFootPoint o d ∈ axialCylinder d hd (-R) R r := by
  have hnormx : ‖x‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hball
  have hinnerAbs : |inner ℝ x d| ≤ R := by
    calc
      |inner ℝ x d| ≤ ‖x‖ * ‖d‖ := abs_real_inner_le_norm _ _
      _ = ‖x‖ := by rw [hd, mul_one]
      _ ≤ R := hnormx
  have hfoot : inner ℝ (lineFootPoint o d) d = 0 :=
    lineFootPoint_orthogonal d o hd
  have hinner : inner ℝ (x - lineFootPoint o d) d = inner ℝ x d := by
    rw [inner_sub_left, hfoot, sub_zero]
  have haxial : inner ℝ (x - lineFootPoint o d) d ∈ Set.Icc (-R) R := by
    rw [hinner]
    exact abs_le.mp hinnerAbs
  have hperp : ‖(x - lineFootPoint o d) -
      (inner ℝ (x - lineFootPoint o d) d : ℝ) • d‖ ≤ r := by
    have hdistE : ENNReal.ofReal ‖(x - lineFootPoint o d) -
        (inner ℝ (x - lineFootPoint o d) d : ℝ) • d‖ ≤
          Metric.infEDist x (Set.range (fun t : ℝ => o + t • d)) := by
      apply Metric.le_infEDist.mpr
      intro y hy
      rw [edist_dist, dist_eq_norm]
      apply ENNReal.ofReal_le_ofReal
      simpa only [dist_eq_norm] using lineFootPoint_perpNorm_le_dist d o x y hd hy
    have hdistR := hdistE.trans hline
    exact (ENNReal.ofReal_le_ofReal_iff hr).mp hdistR
  exact (mem_axialCylinder_iff d hd (-R) R r (x - lineFootPoint o d)).2
    ⟨haxial, hperp⟩

/-- The intersection of a radius-`R` ball and a radius-`r` neighborhood of a line has volume at
most that of a translated cylinder of axial length `2R` and cross-sectional radius `r`. -/
theorem volume_closedBall_inter_lineCthickening_le
    (hdim : Module.finrank ℝ E = 3) (d o : E) (hd : ‖d‖ = 1)
    {R r : ℝ} (_hR : 0 ≤ R) (hr : 0 ≤ r) :
    volume (Metric.closedBall 0 R ∩ Metric.cthickening r
      (Set.range (fun t : ℝ => o + t • d))) ≤
        ENNReal.ofReal (2 * R) *
          (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) := by
  let f := lineFootPoint o d
  have hsubset : Metric.closedBall 0 R ∩ Metric.cthickening r
      (Set.range (fun t : ℝ => o + t • d)) ⊆
        (fun z : E => f + z) '' axialCylinder d hd (-R) R r := by
    intro x hx
    refine ⟨x - f, boundedBall_lineCthickening_subset_translated_axialCylinder
      d o x hd hr hx.1 hx.2, ?_⟩
    dsimp [f]
    abel
  have htrans : volume ((fun z : E => f + z) '' axialCylinder d hd (-R) R r) =
      volume (axialCylinder d hd (-R) R r) := by
    have hf : (fun z : E => f + z) = fun z => z + f := by
      funext z
      exact add_comm f z
    rw [hf, Set.image_add_right, measure_preimage_add_right]
  calc
    volume (Metric.closedBall 0 R ∩ Metric.cthickening r
        (Set.range (fun t : ℝ => o + t • d))) ≤
      volume ((fun z : E => f + z) '' axialCylinder d hd (-R) R r) :=
        measure_mono hsubset
    _ = ENNReal.ofReal (2 * R) *
        (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) := by
      rw [htrans, volume_axialCylinder_three hdim d hd (-R) R r]
      congr 1
      ring

/-- A unit segment in direction `d`, parametrized from `0` to `d`. -/
def unitAxisSegment (d : E) : Set E := segment ℝ (0 : E) d

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The capped axial cylinder of radius `r` lies in the closed `r`-neighborhood of its unit
axis segment. -/
theorem axialCylinder_subset_unitAxisSegment_cthickening
    (d : E) (hd : ‖d‖ = 1) {r : ℝ} (p : E)
    (hp : p ∈ axialCylinder d hd 0 1 r) :
    p ∈ Metric.cthickening r (unitAxisSegment d) := by
  rw [mem_axialCylinder_iff] at hp
  rcases hp with ⟨ht, hperp⟩
  apply Metric.mem_cthickening_of_dist_le p ((inner ℝ p d) • d) r
    (unitAxisSegment d) ?_ ?_
  · rw [unitAxisSegment, segment_eq_image']
    simpa using Set.mem_image_of_mem
      (fun θ : ℝ => (0 : E) + θ • (d - (0 : E))) ht
  · rw [dist_eq_norm]
    simpa using hperp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The closed neighborhood of a unit segment lies in the cylinder whose axial interval is
enlarged by the neighborhood radius. -/
theorem unitAxisSegment_cthickening_subset_axialCylinder
    (d : E) (hd : ‖d‖ = 1) {r : ℝ} (hr : 0 ≤ r) (p : E)
    (hp : p ∈ Metric.cthickening r (unitAxisSegment d)) :
    p ∈ axialCylinder d hd (-r) (1 + r) r := by
  have hs : IsCompact (unitAxisSegment d) := by
    rw [unitAxisSegment, segment_eq_image']
    refine isCompact_Icc.image ?_
    fun_prop
  have hne : (unitAxisSegment d).Nonempty := by
    exact ⟨0, by rw [unitAxisSegment]; exact left_mem_segment ℝ 0 d⟩
  obtain ⟨y, hy, hnearest⟩ := hs.exists_infEDist_eq_edist hne p
  have hdistE : edist p y ≤ ENNReal.ofReal r := by
    rw [← hnearest]
    exact hp
  have hdist : dist p y ≤ r :=
    (ENNReal.ofReal_le_ofReal_iff hr).mp (by simpa [edist_dist] using hdistE)
  rw [unitAxisSegment, segment_eq_image'] at hy
  change ∃ s ∈ Set.Icc (0 : ℝ) 1,
    (0 : E) + s • (d - (0 : E)) = y at hy
  obtain ⟨s, hs01, hsy⟩ := hy
  have hy_eq : y = s • d := by simpa using hsy.symm
  have hs_inner : inner ℝ y d = s := by
    rw [hy_eq, real_inner_smul_left, real_inner_self_eq_norm_sq, hd]
    ring
  have hinnerErr : |inner ℝ (p - y) d| ≤ r := by
    calc
      |inner ℝ (p - y) d| ≤ ‖p - y‖ * ‖d‖ := abs_real_inner_le_norm _ _
      _ = dist p y := by rw [hd, mul_one, dist_eq_norm]
      _ ≤ r := hdist
  have hdecomp : inner ℝ p d = inner ℝ (p - y) d + s := by
    rw [← sub_add_cancel p y, inner_add_left, hs_inner]
    simp
  have haxial : inner ℝ p d ∈ Set.Icc (-r) (1 + r) := by
    rw [hdecomp]
    have herr := abs_le.mp hinnerErr
    change -r ≤ inner ℝ (p - y) d + s ∧ inner ℝ (p - y) d + s ≤ 1 + r
    constructor <;> linarith [hs01.1, hs01.2]
  have hperp : ‖p - (inner ℝ p d : ℝ) • d‖ ≤ r := by
    let K : Submodule ℝ E := ℝ ∙ d
    have hyK : y ∈ K := by
      rw [hy_eq]
      exact K.smul_mem s (Submodule.mem_span_singleton_self d)
    have hyKK : y ∈ Kᗮᗮ := K.le_orthogonal_orthogonal hyK
    have hyproj : Kᗮ.starProjection y = 0 := by
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := Kᗮ)
      · simp
      · intro z hz
        simpa using (Submodule.mem_orthogonal' (K := Kᗮ) y).mp hyKK z hz
    have hproj : Kᗮ.starProjection p = Kᗮ.starProjection (p - y) := by
      calc
        Kᗮ.starProjection p = Kᗮ.starProjection ((p - y) + y) := by congr 1; abel
        _ = Kᗮ.starProjection (p - y) + Kᗮ.starProjection y := map_add _ _ _
        _ = Kᗮ.starProjection (p - y) := by rw [hyproj, add_zero]
    have hresid : p - (inner ℝ p d : ℝ) • d = Kᗮ.starProjection p := by
      rw [Submodule.starProjection_orthogonal_val (K := K) p,
        Submodule.starProjection_unit_singleton (𝕜 := ℝ) hd p, real_inner_comm]
    rw [hresid, hproj]
    calc
      ‖Kᗮ.starProjection (p - y)‖ ≤ ‖p - y‖ := Kᗮ.norm_starProjection_apply_le _
      _ = dist p y := by rw [dist_eq_norm]
      _ ≤ r := hdist
  exact (mem_axialCylinder_iff d hd (-r) (1 + r) r p).2 ⟨haxial, hperp⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A point in the closed `r`-neighborhood of a centered unit segment can be written as an
axis point with parameter in `[-1/2,1/2]`, plus a residual vector of norm at most `r`.
This is the local carrier-to-axis adapter used by tube-intersection geometry. -/
theorem exists_axisParameter_of_mem_unitSegmentCthickening
    (m d p : E) (_hd : ‖d‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (hp : p ∈ Metric.cthickening r
      (segment ℝ (m - (1 / 2 : ℝ) • d) (m + (1 / 2 : ℝ) • d))) :
    ∃ s : ℝ, s ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ∧
      ‖p - m - s • d‖ ≤ r := by
  have hcore_compact : IsCompact
      (segment ℝ (m - (1 / 2 : ℝ) • d) (m + (1 / 2 : ℝ) • d)) := by
    rw [segment_eq_image']
    refine isCompact_Icc.image ?_
    fun_prop
  have hcore_nonempty :
      (segment ℝ (m - (1 / 2 : ℝ) • d) (m + (1 / 2 : ℝ) • d)).Nonempty :=
    ⟨m - (1 / 2 : ℝ) • d, left_mem_segment ℝ _ _⟩
  obtain ⟨q, hqcore, hnearest⟩ := hcore_compact.exists_infEDist_eq_edist hcore_nonempty p
  have hdistE : edist p q ≤ ENNReal.ofReal r := by
    rw [← hnearest]
    exact Metric.mem_cthickening_iff.mp hp
  have hdist : dist p q ≤ r := by
    rw [← ENNReal.ofReal_le_ofReal_iff hr]
    simpa [edist_dist] using hdistE
  rw [segment_eq_image'] at hqcore
  obtain ⟨t, ht, hq⟩ := hqcore
  have ht' : t - 1 / 2 ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    constructor <;> rcases ht with ⟨ht0, ht1⟩ <;> linarith
  refine ⟨t - 1 / 2, ht', ?_⟩
  have hq' : q = m + (t - 1 / 2) • d := by
    calc
      q = (m - (1 / 2 : ℝ) • d) + t •
          ((m + (1 / 2 : ℝ) • d) - (m - (1 / 2 : ℝ) • d)) := hq.symm
      _ = m + (t - 1 / 2) • d := by module
  rw [dist_eq_norm] at hdist
  calc
    ‖p - m - (t - 1 / 2) • d‖ = ‖p - (m + (t - 1 / 2) • d)‖ := by congr 1 <;> module
    _ ≤ r := by rw [← hq']; exact hdist

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Closed neighborhoods commute with translations of compact sets. -/
theorem cthickening_translate_image {S : Set E} (hS : IsCompact S)
    (x : E) {r : ℝ} (hr : 0 ≤ r) :
    Metric.cthickening r ((fun z : E => x + z) '' S) =
      (fun z : E => x + z) '' Metric.cthickening r S := by
  have hSx : IsCompact ((fun z : E => x + z) '' S) := hS.image (by fun_prop)
  ext p
  constructor
  · intro hp
    rw [hSx.cthickening_eq_biUnion_closedBall hr] at hp
    obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.mp hp
    change ∃ y ∈ S, x + y = z at hz
    obtain ⟨y, hy, rfl⟩ := hz
    change ∃ q ∈ Metric.cthickening r S, x + q = p
    refine ⟨p - x, ?_, by abel⟩
    apply Metric.mem_cthickening_of_dist_le (p - x) y r S hy
    rw [Metric.mem_closedBall] at hpz
    simpa [dist_eq_norm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hpz
  · intro hp
    change ∃ q ∈ Metric.cthickening r S, x + q = p at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [hS.cthickening_eq_biUnion_closedBall hr] at hq
    obtain ⟨y, hy, hqy⟩ := Set.mem_iUnion₂.mp hq
    apply Metric.mem_cthickening_of_dist_le (x + q) (x + y) r
      ((fun z : E => x + z) '' S) (Set.mem_image_of_mem _ hy)
    rw [Metric.mem_closedBall] at hqy
    simpa [dist_eq_norm] using hqy

/-- Lebesgue measure is unchanged by translating the closed neighborhood of a compact set. -/
theorem volume_cthickening_translate_image {S : Set E} (hS : IsCompact S)
    (x : E) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.cthickening r ((fun z : E => x + z) '' S)) =
      volume (Metric.cthickening r S) := by
  rw [cthickening_translate_image hS x hr]
  have himage : (fun z : E => x + z) = fun z => z + x := by
    funext z
    exact add_comm x z
  rw [himage, Set.image_add_right, measure_preimage_add_right]

/-- A unit segment's radius-`r` neighborhood is bounded below by its inscribed unit-length
axial cylinder, and above by the cylinder with axial length `1 + 2r`. -/
theorem volume_unitAxisSegment_cthickening_bounds
    (hdim : Module.finrank ℝ E = 3) (d : E) (hd : ‖d‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi ≤
        volume (Metric.cthickening r (unitAxisSegment d)) ∧
      volume (Metric.cthickening r (unitAxisSegment d)) ≤
        ENNReal.ofReal (1 + 2 * r) *
          (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) := by
  constructor
  · have h := measure_mono (μ := volume) (fun p hp =>
      axialCylinder_subset_unitAxisSegment_cthickening d hd (r := r) p hp)
    rw [volume_axialCylinder_three hdim d hd 0 1 r] at h
    simpa using h
  · have h := measure_mono (μ := volume) (fun p hp =>
      unitAxisSegment_cthickening_subset_axialCylinder d hd hr (r := r) p hp)
    rw [volume_axialCylinder_three hdim d hd (-r) (1 + r) r] at h
    convert h using 1
    ring_nf

/-- Halving the radius of a unit-segment neighborhood gives a uniform carrier-volume bound:
for `r ≤ 2`, the parent neighborhood has at most three times the original volume. -/
theorem volume_halfRadius_unitAxisSegment_cthickening_le_three_mul
    (hdim : Module.finrank ℝ E = 3) (d : E) (hd : ‖d‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    volume (Metric.cthickening (r / 2) (unitAxisSegment d)) ≤
      3 * volume (Metric.cthickening r (unitAxisSegment d)) := by
  have hparent := volume_unitAxisSegment_cthickening_bounds hdim d hd (by positivity : 0 ≤ r / 2)
  have horig := volume_unitAxisSegment_cthickening_bounds hdim d hd hr0
  have hball : volume (Metric.closedBall (0 : ((ℝ ∙ d)ᗮ : Submodule ℝ E)) (r / 2)) ≤
      volume (Metric.closedBall (0 : ((ℝ ∙ d)ᗮ : Submodule ℝ E)) r) := by
    apply measure_mono (μ := volume)
    intro x hx
    rw [Metric.mem_closedBall] at hx ⊢
    linarith
  have hdisc (t : ℝ) : volume (Metric.closedBall
      (0 : ((ℝ ∙ d)ᗮ : Submodule ℝ E)) t) =
      ENNReal.ofReal t ^ 2 * ENNReal.ofReal Real.pi := by
    have h := volume_axialCylinder_three hdim d hd 0 1 t
    rw [volume_axialCylinder d hd 0 1 t] at h
    simpa using h
  have hfactor : ENNReal.ofReal (1 + r) ≤ 3 := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : 1 + r ≤ 3)
  calc
    volume (Metric.cthickening (r / 2) (unitAxisSegment d)) ≤
        ENNReal.ofReal (1 + r) * volume (Metric.closedBall
          (0 : ((ℝ ∙ d)ᗮ : Submodule ℝ E)) (r / 2)) := by
          simpa only [show (1 + 2 * (r / 2) : ℝ) = 1 + r by ring,
            hdisc (r / 2)] using hparent.2
    _ ≤ ENNReal.ofReal (1 + r) * volume (Metric.closedBall
        (0 : ((ℝ ∙ d)ᗮ : Submodule ℝ E)) r) :=
      mul_le_mul_of_nonneg_left hball (by positivity)
    _ ≤ 3 * (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) := by
      rw [← hdisc r]
      exact mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ ≤ 3 * volume (Metric.cthickening r (unitAxisSegment d)) :=
      mul_le_mul_of_nonneg_left horig.1 (by positivity)

/-- The exact half-radius carrier ratio for a unit segment in dimension three.
For `r ≤ 2`, the half-radius disk contributes a factor `1/4` and the parent cylinder's
axial length contributes at most `1 + r ≤ 3`. -/
theorem volume_halfRadius_unitAxisSegment_cthickening_le_three_quarters_mul
    (hdim : Module.finrank ℝ E = 3) (d : E) (hd : ‖d‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    volume (Metric.cthickening (r / 2) (unitAxisSegment d)) ≤
      ENNReal.ofReal (3 / 4) * volume (Metric.cthickening r (unitAxisSegment d)) := by
  have hparent := volume_unitAxisSegment_cthickening_bounds hdim d hd (by positivity : 0 ≤ r / 2)
  have horig := volume_unitAxisSegment_cthickening_bounds hdim d hd hr0
  have hdisc (t : ℝ) : volume (Metric.closedBall
      (0 : ((ℝ ∙ d)ᗮ : Submodule ℝ E)) t) =
      ENNReal.ofReal t ^ 2 * ENNReal.ofReal Real.pi := by
    have h := volume_axialCylinder_three hdim d hd 0 1 t
    rw [volume_axialCylinder d hd 0 1 t] at h
    simpa using h
  have hcoeff_real : (1 + r) * (r / 2) ^ 2 ≤ (3 / 4) * r ^ 2 := by
    nlinarith [hr0, hr2]
  have hcoeff : ENNReal.ofReal (1 + r) * ENNReal.ofReal (r / 2) ^ 2 ≤
      ENNReal.ofReal (3 / 4) * ENNReal.ofReal r ^ 2 := by
    have hleft : ENNReal.ofReal (1 + r) * ENNReal.ofReal (r / 2) ^ 2 =
        ENNReal.ofReal ((1 + r) * (r / 2) ^ 2) := by
      rw [← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 + r)]
      positivity
    have hright : ENNReal.ofReal (3 / 4) * ENNReal.ofReal r ^ 2 =
        ENNReal.ofReal ((3 / 4) * r ^ 2) := by
      rw [← ENNReal.ofReal_pow]
      swap
      · positivity
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 4)]
    rw [hleft, hright]
    exact ENNReal.ofReal_le_ofReal hcoeff_real
  have hscaled : ENNReal.ofReal (1 + r) *
      (ENNReal.ofReal (r / 2) ^ 2 * ENNReal.ofReal Real.pi) ≤
      ENNReal.ofReal (3 / 4) *
        (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) := by
    calc
      ENNReal.ofReal (1 + r) *
          (ENNReal.ofReal (r / 2) ^ 2 * ENNReal.ofReal Real.pi) =
          (ENNReal.ofReal (1 + r) * ENNReal.ofReal (r / 2) ^ 2) *
            ENNReal.ofReal Real.pi := by rw [← mul_assoc]
      _ ≤ (ENNReal.ofReal (3 / 4) * ENNReal.ofReal r ^ 2) * ENNReal.ofReal Real.pi :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = ENNReal.ofReal (3 / 4) *
          (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) := by ac_rfl
  calc
    volume (Metric.cthickening (r / 2) (unitAxisSegment d)) ≤
        ENNReal.ofReal (1 + r) *
          (ENNReal.ofReal (r / 2) ^ 2 * ENNReal.ofReal Real.pi) := by
          simpa only [show 1 + 2 * (r / 2) = 1 + r by ring, hdisc (r / 2)] using hparent.2
    _ ≤ ENNReal.ofReal (3 / 4) *
          (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) := hscaled
    _ ≤ ENNReal.ofReal (3 / 4) * volume (Metric.cthickening r (unitAxisSegment d)) :=
      mul_le_mul_of_nonneg_left horig.1 (by positivity)

/-- Translating a unit segment does not change the volume of its closed neighborhood. -/
theorem volume_cthickening_segment_translate (x d : E) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.cthickening r (segment ℝ x (x + d))) =
      volume (Metric.cthickening r (unitAxisSegment d)) := by
  have hs : IsCompact (unitAxisSegment d) := by
    rw [unitAxisSegment, segment_eq_image']
    refine isCompact_Icc.image ?_
    fun_prop
  have hsegment : segment ℝ x (x + d) = (fun z : E => x + z) '' unitAxisSegment d := by
    rw [unitAxisSegment]
    simpa using (segment_translate_image ℝ x 0 d).symm
  rw [hsegment]
  exact volume_cthickening_translate_image hs x hr

/-- The truncated radius-`5δ` neighborhood of a line has volume at most `50R` times the
radius-`δ` carrier volume of a unit segment on that line. -/
theorem volume_closedBall_inter_fiveCthickening_le_mul_unitSegment
    (hdim : Module.finrank ℝ E = 3) (d o : E) (hd : ‖d‖ = 1)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) :
    volume (Metric.closedBall 0 R ∩ Metric.cthickening (5 * δ)
      (Set.range (fun t : ℝ => o + t • d))) ≤
        ENNReal.ofReal (50 * R) *
          volume (Metric.cthickening δ (segment ℝ o (o + d))) := by
  have hcut := volume_closedBall_inter_lineCthickening_le
    hdim d o hd hR (show 0 ≤ 5 * δ by positivity)
  have hunit := volume_unitAxisSegment_cthickening_bounds hdim d hd hδ
  have htranslate := volume_cthickening_segment_translate o d hδ
  have harea5 : ENNReal.ofReal (5 * δ) ^ 2 * ENNReal.ofReal Real.pi =
      ENNReal.ofReal ((5 * δ) ^ 2 * Real.pi) := by
    rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 5 * δ),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (5 * δ) ^ 2)]
  have harea1 : ENNReal.ofReal δ ^ 2 * ENNReal.ofReal Real.pi =
      ENNReal.ofReal (δ ^ 2 * Real.pi) := by
    rw [← ENNReal.ofReal_pow hδ,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ δ ^ 2)]
  have hscale : ENNReal.ofReal (2 * R) *
      (ENNReal.ofReal (5 * δ) ^ 2 * ENNReal.ofReal Real.pi) =
      ENNReal.ofReal (50 * R) *
        (ENNReal.ofReal δ ^ 2 * ENNReal.ofReal Real.pi) := by
    rw [harea5, harea1,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * R),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 50 * R)]
    congr 1
    ring
  calc
    volume (Metric.closedBall 0 R ∩ Metric.cthickening (5 * δ)
        (Set.range (fun t : ℝ => o + t • d))) ≤
      ENNReal.ofReal (2 * R) *
        (ENNReal.ofReal (5 * δ) ^ 2 * ENNReal.ofReal Real.pi) := hcut
    _ = ENNReal.ofReal (50 * R) *
        (ENNReal.ofReal δ ^ 2 * ENNReal.ofReal Real.pi) := hscale
    _ ≤ ENNReal.ofReal (50 * R) *
        volume (Metric.cthickening δ (segment ℝ o (o + d))) := by
      rw [htranslate]
      exact mul_le_mul_of_nonneg_left hunit.1 (by positivity)

/-- The truncated radius-`κδ` neighborhood of a line has volume at most
`2Rκ²` times the radius-`δ` carrier volume of a unit segment. This variable-radius form
supports line tests at constants other than five, including the overlap constant used by the
pairwise essential-distinctness bridge. -/
theorem volume_closedBall_inter_scaledCthickening_le_mul_unitSegment
    (hdim : Module.finrank ℝ E = 3) (d o : E) (hd : ‖d‖ = 1)
    {R δ κ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) :
    volume (Metric.closedBall 0 R ∩ Metric.cthickening (κ * δ)
      (Set.range (fun t : ℝ => o + t • d))) ≤
        ENNReal.ofReal (2 * R * κ ^ 2) *
          volume (Metric.cthickening δ (segment ℝ o (o + d))) := by
  have hcut := volume_closedBall_inter_lineCthickening_le
    hdim d o hd hR (show 0 ≤ κ * δ by positivity)
  have hunit := volume_unitAxisSegment_cthickening_bounds hdim d hd hδ
  have htranslate := volume_cthickening_segment_translate o d hδ
  have hscaledArea : ENNReal.ofReal (κ * δ) ^ 2 * ENNReal.ofReal Real.pi =
      ENNReal.ofReal ((κ * δ) ^ 2 * Real.pi) := by
    rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ κ * δ),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (κ * δ) ^ 2)]
  have hunitArea : ENNReal.ofReal δ ^ 2 * ENNReal.ofReal Real.pi =
      ENNReal.ofReal (δ ^ 2 * Real.pi) := by
    rw [← ENNReal.ofReal_pow hδ,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ δ ^ 2)]
  have hscale : ENNReal.ofReal (2 * R) *
      (ENNReal.ofReal (κ * δ) ^ 2 * ENNReal.ofReal Real.pi) =
      ENNReal.ofReal (2 * R * κ ^ 2) *
        (ENNReal.ofReal δ ^ 2 * ENNReal.ofReal Real.pi) := by
    rw [hscaledArea, hunitArea,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * R),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * R * κ ^ 2)]
    congr 1
    ring
  calc
    volume (Metric.closedBall 0 R ∩ Metric.cthickening (κ * δ)
        (Set.range (fun t : ℝ => o + t • d))) ≤
      ENNReal.ofReal (2 * R) *
        (ENNReal.ofReal (κ * δ) ^ 2 * ENNReal.ofReal Real.pi) := hcut
    _ = ENNReal.ofReal (2 * R * κ ^ 2) *
        (ENNReal.ofReal δ ^ 2 * ENNReal.ofReal Real.pi) := hscale
    _ ≤ ENNReal.ofReal (2 * R * κ ^ 2) *
        volume (Metric.cthickening δ (segment ℝ o (o + d))) := by
      rw [htranslate]
      exact mul_le_mul_of_nonneg_left hunit.1 (by positivity)

/-- Parent carrier-volume estimate for any two unit-distance endpoints in a three-dimensional
Euclidean space. It applies to tube carriers represented as closed neighborhoods of their cores. -/
theorem volume_halfRadius_segment_cthickening_le_three_mul
    (hdim : Module.finrank ℝ E = 3) (x y : E) (hxy : ‖y - x‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    volume (Metric.cthickening (r / 2) (segment ℝ x y)) ≤
      3 * volume (Metric.cthickening r (segment ℝ x y)) := by
  let d : E := y - x
  have hd : ‖d‖ = 1 := hxy
  have hseg : segment ℝ x y = segment ℝ x (x + d) := by
    congr 1
    simp [d]
  rw [hseg,
    volume_cthickening_segment_translate x d (by positivity : 0 ≤ r / 2),
    volume_cthickening_segment_translate x d hr0]
  exact volume_halfRadius_unitAxisSegment_cthickening_le_three_mul hdim d hd hr0 hr2

/-- The exact half-radius carrier ratio for any unit-distance segment in dimension three. -/
theorem volume_halfRadius_segment_cthickening_le_three_quarters_mul
    (hdim : Module.finrank ℝ E = 3) (x y : E) (hxy : ‖y - x‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    volume (Metric.cthickening (r / 2) (segment ℝ x y)) ≤
      ENNReal.ofReal (3 / 4) * volume (Metric.cthickening r (segment ℝ x y)) := by
  let d : E := y - x
  have hd : ‖d‖ = 1 := hxy
  have hseg : segment ℝ x y = segment ℝ x (x + d) := by
    congr 1
    simp [d]
  rw [hseg,
    volume_cthickening_segment_translate x d (by positivity : 0 ≤ r / 2),
    volume_cthickening_segment_translate x d hr0]
  exact volume_halfRadius_unitAxisSegment_cthickening_le_three_quarters_mul hdim d hd hr0 hr2

/-- The `3/4` half-radius carrier ratio is independent of the core line: the parent and original
segments may have different endpoints, as long as each has length one. -/
theorem volume_halfRadius_segment_cthickening_le_three_quarters_mul_of_unit_lengths
    (hdim : Module.finrank ℝ E = 3) (px py ox oy : E)
    (hp : ‖py - px‖ = 1) (ho : ‖oy - ox‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    volume (Metric.cthickening (r / 2) (segment ℝ px py)) ≤
      ENNReal.ofReal (3 / 4) * volume (Metric.cthickening r (segment ℝ ox oy)) := by
  let dp : E := py - px
  let do_ : E := oy - ox
  have hdp : ‖dp‖ = 1 := hp
  have hdo : ‖do_‖ = 1 := ho
  have hparent := volume_unitAxisSegment_cthickening_bounds hdim dp hdp
    (by positivity : 0 ≤ r / 2)
  have horig := volume_unitAxisSegment_cthickening_bounds hdim do_ hdo hr0
  have hdisc : ∀ t : ℝ, volume
      (Metric.closedBall (0 : ((ℝ ∙ dp)ᗮ : Submodule ℝ E)) t) =
        ENNReal.ofReal t ^ 2 * ENNReal.ofReal Real.pi := by
    intro t
    have h := volume_axialCylinder_three hdim dp hdp 0 1 t
    rw [volume_axialCylinder dp hdp 0 1 t] at h
    simpa using h
  have hcoeff_real : (1 + r) * (r / 2) ^ 2 ≤ (3 / 4) * r ^ 2 := by
    nlinarith [hr0, hr2]
  have hcoeff : ENNReal.ofReal (1 + r) * ENNReal.ofReal (r / 2) ^ 2 ≤
      ENNReal.ofReal (3 / 4) * ENNReal.ofReal r ^ 2 := by
    have hleft : ENNReal.ofReal (1 + r) * ENNReal.ofReal (r / 2) ^ 2 =
        ENNReal.ofReal ((1 + r) * (r / 2) ^ 2) := by
      rw [← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 + r)]
      positivity
    have hright : ENNReal.ofReal (3 / 4) * ENNReal.ofReal r ^ 2 =
        ENNReal.ofReal ((3 / 4) * r ^ 2) := by
      rw [← ENNReal.ofReal_pow]
      swap
      · positivity
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 4)]
    rw [hleft, hright]
    exact ENNReal.ofReal_le_ofReal hcoeff_real
  have hscaled : ENNReal.ofReal (1 + r) *
      (ENNReal.ofReal (r / 2) ^ 2 * ENNReal.ofReal Real.pi) ≤
      ENNReal.ofReal (3 / 4) *
        (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) := by
    calc
      ENNReal.ofReal (1 + r) *
          (ENNReal.ofReal (r / 2) ^ 2 * ENNReal.ofReal Real.pi) =
          (ENNReal.ofReal (1 + r) * ENNReal.ofReal (r / 2) ^ 2) *
            ENNReal.ofReal Real.pi := by rw [← mul_assoc]
      _ ≤ (ENNReal.ofReal (3 / 4) * ENNReal.ofReal r ^ 2) * ENNReal.ofReal Real.pi :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = ENNReal.ofReal (3 / 4) *
          (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) := by ac_rfl
  have hparentSeg : segment ℝ px py = segment ℝ px (px + dp) := by
    congr 1
    simp [dp]
  have horigSeg : segment ℝ ox oy = segment ℝ ox (ox + do_) := by
    congr 1
    simp [do_]
  calc
    volume (Metric.cthickening (r / 2) (segment ℝ px py)) =
        volume (Metric.cthickening (r / 2) (unitAxisSegment dp)) := by
          rw [hparentSeg, volume_cthickening_segment_translate px dp (by positivity)]
    _ ≤ ENNReal.ofReal (1 + r) *
          (ENNReal.ofReal (r / 2) ^ 2 * ENNReal.ofReal Real.pi) := by
          simpa only [show 1 + 2 * (r / 2) = 1 + r by ring,
            hdisc (r / 2)] using hparent.2
    _ ≤ ENNReal.ofReal (3 / 4) *
          (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) := hscaled
    _ ≤ ENNReal.ofReal (3 / 4) *
          volume (Metric.cthickening r (unitAxisSegment do_)) :=
        mul_le_mul_of_nonneg_left horig.1 (by positivity)
    _ = ENNReal.ofReal (3 / 4) *
          volume (Metric.cthickening r (segment ℝ ox oy)) := by
        rw [← volume_cthickening_segment_translate ox do_ hr0, ← horigSeg]

end Kakeya4.Construction
