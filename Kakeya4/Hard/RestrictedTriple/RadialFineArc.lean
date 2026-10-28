import Kakeya4.Hard.RestrictedTriple.AngularFrostmanInput

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem unit_cap_distance_le_cross (x y : Plane) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : 1/2 ≤ inner ℝ x y) : dist x y ≤ 3*|cross2 x y| := by
  have hyy : 1/2 ≤ inner ℝ y y := by rw [real_inner_self_eq_norm_sq,hy]; norm_num
  have hh := unit_cap_chart_distance x y y hx hy hy hxy hyy
  rw [inner_sub_left,inner_quarterTurn_eq_cross2,inner_quarterTurn_eq_cross2] at hh
  have hzero : cross2 y y = 0 := by unfold cross2; ring
  simpa only [hzero,neg_zero,sub_zero,abs_neg] using hh

theorem normalized_distance_le_twelve_cross (v u : Plane)
    (hv : 1/2 ≤ ‖v‖) (hu : 1/2 ≤ ‖u‖)
    (hcap : 1/2 ≤ inner ℝ (NormedSpace.normalize v) (NormedSpace.normalize u)) :
    dist (NormedSpace.normalize v) (NormedSpace.normalize u) ≤ 12*|cross2 v u| := by
  have hvne : v ≠ 0 := by intro heq; rw [heq,norm_zero] at hv; norm_num at hv
  have hune : u ≠ 0 := by intro heq; rw [heq,norm_zero] at hu; norm_num at hu
  have hchart := unit_cap_distance_le_cross _ _ (NormedSpace.norm_normalize hvne)
    (NormedSpace.norm_normalize hune) hcap
  have hid : ‖v‖*‖u‖*|cross2 (NormedSpace.normalize v) (NormedSpace.normalize u)| = |cross2 v u| := by
    have hh := cross2_smul_smul ‖v‖ ‖u‖ (NormedSpace.normalize v) (NormedSpace.normalize u)
    rw [NormedSpace.norm_smul_normalize,NormedSpace.norm_smul_normalize] at hh
    have ha := congrArg abs hh
    simpa only [abs_mul,abs_of_nonneg (norm_nonneg v),abs_of_nonneg (norm_nonneg u)] using ha.symm
  have hprod : 1/4 ≤ ‖v‖*‖u‖ := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hchart (mul_nonneg (norm_nonneg v) (norm_nonneg u))
  have hm' : ‖v‖*‖u‖*dist (NormedSpace.normalize v) (NormedSpace.normalize u) ≤ 3*|cross2 v u| := by
    calc
      _ ≤ (‖v‖*‖u‖)*(3*|cross2 (NormedSpace.normalize v) (NormedSpace.normalize u)|) := hm
      _ = 3*(‖v‖*‖u‖*|cross2 (NormedSpace.normalize v) (NormedSpace.normalize u)|) := by ring
      _ = _ := by rw [hid]
  have hlo := mul_le_mul_of_nonneg_right hprod
    (dist_nonneg : 0 ≤ dist (NormedSpace.normalize v) (NormedSpace.normalize u))
  linarith

theorem strip_vantage_determinant_upper {w : ℝ} (hw : 0 ≤ w) (L : AffineLine)
    (b x y : Plane) (hx : x ∈ lineNeighborhood w L) (hy : y ∈ lineNeighborhood w L)
    (hxnorm : ‖x‖ ≤ 1) (hynorm : ‖y‖ ≤ 1) (hyb : dist y b ≤ 2) :
    |cross2 (x-b) (y-b)| ≤ 2*|cross2 (b-L.anchor) L.direction|+6*w := by
  have hystrip := hy
  rw [← determinantStrip_eq_lineNeighborhood hw] at hystrip
  change |cross2 (y-L.anchor) L.direction| ≤ w at hystrip
  have hheight : |cross2 (y-b) L.direction| ≤ w+|cross2 (b-L.anchor) L.direction| := by
    have hid : cross2 (y-b) L.direction = cross2 (y-L.anchor) L.direction-cross2 (b-L.anchor) L.direction := by
      simp only [cross2,PiLp.sub_apply]
      ring
    rw [hid,sub_eq_add_neg]
    exact (abs_add_le _ _).trans (by rw [abs_neg]; linarith)
  let a := (1/2:ℝ) • quarterTurn (y-b)
  have ha : ‖a‖ ≤ 1 := by
    dsimp [a]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2),quarterTurn_norm,← dist_eq_norm]
    linarith
  have hh := strip_projection_upper hw L a x y ha hxnorm hynorm hx hy
  have hleft : inner ℝ a (x-y) = -(1/2)*cross2 (x-b) (y-b) := by
    dsimp [a]
    rw [real_inner_smul_left,real_inner_comm,inner_quarterTurn_eq_cross2]
    simp only [cross2,PiLp.sub_apply]
    ring
  have hright : inner ℝ a L.direction = (1/2)*cross2 (y-b) L.direction := by
    dsimp [a]
    rw [real_inner_smul_left,real_inner_comm,inner_quarterTurn_eq_cross2]
    unfold cross2
    ring
  rw [hleft,hright,abs_mul,abs_mul] at hh
  norm_num at hh
  linarith

/-- Fine, height-dependent cap for the actual same-viewpoint direction set. -/
theorem occupied_radial_fine_arc {w : ℝ} (hw : 0 ≤ w) (L : AffineLine)
    (Q : Finset Triple) (q : Triple) (hq : q ∈ Q) (hgeom : standardTripleGeometry Q)
    (hstrip : ∀ x ∈ activeTripleClasses Q 1, x ∈ lineNeighborhood w L)
    (hwidth : w ≤ |cross2 (q.2.2-L.anchor) L.direction|) :
    ∀ x ∈ activeTripleClasses Q 1,
      dist (radialProjection q.2.2 x) (radialProjection q.2.2 q.2.1) ≤
        96*|cross2 (q.2.2-L.anchor) L.direction| := by
  intro x hx
  have hcap := (occupied_radial_cap Q q hq hgeom).2 x hx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  have hvdist : 1/2 ≤ ‖v.2.1-q.2.2‖ := by simpa only [dist_eq_norm] using (hgeom.2 v hv q hq).2.2.2
  have hqdist : 1/2 ≤ ‖q.2.1-q.2.2‖ := by simpa only [dist_eq_norm] using (hgeom.2 q hq q hq).2.2.2
  have hdist := normalized_distance_le_twelve_cross _ _ hvdist hqdist hcap.2
  have hyb : dist q.2.1 q.2.2 ≤ 2 := by
    have hh := dist_le_norm_add_norm q.2.1 q.2.2
    linarith [(hgeom.1 q hq).2.2.1,(hgeom.1 q hq).2.2.2]
  have hcross := strip_vantage_determinant_upper hw L q.2.2 v.2.1 q.2.1
    (hstrip _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩))
    (hstrip _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩))
    (hgeom.1 v hv).2.2.1 (hgeom.1 q hq).2.2.1 hyb
  change dist (NormedSpace.normalize _) (NormedSpace.normalize _) ≤ _
  linarith

end Kakeya4.Hard.RestrictedTriple
