import Kakeya4.Hard.RestrictedTriple.AxialDirections

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal Classical

namespace Kakeya4.Hard.RestrictedTriple

theorem occupied_radial_pair_inner (Q : Finset Triple) (q : Triple) (hq : q ∈ Q)
    (hgeom : standardTripleGeometry Q) (x y : Plane)
    (hx : x ∈ activeTripleClasses Q 1) (hy : y ∈ activeTripleClasses Q 1) :
    3/4 ≤ inner ℝ (radialProjection q.2.2 x) (radialProjection q.2.2 y) := by
  have hunitx := ((occupied_radial_cap Q q hq hgeom).2 x hx).1
  have hunity := ((occupied_radial_cap Q q hq hgeom).2 y hy).1
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hy
  have hvdist : 1/2 ≤ ‖v.2.1-q.2.2‖ := by simpa only [dist_eq_norm] using (hgeom.2 v hv q hq).2.2.2
  have hudist : 1/2 ≤ ‖u.2.1-q.2.2‖ := by simpa only [dist_eq_norm] using (hgeom.2 u hu q hq).2.2.2
  have hune : u.2.1-q.2.2 ≠ 0 := by intro hz; rw [hz,norm_zero] at hudist; norm_num at hudist
  have hds := normalize_distance_le_four hvdist hune
  have hid : dist (v.2.1-q.2.2) (u.2.1-q.2.2) = dist v.2.1 u.2.1 := by simp
  rw [hid] at hds
  have hclose : dist (radialProjection q.2.2 v.2.1) (radialProjection q.2.2 u.2.1) ≤ 2/5 := by
    change dist (NormedSpace.normalize _) (NormedSpace.normalize _) ≤ 2/5
    linarith [(hgeom.2 v hv u hu).2.1]
  have hs := norm_sub_sq_real (radialProjection q.2.2 v.2.1) (radialProjection q.2.2 u.2.1)
  rw [hunitx,hunity,← dist_eq_norm] at hs
  nlinarith [dist_nonneg (x := radialProjection q.2.2 v.2.1) (y := radialProjection q.2.2 u.2.1)]

/-- The actual anisotropic radial image has no inverse-height loss in its Frostman constant. -/
theorem common_strip_or_rescaled_angular_input {p w K c : ℝ} (hp : 0 < p)
    (hw : p/2 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c) (hK : 0 < K)
    (L : AffineLine) (Q : Finset Triple) (hgeom : standardTripleGeometry Q)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap))
    (hF : finiteFrostman p K (activeTripleClasses Q 1))
    (hstrip : ∀ x ∈ activeTripleClasses Q 1, x ∈ lineNeighborhood w L) :
    (∀ x ∈ activeTripleClasses Q 2, x ∈ lineNeighborhood (4*w) L) ∨
    ∃ q ∈ Q, ∃ D : ℝ, D = |cross2 (q.2.2-L.anchor) L.direction| ∧ 4*w < D ∧ D ≤ 3 ∧
      ∃ Ω : Finset Plane, Ω.Nonempty ∧
        (Ω : Set Plane) ⊆ (fun x ↦ radialProjection
          (axialScale (radialProjection q.2.2 q.2.1) (192*D) q.2.2)
          (axialScale (radialProjection q.2.2 q.2.1) (192*D) x)) '' (fixedOuterFiber Q q : Set Plane) ∧
        IsSeparated (Real.toNNReal (w/(1536*D))) (Ω : Set Plane) ∧
        c*D/(32*K*w) ≤ (Ω.card : ℝ) ∧
        (∀ θ ∈ Ω, ‖θ‖ = 1 ∧ 1/2 ≤ inner ℝ θ (radialProjection q.2.2 q.2.1)) ∧
        finiteFrostman (w/(1536*D)) (344064*K/c) Ω := by
  rcases common_strip_or_actual_fine_arc hp hw hw1 hc hK L Q hgeom hdense hF hstrip with
    hcommon | ⟨q,hq,D,hDdef,hfar,hDhi,Λ,hΛne,hΛsrc,hsep,hmass,hcap,_hΛF⟩
  · exact Or.inl hcommon
  · right
    have hwpos : 0 < w := lt_of_lt_of_le (by positivity : 0 < p/2) hw
    have hD : 0 < D := (by positivity : 0 < 4*w).trans hfar
    let e := radialProjection q.2.2 q.2.1
    let d := 192*D
    let s := w/(8*d)
    let f := axialDirection e d
    let Ω := Λ.image f
    have he : ‖e‖ = 1 := (occupied_radial_cap Q q hq hgeom).1
    have hd : 0 < d := by dsimp [d]; positivity
    have hs : 0 < s := by dsimp [s]; positivity
    have hscale : s = w/(1536*D) := by dsimp [s,d]; ring
    have hunit : ∀ θ ∈ Λ, ‖θ‖ = 1 := fun θ hθ ↦ (hcap θ hθ).1
    have hclose : ∀ θ ∈ Λ, dist θ e ≤ d/2 := by
      intro θ hθ
      have hh := (hcap θ hθ).2.2
      dsimp [e,d]
      linarith
    have hpair : ∀ θ ∈ Λ, ∀ φ ∈ Λ, 3/4 ≤ inner ℝ θ φ := by
      intro θ hθ φ hφ
      obtain ⟨x,hx,rfl⟩ := hΛsrc hθ
      obtain ⟨y,hy,rfl⟩ := hΛsrc hφ
      exact occupied_radial_pair_inner Q q hq hgeom x y
        (fixedOuterFiber_subset Q q hx) (fixedOuterFiber_subset Q q hy)
    have hstrong : ∀ θ ∈ Λ, 3/4 ≤ inner ℝ θ e := by
      intro θ hθ
      obtain ⟨x,hx,rfl⟩ := hΛsrc hθ
      exact occupied_radial_pair_inner Q q hq hgeom x q.2.1
        (fixedOuterFiber_subset Q q hx) (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
    have hnorm : ∀ θ ∈ Λ, ‖axialScale e d θ‖ ≤ 3/2 := fun θ hθ ↦
      axialScale_fine_cap_norm e θ he (hunit θ hθ) hd (hclose θ hθ)
    have hdist : ∀ θ ∈ Λ, ∀ φ ∈ Λ, dist θ φ ≤ 8*d*dist (f θ) (f φ) := by
      intro θ hθ φ hφ
      exact axialDirection_distance_lower e θ φ he (hunit θ hθ) (hunit φ hφ)
        (by linarith [hpair θ hθ φ hφ]) hd (hnorm θ hθ) (hnorm φ hφ)
    have hinj : Set.InjOn f (Λ : Set Plane) := by
      intro θ hθ φ hφ heq
      have hh := hdist θ hθ φ hφ
      rw [heq,dist_self,mul_zero] at hh
      exact dist_le_zero.mp hh
    have hsepΩ : IsSeparated (Real.toNNReal s) (Ω : Set Plane) := by
      intro x hx y hy hne
      obtain ⟨θ,hθ,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨φ,hφ,rfl⟩ := Finset.mem_image.mp hy
      have hθφ : θ ≠ φ := fun hh ↦ hne (congrArg f hh)
      have hold : w < dist θ φ := by
        have hh := hsep hθ hφ hθφ
        apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hwpos.le).mp
        simpa only [ENNReal.coe_nnreal_eq,Real.coe_toNNReal _ hwpos.le,edist_dist] using hh
      have hnew : s < dist (f θ) (f φ) := by
        dsimp [s]
        apply (div_lt_iff₀ (show 0 < 8*d by positivity)).mpr
        nlinarith [hdist θ hθ φ hφ]
      have hh := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs.le).mpr hnew
      simpa only [ENNReal.coe_nnreal_eq,Real.coe_toNNReal _ hs.le,edist_dist] using hh
    have hΩne : Ω.Nonempty := hΛne.image f
    have hcard : Ω.card = Λ.card := Finset.card_image_of_injOn hinj
    have hΩmass : c*D/(32*K*w) ≤ (Ω.card : ℝ) := by rwa [hcard]
    have hΩcap : ∀ θ ∈ Ω, ‖θ‖ = 1 ∧ 1/2 ≤ inner ℝ θ e := by
      intro θ hθ
      obtain ⟨φ,hφ,rfl⟩ := Finset.mem_image.mp hθ
      exact axialDirection_fine_cap e φ he (hunit φ hφ) hd (hclose φ hφ) (hstrong φ hφ)
    have hΩF := unit_cap_separated_finiteFrostman hs Ω hΩne e he
      (fun θ hθ ↦ (hΩcap θ hθ).1) (fun θ hθ ↦ (hΩcap θ hθ).2) hsepΩ
    have hΩpos : (0:ℝ) < Ω.card := by exact_mod_cast Finset.card_pos.mpr hΩne
    have hpaid : c/(49152*K) ≤ s*(Ω.card : ℝ) := by
      have hid : c/(49152*K) = s*(c*D/(32*K*w)) := by
        dsimp [s,d]
        field_simp
        <;> ring
      rw [hid]
      exact mul_le_mul_of_nonneg_left hΩmass hs.le
    have hcoef : 7/(s*(Ω.card:ℝ)) ≤ 344064*K/c := by
      apply (div_le_div_iff₀ (mul_pos hs hΩpos) hc).mpr
      have hh := (div_le_iff₀ (show 0 < 49152*K by positivity)).mp hpaid
      nlinarith
    refine ⟨q,hq,D,hDdef,hfar,hDhi,Ω,hΩne,?_,?_,hΩmass,hΩcap,?_⟩
    · intro θ hθ
      obtain ⟨φ,hφ,rfl⟩ := Finset.mem_image.mp hθ
      obtain ⟨x,hx,rfl⟩ := hΛsrc hφ
      have hxb : x-q.2.2 ≠ 0 := by
        have hunitx := ((occupied_radial_cap Q q hq hgeom).2 x (fixedOuterFiber_subset Q q hx)).1
        intro hz
        change ‖NormedSpace.normalize (x-q.2.2)‖ = 1 at hunitx
        rw [hz,NormedSpace.normalize_zero_eq_zero,norm_zero] at hunitx
        norm_num at hunitx
      exact ⟨x,hx,by exact (axialDirection_radialProjection e q.2.2 x d hxb).symm⟩
    · rwa [← hscale]
    · rw [← hscale]
      exact finiteFrostman_mono hs.le hcoef hΩF

end Kakeya4.Hard.RestrictedTriple
