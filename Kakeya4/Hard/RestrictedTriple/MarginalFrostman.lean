import Kakeya4.Hard.RestrictedTriple.MarginalCardinality

set_option autoImplicit false
noncomputable section
open Set Metric

namespace Kakeya4.Hard.RestrictedTriple

/-- Normalized exponent-one Frostman count, for all radii at least p.
The cardinality factor is essential; no lower local regularity is required. -/
def finiteFrostman (p K : ℝ) (F : Finset Plane) : Prop :=
  ∀ (z : Plane) (r : ℝ), p ≤ r → ((F.filter (fun x ↦ dist z x ≤ r)).card : ℝ) ≤ K*r*(F.card : ℝ)

theorem finiteFrostman_mono {p K L : ℝ} {F : Finset Plane} (hp : 0 ≤ p)
    (hKL : K ≤ L) (h : finiteFrostman p K F) : finiteFrostman p L F := by
  intro z r hr
  refine (h z r hr).trans ?_
  have hr0 : 0 ≤ r := hp.trans hr
  gcongr

theorem finiteFrostman_of_AD_marginal {A : Set Plane} {p η : ℝ}
    (hp : 0 < p) (hpay : 128 ≤ p^(-η)) (hAD : ADUpperBound p (p^(-η)) A)
    (F : Finset Plane) (hFA : (F : Set Plane) ⊆ A)
    (hsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (F : Set Plane)))
    (hlower : p^(4*η-1)/64 ≤ (F.card : ℝ)) : finiteFrostman p (p^(-6*η)) F := by
  intro z r hr
  have hrpos : 0 < r := hp.trans_le hr
  have hlocal := finset_closedBall_count_real F z r
    (show 0 ≤ 2*p^(-η)*r/p by positivity)
    (closedBall_local_count_of_ADUpperBound hp hAD hFA hsep z hr)
  have hidentity : (128*p^(-5*η))*(p^(4*η-1)/64) = 2*p^(-η)/p := by
    calc
      _ = 2*(p^(-5*η)*p^(4*η-1)) := by ring
      _ = 2*p^((-5*η)+(4*η-1)) := by rw [← Real.rpow_add hp]
      _ = 2*p^((-η)-1) := by congr 2; ring
      _ = _ := by rw [Real.rpow_sub_one hp.ne']; ring
  have hconstant : 128*p^(-5*η) ≤ p^(-6*η) := by
    calc
      _ ≤ p^(-η)*p^(-5*η) := mul_le_mul_of_nonneg_right hpay (Real.rpow_pos_of_pos hp _).le
      _ = _ := by rw [← Real.rpow_add hp]; congr 1; ring
  calc
    _ ≤ 2*p^(-η)*r/p := hlocal
    _ = (128*p^(-5*η))*r*(p^(4*η-1)/64) := by
      calc
        _ = ((128*p^(-5*η))*(p^(4*η-1)/64))*r := by rw [hidentity]; ring
        _ = _ := by ring
    _ ≤ (128*p^(-5*η))*r*(F.card : ℝ) := by gcongr
    _ ≤ _ := by gcongr

theorem finiteFrostman_halfPlane {p K : ℝ} {F : Finset Plane}
    (h : finiteFrostman p K F) : finiteFrostman (p/2) (2*K) (F.image halfPlane) := by
  classical
  intro z r hr
  have hhalf : halfPlane ((2:ℝ) • z) = z := by simp [halfPlane,smul_smul]
  have hd (x : Plane) : dist z (halfPlane x) = dist ((2:ℝ) • z) x/2 := by
    have hh := halfPlane_dist ((2:ℝ) • z) x
    rwa [hhalf] at hh
  have hfilter : (F.image halfPlane).filter (fun x ↦ dist z x ≤ r) =
      (F.filter (fun x ↦ dist ((2:ℝ) • z) x ≤ 2*r)).image halfPlane := by
    ext y
    constructor
    · intro hy
      obtain ⟨hyF,hyb⟩ := Finset.mem_filter.mp hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hyF
      rw [hd] at hyb
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,by linarith⟩,rfl⟩
    · intro hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hxF,hxb⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,hxF,rfl⟩,?_⟩
      rw [hd]
      linarith
  rw [hfilter,Finset.card_image_of_injective _ halfPlane_injective,
    Finset.card_image_of_injective _ halfPlane_injective]
  have hh := h ((2:ℝ) • z) (2*r) (by linarith)
  convert hh using 1 <;> ring

end Kakeya4.Hard.RestrictedTriple
