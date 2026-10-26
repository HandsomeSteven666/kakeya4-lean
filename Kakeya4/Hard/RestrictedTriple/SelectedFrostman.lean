import Kakeya4.Hard.RestrictedTriple.SelectedClassPayment

set_option autoImplicit false
noncomputable section
open Set Metric

namespace Kakeya4.Hard.RestrictedTriple

theorem finiteFrostman_of_selected_marginal {A : Set Plane} {p η : ℝ}
    (hp : 0 < p) (hpay : 256 ≤ p^(-η)) (hAD : ADUpperBound p (p^(-η)) A)
    (F : Finset Plane) (hFA : (F : Set Plane) ⊆ A)
    (hsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (F : Set Plane)))
    (hlower : p^(41*η-1)/128 ≤ (F.card : ℝ)) : finiteFrostman p (p^(-43*η)) F := by
  intro z r hr
  have hrpos : 0 < r := hp.trans_le hr
  have hlocal := finset_closedBall_count_real F z r
    (show 0 ≤ 2*p^(-η)*r/p by positivity)
    (closedBall_local_count_of_ADUpperBound hp hAD hFA hsep z hr)
  have hidentity : (256*p^(-42*η))*(p^(41*η-1)/128) = 2*p^(-η)/p := by
    calc
      _ = 2*(p^(-42*η)*p^(41*η-1)) := by ring
      _ = 2*p^((-42*η)+(41*η-1)) := by rw [← Real.rpow_add hp]
      _ = 2*p^((-η)-1) := by congr 2; ring
      _ = _ := by rw [Real.rpow_sub_one hp.ne']; ring
  have hconstant : 256*p^(-42*η) ≤ p^(-43*η) := by
    calc
      _ ≤ p^(-η)*p^(-42*η) := mul_le_mul_of_nonneg_right hpay (Real.rpow_pos_of_pos hp _).le
      _ = _ := by rw [← Real.rpow_add hp]; congr 1; ring
  calc
    _ ≤ 2*p^(-η)*r/p := hlocal
    _ = (256*p^(-42*η))*r*(p^(41*η-1)/128) := by
      calc
        _ = ((256*p^(-42*η))*(p^(41*η-1)/128))*r := by rw [hidentity]; ring
        _ = _ := by ring
    _ ≤ (256*p^(-42*η))*r*(F.card : ℝ) := by gcongr
    _ ≤ _ := by gcongr

/-- Uniform lower scale: even when r/c falls below p, count at radius p first.
The common bound c>=1/8 pays only a factor eight in normalized Frostman. -/
theorem finiteFrostman_affine_eighth {p K c : ℝ} (hp : 0 < p) (hK : 0 ≤ K)
    (hc : 1/8 ≤ c) (z : Plane) (F : Finset Plane) (h : finiteFrostman p K F) :
    finiteFrostman (p/8) (8*K) (F.image (fun x ↦ z+c • x)) := by
  classical
  have hcp : 0 < c := by linarith
  have haff (u x y : Plane) : dist (u+c • x) (u+c • y) = c*dist x y := by
    have heq : (u+c • x)-(u+c • y) = c • (x-y) := by module
    simp only [dist_eq_norm,heq,norm_smul,Real.norm_eq_abs,abs_of_pos hcp]
  let f : Plane → Plane := fun x ↦ z+c • x
  have hinj : Function.Injective f := by
    intro x y hxy
    apply dist_eq_zero.mp
    have heq := haff z x y
    have hzero : c*dist x y = 0 := by rw [← heq]; exact dist_eq_zero.mpr hxy
    exact (mul_eq_zero.mp hzero).resolve_left hcp.ne'
  intro w r hr
  let center : Plane := c⁻¹ • (w-z)
  have hcenter : z+c • center = w := by
    dsimp [center]
    rw [smul_smul,mul_inv_cancel₀ hcp.ne',one_smul]
    module
  have hd (x : Plane) : dist w (f x) = c*dist center x := by
    dsimp [f]
    calc
      _ = dist (z+c • center) (z+c • x) := by rw [hcenter]
      _ = _ := haff z center x
  let R : ℝ := max p (r/c)
  have hr0 : 0 < r := (by linarith : 0 < p/8).trans_le hr
  have hR : R ≤ 8*r := by
    apply max_le
    · linarith
    · apply (div_le_iff₀ hcp).mpr
      nlinarith
  have hsub : ((F.image f).filter (fun x ↦ dist w x ≤ r)) ⊆
      (F.filter (fun x ↦ dist center x ≤ R)).image f := by
    intro y hy
    obtain ⟨hyF,hyd⟩ := Finset.mem_filter.mp hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hyF
    apply Finset.mem_image.mpr
    refine ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have hsmall : dist center x ≤ r/c := by
      apply (le_div_iff₀ hcp).mpr
      rw [hd] at hyd
      nlinarith
    exact hsmall.trans (le_max_right _ _)
  have hcount : (((F.image f).filter (fun x ↦ dist w x ≤ r)).card : ℝ) ≤
      (F.filter (fun x ↦ dist center x ≤ R)).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_image_le)
  rw [Finset.card_image_of_injective _ hinj]
  calc
    _ ≤ _ := hcount
    _ ≤ K*R*(F.card : ℝ) := h center R (le_max_left _ _)
    _ ≤ K*(8*r)*(F.card : ℝ) := by gcongr
    _ = _ := by ring

theorem finiteFrostman_selected_affine_power {p η c : ℝ} (hp : 0 < p) (hη : 0 ≤ η)
    (hpay : 8 ≤ p^(-η)) (hc : 1/8 ≤ c) (z : Plane) (F : Finset Plane)
    (h : finiteFrostman p (p^(-43*η)) F) :
    finiteFrostman (p/8) ((p/8)^(-44*η)) (F.image (fun x ↦ z+c • x)) := by
  have hcoef : 8*p^(-43*η) ≤ (p/8)^(-44*η) := by
    calc
      _ ≤ p^(-η)*p^(-43*η) := mul_le_mul_of_nonneg_right hpay (Real.rpow_pos_of_pos hp _).le
      _ = p^(-44*η) := by rw [← Real.rpow_add hp]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  exact finiteFrostman_mono (by positivity) hcoef
    (finiteFrostman_affine_eighth hp (Real.rpow_pos_of_pos hp _).le hc z F h)

end Kakeya4.Hard.RestrictedTriple
