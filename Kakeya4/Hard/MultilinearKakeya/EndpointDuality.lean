import Kakeya4.Hard.MultilinearKakeya.RealFiniteFactors

/-! Finite rescaling and exact power algebra for the endpoint duality step.
All divisions and root cancellations are performed on proved positive values. -/

noncomputable section
open scoped BigOperators

namespace Kakeya4.Hard.MultilinearKakeya

theorem exists_positive_finite_rescaling {κ : Type*} [Fintype κ]
    (f : κ → ℝ) (hf : ∀ q, 0 < f q) : ∃ α : ℝ, 0 < α ∧ ∀ q, 1 ≤ α*f q := by
  classical
  let α := 1+∑ q, (f q)⁻¹
  have hs : 0 ≤ ∑ q, (f q)⁻¹ := Finset.sum_nonneg (fun q _ => (inv_pos.mpr (hf q)).le)
  refine ⟨α,by dsimp [α]; linarith,fun q => ?_⟩
  have hle : (f q)⁻¹ ≤ α := by
    have h := Finset.single_le_sum (fun i _ => (inv_pos.mpr (hf i)).le) (Finset.mem_univ q)
    dsimp [α]
    linarith
  have h := mul_le_mul_of_nonneg_right hle (hf q).le
  simpa only [inv_mul_cancel₀ (hf q).ne'] using h

theorem endpoint_dual_power_identity {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x) :
    (x^endpointExponent n*x)^((n : ℝ)⁻¹) = x^endpointExponent n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ)-1 ≠ 0 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have he : (endpointExponent n+1)*(n : ℝ)⁻¹ = endpointExponent n := by
    unfold endpointExponent
    field_simp [hn0,hn1]
    <;> ring
  calc
    _ = (x^(endpointExponent n+1))^((n : ℝ)⁻¹) := by rw [Real.rpow_add hx,Real.rpow_one]
    _ = x^((endpointExponent n+1)*(n : ℝ)⁻¹) := (Real.rpow_mul hx.le _ _).symm
    _ = _ := by rw [he]

theorem weighted_endpoint_dual_power_identity {n : ℕ} (hn : 2 ≤ n)
    {c α x : ℝ} (hc : 0 ≤ c) (hα : 0 ≤ α) (hx : 0 < x) :
    (c*(α*x^endpointExponent n)*x)^((n : ℝ)⁻¹) =
      (c*α)^((n : ℝ)⁻¹)*x^endpointExponent n := by
  have he : c*(α*x^endpointExponent n)*x = (c*α)*(x^endpointExponent n*x) := by ring
  rw [he,Real.mul_rpow (mul_nonneg hc hα) (mul_nonneg (Real.rpow_nonneg hx.le _) hx.le),
    endpoint_dual_power_identity hn hx]

theorem cancel_endpoint_duality {n : ℕ} (hn : 2 ≤ n)
    {c α H G K T : ℝ} (hc : 0 < c) (hα : 0 < α) (hH : 0 < H)
    (hG : 0 ≤ G) (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hdual : (c*α)^((n : ℝ)⁻¹)*H ≤ G*(K*α*H)^((n : ℝ)⁻¹)*T^((n : ℝ)⁻¹)) :
    H ≤ (G^n*K/c*T)^endpointExponent n := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n-1 ≠ 0 := by omega
  have hroot (x : ℝ) (hx : 0 ≤ x) : (x^((n : ℝ)⁻¹))^n = x := Real.rpow_inv_natCast_pow hx hn0
  have hpow := pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg (mul_pos hc hα).le _) hH.le) hdual n
  simp only [mul_pow,hroot _ (mul_pos hc hα).le,hroot _ (mul_nonneg (mul_nonneg hK hα.le) hH.le),hroot _ hT] at hpow
  have hHpow : H^n = H^(n-1)*H := by rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ n)]
  rw [hHpow] at hpow
  have hcancel : c*H^(n-1) ≤ G^n*K*T := by
    have he : (c*H^(n-1))*(α*H) ≤ (G^n*K*T)*(α*H) := by nlinarith [hpow]
    exact (mul_le_mul_iff_left₀ (mul_pos hα hH)).mp (by simpa only [mul_comm] using he)
  have hbase : H^(n-1) ≤ G^n*K/c*T := by
    have h := (le_div_iff₀ hc).mpr (by nlinarith [hcancel] : H^(n-1)*c ≤ G^n*K*T)
    simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h
  have he : endpointExponent n = ((n-1 : ℕ) : ℝ)⁻¹ := by
    simp only [endpointExponent,one_div,Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  have h : (H^(n-1))^endpointExponent n ≤ (G^n*K/c*T)^endpointExponent n :=
    Real.rpow_le_rpow (pow_nonneg hH.le _) hbase (by rw [he]; positivity)
  rw [he,Real.pow_rpow_inv_natCast hH.le hn1] at h
  simpa only [he] using h

end Kakeya4.Hard.MultilinearKakeya
