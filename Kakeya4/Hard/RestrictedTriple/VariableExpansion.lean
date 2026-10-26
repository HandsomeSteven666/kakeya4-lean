import Kakeya4.Hard.RestrictedTriple.IntervalMesh

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem entropy_coarsening_power_budget {n R ε ε₀ : ℝ} (hn : 0 < n) (hR : 0 < R)
    (hbudget : n^ε₀ ≤ R^(ε-ε₀)) : n*R^(1-ε) ≤ (n*R)^(1-ε₀) := by
  have hnid : n^(1-ε₀)*n^ε₀ = n := by rw [← Real.rpow_add hn]; simp
  calc
    _ = (n^(1-ε₀)*n^ε₀)*R^(1-ε) := by rw [hnid]
    _ ≤ (n^(1-ε₀)*R^(ε-ε₀))*R^(1-ε) := by gcongr
    _ = n^(1-ε₀)*R^(1-ε₀) := by
      rw [mul_assoc,← Real.rpow_add hR]
      congr 2
      ring
    _ = _ := (Real.mul_rpow hn.le hR.le).symm

theorem exists_paid_coarsening_integer {p η σ s : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hη : 0 ≤ η) (hσ : 0 < σ) (hσup : σ ≤ p^(-12*η)) (hs : p/8 ≤ s)
    (hpay : 9 ≤ p^(-η)) :
    ∃ N : ℕ, 0 < N ∧ p ≤ (N:ℝ)*(s/σ) ∧ (N:ℝ) ≤ p^(-13*η) := by
  let t := s/σ
  have hspos : 0 < s := (by positivity : 0 < p/8).trans_le hs
  have ht : 0 < t := div_pos hspos hσ
  let N := ⌈p/t⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (div_pos hp ht)
  have hlo : p ≤ (N:ℝ)*t := (div_le_iff₀ ht).mp (Nat.le_ceil (p/t))
  have hratio : p/t ≤ 8*σ := by
    apply (div_le_iff₀ ht).mpr
    have heq : σ*t = s := by dsimp [t]; field_simp
    nlinarith
  have hone : 1 ≤ p^(-12*η) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hp hp1 (by linarith)
  have hNup : (N:ℝ) ≤ 9*p^(-12*η) := by
    have hh := (Nat.ceil_lt_add_one (div_pos hp ht).le).le
    change (N:ℝ) ≤ _ at hh
    linarith
  refine ⟨N,hN,hlo,?_⟩
  calc
    _ ≤ 9*p^(-12*η) := hNup
    _ ≤ p^(-η)*p^(-12*η) := mul_le_mul_of_nonneg_right hpay (Real.rpow_pos_of_pos hp _).le
    _ = _ := by rw [← Real.rpow_add hp]; congr 1; ring

/-- A supplied normalized expansion branch pulls back even if its raw fine scale is below p.
The integer mesh has linear entropy cost; exponent slack pays its epsilon-power loss.
This theorem transports a branch, and does not prove the finite dichotomy. -/
theorem longIntervalExpansion_of_variable_factor {p η σ ε ε₀ : ℝ} {P Q : Set Triple}
    (hp : 0 < p) (hp1 : p ≤ 1) (hη : 0 ≤ η) (hσ : 0 < σ)
    (hσup : σ ≤ p^(-12*η)) (hpay : 9 ≤ p^(-η))
    (hε₀ : 0 ≤ ε₀) (hgap : ε₀ ≤ ε) (hexponent : 44*ε₀ ≤ 31*ε)
    (himage : dotDifferenceImage P = (fun x : ℝ ↦ σ*x) '' dotDifferenceImage Q)
    (hexpand : LongIntervalExpansion (p/8) ε₀ (44*η) P) :
    LongIntervalExpansion p ε η Q := by
  obtain ⟨s,l,u,hs,hlu,hwidth,hlower⟩ := hexpand
  have hspos : 0 < s := (by positivity : 0 < p/8).trans_le hs
  let t := s/σ
  let L := u/σ-l/σ
  have ht : 0 < t := div_pos hspos hσ
  obtain ⟨N,hN,hcut,hNup⟩ := exists_paid_coarsening_integer hp hp1 hη hσ hσup hs hpay
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  let R := L/((N:ℝ)*t)
  have hratio : L/t = (u-l)/s := by dsimp [L,t]; field_simp
  have hNR : (N:ℝ)*R = L/t := by dsimp [R]; field_simp
  have hsource : p^(-44*η) ≤ L/t := by
    rw [hratio]
    have hh : (p/8)^(-(44*η)) ≤ (u-l)/s := (le_div_iff₀ hspos).mpr hwidth
    have hpow : p^(-44*η) ≤ (p/8)^(-44*η) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have he : -44*η = -(44*η) := by ring
    rw [he] at hpow
    rw [he]
    exact hpow.trans hh
  have hL : 0 < L := by
    have hh := (le_div_iff₀ ht).mp hsource
    exact lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hp _) ht) hh
  have hR : 0 < R := div_pos hL (mul_pos hNr ht)
  have hRlower : p^(-31*η) ≤ R := by
    have heq : p^(-13*η)*p^(-31*η) = p^(-44*η) := by
      rw [← Real.rpow_add hp]; congr 1; ring
    have hh : p^(-13*η)*p^(-31*η) ≤ p^(-13*η)*R := by
      rw [heq]
      exact hsource.trans (by rw [← hNR]; exact mul_le_mul_of_nonneg_right hNup hR.le)
    exact le_of_mul_le_mul_left hh (Real.rpow_pos_of_pos hp _)
  have hbudget : (N:ℝ)^ε₀ ≤ R^(ε-ε₀) := by
    calc
      _ ≤ (p^(-13*η))^ε₀ := Real.rpow_le_rpow hNr.le hNup hε₀
      _ = p^((-13*η)*ε₀) := (Real.rpow_mul hp.le _ _).symm
      _ ≤ p^((-31*η)*(ε-ε₀)) := Real.rpow_le_rpow_of_exponent_ge hp hp1 (by nlinarith)
      _ = (p^(-31*η))^(ε-ε₀) := Real.rpow_mul hp.le _ _
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_pos_of_pos hp _).le hRlower (sub_nonneg.mpr hgap)
  have hpower : (N:ℝ)*R^(1-ε) ≤ (L/t)^(1-ε₀) := by
    rw [← hNR]
    exact entropy_coarsening_power_budget hNr hR hbudget
  have hscale : σ*t = s := by dsimp [t]; field_simp
  have hl : σ*(l/σ) = l := by field_simp
  have hu : σ*(u/σ) = u := by field_simp
  have hcover : intervalCover s (Icc l u ∩ dotDifferenceImage P) =
      intervalCover t (Icc (l/σ) (u/σ) ∩ dotDifferenceImage Q) := by
    have hh := intervalCover_mul_Icc_inter hσ ht.le (l/σ) (u/σ) (dotDifferenceImage Q)
    rwa [hscale,hl,hu,← himage] at hh
  have hcoarse := intervalCover_le_nat_mul_scale hN ht
    (Icc (l/σ) (u/σ) ∩ dotDifferenceImage Q)
  have hbound : ENNReal.ofReal ((N:ℝ)*R^(1-ε)) ≤
      (N:ℝ≥0∞)*intervalCover ((N:ℝ)*t) (Icc (l/σ) (u/σ) ∩ dotDifferenceImage Q) := by
    refine (ENNReal.ofReal_le_ofReal hpower).trans ?_
    rw [hratio]
    exact hlower.trans (hcover.le.trans hcoarse)
  rw [ENNReal.ofReal_mul hNr.le,ENNReal.ofReal_natCast] at hbound
  have hcancel := (ENNReal.mul_le_mul_iff_right
    (show (N:ℝ≥0∞) ≠ 0 by exact_mod_cast hN.ne') (by simp : (N:ℝ≥0∞) ≠ ∞)).mp hbound
  refine ⟨(N:ℝ)*t,l/σ,u/σ,hcut,(div_le_div_iff_of_pos_right hσ).mpr hlu,?_,hcancel⟩
  have hwidthlower : p^(-η) ≤ R := by
    refine (Real.rpow_le_rpow_of_exponent_ge hp hp1 ?_).trans hRlower
    linarith
  exact (le_div_iff₀ (mul_pos hNr ht)).mp hwidthlower

end Kakeya4.Hard.RestrictedTriple
