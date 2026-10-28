import Kakeya4.Hard.RestrictedTriple.SquareReadyInput

set_option autoImplicit false
noncomputable section
open Set Metric

namespace Kakeya4.Hard.RestrictedTriple

/-- A finite width mesh with multiplicative rounding cost at most two above p.
Its smallest width is at least p/2, and width one is present exactly. -/
theorem exists_strip_width_mesh {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ W : Finset ℝ, 1 ∈ W ∧ (∀ w ∈ W, p/2 ≤ w ∧ w ≤ 1) ∧
      ∀ r : ℝ, p ≤ r → r ≤ 1 → ∃ s ∈ W, r ≤ s ∧ s ≤ 2*r := by
  classical
  let N := ⌈1/p⌉₊
  have hlo : 1/p ≤ (N:ℝ) := Nat.le_ceil _
  have hNr : (0:ℝ) < N := (by positivity : (0:ℝ) < 1/p).trans_le hlo
  have hN : 0 < N := by exact_mod_cast hNr
  have hNlower : 1 ≤ (N:ℝ)*p := (div_le_iff₀ hp).mp hlo
  have hNupper : (N:ℝ)*p ≤ 2 := by
    have hh := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (show 0 ≤ 1/p by positivity)) hp
    change (N:ℝ)*p < (1/p+1)*p at hh
    have heq : (1/p+1)*p = 1+p := by field_simp
    rw [heq] at hh
    linarith
  let W := (Finset.Icc 1 N).image (fun j : ℕ ↦ (j:ℝ)/(N:ℝ))
  have hone : (1:ℝ) ∈ W := by
    refine Finset.mem_image.mpr ⟨N,Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩,?_⟩
    exact div_self hNr.ne'
  refine ⟨W,hone,?_,?_⟩
  · intro w hw
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hjlo,hjhi⟩ := Finset.mem_Icc.mp hj
    have hjrlo : (1:ℝ) ≤ j := by exact_mod_cast hjlo
    have hjrhi : (j:ℝ) ≤ N := by exact_mod_cast hjhi
    constructor
    · apply (le_div_iff₀ hNr).mpr
      nlinarith
    · exact (div_le_iff₀ hNr).mpr (by linarith)
  · intro r hpr hr1
    have hr : 0 < r := hp.trans_le hpr
    let j := ⌈(N:ℝ)*r⌉₊
    have hjpos : 0 < j := Nat.ceil_pos.mpr (mul_pos hNr hr)
    have hjN : j ≤ N := Nat.ceil_le.mpr (by nlinarith : (N:ℝ)*r ≤ N)
    have hjlo : (N:ℝ)*r ≤ (j:ℝ) := Nat.le_ceil _
    have hjhi : (j:ℝ) < (N:ℝ)*r+1 := Nat.ceil_lt_add_one (by positivity)
    refine ⟨(j:ℝ)/(N:ℝ),Finset.mem_image.mpr ⟨j,Finset.mem_Icc.mpr ⟨by omega,hjN⟩,rfl⟩,
      (le_div_iff₀ hNr).mpr (by nlinarith),?_⟩
    apply (div_le_iff₀ hNr).mpr
    have hh : 1 ≤ (N:ℝ)*r := hNlower.trans (mul_le_mul_of_nonneg_left hpr hNr.le)
    nlinarith

end Kakeya4.Hard.RestrictedTriple
