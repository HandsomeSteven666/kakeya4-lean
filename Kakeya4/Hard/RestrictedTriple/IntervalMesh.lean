import Kakeya4.Hard.RestrictedTriple.StandardDenseInput

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem exists_mesh_interval_center {N : ℕ} (hN : 0 < N) {r t : ℝ}
    (hr : 0 < r) (ht : |t| ≤ (N:ℝ)*r/2) :
    ∃ j : Fin N, |t-(((j:ℝ)+1/2)-(N:ℝ)/2)*r| ≤ r/2 := by
  let u : ℝ := (t+(N:ℝ)*r/2)/r
  have hu : u*r = t+(N:ℝ)*r/2 := div_mul_cancel₀ _ hr.ne'
  have ht' := abs_le.mp ht
  have hu0 : 0 ≤ u := by
    apply div_nonneg _ hr.le
    linarith [ht'.1]
  have huN : u ≤ N := by nlinarith
  by_cases hlt : u < N
  · let j : Fin N := ⟨⌊u⌋₊,(Nat.floor_lt hu0).mpr hlt⟩
    refine ⟨j,?_⟩
    have hlo := Nat.floor_le hu0
    have hhi := Nat.lt_floor_add_one u
    change |t-((((⌊u⌋₊:ℕ):ℝ)+1/2)-(N:ℝ)/2)*r| ≤ r/2
    apply abs_le.mpr
    constructor <;> nlinarith
  · let j : Fin N := ⟨N-1,Nat.sub_lt hN (by norm_num)⟩
    refine ⟨j,?_⟩
    have hueq : u = N := by linarith
    have hj : ((N-1:ℕ):ℝ) = (N:ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N)]
      norm_num
    change |t-((((N-1:ℕ):ℝ)+1/2)-(N:ℝ)/2)*r| ≤ r/2
    rw [hj]
    apply abs_le.mpr
    constructor <;> nlinarith

/-- Linear, rather than quadratic or exponential, entropy cost for an integer scale ratio.
The comparison retains ENNReal infinity and needs no measurable-set assumptions. -/
theorem intervalCover_le_nat_mul_scale {N : ℕ} (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (E : Set ℝ) :
    intervalCover r E ≤ (N:ℝ≥0∞)*intervalCover ((N:ℝ)*r) E := by
  classical
  obtain ⟨Q,hQ,hcard⟩ := exists_external_optimal_cover (Real.toNNReal (((N:ℝ)*r)/2)) E
  let f : ℝ × Fin N → ℝ := fun q ↦ q.1+(((q.2:ℝ)+1/2)-(N:ℝ)/2)*r
  let R : Set ℝ := f '' (Q ×ˢ (univ : Set (Fin N)))
  have hcover : IsCover (Real.toNNReal (r/2)) E R := by
    intro x hx
    obtain ⟨q,hq,hd⟩ := hQ hx
    change edist x q ≤ (Real.toNNReal (((N:ℝ)*r)/2) : ℝ≥0∞) at hd
    have hd' : |x-q| ≤ (N:ℝ)*r/2 := by
      have hh : dist x q ≤ (N:ℝ)*r/2 := (edist_le_ofReal (by positivity)).mp (by
        simpa only [ENNReal.coe_nnreal_eq,Real.coe_toNNReal _ (show 0 ≤ (N:ℝ)*r/2 by positivity)] using hd)
      simpa only [Real.dist_eq] using hh
    obtain ⟨j,hj⟩ := exists_mesh_interval_center hN hr hd'
    refine ⟨f (q,j),⟨(q,j),⟨hq,mem_univ _⟩,rfl⟩,?_⟩
    change edist x (f (q,j)) ≤ (Real.toNNReal (r/2) : ℝ≥0∞)
    have heq : x-f (q,j) = (x-q)-(((j:ℝ)+1/2)-(N:ℝ)/2)*r := by dsimp [f]; ring
    have hh : dist x (f (q,j)) ≤ r/2 := by simpa only [Real.dist_eq,heq] using hj
    have he := (edist_le_ofReal (show 0 ≤ r/2 by positivity)).mpr hh
    simpa only [ENNReal.coe_nnreal_eq,Real.coe_toNNReal _ (show 0 ≤ r/2 by positivity)] using he
  have hR : R.encard ≤ Q.encard*(N:ℕ∞) := by
    have hh := encard_image_le f (Q ×ˢ (univ : Set (Fin N)))
    simpa [R,encard_prod,encard_univ,ENat.card_eq_coe_fintype_card] using hh
  have hh := ENat.toENNReal_mono (hcover.externalCoveringNumber_le_encard.trans hR)
  simpa [intervalCover,ENat.toENNReal_mul,hcard,mul_comm] using hh

end Kakeya4.Hard.RestrictedTriple
