






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningLowerExponent

/-! A genuinely finite grid of positive lower input exponents. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem exists_positive_lower_grid_index {h α s : ℝ} (hh : 0 < h)
    (hhα : 2*h ≤ α) (hαs : α ≤ s) (hs1 : s ≤ 1) :
    ∃ j : Fin (Nat.ceil (1/h)+1), 0 < (j:ℕ) ∧
      (j:ℝ)*h ≤ s ∧ s < ((j:ℝ)+1)*h := by
  have hs : 0 < s := by linarith
  let n : ℕ := Nat.floor (s/h)
  have hn : n ≤ Nat.ceil (1/h) :=
    (Nat.floor_mono (div_le_div_of_nonneg_right hs1 hh.le)).trans (Nat.floor_le_ceil _)
  have hn0 : 0 < n := Nat.floor_pos.mpr ((le_div_iff₀ hh).mpr (by linarith))
  refine ⟨⟨n,by omega⟩,hn0,?_,?_⟩
  · exact (le_div_iff₀ hh).mp (Nat.floor_le (by positivity : 0 ≤ s/h))
  · exact (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (s/h))

theorem exists_uniform_intermediate_L2_iteration_budget (kernel : SmoothKernel) {α β a : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (ha : 0 < a) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ s t : ℝ, α ≤ s → α ≤ t → s+t ≤ 1 →
      ∃ ε r₀ : ℝ, 0 < ε ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ δ r : ℝ, 0 < δ → 0 < r → δ ≤ r → r ≤ δ^a → r ≤ r₀ →
      ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        UnitSupported μ → UnitSupported ν →
        smoothEnergy kernel.law s δ μ ≤ ENNReal.ofReal (δ^(-ε)) →
        smoothEnergy kernel.law t δ ν ≤ ENNReal.ofReal (δ^(-ε)) →
        ∀ k : ℕ, K ≤ k →
        densityL2 (additiveLawPower (differenceLaw μ ∗ₘ differenceLaw ν) k)
          (kernelProfile kernel r) ≤ ENNReal.ofReal (r^(s+t-1-β)) := by
  classical
  let h : ℝ := min (α/2) (β/4)
  have hh : 0 < h := lt_min (by positivity) (by positivity)
  have hhα : 2*h ≤ α := by have hp := min_le_left (α/2) (β/4); dsimp [h]; linarith
  have hhβ : 2*h ≤ β/2 := by have hp := min_le_right (α/2) (β/4); dsimp [h]; linarith
  let J := Fin (Nat.ceil (1/h)+1)
  let I := {p : J×J // 0 < (p.1:ℕ) ∧ 0 < (p.2:ℕ) ∧ (p.1:ℝ)*h+(p.2:ℝ)*h ≤ 1}
  have hex (i : I) := OSS_original_energy_intermediate_L2_flattening kernel
    (mul_pos (Nat.cast_pos.mpr i.property.1) hh)
    (mul_pos (Nat.cast_pos.mpr i.property.2.1) hh) i.property.2.2
    (by positivity : 0 < β/2) ha
  choose εg Rg Kg hεg hRg hRg1 hKg hg using hex
  let K : ℕ := max 2 (Finset.univ.sup Kg)
  refine ⟨K,le_max_left _ _,?_⟩
  intro s t hαs hαt hst
  have hs : 0 < s := hα.trans_le hαs
  have ht : 0 < t := hα.trans_le hαt
  obtain ⟨j,hj,hjs,hsj⟩ := exists_positive_lower_grid_index hh hhα hαs (by linarith : s≤1)
  obtain ⟨l,hl,hlt,htl⟩ := exists_positive_lower_grid_index hh hhα hαt (by linarith : t≤1)
  let i : I := ⟨(j,l),hj,hl,by linarith⟩
  obtain ⟨δp,hδp,hδp1,hpay⟩ := exists_uniform_lower_exponent_cap kernel (hεg i)
  refine ⟨εg i/2,min (Rg i) δp,div_pos (hεg i) (by norm_num),lt_min (hRg i) hδp,
    (min_le_left _ _).trans (hRg1 i),?_⟩
  intro δ r hδ hr hδr hwindow hrr μ ν _ _ hμU hνU hμE hνE k hk
  have hδp' : δ ≤ δp := hδr.trans (hrr.trans (min_le_right _ _))
  have hμcap := hpay δ hδ hδp' μ hμU ((j:ℝ)*h) s (by positivity) hjs (by linarith) hμE
  have hνcap := hpay δ hδ hδp' ν hνU ((l:ℝ)*h) t (by positivity) hlt (by linarith) hνE
  have hKi : Kg i ≤ K := (Finset.le_sup (f := Kg) (Finset.mem_univ i)).trans (le_max_right _ _)
  have hb := hg i δ r hδ hr hδr hwindow (hrr.trans (min_le_left _ _))
    μ ν hμU hνU hμcap hνcap k (hKi.trans hk)
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_exponent_ge hr ((hrr.trans (min_le_left _ _)).trans (hRg1 i))
  change s+t-1-β ≤ (j:ℝ)*h+(l:ℝ)*h-1-β/2
  nlinarith

#print axioms exists_positive_lower_grid_index
#print axioms exists_uniform_intermediate_L2_iteration_budget
end OAI.Falconer
