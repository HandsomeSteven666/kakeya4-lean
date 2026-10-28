import Kakeya4.Hard.RestrictedTriple.RadialCap

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal Classical

namespace Kakeya4.Hard.RestrictedTriple

/-- Linear local packing on a unit cap, using a real interval mesh. -/
theorem unit_cap_separated_card_le {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    (F : Finset Plane) (e z : Plane) (he : ‖e‖ = 1)
    (hunit : ∀ x ∈ F, ‖x‖ = 1) (hcap : ∀ x ∈ F, 1/2 ≤ inner ℝ x e)
    (hball : ∀ x ∈ F, dist z x ≤ r)
    (hsep : IsSeparated (Real.toNNReal s) (F : Set Plane)) : (F.card : ℝ) ≤ 7*r/s := by
  let N := ⌈6*r/s⌉₊
  have hr : 0 < r := hs.trans_le hsr
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hmesh : r ≤ (N:ℝ)*(s/3)/2 := by
    have hh := Nat.le_ceil (6*r/s)
    change 6*r/s ≤ (N:ℝ) at hh
    have hh' := (div_le_iff₀ hs).mp hh
    nlinarith
  let n := quarterTurn e
  have hn : ‖n‖ = 1 := (quarterTurn_norm e).trans he
  have hchoose : ∀ x : F, ∃ j : Fin N,
      |inner ℝ ((x:Plane)-z) n-(((j:ℝ)+1/2)-(N:ℝ)/2)*(s/3)| ≤ (s/3)/2 := by
    intro x
    have hh : |inner ℝ ((x:Plane)-z) n| ≤ r := by
      have hi := abs_real_inner_le_norm ((x:Plane)-z) n
      rw [hn,mul_one,← dist_eq_norm,dist_comm] at hi
      exact hi.trans (hball x x.property)
    exact exists_mesh_interval_center hN (by positivity) (hh.trans hmesh)
  let f : F → Fin N := fun x ↦ Classical.choose (hchoose x)
  have hinj : Function.Injective f := by
    intro x y heq
    apply Subtype.ext
    by_contra hne
    have hx := Classical.choose_spec (hchoose x)
    have hy := Classical.choose_spec (hchoose y)
    change |inner ℝ ((x:Plane)-z) n-(((f x:ℝ)+1/2)-(N:ℝ)/2)*(s/3)| ≤ (s/3)/2 at hx
    change |inner ℝ ((y:Plane)-z) n-(((f y:ℝ)+1/2)-(N:ℝ)/2)*(s/3)| ≤ (s/3)/2 at hy
    rw [heq] at hx
    have hcoord : |inner ℝ ((x:Plane)-(y:Plane)) n| ≤ s/3 := by
      have hid : inner ℝ ((x:Plane)-(y:Plane)) n =
          inner ℝ ((x:Plane)-z) n-inner ℝ ((y:Plane)-z) n := by simp only [inner_sub_left]; ring
      rw [hid]
      apply abs_le.mpr
      constructor <;> linarith [(abs_le.mp hx).1,(abs_le.mp hx).2,(abs_le.mp hy).1,(abs_le.mp hy).2]
    have hdist := unit_cap_chart_distance x y e (hunit x x.property) (hunit y y.property)
      he (hcap x x.property) (hcap y y.property)
    have hstrict : s < dist (x:Plane) (y:Plane) := by
      have hh := hsep x.property y.property hne
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs.le).mp
      simpa only [ENNReal.coe_nnreal_eq,Real.coe_toNNReal _ hs.le,edist_dist] using hh
    change |inner ℝ ((x:Plane)-(y:Plane)) (quarterTurn e)| ≤ s/3 at hcoord
    linarith
  have hcard : F.card ≤ N := by simpa using Fintype.card_le_of_injective f hinj
  have hcardReal : (F.card:ℝ) ≤ (N:ℝ) := by exact_mod_cast hcard
  have hupper := (Nat.ceil_lt_add_one (show 0 ≤ 6*r/s by positivity)).le
  change (N:ℝ) ≤ 6*r/s+1 at hupper
  have hratio : 1 ≤ r/s := (le_div_iff₀ hs).mpr (by linarith)
  have heq : 7*r/s = 6*r/s+r/s := by ring
  rw [heq]
  linarith

theorem unit_cap_separated_finiteFrostman {s : ℝ} (hs : 0 < s) (F : Finset Plane)
    (hne : F.Nonempty) (e : Plane) (he : ‖e‖ = 1)
    (hunit : ∀ x ∈ F, ‖x‖ = 1) (hcap : ∀ x ∈ F, 1/2 ≤ inner ℝ x e)
    (hsep : IsSeparated (Real.toNNReal s) (F : Set Plane)) :
    finiteFrostman s (7/(s*(F.card:ℝ))) F := by
  intro z r hsr
  let E := F.filter (fun x ↦ dist z x ≤ r)
  have hEF : E ⊆ F := Finset.filter_subset _ _
  have hh := unit_cap_separated_card_le hs hsr E e z he
    (fun x hx ↦ hunit x (hEF hx)) (fun x hx ↦ hcap x (hEF hx))
    (fun x hx ↦ (Finset.mem_filter.mp hx).2) (hsep.mono hEF)
  have hc : (0:ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hid : 7*r/s = (7/(s*(F.card:ℝ)))*r*(F.card:ℝ) := by field_simp
  exact hh.trans_eq hid

end Kakeya4.Hard.RestrictedTriple
