import Kakeya4.Hard.RestrictedTriple.FrostmanInput
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators

namespace Kakeya4.Hard.RestrictedTriple

def scalarCell (N : ℕ) (x : ℝ) : Fin (N+1) :=
  ⟨min ⌊(N:ℝ)*x⌋₊ N,Nat.lt_succ_of_le (min_le_right _ _)⟩

def planeCell (N : ℕ) (x : Plane) : Fin 2 → Fin (N+1) := fun i ↦ scalarCell N (x i)
def tripleCell (N : ℕ) (t : Triple) : Fin 3 × Fin 2 → Fin (N+1) :=
  fun ji ↦ scalarCell N (tripleCoordinates t ji)

theorem scalarCell_dist_le {N : ℕ} (hN : 0 < N) {x y : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (h : scalarCell N x = scalarCell N y) :
    |x-y| ≤ 1/(N:ℝ) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hx0 : 0 ≤ x := hx.1
  have hy0 : 0 ≤ y := hy.1
  have hFx : ⌊(N:ℝ)*x⌋₊ ≤ N := by
    have hh := Nat.floor_mono (show (N:ℝ)*x ≤ (N:ℝ) by nlinarith [hx.2])
    simpa only [Nat.floor_natCast] using hh
  have hFy : ⌊(N:ℝ)*y⌋₊ ≤ N := by
    have hh := Nat.floor_mono (show (N:ℝ)*y ≤ (N:ℝ) by nlinarith [hy.2])
    simpa only [Nat.floor_natCast] using hh
  have heq := congrArg Fin.val h
  change min ⌊(N:ℝ)*x⌋₊ N = min ⌊(N:ℝ)*y⌋₊ N at heq
  rw [min_eq_left hFx,min_eq_left hFy] at heq
  have heqR : (⌊(N:ℝ)*x⌋₊ : ℝ) = ⌊(N:ℝ)*y⌋₊ := by exact_mod_cast heq
  have hxlo := Nat.floor_le (show 0 ≤ (N:ℝ)*x by positivity)
  have hylo := Nat.floor_le (show 0 ≤ (N:ℝ)*y by positivity)
  have hxhi := Nat.lt_floor_add_one ((N:ℝ)*x)
  have hyhi := Nat.lt_floor_add_one ((N:ℝ)*y)
  apply abs_le.mpr
  constructor
  · have hh : (-1:ℝ)/(N:ℝ) ≤ x-y := (div_le_iff₀ hNr).mpr (by nlinarith)
    simpa only [neg_div,one_div] using hh
  · exact (le_div_iff₀ hNr).mpr (by nlinarith)

theorem planeCell_dist_le {N : ℕ} (hN : 0 < N) {x y : Plane}
    (hx : x ∈ unitSquare) (hy : y ∈ unitSquare) (h : planeCell N x = planeCell N y) :
    dist x y ≤ 2/(N:ℝ) := by
  have hh : dist (planeCoordinates x) (planeCoordinates y) ≤ 1/(N:ℝ) := by
    apply (dist_pi_le_iff (by positivity)).mpr
    intro i
    simpa only [planeCoordinates,Real.dist_eq] using scalarCell_dist_le hN (hx i) (hy i) (congrFun h i)
  have hxy := (plane_dist_le_two_coordinates x y).trans (mul_le_mul_of_nonneg_left hh (by norm_num))
  convert hxy using 1 <;> ring

/-- The selected fiber is nonempty; the full color-count cost remains explicit. -/
theorem exists_large_color_fiber {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (f : α → β) (H : Finset α) (hH : H.Nonempty) :
    ∃ b : β, (H.filter (fun x ↦ f x = b)).Nonempty ∧
      (H.card : ℝ) ≤ (Fintype.card β : ℝ)*((H.filter (fun x ↦ f x = b)).card : ℝ) := by
  classical
  obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image (H.image f)
    (fun b ↦ (H.filter (fun x ↦ f x = b)).card) (hH.image f)
  obtain ⟨x,hx,hxb⟩ := Finset.mem_image.mp hb
  refine ⟨b,⟨x,Finset.mem_filter.mpr ⟨hx,hxb⟩⟩,?_⟩
  have hsum : (H.card : ℝ) = ∑ c ∈ H.image f, ((H.filter (fun x ↦ f x = c)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image f H
  calc
    _ = _ := hsum
    _ ≤ ∑ _c ∈ H.image f, ((H.filter (fun x ↦ f x = b)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro c hc
      exact_mod_cast hmax c hc
    _ = ((H.image f).card : ℝ)*((H.filter (fun x ↦ f x = b)).card : ℝ) := by simp
    _ ≤ _ := by
      gcongr
      exact_mod_cast Finset.card_le_univ (H.image f)

theorem exists_small_cell_triples {A B : Set Plane} (hA : A ⊆ unitSquare) (hB : B ⊆ unitSquare)
    (H : Finset Triple) (hH : H.Nonempty)
    (hsupport : ∀ t ∈ H, t.1 ∈ A ∧ t.2.1 ∈ B ∧ t.2.2 ∈ B)
    {N : ℕ} (hN : 0 < N) :
    ∃ Q : Finset Triple, Q ⊆ H ∧ Q.Nonempty ∧
      (H.card : ℝ) ≤ ((N+1:ℕ)^6 : ℝ)*(Q.card : ℝ) ∧
      ∀ t ∈ Q, ∀ u ∈ Q,
        dist t.1 u.1 ≤ 2/(N:ℝ) ∧ dist t.2.1 u.2.1 ≤ 2/(N:ℝ) ∧ dist t.2.2 u.2.2 ≤ 2/(N:ℝ) := by
  classical
  obtain ⟨b,hne,hcard⟩ := exists_large_color_fiber (tripleCell N) H hH
  let Q := H.filter (fun t ↦ tripleCell N t = b)
  refine ⟨Q,Finset.filter_subset _ _,hne,?_,?_⟩
  · simpa [Fintype.card_fun,Fintype.card_prod,Fintype.card_fin] using hcard
  · intro t ht u hu
    obtain ⟨htH,htb⟩ := Finset.mem_filter.mp ht
    obtain ⟨huH,hub⟩ := Finset.mem_filter.mp hu
    have hsame : tripleCell N t = tripleCell N u := htb.trans hub.symm
    have h0 : planeCell N t.1 = planeCell N u.1 := by
      funext i
      simpa [planeCell,tripleCell,tripleCoordinates] using congrFun hsame ((0:Fin 3),i)
    have h1 : planeCell N t.2.1 = planeCell N u.2.1 := by
      funext i
      simpa [planeCell,tripleCell,tripleCoordinates] using congrFun hsame ((1:Fin 3),i)
    have h2 : planeCell N t.2.2 = planeCell N u.2.2 := by
      funext i
      simpa [planeCell,tripleCell,tripleCoordinates] using congrFun hsame ((2:Fin 3),i)
    exact ⟨planeCell_dist_le hN (hA (hsupport t htH).1) (hA (hsupport u huH).1) h0,
      planeCell_dist_le hN (hB (hsupport t htH).2.1) (hB (hsupport u huH).2.1) h1,
      planeCell_dist_le hN (hB (hsupport t htH).2.2) (hB (hsupport u huH).2.2) h2⟩

end Kakeya4.Hard.RestrictedTriple
