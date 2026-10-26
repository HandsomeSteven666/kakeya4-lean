/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Card

/-!
# Weighted finite conflict selection

Given a finite symmetric irreflexive conflict relation of degree at most `D`, the same selected
subfamily retains at least a `1/(D+1)` fraction of one chosen `ℝ≥0∞` weight and of the
cardinality. This is a combinatorial selector for later geometric applications; it assumes the
conflict-degree bound and does not prove any geometric estimate that supplies it.
-/

@[expose] public section

open scoped ENNReal

open Finset

namespace Kakeya4.Construction

/-- A bounded-degree conflict relation has an independent subfamily retaining both the chosen
weight and cardinality up to the degree-plus-one factor. -/
theorem exists_pairwise_conflictFree_retaining_weight_and_card {ι : Type*} (J : Finset ι)
    (r : ι → ι → Prop) (hsymm : ∀ i j, r i j → r j i) (hirr : ∀ i, ¬ r i i)
    {D : ℕ} (hdeg : ∀ i ∈ J, {j ∈ (J : Set ι) | r j i}.ncard ≤ D) (y : ι → ℝ≥0∞) :
    ∃ J' ⊆ J, (J' : Set ι).Pairwise (fun i j => ¬ r i j) ∧
      ∑ j ∈ J, y j ≤ (D + 1 : ℕ) * ∑ j ∈ J', y j ∧
      J.card ≤ (D + 1) * J'.card := by
  classical
  let q : Finset ι → Prop := fun S =>
    (∀ i ∈ S, (S.filter (fun j => r j i)).card ≤ D) →
      ∃ J' ⊆ S, (J' : Set ι).Pairwise (fun i j => ¬ r i j) ∧
        ∑ j ∈ S, y j ≤ (D + 1 : ℕ) * ∑ j ∈ J', y j ∧
        S.card ≤ (D + 1) * J'.card
  let step : ∀ s : Finset ι, (∀ t ⊂ s, q t) → q s := by
    intro S ih hdegS
    by_cases hS : S = ∅
    · subst S
      exact ⟨∅, by simp, by simp, by simp, by simp⟩
    · have hnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
      rcases Finset.exists_max_image S y hnonempty with ⟨i, hiS, himax⟩
      let T : Finset ι := S.filter (fun j => r j i)
      let N : Finset ι := insert i T
      have hTcard : T.card ≤ D := by simpa [T] using hdegS i hiS
      have hNcard : N.card ≤ D + 1 := by
        calc
          N.card = (insert i T).card := rfl
          _ ≤ T.card + 1 := Finset.card_insert_le i T
          _ ≤ D + 1 := Nat.add_le_add_right hTcard 1
      have hle : ∀ j ∈ N, y j ≤ y i := by
        intro j hj
        simp only [N, T, Finset.mem_insert, Finset.mem_filter] at hj
        rcases hj with rfl | ⟨hjS, _⟩
        · rfl
        · exact himax j hjS
      have hNsum : ∑ j ∈ N, y j ≤ (D + 1 : ℕ) * y i := by
        calc
          ∑ j ∈ N, y j ≤ N.card • y i :=
            Finset.sum_le_card_nsmul N (fun j => y j) (y i) hle
          _ ≤ (D + 1 : ℕ) • y i := nsmul_le_nsmul_left zero_le hNcard
          _ = (D + 1 : ℕ) * y i := by rw [nsmul_eq_mul]
      have hNS : N ⊆ S := by
        intro x hx
        simp only [N, T, Finset.mem_insert, Finset.mem_filter] at hx
        rcases hx with rfl | ⟨hxS, _⟩
        · exact hiS
        · exact hxS
      have hsubN : S \ N ⊂ S := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro hEq
        have hmem : i ∈ S \ N := by rw [hEq]; exact hiS
        exact (Finset.mem_sdiff.mp hmem).2 (by simp [N])
      have hdegSub : ∀ i ∈ S \ N, ((S \ N).filter (fun j => r j i)).card ≤ D := by
        intro i' hiSub
        have hi'S : i' ∈ S := (Finset.mem_sdiff.mp hiSub).1
        have hsubf : (S \ N).filter (fun j => r j i') ⊆ S.filter (fun j => r j i') := by
          intro j hj
          have hjf := Finset.mem_filter.mp hj
          exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hjf.1).1, hjf.2⟩
        exact le_trans (Finset.card_le_card hsubf) (hdegS i' hi'S)
      rcases ih (S \ N) hsubN hdegSub with ⟨A, hAsub, hApair, hAsum, hAcard⟩
      have hiNotA : i ∉ A := by
        intro hmem
        have hmem' : i ∈ S \ N := hAsub hmem
        exact (Finset.mem_sdiff.mp hmem').2 (by simp [N])
      have hnotI : ∀ a ∈ S \ N, ¬ r a i := by
        intro a haN hri
        have haS : a ∈ S := (Finset.mem_sdiff.mp haN).1
        exact (Finset.mem_sdiff.mp haN).2 (by simp [N, T, haS, hri])
      let ans : Finset ι := insert i A
      have hansSub : ans ⊆ S := by
        intro x hx
        rcases by simpa [ans] using hx with rfl | hxA
        · exact hiS
        · exact (Finset.mem_sdiff.mp (hAsub hxA)).1
      have hpair : (ans : Set ι).Pairwise (fun i j => ¬ r i j) := by
        intro a ha b hb hab
        have ha' : a = i ∨ a ∈ A := by
          simpa [ans, Finset.mem_insert, Finset.mem_coe] using ha
        have hb' : b = i ∨ b ∈ A := by
          simpa [ans, Finset.mem_insert, Finset.mem_coe] using hb
        rcases ha' with ha_eq | haA
        · rcases hb' with hb_eq | hbA
          · subst a; subst b; exact hirr i
          · subst a; exact fun hrib => hnotI b (hAsub hbA) (hsymm i b hrib)
        · rcases hb' with hb_eq | hbA
          · subst b; exact hnotI a (hAsub haA)
          · exact hApair haA hbA hab
      have hsumAns : ∑ j ∈ ans, y j = y i + ∑ j ∈ A, y j := by
        unfold ans; rw [Finset.sum_insert hiNotA]
      have hcardAns : ans.card = A.card + 1 := by
        unfold ans; rw [Finset.card_insert_of_notMem hiNotA]
      have hsplit : ∑ j ∈ S, y j = ∑ j ∈ N, y j + ∑ j ∈ S \ N, y j := by
        calc
          ∑ j ∈ S, y j = (∑ j ∈ S \ N, y j) + ∑ j ∈ N, y j :=
            (Finset.sum_sdiff (s₁ := N) (s₂ := S) (f := fun j => y j) hNS).symm
          _ = ∑ j ∈ N, y j + ∑ j ∈ S \ N, y j := by rw [add_comm]
      have hcardsplit : S.card = N.card + (S \ N).card := by
        rw [add_comm]
        exact (Finset.card_sdiff_add_card_eq_card hNS).symm
      have hfinal : ∑ j ∈ S, y j ≤ (D + 1 : ℕ) * ∑ j ∈ ans, y j := by
        rw [hsplit]
        calc
          ∑ j ∈ N, y j + ∑ j ∈ S \ N, y j ≤ (D + 1 : ℕ) * y i + (D + 1 : ℕ) * ∑ j ∈ A, y j :=
            add_le_add hNsum hAsum
          _ = (D + 1 : ℕ) * (y i + ∑ j ∈ A, y j) := by rw [mul_add]
          _ = (D + 1 : ℕ) * ∑ j ∈ ans, y j := by rw [hsumAns]
      have hfinalcard : S.card ≤ (D + 1) * ans.card := by
        rw [hcardsplit, hcardAns]
        calc
          N.card + (S \ N).card ≤ (D + 1) + (D + 1) * A.card :=
            Nat.add_le_add hNcard hAcard
          _ = (D + 1) * (A.card + 1) := by ring
      exact ⟨ans, hansSub, hpair, hfinal, hfinalcard⟩
  let hJ : ∀ i ∈ J, (J.filter (fun j => r j i)).card ≤ D := by
    intro i hiJ
    have hTset : (J.filter (fun j => r j i) : Set ι) = {j ∈ (J : Set ι) | r j i} := by
      ext j; simp
    have hcard : (J.filter (fun j => r j i)).card =
        (J.filter (fun j => r j i) : Set ι).ncard := by
      rw [Set.ncard_coe_finset]
    rw [hcard, hTset]
    exact hdeg i hiJ
  exact (Finset.strongInductionOn (p := q) J step) hJ

/-- If the original family has fullness `τ` and a subfamily retains at least a `1/(D+1)`
fraction of its shade mass, then the same subfamily has fullness at least `τ/(D+1)`.

This is the exact fullness cost of the weighted selector; it is independent of the geometric
argument that supplies the conflict degree and does not assert Frostman or Katz--Tao bounds. -/
theorem selectedFullness_mul_le_degreePlusOne_of_massRetention {ι : Type*}
    (J J' : Finset ι) (hJ' : J' ⊆ J) (D : ℕ) (τ : ℝ≥0∞)
    (carrierMass shadeMass : ι → ℝ≥0∞)
    (hfull : τ * (∑ j ∈ J, carrierMass j) ≤ ∑ j ∈ J, shadeMass j)
    (hmass : ∑ j ∈ J, shadeMass j ≤
      (D + 1 : ℕ) * ∑ j ∈ J', shadeMass j) :
    τ * (∑ j ∈ J', carrierMass j) ≤ (D + 1 : ℕ) * ∑ j ∈ J', shadeMass j := by
  have hcarrier : (∑ j ∈ J', carrierMass j) ≤ ∑ j ∈ J, carrierMass j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact hJ'
    · intro j hj hjnot
      exact bot_le
  calc
    τ * (∑ j ∈ J', carrierMass j) ≤ τ * (∑ j ∈ J, carrierMass j) := by gcongr
    _ ≤ ∑ j ∈ J, shadeMass j := hfull
    _ ≤ (D + 1 : ℕ) * ∑ j ∈ J', shadeMass j := hmass

/-- A local upper-mass estimate transfers to a selected subfamily with the same loss as
the retained total shade mass. `test` may encode balls or any other finite test region, and
`profile` records the scale dependence supplied by the caller. This theorem transfers the
caller-provided estimate; it does not establish a geometric Frostman hypothesis. -/
theorem selectedLocalMass_le_of_massRetention {ι σ : Type*} [DecidableEq ι]
    (J J' : Finset ι) (hJ' : J' ⊆ J) (D : ℕ) (shadeMass : ι → ℝ≥0∞)
    (test : σ → Finset ι) (profile : σ → ℝ≥0∞) (C : ℝ≥0∞)
    (hmass : ∑ j ∈ J, shadeMass j ≤
      (D + 1 : ℕ) * ∑ j ∈ J', shadeMass j)
    (hloc : ∀ s, ∑ j ∈ J.filter (· ∈ test s), shadeMass j ≤
      C * (∑ j ∈ J, shadeMass j) * profile s) :
    ∀ s, ∑ j ∈ J'.filter (· ∈ test s), shadeMass j ≤
      (D + 1 : ℕ) * C * (∑ j ∈ J', shadeMass j) * profile s := by
  intro s
  have hsubset : J'.filter (· ∈ test s) ⊆ J.filter (· ∈ test s) := by
    intro j hj
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨hJ' hj.1, hj.2⟩
  have htest : (∑ j ∈ J'.filter (· ∈ test s), shadeMass j) ≤
      ∑ j ∈ J.filter (· ∈ test s), shadeMass j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro j hj hjnot
    exact bot_le
  calc
    (∑ j ∈ J'.filter (· ∈ test s), shadeMass j) ≤
      ∑ j ∈ J.filter (· ∈ test s), shadeMass j := htest
    _ ≤ C * (∑ j ∈ J, shadeMass j) * profile s := hloc s
    _ ≤ C * ((D + 1 : ℕ) * ∑ j ∈ J', shadeMass j) * profile s := by gcongr
    _ = (D + 1 : ℕ) * C * (∑ j ∈ J', shadeMass j) * profile s := by ac_rfl

/-- A bounded-degree conflict selector can simultaneously preserve pairwise conflict-freeness,
shade mass, cardinality, and an explicit fullness lower bound. The mass and fullness losses are
both exactly recorded with the factor `D + 1`; no geometric conflict-degree estimate is assumed. -/
theorem exists_pairwise_conflictFree_retaining_weight_card_and_fullness {ι : Type*}
    (J : Finset ι) (r : ι → ι → Prop)
    (hsymm : ∀ i j, r i j → r j i) (hirr : ∀ i, ¬ r i i)
    {D : ℕ} (hdeg : ∀ i ∈ J, {j ∈ (J : Set ι) | r j i}.ncard ≤ D)
    (shadeMass carrierMass : ι → ℝ≥0∞) (τ : ℝ≥0∞)
    (hfull : τ * (∑ j ∈ J, carrierMass j) ≤ ∑ j ∈ J, shadeMass j) :
    ∃ J' ⊆ J,
      (J' : Set ι).Pairwise (fun i j => ¬ r i j) ∧
      ∑ j ∈ J, shadeMass j ≤ (D + 1 : ℕ) * ∑ j ∈ J', shadeMass j ∧
      J.card ≤ (D + 1) * J'.card ∧
      τ * (∑ j ∈ J', carrierMass j) ≤ (D + 1 : ℕ) * ∑ j ∈ J', shadeMass j := by
  obtain ⟨J', hsub, hpair, hmass, hcard⟩ :=
    exists_pairwise_conflictFree_retaining_weight_and_card J r hsymm hirr hdeg shadeMass
  exact ⟨J', hsub, hpair, hmass, hcard,
    selectedFullness_mul_le_degreePlusOne_of_massRetention J J' hsub D τ
      carrierMass shadeMass hfull hmass⟩

end Kakeya4.Construction

end
