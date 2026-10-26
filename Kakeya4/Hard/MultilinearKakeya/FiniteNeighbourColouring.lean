import Kakeya4.Hard.MultilinearKakeya.Basic

/-! The finite vertex-colouring step for a symmetric irreflexive relation.
The palette size is controlled by the number of neighbours, not by the total
number of vertices. -/

noncomputable section
open Set

namespace Kakeya4.Hard.MultilinearKakeya

theorem finite_neighbour_colouring {ι : Type*} [Fintype ι]
    (R : ι → ι → Prop) [DecidableRel R] (hirr : ∀ i, ¬ R i i) (hsym : ∀ i j, R i j → R j i)
    (N : ℕ) (hdegree : ∀ i, Fintype.card {j | R i j} ≤ N) :
    ∃ colour : ι → Fin (N+1), ∀ i j, R i j → colour i ≠ colour j := by
  classical
  have hfinite (s : Finset ι) : ∃ colour : ι → Fin (N+1),
      ∀ i ∈ s, ∀ j ∈ s, R i j → colour i ≠ colour j := by
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => 0, by simp⟩
    | @insert a s has ih =>
      obtain ⟨colour, hc⟩ := ih
      let blocked := (Finset.univ.filter (R a)).image colour
      have hb : blocked.card < (Finset.univ : Finset (Fin (N+1))).card := by
        calc
          blocked.card ≤ (Finset.univ.filter (R a)).card := Finset.card_image_le
          _ ≤ N := by simpa [Fintype.card_subtype] using hdegree a
          _ < _ := by simp
      obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hb
      have havoid (j : ι) (hj : R a j) : b ≠ colour j := by
        intro he
        apply hb
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩, he.symm⟩
      refine ⟨Function.update colour a b, ?_⟩
      intro i hi j hj hij
      by_cases hia : i = a
      · subst i
        have hja : j ≠ a := by intro he; subst j; exact hirr a hij
        simpa only [Function.update_self, Function.update_of_ne hja] using havoid j hij
      · by_cases hja : j = a
        · subst j
          have hne := havoid i (hsym i a hij)
          simpa only [Function.update_self, Function.update_of_ne hia] using hne.symm
        · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hia
          have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hja
          simpa only [Function.update_of_ne hia, Function.update_of_ne hja] using hc i his j hjs hij
  obtain ⟨colour, hc⟩ := hfinite Finset.univ
  exact ⟨colour, fun i j hij => hc i (Finset.mem_univ i) j (Finset.mem_univ j) hij⟩

end Kakeya4.Hard.MultilinearKakeya
