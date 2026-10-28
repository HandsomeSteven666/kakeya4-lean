import Kakeya4.Hard.RestrictedTriple.StripProjectionEntropy

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal BigOperators Classical

namespace Kakeya4.Hard.RestrictedTriple

theorem exists_finite_euclidean_net (E : Finset Plane) {s : ℝ} (hs : 0 < s) :
    ∃ P : Finset Plane, P ⊆ E ∧ IsSeparated (Real.toNNReal s) (P : Set Plane) ∧
      ∀ x ∈ E, ∃ y ∈ P, dist x y ≤ s := by
  classical
  have hEcard : (E : Set Plane).encard ≠ ⊤ := by simp
  have hpack : packingNumber (Real.toNNReal s) (E : Set Plane) ≠ ⊤ :=
    ne_top_of_le_ne_top hEcard (packingNumber_le_encard_self (E : Set Plane))
  let A := maximalSeparatedSet (Real.toNNReal s) (E : Set Plane)
  have hAE : A ⊆ (E : Set Plane) := maximalSeparatedSet_subset
  have hA : A.Finite := E.finite_toSet.subset hAE
  refine ⟨hA.toFinset,?_,?_,?_⟩
  · intro x hx
    exact hAE (hA.mem_toFinset.mp hx)
  · simpa only [hA.coe_toFinset] using (isSeparated_maximalSeparatedSet (ε := Real.toNNReal s) (A := (E : Set Plane)))
  · intro x hx
    obtain ⟨y,hy,hd⟩ := isCover_maximalSeparatedSet hpack hx
    change edist x y ≤ (Real.toNNReal s : ℝ≥0∞) at hd
    refine ⟨y,hA.mem_toFinset.mpr hy,?_⟩
    apply (edist_le_ofReal hs.le).mp
    simpa only [ENNReal.coe_nnreal_eq,Real.coe_toNNReal _ hs.le] using hd

/-- A genuinely large fiber of a normalized Frostman set has many separated representatives. -/
theorem exists_Frostman_fiber_packing {p s K c : ℝ} (hp : 0 < p) (hps : p ≤ s)
    (hK : 0 < K) (G E : Finset Plane) (hG : G.Nonempty) (hEG : E ⊆ G)
    (hmass : c*(G.card : ℝ) ≤ E.card) (hF : finiteFrostman p K G) :
    ∃ P : Finset Plane, P ⊆ E ∧ IsSeparated (Real.toNNReal s) (P : Set Plane) ∧
      c/(K*s) ≤ (P.card : ℝ) := by
  classical
  have hs : 0 < s := hp.trans_le hps
  obtain ⟨P,hPE,hsep,hcover⟩ := exists_finite_euclidean_net E hs
  have hsub : E ⊆ P.biUnion (fun y ↦ G.filter (fun x ↦ dist y x ≤ s)) := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨y,hy,Finset.mem_filter.mpr ⟨hEG hx,by rwa [dist_comm]⟩⟩
  have hcountNat := (Finset.card_le_card hsub).trans
    (Finset.card_biUnion_le (s := P) (t := fun y ↦ G.filter (fun x ↦ dist y x ≤ s)))
  have hcount : (E.card : ℝ) ≤ ∑ y ∈ P, ((G.filter (fun x ↦ dist y x ≤ s)).card : ℝ) := by
    exact_mod_cast hcountNat
  have hsum : (E.card : ℝ) ≤ (P.card : ℝ)*(K*s*(G.card : ℝ)) := by
    calc
      _ ≤ _ := hcount
      _ ≤ ∑ _y ∈ P, K*s*(G.card : ℝ) := Finset.sum_le_sum (fun y _ ↦ hF y s hps)
      _ = _ := by simp
  have hGpos : (0:ℝ) < G.card := by exact_mod_cast Finset.card_pos.mpr hG
  have hmass' : c ≤ (P.card : ℝ)*(K*s) := by
    have hh : c*(G.card : ℝ) ≤ ((P.card : ℝ)*(K*s))*(G.card : ℝ) := by
      nlinarith [hmass.trans hsum]
    exact le_of_mul_le_mul_right hh hGpos
  exact ⟨P,hPE,hsep,(div_le_iff₀ (mul_pos hK hs)).mpr (by nlinarith)⟩

/-- Quantitative growth of the actual translated dot image, from an actual large fiber.
This is a proved projection bound, not an assumed expansion branch. -/
theorem strip_fiber_projection_growth {p t K c : ℝ} (hp : 0 < p) (ht : 0 < t)
    (hpt : p ≤ 2*t) (hK : 0 < K) (L : AffineLine) (a b : Plane)
    (ha : ‖a‖ ≤ 1) (hA : 0 < |inner ℝ a L.direction|)
    (G E : Finset Plane) (hG : G.Nonempty) (hEG : E ⊆ G)
    (hmass : c*(G.card : ℝ) ≤ E.card) (hF : finiteFrostman p K G)
    (hstrip : ∀ x ∈ E, x ∈ lineNeighborhood t L) :
    ENNReal.ofReal (c*|inner ℝ a L.direction|/(8*K*t)) ≤
      intervalCover (2*t) ((fun x : Plane ↦ inner ℝ a (x-b)) '' (E : Set Plane)) := by
  have hA1 : |inner ℝ a L.direction| ≤ 1 := by
    have hh := abs_real_inner_le_norm a L.direction
    rw [L.direction_unit,mul_one] at hh
    exact hh.trans ha
  have hps : p ≤ 8*t/|inner ℝ a L.direction| := (le_div_iff₀ hA).mpr (by nlinarith)
  obtain ⟨P,hPE,hsep,hcard⟩ := exists_Frostman_fiber_packing hp hps hK G E hG hEG hmass hF
  have hidentity : c/(K*(8*t/|inner ℝ a L.direction|)) = c*|inner ℝ a L.direction|/(8*K*t) := by
    field_simp
    <;> ring
  rw [hidentity] at hcard
  have hh := ENNReal.ofReal_le_ofReal hcard
  rw [ENNReal.ofReal_natCast] at hh
  exact hh.trans (strip_projection_image_card_le_cover ht L a b ha hA P (E : Set Plane)
    (show (P : Set Plane) ⊆ (E : Set Plane) from hPE) (fun x hx ↦ hstrip x (hPE hx)) hsep)

end Kakeya4.Hard.RestrictedTriple
