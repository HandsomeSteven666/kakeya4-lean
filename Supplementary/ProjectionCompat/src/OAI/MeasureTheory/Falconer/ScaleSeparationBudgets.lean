import OAI.MeasureTheory.Falconer.UniformRadialBootstrapEndpoint

/-! Concrete ingredients for scale-dependent separation. The first lemma
adapts Radial/RadialPairSeparation.original_close_pair_mass from OpenAI math,
Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a, to two laws.
Complete original license: COPYING. Other proofs use the already imported
normalization and exact zoom APIs; no upstream checkout is modified.
These ingredients do not yet assert a separated product-cell partition. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal

theorem original_two_law_close_pair_mass {d : ℕ}
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [SFinite ν]
    (r : ℝ) (K : ℝ≥0∞) (hball : ∀ x, ν (ball x r) ≤ K) :
    (μ.prod ν) {p : Space d × Space d | dist p.1 p.2 < r} ≤ K := by
  have hS : MeasurableSet {p : Space d × Space d | dist p.1 p.2 < r} :=
    measurableSet_lt (by fun_prop) measurable_const
  rw [Measure.prod_apply hS]
  calc
    _ ≤ ∫⁻ _x, K ∂μ := lintegral_mono (fun x => by
      simpa only [preimage_ofPred_eq,Metric.ball,dist_comm] using hball x)
    _ = _ := by simp

theorem exists_relative_separated_pairs {d : ℕ}
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [SFinite ν]
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    {r α C : ℝ} (hr : 0 < r) (hfrost : FrostmanBallBound ν α C) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (∀ z ∈ H, r ≤ dist z.1 z.2) ∧
      (μ.prod ν) (G \ H) ≤ ENNReal.ofReal (C*r^α) := by
  let H := G ∩ {z : Space d × Space d | r ≤ dist z.1 z.2}
  have hH : MeasurableSet H := hG.inter (measurableSet_le measurable_const (by fun_prop))
  refine ⟨H,hH,inter_subset_left,fun z hz => hz.2,?_⟩
  apply (measure_mono (show G \ H ⊆ {z | dist z.1 z.2 < r} from ?_)).trans
    (original_two_law_close_pair_mass μ ν r _ (fun x => hfrost x r hr))
  intro z hz
  by_contra hn
  change ¬ dist z.1 z.2 < r at hn
  have hsep : r ≤ dist z.1 z.2 := le_of_not_gt hn
  exact hz.2 ⟨hz.1,hsep⟩

theorem normalized_restriction_full_frostman {d : ℕ}
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (A : Set (Space d)) (hA : MeasurableSet A)
    (hpos : (μ.restrict A) univ ≠ 0)
    {L C α : ℝ} (hL : 0 < L) (hmass : ENNReal.ofReal L ≤ μ A)
    (hfrost : FrostmanBallBound μ α C) :
    FrostmanBallBound (normalizedSliceLaw (μ.restrict A) hpos : Measure (Space d)) α (C/L) := by
  intro x r hr
  have hmass' : ENNReal.ofReal L ≤ (μ.restrict A) univ := by simpa using hmass
  have hb : (μ.restrict A) (ball x r) ≤ ENNReal.ofReal (C*r^α) :=
    (Measure.restrict_le_self (ball x r)).trans (hfrost x r hr)
  apply (normalizedSliceLaw_bound (μ.restrict A) hpos (ball x r) hmass' hb).trans_eq
  rw [← ENNReal.ofReal_inv_of_pos hL,← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem normalized_restriction_zoom_frostman {d : ℕ}
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (A : Set (Space d)) (hA : MeasurableSet A)
    (hpos : (μ.restrict A) univ ≠ 0)
    {L C α a : ℝ} (hL : 0 < L) (hmass : ENNReal.ofReal L ≤ μ A)
    (ha : 0 < a) (center : Space d) (hfrost : FrostmanBallBound μ α C) :
    FrostmanBallBound (Measure.map (radialZoom a ha.ne' center)
      (normalizedSliceLaw (μ.restrict A) hpos : Measure (Space d))) α ((C/L)*a^(-α)) :=
  radialZoom_full_frostman _ ha center
    (normalized_restriction_full_frostman μ A hA hpos hL hmass hfrost)

theorem normalized_restriction_zoom_scale_budget {d : ℕ}
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (A : Set (Space d)) (hA : MeasurableSet A)
    (hpos : (μ.restrict A) univ ≠ 0)
    {R ε κ L C α a : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hL : 0 < L) (hmass : ENNReal.ofReal L ≤ μ A)
    (hCbudget : C ≤ R^ε) (hLbudget : R^(-κ) ≤ L)
    (ha : 0 < a) (ha1 : 1 ≤ a) (center : Space d)
    (hfrost : FrostmanBallBound μ α C) :
    FrostmanBallBound (Measure.map (radialZoom a ha.ne' center)
      (normalizedSliceLaw (μ.restrict A) hpos : Measure (Space d))) α (R^(ε+κ)) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hInv : L⁻¹ ≤ R^κ := calc
    _ ≤ (R^(-κ))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hR0 _) hLbudget
    _ = _ := by rw [Real.rpow_neg hR0.le,inv_inv]
  have hcoef : (C/L)*a^(-α) ≤ R^(ε+κ) := calc
    _ ≤ C/L := mul_le_of_le_one_right (div_nonneg hC hL.le)
      (Real.rpow_le_one_of_one_le_of_nonpos ha1 (neg_nonpos.mpr hα))
    _ = C*L⁻¹ := div_eq_mul_inv _ _
    _ ≤ R^ε*R^κ := mul_le_mul hCbudget hInv (inv_nonneg.mpr hL.le) (Real.rpow_nonneg hR0.le _)
    _ = _ := (Real.rpow_add hR0 _ _).symm
  intro x r hr
  exact (normalized_restriction_zoom_frostman μ A hA hpos hL hmass ha center hfrost x r hr).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hr.le _)))

#print axioms original_two_law_close_pair_mass
#print axioms exists_relative_separated_pairs
#print axioms normalized_restriction_full_frostman
#print axioms normalized_restriction_zoom_frostman
#print axioms normalized_restriction_zoom_scale_budget
end OAI.Falconer
