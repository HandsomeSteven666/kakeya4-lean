import Kakeya4.Hard.RestrictedTriple.Rounding

/-! Exact fixed-factor entropy comparison for arbitrary sets, including infinite counts. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem exists_quarter_interval_center {r t : ℝ} (hr : 0 ≤ r) (ht : |t| ≤ 2*r) :
    ∃ j : Fin 4, |t-((j:ℝ)-3/2)*r| ≤ r/2 := by
  have ht' := abs_le.mp ht
  by_cases h1 : t ≤ -r
  · refine ⟨0, ?_⟩
    norm_num
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  by_cases h2 : t ≤ 0
  · refine ⟨1, ?_⟩
    norm_num
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  by_cases h3 : t ≤ r
  · refine ⟨2, ?_⟩
    norm_num
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · refine ⟨3, ?_⟩
    norm_num
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- An external optimal cover exists even when its cardinality is infinite. -/
theorem exists_external_optimal_cover {X : Type*} [PseudoEMetricSpace X]
    (e : ℝ≥0) (E : Set X) :
    ∃ Q : Set X, IsCover e E Q ∧ Q.encard = externalCoveringNumber e E := by
  have : Nonempty {Q : Set X // IsCover e E Q} := by
    refine ⟨⟨univ, ?_⟩⟩
    intro x _hx
    exact ⟨x, mem_univ _, by simp⟩
  obtain ⟨Q, hQ⟩ := ENat.exists_eq_iInf
    (fun Q : {Q : Set X // IsCover e E Q} ↦ Q.val.encard)
  refine ⟨Q.val, Q.property, ?_⟩
  rw [hQ]
  simp only [iInf_subtype, externalCoveringNumber]

/-- A side-4r cube can be covered by 4^dimension side-r cubes; centres remain external. -/
theorem cubeCover_le_four_pow_mul {ι : Type*} [Fintype ι] {r : ℝ}
    (hr : 0 ≤ r) (E : Set (ι → ℝ)) :
    cubeCover r E ≤ (4:ℝ≥0∞)^(Fintype.card ι)*cubeCover (4*r) E := by
  classical
  obtain ⟨Q, hQ, hcard⟩ := exists_external_optimal_cover (Real.toNNReal ((4*r)/2)) E
  let refineCenter : ((ι → ℝ) × (ι → Fin 4)) → ι → ℝ :=
    fun q i ↦ q.1 i + ((q.2 i:ℝ)-3/2)*r
  let R : Set (ι → ℝ) := refineCenter '' (Q ×ˢ (univ : Set (ι → Fin 4)))
  have hcover : IsCover (Real.toNNReal (r/2)) E R := by
    intro x hx
    obtain ⟨q, hq, hd⟩ := hQ hx
    change edist x q ≤ (Real.toNNReal ((4*r)/2) : ℝ≥0∞) at hd
    have hd' : dist x q ≤ 2*r := by
      have hh : dist x q ≤ (4*r)/2 := (edist_le_ofReal (by positivity)).mp (by
        simpa only [ENNReal.coe_nnreal_eq,
          Real.coe_toNNReal _ (show 0 ≤ (4*r)/2 by positivity)] using hd)
      linarith
    have hcoords (i : ι) : ∃ j : Fin 4, |(x i-q i)-((j:ℝ)-3/2)*r| ≤ r/2 := by
      apply exists_quarter_interval_center hr
      simpa only [Real.dist_eq] using (dist_le_pi_dist x q i).trans hd'
    choose js hjs using hcoords
    refine ⟨refineCenter (q,js), ⟨(q,js), ⟨hq, mem_univ _⟩, rfl⟩, ?_⟩
    change edist x (refineCenter (q,js)) ≤ (Real.toNNReal (r/2) : ℝ≥0∞)
    have hh : dist x (refineCenter (q,js)) ≤ r/2 := by
      apply (dist_pi_le_iff (by positivity)).mpr
      intro i
      have heq : x i-refineCenter (q,js) i = (x i-q i)-((js i:ℝ)-3/2)*r := by
        dsimp [refineCenter]
        ring
      simpa only [Real.dist_eq, heq] using hjs i
    have hh' := (edist_le_ofReal (show 0 ≤ r/2 by positivity)).mpr hh
    simpa only [ENNReal.coe_nnreal_eq,
      Real.coe_toNNReal _ (show 0 ≤ r/2 by positivity)] using hh'
  have hR : R.encard ≤ Q.encard * (4:ℕ∞)^(Fintype.card ι) := by
    have hh := encard_image_le refineCenter (Q ×ˢ (univ : Set (ι → Fin 4)))
    simpa [R, encard_prod, encard_univ, ENat.card_eq_coe_fintype_card] using hh
  have hh := ENat.toENNReal_mono (hcover.externalCoveringNumber_le_encard.trans hR)
  simpa only [cubeCover, ENat.toENNReal_mul, ENat.toENNReal_pow, ENat.toENNReal_ofNat,
    hcard, mul_comm] using hh

theorem tripleCover_le_4096_mul_four_scale (r : ℝ) (hr : 0 ≤ r) (H : Set Triple) :
    tripleCover r H ≤ 4096*tripleCover (4*r) H := by
  have hh := cubeCover_le_four_pow_mul hr (tripleCoordinates '' H)
  norm_num at hh
  exact hh

end Kakeya4.Hard.RestrictedTriple
