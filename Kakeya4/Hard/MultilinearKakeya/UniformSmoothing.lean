import Kakeya4.Hard.MultilinearKakeya.PolynomialBisection

/-! Uniform saturation of polynomial arctangent smoothing on compact nonzero
coefficient families. A common parameter is obtained by dominated convergence
and Dini's theorem, without interchanging pointwise and uniform quantifiers. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace Kakeya4.Hard.MultilinearKakeya

def arctanGap (m : ℕ) (s : ℝ) : ℝ :=
  Real.pi / 2 - Real.arctan (((m : ℝ)+1) * |s|)

theorem continuous_arctanGap (m : ℕ) : Continuous (arctanGap m) := by
  unfold arctanGap
  fun_prop

theorem arctanGap_nonneg (m : ℕ) (s : ℝ) : 0 ≤ arctanGap m s :=
  sub_nonneg.mpr (Real.arctan_lt_pi_div_two _).le

theorem norm_arctanGap_le (m : ℕ) (s : ℝ) : ‖arctanGap m s‖ ≤ Real.pi/2 := by
  rw [Real.norm_of_nonneg (arctanGap_nonneg m s)]
  exact sub_le_self _ (Real.arctan_nonneg.mpr (by positivity))

theorem antitone_arctanGap (s : ℝ) : Antitone (fun m => arctanGap m s) := by
  intro i j hij
  apply sub_le_sub_left (Real.arctan_mono ?_)
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg s)
  have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  linarith only [hijR]

theorem tendsto_arctanGap_zero {s : ℝ} (hs : s ≠ 0) :
    Tendsto (fun m => arctanGap m s) atTop (𝓝 0) := by
  have hscale : Tendsto (fun m : ℕ => (m : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun _ => by linarith) tendsto_natCast_atTop_atTop
  have harg := hscale.atTop_mul_const (abs_pos.mpr hs)
  have hat := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp harg
  simpa only [arctanGap, sub_self, Function.comp_def] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.pi/2) atTop (𝓝 (Real.pi/2))).sub hat

theorem integrable_arctanGap {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f) (m : ℕ) :
    Integrable (fun x => arctanGap m (f x)) μ :=
  (integrable_const (Real.pi/2)).mono'
    (((continuous_arctanGap m).measurable.comp hf).aestronglyMeasurable)
    (Eventually.of_forall (fun x => norm_arctanGap_le m (f x)))

theorem antitone_integral_arctanGap {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f) :
    Antitone (fun m => ∫ x, arctanGap m (f x) ∂μ) := by
  intro i j hij
  exact integral_mono (integrable_arctanGap μ f hf j) (integrable_arctanGap μ f hf i)
    (fun x => antitone_arctanGap (f x) hij)

theorem tendsto_integral_arctanGap_zero {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f) (hz : ∀ᵐ x ∂μ, f x ≠ 0) :
    Tendsto (fun m => ∫ x, arctanGap m (f x) ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (f := fun _ => (0 : ℝ))
    (fun _ => Real.pi/2)
    (fun m => ((continuous_arctanGap m).measurable.comp hf).aestronglyMeasurable)
    (integrable_const _) (fun m => Eventually.of_forall (fun x => norm_arctanGap_le m (f x)))
    (hz.mono (fun x hx => tendsto_arctanGap_zero hx))
  simpa only [integral_zero, Function.comp_def] using h

theorem continuous_integral_arctanGap {X α : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : X → α → ℝ) (hf : ∀ a, Measurable (f a))
    (hc : ∀ x, Continuous (fun a => f a x)) (m : ℕ) :
    Continuous (fun a => ∫ x, arctanGap m (f a x) ∂μ) := by
  apply continuous_of_dominated (bound := fun _ => Real.pi/2)
  · intro a
    exact ((continuous_arctanGap m).measurable.comp (hf a)).aestronglyMeasurable
  · exact fun a => Eventually.of_forall (fun x => norm_arctanGap_le m (f a x))
  · exact integrable_const _
  · exact Eventually.of_forall (fun x => (continuous_arctanGap m).comp (hc x))

theorem tendstoUniformlyOn_integral_arctanGap_zero {X α : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : X → α → ℝ) (hf : ∀ a, Measurable (f a))
    (hc : ∀ x, Continuous (fun a => f a x)) {S : Set X} (hS : IsCompact S)
    (hz : ∀ a ∈ S, ∀ᵐ x ∂μ, f a x ≠ 0) :
    TendstoUniformlyOn (fun m a => ∫ x, arctanGap m (f a x) ∂μ) (fun _ => 0) atTop S := by
  apply Antitone.tendstoUniformlyOn_of_forall_tendsto hS
    (fun m => (continuous_integral_arctanGap μ f hf hc m).continuousOn)
    (fun a _ => antitone_integral_arctanGap μ (f a) (hf a)) continuousOn_const
  exact fun a ha => tendsto_integral_arctanGap_zero μ (f a) (hf a) (hz a ha)

def polynomialSmoothingError {n : ℕ} (μ : Measure (Fin n → ℝ)) (m : ℕ)
    (P : MvPolynomial (Fin n) ℝ) : ℝ := ∫ x, arctanGap m (MvPolynomial.eval x P) ∂μ

theorem polynomialSmoothingError_nonneg {n : ℕ} (μ : Measure (Fin n → ℝ))
    (m : ℕ) (P : MvPolynomial (Fin n) ℝ) : 0 ≤ polynomialSmoothingError μ m P :=
  integral_nonneg (fun x => arctanGap_nonneg m (MvPolynomial.eval x P))

theorem tendstoUniformlyOn_polynomialSmoothingError {n k : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] (hac : μ ≪ volume)
    {S : Set (E k)} (hS : IsCompact S) (hzero : ∀ u ∈ S, u ≠ 0) :
    TendstoUniformlyOn (fun m u => polynomialSmoothingError μ m (coefficientPolynomial B u))
      (fun _ => 0) atTop S := by
  apply tendstoUniformlyOn_integral_arctanGap_zero μ
    (fun u x => MvPolynomial.eval x (coefficientPolynomial B u))
    (fun u => (MvPolynomial.continuous_eval _).measurable)
    (fun x => continuous_eval_coefficientPolynomial B x) hS
  intro u hu
  exact measure_eq_zero_iff_ae_notMem.mp
    (hac (real_polynomial_zero_volume _ (coefficientPolynomial_ne_zero B hB u (hzero u hu))))

theorem eventually_polynomialSmoothingError_lt {n k : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] (hac : μ ≪ volume)
    {S : Set (E k)} (hS : IsCompact S) (hzero : ∀ u ∈ S, u ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ m in atTop, ∀ u ∈ S, polynomialSmoothingError μ m (coefficientPolynomial B u) < η := by
  have h := (Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_polynomialSmoothingError B hB μ hac hS hzero)) η hη
  apply h.mono
  intro m hm u hu
  have he := hm u hu
  rw [dist_zero_left, Real.norm_eq_abs] at he
  exact (le_abs_self _).trans_lt he

theorem exists_common_polynomialSmoothing_index {n k : ℕ} {ι : Type*} [Fintype ι]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (μ : ι → Measure (Fin n → ℝ)) (hfin : ∀ i, IsFiniteMeasure (μ i))
    (hac : ∀ i, μ i ≪ volume) {S : Set (E k)} (hS : IsCompact S)
    (hzero : ∀ u ∈ S, u ≠ 0) (η : ι → ℝ) (hη : ∀ i, 0 < η i) :
    ∃ M : ℕ, ∀ i, ∀ u ∈ S,
      polynomialSmoothingError (μ i) M (coefficientPolynomial B u) < η i := by
  have hi (i : ι) : ∀ᶠ m in atTop, ∀ u ∈ S,
      polynomialSmoothingError (μ i) m (coefficientPolynomial B u) < η i := by
    let := hfin i
    exact eventually_polynomialSmoothingError_lt B hB (μ i) (hac i) hS hzero (hη i)
  exact (eventually_all.mpr hi).exists

theorem exists_common_polynomialSmoothing_index_sphere {n k : ℕ} {ι : Type*} [Fintype ι]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (μ : ι → Measure (Fin n → ℝ)) (hfin : ∀ i, IsFiniteMeasure (μ i))
    (hac : ∀ i, μ i ≪ volume) (η : ι → ℝ) (hη : ∀ i, 0 < η i) :
    ∃ M : ℕ, ∀ i, ∀ u ∈ Metric.sphere (0 : E k) 1,
      polynomialSmoothingError (μ i) M (coefficientPolynomial B u) < η i := by
  apply exists_common_polynomialSmoothing_index B hB μ hfin hac (isCompact_sphere _ _) ?_ η hη
  intro u hu hz
  subst u
  simp at hu

def smoothingScale (m : ℕ) : ℝ := ((m : ℝ)+1)⁻¹

theorem smoothingScale_pos (m : ℕ) : 0 < smoothingScale m := by
  unfold smoothingScale
  positivity

theorem arctan_abs_eq_abs (s : ℝ) : Real.arctan |s| = |Real.arctan s| := by
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs, abs_of_nonneg (Real.arctan_nonneg.mpr hs)]
  · have hs' : s ≤ 0 := le_of_lt (lt_of_not_ge hs)
    rw [abs_of_nonpos hs', Real.arctan_neg, abs_of_nonpos (Real.arctan_le_zero.mpr hs')]

theorem arctanGap_eq_smoothing_error (m : ℕ) (s : ℝ) :
    arctanGap m s = Real.pi/2 - |Real.arctan (s / smoothingScale m)| := by
  rw [← arctan_abs_eq_abs]
  unfold arctanGap smoothingScale
  simp only [div_inv_eq_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ)+1)]
  rw [mul_comm |s|]

theorem pi_div_four_le_arctanGap_of_small (m : ℕ) {s : ℝ}
    (hs : |s| ≤ smoothingScale m) : Real.pi/4 ≤ arctanGap m s := by
  have harg : ((m : ℝ)+1) * |s| ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ (m : ℝ)+1)
    simpa only [smoothingScale, mul_inv_cancel₀ (by positivity : (m : ℝ)+1 ≠ 0)] using h
  have hat := Real.arctan_mono harg
  rw [Real.arctan_one] at hat
  unfold arctanGap
  linarith

theorem measure_small_polynomial_values_le_error {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] (P : MvPolynomial (Fin n) ℝ) (m : ℕ) :
    μ {x | |MvPolynomial.eval x P| ≤ smoothingScale m} ≤
      ENNReal.ofReal ((4 / Real.pi) * polynomialSmoothingError μ m P) := by
  let g : (Fin n → ℝ) → ℝ := fun x => (4 / Real.pi) * arctanGap m (MvPolynomial.eval x P)
  have hgmeas : Measurable g := by
    exact measurable_const.mul ((continuous_arctanGap m).measurable.comp
      (MvPolynomial.continuous_eval P).measurable)
  have hgnonneg (x) : 0 ≤ g x := mul_nonneg (by positivity) (arctanGap_nonneg _ _)
  have hgi : Integrable g μ :=
    (integrable_arctanGap μ _ (MvPolynomial.continuous_eval P).measurable m).const_mul _
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
      apply meas_le_lintegral₀ hgmeas.ennreal_ofReal.aemeasurable
      intro x hx
      have hxg := mul_le_mul_of_nonneg_left (pi_div_four_le_arctanGap_of_small m hx)
        (by positivity : (0 : ℝ) ≤ 4 / Real.pi)
      have heq : (4 / Real.pi) * (Real.pi/4) = 1 := by field_simp
      rw [heq] at hxg
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hxg
    _ = ENNReal.ofReal (∫ x, g x ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall hgnonneg)).symm
    _ = _ := by rw [show (∫ x, g x ∂μ) =
        (4 / Real.pi) * polynomialSmoothingError μ m P from integral_const_mul _ _]

theorem exists_common_smoothingScale_small_values {n k : ℕ} {ι : Type*} [Fintype ι]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (μ : ι → Measure (Fin n → ℝ)) (hfin : ∀ i, IsFiniteMeasure (μ i))
    (hac : ∀ i, μ i ≪ volume) {S : Set (E k)} (hS : IsCompact S)
    (hzero : ∀ u ∈ S, u ≠ 0) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ∀ u ∈ S,
      μ i {x | |MvPolynomial.eval x (coefficientPolynomial B u)| ≤ ε} ≤ ENNReal.ofReal (δ i) := by
  obtain ⟨M, hM⟩ := exists_common_polynomialSmoothing_index B hB μ hfin hac hS hzero
    (fun i => (Real.pi/4) * δ i) (fun i => mul_pos (by positivity) (hδ i))
  refine ⟨smoothingScale M, smoothingScale_pos M, fun i u hu => ?_⟩
  let := hfin i
  apply (measure_small_polynomial_values_le_error (μ i) (coefficientPolynomial B u) M).trans
  apply ENNReal.ofReal_le_ofReal
  have h := mul_lt_mul_of_pos_left (hM i u hu) (by positivity : (0 : ℝ) < 4/Real.pi)
  have heq : (4 / Real.pi) * ((Real.pi/4) * δ i) = δ i := by field_simp
  rw [heq] at h
  exact h.le

theorem exists_common_smoothingScale_regions {n k : ℕ} {ι : Type*} [Fintype ι]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (A : ι → Set (Fin n → ℝ)) (hA : ∀ i, volume (A i) < ⊤)
    {S : Set (E k)} (hS : IsCompact S) (hzero : ∀ u ∈ S, u ≠ 0)
    (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ∀ u ∈ S,
      volume (A i ∩ {x | |MvPolynomial.eval x (coefficientPolynomial B u)| ≤ ε}) ≤
        ENNReal.ofReal (δ i) := by
  let μ : ι → Measure (Fin n → ℝ) := fun i => volume.restrict (A i)
  have hfin (i : ι) : IsFiniteMeasure (μ i) := isFiniteMeasure_restrict.mpr (hA i).ne
  obtain ⟨ε, hε, h⟩ := exists_common_smoothingScale_small_values B hB μ hfin
    (fun _ => Measure.absolutelyContinuous_restrict) hS hzero δ hδ
  refine ⟨ε, hε, fun i u hu => ?_⟩
  have hi := h i u hu
  have hm : MeasurableSet {x | |MvPolynomial.eval x (coefficientPolynomial B u)| ≤ ε} :=
    (isClosed_le (MvPolynomial.continuous_eval _).abs continuous_const).measurableSet
  dsimp [μ] at hi
  rwa [Measure.restrict_apply hm, inter_comm] at hi

theorem exists_common_smoothingScale_regions_sphere {n k : ℕ} {ι : Type*} [Fintype ι]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (A : ι → Set (Fin n → ℝ)) (hA : ∀ i, volume (A i) < ⊤)
    (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ∀ u ∈ Metric.sphere (0 : E k) 1,
      volume (A i ∩ {x | |MvPolynomial.eval x (coefficientPolynomial B u)| ≤ ε}) ≤
        ENNReal.ofReal (δ i) := by
  apply exists_common_smoothingScale_regions B hB A hA (isCompact_sphere _ _) ?_ δ hδ
  intro u hu hz
  subst u
  simp at hu

theorem negative_half_mass_le_smoothed_mass_add_error {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) {ε : ℝ} (hε : 0 < ε) (δ : ℝ)
    (hhalf : μ {x | f x ≤ 0} = μ univ / 2)
    (hsmall : μ {x | |f x| ≤ ε} ≤ ENNReal.ofReal δ) :
    μ univ / 2 ≤ μ {x | Real.arctan (f x / ε) ≤ -(Real.pi/4)} + ENNReal.ofReal δ := by
  have hsub : {x | f x ≤ 0} ⊆
      {x | Real.arctan (f x / ε) ≤ -(Real.pi/4)} ∪ {x | |f x| ≤ ε} := by
    intro x hx
    by_cases hs : |f x| ≤ ε
    · exact Or.inr hs
    · left
      change Real.arctan (f x / ε) ≤ -(Real.pi/4)
      have hf : f x / ε ≤ -1 := by
        apply (div_le_iff₀ hε).mpr
        rw [abs_of_nonpos hx] at hs
        push Not at hs
        linarith
      have h := Real.arctan_mono hf
      simpa only [Real.arctan_neg, Real.arctan_one] using h
  rw [← hhalf]
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl hsmall))

theorem positive_half_mass_le_smoothed_mass_add_error {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) {ε : ℝ} (hε : 0 < ε) (δ : ℝ)
    (hhalf : μ {x | 0 ≤ f x} = μ univ / 2)
    (hsmall : μ {x | |f x| ≤ ε} ≤ ENNReal.ofReal δ) :
    μ univ / 2 ≤ μ {x | Real.pi/4 ≤ Real.arctan (f x / ε)} + ENNReal.ofReal δ := by
  have hsub : {x | 0 ≤ f x} ⊆
      {x | Real.pi/4 ≤ Real.arctan (f x / ε)} ∪ {x | |f x| ≤ ε} := by
    intro x hx
    by_cases hs : |f x| ≤ ε
    · exact Or.inr hs
    · left
      change Real.pi/4 ≤ Real.arctan (f x / ε)
      have hf : 1 ≤ f x / ε := by
        apply (le_div_iff₀ hε).mpr
        rw [abs_of_nonneg hx] at hs
        push Not at hs
        linarith
      simpa only [Real.arctan_one] using Real.arctan_mono hf
  rw [← hhalf]
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl hsmall))

theorem exists_common_smoothing_bisection_stability {n k : ℕ} {ι : Type*} [Fintype ι]
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (μ : ι → Measure (Fin n → ℝ)) (hfin : ∀ i, IsFiniteMeasure (μ i))
    (hac : ∀ i, μ i ≪ volume) {S : Set (E k)} (hS : IsCompact S)
    (hzero : ∀ u ∈ S, u ≠ 0) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ∀ u ∈ S,
      (μ i {x | MvPolynomial.eval x (coefficientPolynomial B u) ≤ 0} = μ i univ / 2) →
      (μ i {x | 0 ≤ MvPolynomial.eval x (coefficientPolynomial B u)} = μ i univ / 2) →
      (μ i univ / 2 ≤ μ i {x | Real.arctan
        (MvPolynomial.eval x (coefficientPolynomial B u) / ε) ≤ -(Real.pi/4)} + ENNReal.ofReal (δ i)) ∧
      (μ i univ / 2 ≤ μ i {x | Real.pi/4 ≤ Real.arctan
        (MvPolynomial.eval x (coefficientPolynomial B u) / ε)} + ENNReal.ofReal (δ i)) := by
  obtain ⟨ε, hε, hsmall⟩ := exists_common_smoothingScale_small_values B hB μ hfin hac hS hzero δ hδ
  refine ⟨ε, hε, fun i u hu hneg hpos => ?_⟩
  exact ⟨negative_half_mass_le_smoothed_mass_add_error (μ i) _ hε _ hneg (hsmall i u hu),
    positive_half_mass_le_smoothed_mass_add_error (μ i) _ hε _ hpos (hsmall i u hu)⟩

end Kakeya4.Hard.MultilinearKakeya
