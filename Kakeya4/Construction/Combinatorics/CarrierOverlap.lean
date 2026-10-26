import Kakeya4.Construction.Combinatorics.CylinderVolume

/-!
# Same-scale tube overlap geometry

This file develops the local carrier version of the same-scale overlap argument used in the
licensed Numina tube development. It works directly with closed neighborhoods of centered unit
segments, so it does not import Numina's `Tube` hierarchy or its theorem dependency closure.
-/

set_option autoImplicit false

namespace Kakeya4.Construction

open MeasureTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The centered unit segment with midpoint `m` and unit direction `d`. -/
def centeredUnitSegment (m d : E) : Set E :=
  segment ℝ (m - (1 / 2 : ℝ) • d) (m + (1 / 2 : ℝ) • d)

/-- The closed `δ`-carrier of a centered unit segment. -/
def centeredUnitCarrier (δ : ℝ) (m d : E) : Set E :=
  Metric.cthickening δ (centeredUnitSegment m d)

private def perpendicularProjection (u : E) : E →ₗ[ℝ] E where
  toFun x := x - inner ℝ x u • u
  map_add' x y := by
    simp only [inner_add_left, add_smul]
    module
  map_smul' c x := by
    change c • x - inner ℝ (c • x) u • u = _
    rw [real_inner_smul_left, smul_sub, smul_smul]
    rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_perpendicularProjection_le (u x : E) (hu : ‖u‖ = 1) :
    ‖perpendicularProjection u x‖ ≤ ‖x‖ := by
  have hsq : ‖perpendicularProjection u x‖ ^ 2 = ‖x‖ ^ 2 - (inner ℝ x u) ^ 2 := by
    change ‖x - inner ℝ x u • u‖ ^ 2 = _
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hu, mul_one,
      sq_abs]
    ring
  nlinarith [sq_nonneg (inner ℝ x u), norm_nonneg (perpendicularProjection u x), norm_nonneg x]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem perpendicularProjection_self_eq_zero (u : E) (hu : ‖u‖ = 1) :
    perpendicularProjection u u = 0 := by
  change u - inner ℝ u u • u = 0
  rw [real_inner_self_eq_norm_sq, hu]
  norm_num

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_perpendicularProjection_eq_sine {u v : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖perpendicularProjection u v‖ = Real.sqrt (1 - (inner ℝ u v) ^ 2) := by
  have hsq : ‖perpendicularProjection u v‖ ^ 2 =
      1 - (inner ℝ u v) ^ 2 := by
    change ‖v - inner ℝ v u • u‖ ^ 2 = _
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hu, mul_one,
      sq_abs, real_inner_comm v u]
    rw [hv]
    ring
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem axisParameter_difference_mul_sine_le
    {u v p q m₁ m₂ : E} {s₁ s₂ t₁ t₂ δ : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {e₁ e₂ f₁ f₂ : E}
    (hp₁ : p = m₁ + s₁ • u + e₁) (hq₁ : q = m₁ + s₂ • u + e₂)
    (hp₂ : p = m₂ + t₁ • v + f₁) (hq₂ : q = m₂ + t₂ • v + f₂)
    (he₁ : ‖e₁‖ ≤ δ) (he₂ : ‖e₂‖ ≤ δ)
    (hf₁ : ‖f₁‖ ≤ δ) (hf₂ : ‖f₂‖ ≤ δ) :
    |t₁ - t₂| * Real.sqrt (1 - (inner ℝ u v) ^ 2) ≤ 4 * δ := by
  have hdiff₁ : p - q = (s₁ - s₂) • u + (e₁ - e₂) := by
    rw [hp₁, hq₁]
    module
  have hdiff₂ : p - q = (t₁ - t₂) • v + (f₁ - f₂) := by
    rw [hp₂, hq₂]
    module
  let P := perpendicularProjection u
  have hPu : P u = 0 := perpendicularProjection_self_eq_zero u hu
  have hfirst : P (p - q) = P (e₁ - e₂) := by
    rw [hdiff₁, map_add, map_smul, hPu, smul_zero, zero_add]
  have hsecond : P (p - q) = (t₁ - t₂) • P v + P (f₁ - f₂) := by
    rw [hdiff₂, map_add, map_smul]
  have hvec : (t₁ - t₂) • P v = P (e₁ - e₂) - P (f₁ - f₂) := by
    calc
      (t₁ - t₂) • P v = ((t₁ - t₂) • P v + P (f₁ - f₂)) - P (f₁ - f₂) := by abel
      _ = P (p - q) - P (f₁ - f₂) := by rw [hsecond]
      _ = P (e₁ - e₂) - P (f₁ - f₂) := by rw [hfirst]
  have herror₁ : ‖P (e₁ - e₂)‖ ≤ 2 * δ := by
    calc
      ‖P (e₁ - e₂)‖ ≤ ‖e₁ - e₂‖ := norm_perpendicularProjection_le u _ hu
      _ ≤ ‖e₁‖ + ‖e₂‖ := norm_sub_le _ _
      _ ≤ δ + δ := add_le_add he₁ he₂
      _ = 2 * δ := by ring
  have herror₂ : ‖P (f₁ - f₂)‖ ≤ 2 * δ := by
    calc
      ‖P (f₁ - f₂)‖ ≤ ‖f₁ - f₂‖ := norm_perpendicularProjection_le u _ hu
      _ ≤ ‖f₁‖ + ‖f₂‖ := norm_sub_le _ _
      _ ≤ δ + δ := add_le_add hf₁ hf₂
      _ = 2 * δ := by ring
  have hPnorm : ‖P v‖ = Real.sqrt (1 - (inner ℝ u v) ^ 2) :=
    norm_perpendicularProjection_eq_sine hu hv
  calc
    |t₁ - t₂| * Real.sqrt (1 - (inner ℝ u v) ^ 2) = ‖(t₁ - t₂) • P v‖ := by
      rw [norm_smul, Real.norm_eq_abs, hPnorm]
    _ = ‖P (e₁ - e₂) - P (f₁ - f₂)‖ := by rw [hvec]
    _ ≤ ‖P (e₁ - e₂)‖ + ‖P (f₁ - f₂)‖ := norm_sub_le _ _
    _ ≤ 4 * δ := by linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem exists_centered_unitCarrier_parameter
    {δ : ℝ} {m d p : E} (hd : ‖d‖ = 1) (hδ : 0 ≤ δ)
    (hp : p ∈ centeredUnitCarrier δ m d) :
    ∃ s : ℝ, ∃ e : E, s ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ∧
      ‖e‖ ≤ δ ∧ p = m + s • d + e := by
  obtain ⟨s, hs, he⟩ :=
    exists_axisParameter_of_mem_unitSegmentCthickening m d p hd hδ hp
  refine ⟨s, p - m - s • d, hs, he, ?_⟩
  module

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem centeredUnitCarrier_axisCoordinate_difference
    {δ : ℝ} (hδ : 0 ≤ δ) {m n u v p q : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hp₁ : p ∈ centeredUnitCarrier δ m u) (hq₁ : q ∈ centeredUnitCarrier δ m u)
    (hp₂ : p ∈ centeredUnitCarrier δ n v) (hq₂ : q ∈ centeredUnitCarrier δ n v) :
    |inner ℝ (p - n) v - inner ℝ (q - n) v| *
        Real.sqrt (1 - (inner ℝ u v) ^ 2) ≤ 6 * δ := by
  obtain ⟨sp, ep, _, hep, hp⟩ := exists_centered_unitCarrier_parameter hu hδ hp₁
  obtain ⟨sq, eq, _, heq, hq⟩ := exists_centered_unitCarrier_parameter hu hδ hq₁
  obtain ⟨tp, fp, _, hfp, hp'⟩ := exists_centered_unitCarrier_parameter hv hδ hp₂
  obtain ⟨tq, fq, _, hfq, hq'⟩ := exists_centered_unitCarrier_parameter hv hδ hq₂
  have hparam := axisParameter_difference_mul_sine_le hu hv hp hq hp' hq' hep heq hfp hfq
  have hcoord : inner ℝ (p - n) v - inner ℝ (q - n) v =
      (tp - tq) + inner ℝ (fp - fq) v := by
    rw [hp', hq']
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hv]
    ring
  have herror : |inner ℝ (fp - fq) v| ≤ 2 * δ := by
    calc
      |inner ℝ (fp - fq) v| ≤ ‖fp - fq‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖fp‖ + ‖fq‖) * ‖v‖ := mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ (δ + δ) * 1 := by rw [hv]; nlinarith [hfp, hfq]
      _ = 2 * δ := by ring
  have hσnonneg : 0 ≤ Real.sqrt (1 - (inner ℝ u v) ^ 2) := Real.sqrt_nonneg _
  have hσle : Real.sqrt (1 - (inner ℝ u v) ^ 2) ≤ 1 := by
    rw [← norm_perpendicularProjection_eq_sine hu hv]
    calc
      ‖perpendicularProjection u v‖ ≤ ‖v‖ := norm_perpendicularProjection_le u v hu
      _ = 1 := hv
  have habs : |inner ℝ (p - n) v - inner ℝ (q - n) v| ≤ |tp - tq| + 2 * δ := by
    rw [hcoord]
    exact (abs_add_le _ _).trans (add_le_add_right herror _)
  calc
    |inner ℝ (p - n) v - inner ℝ (q - n) v| *
          Real.sqrt (1 - (inner ℝ u v) ^ 2) ≤
        (|tp - tq| + 2 * δ) * Real.sqrt (1 - (inner ℝ u v) ^ 2) :=
      mul_le_mul_of_nonneg_right habs hσnonneg
    _ = |tp - tq| * Real.sqrt (1 - (inner ℝ u v) ^ 2) +
          2 * δ * Real.sqrt (1 - (inner ℝ u v) ^ 2) := by ring
    _ ≤ 4 * δ + 2 * δ := by
      exact add_le_add hparam
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hσle (by positivity : 0 ≤ 2 * δ))
    _ = 6 * δ := by ring

private theorem centeredUnitCarrier_volume_eq_unitAxis
    {δ : ℝ} {m d : E} (hδ : 0 ≤ δ) :
    volume (centeredUnitCarrier δ m d) =
      volume (Metric.cthickening δ (unitAxisSegment d)) := by
  have hsegment : centeredUnitSegment m d =
      segment ℝ (m - (1 / 2 : ℝ) • d) ((m - (1 / 2 : ℝ) • d) + d) := by
    unfold centeredUnitSegment
    congr 1
    module
  rw [centeredUnitCarrier, hsegment]
  exact volume_cthickening_segment_translate (m - (1 / 2 : ℝ) • d) d hδ

private theorem sine_le_24delta_of_heavy_overlap
    (hdim : Module.finrank ℝ E = 3) {δ : ℝ} (hδ : 0 < δ)
    (m n u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hoverlap : (1 / 2 : ℝ≥0∞) * volume (centeredUnitCarrier δ m u) <
      volume (centeredUnitCarrier δ m u ∩ centeredUnitCarrier δ n v)) :
    Real.sqrt (1 - (inner ℝ u v) ^ 2) ≤ 24 * δ := by
  let T₁ := centeredUnitCarrier δ m u
  let T₂ := centeredUnitCarrier δ n v
  let B : ℝ≥0∞ := ENNReal.ofReal δ ^ 2 * ENNReal.ofReal Real.pi
  have hδ0 : 0 ≤ δ := hδ.le
  have hvol₁ := volume_unitAxisSegment_cthickening_bounds hdim u hu hδ0
  have hvol₁eq := centeredUnitCarrier_volume_eq_unitAxis (m := m) (d := u) hδ0
  have hvolLower : B ≤ volume T₁ := by
    dsimp [T₁, B]
    rw [hvol₁eq]
    exact hvol₁.1
  have hvolUpper : volume T₁ ≤ ENNReal.ofReal (1 + 2 * δ) * B := by
    dsimp [T₁, B]
    rw [hvol₁eq]
    exact hvol₁.2
  have hBtop : B < ∞ := by
    dsimp [B]
    apply ENNReal.mul_lt_top
    · exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
    · exact ENNReal.ofReal_lt_top
  have hVtop : ENNReal.ofReal (1 + 2 * δ) * B < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBtop
  have hVfinite : volume T₁ ≠ ∞ := ne_top_of_le_ne_top hVtop.ne hvolUpper
  have hrealBase : 0 < δ ^ 2 * Real.pi := by positivity
  have hB_eq : B = ENNReal.ofReal (δ ^ 2 * Real.pi) := by
    dsimp [B]
    rw [← ENNReal.ofReal_pow hδ0,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ δ ^ 2)]
  have hBpos : 0 < B := by
    rw [hB_eq]
    exact ENNReal.ofReal_pos.mpr hrealBase
  have hheavy : 0 < volume (T₁ ∩ T₂) := by
    exact lt_of_le_of_lt (by positivity) hoverlap
  obtain ⟨p₀, hp₀⟩ := nonempty_of_measure_ne_zero hheavy.ne'
  have hp₀mem : p₀ ∈ T₁ ∩ T₂ := hp₀
  let a₀ := inner ℝ (p₀ - n) v
  let σ := Real.sqrt (1 - (inner ℝ u v) ^ 2)
  have hσnonneg : 0 ≤ σ := Real.sqrt_nonneg _
  by_cases hσpos : 0 < σ
  · let L := 6 * δ / σ
    let cyl := axialCylinder v hv (a₀ - L) (a₀ + L) δ
    have hsubset : T₁ ∩ T₂ ⊆ (fun z : E => n + z) '' cyl := by
      intro x hx
      have hx₁ : x ∈ T₁ := hx.1
      have hx₂ : x ∈ T₂ := hx.2
      obtain ⟨t, f, _, hf, hxrep⟩ :=
        exists_centered_unitCarrier_parameter hv hδ0 hx₂
      have hcoordProduct := centeredUnitCarrier_axisCoordinate_difference hδ0 hu hv
        hx₁ hp₀mem.1 hx₂ hp₀mem.2
      have hcoordBound : |inner ℝ (x - n) v - a₀| ≤ L := by
        have hdiv := (le_div_iff₀ hσpos).2 hcoordProduct
        simpa [L, a₀, σ] using hdiv
      have hcoordIcc : inner ℝ (x - n) v ∈ Set.Icc (a₀ - L) (a₀ + L) := by
        rcases abs_le.mp hcoordBound with ⟨hlo, hhi⟩
        constructor <;> dsimp [a₀] at hlo hhi ⊢ <;> linarith
      have hxrep' : x - n = t • v + f := by
        rw [hxrep]
        module
      have hproj : perpendicularProjection v (x - n) = perpendicularProjection v f := by
        rw [hxrep', map_add, map_smul, perpendicularProjection_self_eq_zero v hv,
          smul_zero, zero_add]
      have hperp : ‖(x - n) - inner ℝ (x - n) v • v‖ ≤ δ := by
        change ‖perpendicularProjection v (x - n)‖ ≤ δ
        rw [hproj]
        exact (norm_perpendicularProjection_le v f hv).trans hf
      have hxCyl : x - n ∈ cyl := by
        change x - n ∈ axialCylinder v hv (a₀ - L) (a₀ + L) δ
        exact (mem_axialCylinder_iff v hv (a₀ - L) (a₀ + L) δ (x - n)).2
          ⟨hcoordIcc, hperp⟩
      exact ⟨x - n, hxCyl, by abel⟩
    have htrans : volume ((fun z : E => n + z) '' cyl) = volume cyl := by
      have hfun : (fun z : E => n + z) = fun z => z + n := by
        funext z
        exact add_comm n z
      rw [hfun, Set.image_add_right, measure_preimage_add_right]
    have hlength : (a₀ + L) - (a₀ - L) = 12 * δ / σ := by
      dsimp [L]
      ring
    have hformula : volume cyl = ENNReal.ofReal (12 * δ / σ) * B := by
      calc
        volume cyl = ENNReal.ofReal ((a₀ + L) - (a₀ - L)) * B := by
          dsimp [cyl, B]
          rw [volume_axialCylinder_three hdim v hv]
        _ = ENNReal.ofReal (12 * δ / σ) * B := by rw [hlength]
    have hAupper : volume (T₁ ∩ T₂) ≤ ENNReal.ofReal (12 * δ / σ) * B := by
      calc
        volume (T₁ ∩ T₂) ≤ volume ((fun z : E => n + z) '' cyl) := measure_mono hsubset
        _ = volume cyl := htrans
        _ = ENNReal.ofReal (12 * δ / σ) * B := hformula
    have hRhsTop : ENNReal.ofReal (12 * δ / σ) * B < ∞ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBtop
    have hAfin : volume (T₁ ∩ T₂) ≠ ∞ := ne_top_of_le_ne_top hRhsTop.ne hAupper
    have hvolLowerReal : δ ^ 2 * Real.pi ≤ (volume T₁).toReal := by
      have h := ENNReal.toReal_mono hVfinite hvolLower
      rw [hB_eq, ENNReal.toReal_ofReal hrealBase.le] at h
      exact h
    have hhalfReal : (1 / 2 : ℝ) * (volume T₁).toReal <
        (volume (T₁ ∩ T₂)).toReal := by
      have hleftfinite : (1 / 2 : ℝ≥0∞) * volume T₁ ≠ ∞ :=
        ENNReal.mul_ne_top (by norm_num) hVfinite
      have h := (ENNReal.toReal_lt_toReal hleftfinite hAfin).2 hoverlap
      rw [ENNReal.toReal_mul, one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
        ← one_div] at h
      exact h
    have hAupperReal : (volume (T₁ ∩ T₂)).toReal ≤
        (12 * δ / σ) * (δ ^ 2 * Real.pi) := by
      have h := ENNReal.toReal_mono hRhsTop.ne hAupper
      rw [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ 12 * δ / σ),
        hB_eq, ENNReal.toReal_ofReal hrealBase.le] at h
      exact h
    have hratio : (1 / 2 : ℝ) < 12 * δ / σ := by
      have hmul : (1 / 2 : ℝ) * (δ ^ 2 * Real.pi) <
          (12 * δ / σ) * (δ ^ 2 * Real.pi) := by
        calc
          (1 / 2 : ℝ) * (δ ^ 2 * Real.pi) ≤
              (1 / 2 : ℝ) * (volume T₁).toReal :=
            mul_le_mul_of_nonneg_left hvolLowerReal (by norm_num)
          _ < (volume (T₁ ∩ T₂)).toReal := hhalfReal
          _ ≤ (12 * δ / σ) * (δ ^ 2 * Real.pi) := hAupperReal
      exact lt_of_mul_lt_mul_right hmul hrealBase.le
    have hangle : σ < 24 * δ := by
      have h := (lt_div_iff₀ hσpos).mp hratio
      norm_num at h
      linarith
    exact le_of_lt (by simpa [σ] using hangle)
  · have hσzero : σ = 0 := le_antisymm (not_lt.mp hσpos) hσnonneg
    have hs : Real.sqrt (1 - (inner ℝ u v) ^ 2) = 0 := by simpa [σ] using hσzero
    rw [hs]
    positivity

/-- Heavy overlap of two equal-radius three-dimensional unit-segment carriers forces the second
carrier into a fixed `27δ` neighborhood of the first core line. -/
theorem centeredUnitCarrier_subset_lineCthickening_of_heavy_overlap
    (hdim : Module.finrank ℝ E = 3) {δ : ℝ} (hδ : 0 < δ)
    (m n u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hoverlap : (1 / 2 : ℝ≥0∞) * volume (centeredUnitCarrier δ m u) <
      volume (centeredUnitCarrier δ m u ∩ centeredUnitCarrier δ n v)) :
    centeredUnitCarrier δ n v ⊆ Metric.cthickening (27 * δ)
      (Set.range (fun t : ℝ => m + t • u)) := by
  have hangle := sine_le_24delta_of_heavy_overlap hdim hδ m n u v hu hv hoverlap
  let T₁ := centeredUnitCarrier δ m u
  let T₂ := centeredUnitCarrier δ n v
  have hheavy : 0 < volume (T₁ ∩ T₂) := by
    exact lt_of_le_of_lt (by positivity) hoverlap
  obtain ⟨p₀, hp₀⟩ := nonempty_of_measure_ne_zero hheavy.ne'
  have hp₀mem : p₀ ∈ T₁ ∩ T₂ := hp₀
  obtain ⟨s₀, e₁, hs₀, he₁, hp₀₁⟩ :=
    exists_centered_unitCarrier_parameter hu hδ.le hp₀mem.1
  obtain ⟨t₀, f₀, ht₀, hf₀, hp₀₂⟩ :=
    exists_centered_unitCarrier_parameter hv hδ.le hp₀mem.2
  intro z hz
  obtain ⟨t, f, ht, hf, hzrep⟩ :=
    exists_centered_unitCarrier_parameter hv hδ.le hz
  let dt := t - t₀
  let q := m + (s₀ + dt * inner ℝ v u) • u
  have hdt : |dt| ≤ 1 := by
    change |t - t₀| ≤ 1
    rw [abs_le]
    rcases ht with ⟨htlo, hthi⟩
    rcases ht₀ with ⟨ht₀lo, ht₀hi⟩
    constructor <;> linarith
  have hqline : q ∈ Set.range (fun r : ℝ => m + r • u) := by
    refine ⟨s₀ + dt * inner ℝ v u, ?_⟩
    rfl
  have hzfromp₀ : z = p₀ + dt • v + (f - f₀) := by
    change z = p₀ + (t - t₀) • v + (f - f₀)
    rw [hp₀₂, hzrep]
    module
  have hzq : z - q = e₁ + dt • (v - inner ℝ v u • u) + (f - f₀) := by
    rw [hzfromp₀, hp₀₁]
    dsimp [q]
    module
  have hdirnorm : ‖dt • (v - inner ℝ v u • u)‖ = |dt| *
      Real.sqrt (1 - (inner ℝ u v) ^ 2) := by
    calc
      ‖dt • (v - inner ℝ v u • u)‖ = |dt| * ‖v - inner ℝ v u • u‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = |dt| * ‖perpendicularProjection u v‖ := by rfl
      _ = |dt| * Real.sqrt (1 - (inner ℝ u v) ^ 2) := by
        rw [norm_perpendicularProjection_eq_sine hu hv]
  have hzqBound : dist z q ≤ 27 * δ := by
    rw [dist_eq_norm]
    have hfdiff : ‖f - f₀‖ ≤ ‖f‖ + ‖f₀‖ := norm_sub_le _ _
    calc
      ‖z - q‖ ≤ ‖e₁‖ + ‖dt • (v - inner ℝ v u • u)‖ + ‖f - f₀‖ := by
        rw [hzq]
        calc
          ‖e₁ + dt • (v - inner ℝ v u • u) + (f - f₀)‖ ≤
              ‖e₁ + dt • (v - inner ℝ v u • u)‖ + ‖f - f₀‖ := norm_add_le _ _
          _ ≤ ‖e₁‖ + ‖dt • (v - inner ℝ v u • u)‖ + ‖f - f₀‖ := by
            nlinarith [norm_add_le e₁ (dt • (v - inner ℝ v u • u))]
      _ ≤ δ + |dt| * Real.sqrt (1 - (inner ℝ u v) ^ 2) + (‖f‖ + ‖f₀‖) := by
        rw [hdirnorm]
        exact add_le_add (add_le_add_left he₁ _) hfdiff
      _ ≤ δ + 24 * δ + (δ + δ) := by
        have hmul : |dt| * Real.sqrt (1 - (inner ℝ u v) ^ 2) ≤ 24 * δ := by
          calc
            |dt| * Real.sqrt (1 - (inner ℝ u v) ^ 2) ≤
                1 * Real.sqrt (1 - (inner ℝ u v) ^ 2) :=
              mul_le_mul_of_nonneg_right hdt (Real.sqrt_nonneg _)
            _ = Real.sqrt (1 - (inner ℝ u v) ^ 2) := by ring
            _ ≤ 24 * δ := hangle
        nlinarith [hf, hf₀]
      _ = 27 * δ := by ring
  exact Metric.mem_cthickening_of_dist_le z q (27 * δ)
    (Set.range (fun t : ℝ => m + t • u)) hqline hzqBound

/-- Failure of carrier essential distinctness implies heavy overlap and hence `27δ` containment
for centered unit-segment carriers. No equal-volume assumption is needed: the definition uses the
larger of the two carrier volumes, which is at least the first carrier's volume. -/
theorem centeredUnitCarrier_subset_lineCthickening_of_not_essentiallyDistinct
    (hdim : Module.finrank ℝ E = 3) {δ : ℝ} (hδ : 0 < δ)
    (m n u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hnot : ¬ IsCarrierEssentiallyDistinct
      (centeredUnitCarrier δ m u) (centeredUnitCarrier δ n v)) :
    centeredUnitCarrier δ n v ⊆ Metric.cthickening (27 * δ)
      (Set.range (fun t : ℝ => m + t • u)) := by
  have hheavyMax := not_le.mp hnot
  have hhalf : (1 / 2 : ℝ≥0∞) * volume (centeredUnitCarrier δ m u) <
      volume (centeredUnitCarrier δ m u ∩ centeredUnitCarrier δ n v) := by
    calc
      (1 / 2 : ℝ≥0∞) * volume (centeredUnitCarrier δ m u) ≤
          (1 / 2 : ℝ≥0∞) * max
            (volume (centeredUnitCarrier δ m u))
            (volume (centeredUnitCarrier δ n v)) := by
        gcongr
        exact le_max_left _ _
      _ < volume (centeredUnitCarrier δ m u ∩ centeredUnitCarrier δ n v) := hheavyMax
  exact centeredUnitCarrier_subset_lineCthickening_of_heavy_overlap
    hdim hδ m n u v hu hv hhalf

end Kakeya4.Construction
