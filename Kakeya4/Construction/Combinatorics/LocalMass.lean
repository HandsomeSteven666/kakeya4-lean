import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/-!
# Finite local mass retention

This is the elementary averaging step needed before applying a local finite-scale estimate
cell by cell: if the global shading mass is at least `τ` times the carrier mass, cells whose
local ratio is below `τ/2` carry at most half of the global carrier budget.
-/

set_option autoImplicit false

namespace Kakeya4.Construction

open scoped ENNReal
open MeasureTheory

/-- Cells whose local shading mass is at least half the global density threshold. -/
noncomputable def goodMassCells {m : ℕ} (τ : ℝ) (carrier shade : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun c => τ / 2 * carrier c ≤ shade c

/-- A global lower bound on shading mass forces the locally dense cells to retain at least
half the corresponding carrier mass. The statement is purely finite and does not assume a
bound on the number of cells. -/
theorem sum_shade_goodMassCells_ge_half {m : ℕ} (τ : ℝ) (carrier shade : Fin m → ℝ)
    (hτ : 0 ≤ τ)
    (hcarrier : ∀ c, 0 ≤ carrier c)
    (hglobal : τ * (∑ c, carrier c) ≤ ∑ c, shade c) :
    τ / 2 * (∑ c, carrier c) ≤ ∑ c ∈ goodMassCells τ carrier shade, shade c := by
  let good := goodMassCells τ carrier shade
  let bad := Finset.univ.filter fun c : Fin m => ¬ (c ∈ good)
  have hbad_point : ∀ c ∈ bad, shade c ≤ τ / 2 * carrier c := by
    intro c hc
    have hnot : ¬ τ / 2 * carrier c ≤ shade c := by
      have hmem := (Finset.mem_filter.mp hc).2
      simpa [bad, good, goodMassCells] using hmem
    exact le_of_not_ge hnot
  have hbad_sum : (∑ c ∈ bad, shade c) ≤ τ / 2 * (∑ c ∈ bad, carrier c) := by
    calc
      (∑ c ∈ bad, shade c) ≤ ∑ c ∈ bad, τ / 2 * carrier c := by
        apply Finset.sum_le_sum
        intro c hc
        exact hbad_point c hc
      _ = τ / 2 * (∑ c ∈ bad, carrier c) := by rw [Finset.mul_sum]
  have hbad_carrier : (∑ c ∈ bad, carrier c) ≤ ∑ c, carrier c := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro c hc
      exact Finset.mem_univ c
    · intro c hc hnot
      exact hcarrier c
  have hbad_bound : (∑ c ∈ bad, shade c) ≤ τ / 2 * (∑ c, carrier c) := by
    calc
      (∑ c ∈ bad, shade c) ≤ τ / 2 * (∑ c ∈ bad, carrier c) := hbad_sum
      _ ≤ τ / 2 * (∑ c, carrier c) := by
        exact mul_le_mul_of_nonneg_left hbad_carrier (by positivity)
  have hpartition :
      (∑ c ∈ good, shade c) + (∑ c ∈ bad, shade c) = ∑ c, shade c := by
    have h := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun c : Fin m => τ / 2 * carrier c ≤ shade c) (f := shade)
    simpa [good, bad, goodMassCells] using h
  linarith

/-- If each local shading is contained in its carrier, the locally dense cells themselves
retain at least half the threshold times the total carrier mass. -/
theorem sum_carrier_goodMassCells_ge_half {m : ℕ} (τ : ℝ) (carrier shade : Fin m → ℝ)
    (hτ : 0 ≤ τ)
    (hcarrier : ∀ c, 0 ≤ carrier c)
    (hshade_le_carrier : ∀ c, shade c ≤ carrier c)
    (hglobal : τ * (∑ c, carrier c) ≤ ∑ c, shade c) :
    τ / 2 * (∑ c, carrier c) ≤ ∑ c ∈ goodMassCells τ carrier shade, carrier c := by
  calc
    τ / 2 * (∑ c, carrier c) ≤
        ∑ c ∈ goodMassCells τ carrier shade, shade c :=
      sum_shade_goodMassCells_ge_half τ carrier shade hτ hcarrier hglobal
    _ ≤ ∑ c ∈ goodMassCells τ carrier shade, carrier c := by
      apply Finset.sum_le_sum
      intro c hc
      exact hshade_le_carrier c

/-- A finite phase decomposition has a phase carrying at least the average mass. The caller
supplies the partition identity, so this lemma is independent of how spatial colors are encoded. -/
theorem exists_phase_mass_ge_average {k : ℕ} (hk : 0 < k) (total : ℝ)
    (phaseMass : Fin k → ℝ)
    (hTotal : total ≤ ∑ j, phaseMass j) :
    ∃ j, total / (k : ℝ) ≤ phaseMass j := by
  have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have haverage : Fintype.card (Fin k) • (total / (k : ℝ)) ≤ ∑ j, phaseMass j := by
    simp only [Fintype.card_fin, nsmul_eq_mul]
    have hcancel : (k : ℝ) * (total / (k : ℝ)) = total := by
      field_simp [ne_of_gt hkR]
    rw [hcancel]
    exact hTotal
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨j, hj⟩ := Fintype.exists_le_sum_fiber_of_nsmul_le_sum
    (f := id) (w := phaseMass) (b := total / (k : ℝ)) haverage
  refine ⟨j, ?_⟩
  have hfiber : (∑ x with id x = j, phaseMass x) = phaseMass j := by
    classical
    rw [show Finset.univ.filter (fun x : Fin k => id x = j) = {j} by
      ext x
      simp]
    simp
  rw [hfiber] at hj
  exact hj

/-- The mass assigned to one phase by a finite phase map on a selected cell family. -/
noncomputable def phaseMassOn {m k : ℕ} (phase : Fin m → Fin k) (cells : Finset (Fin m))
    (mass : Fin m → ℝ) (j : Fin k) : ℝ :=
  ∑ c ∈ cells, if phase c = j then mass c else 0

/-- Summing phase masses recovers the mass of the selected cells. -/
theorem sum_phaseMassOn_eq {m k : ℕ} (phase : Fin m → Fin k) (cells : Finset (Fin m))
    (mass : Fin m → ℝ) :
    (∑ j, phaseMassOn phase cells mass j) = ∑ c ∈ cells, mass c := by
  simp [phaseMassOn, Finset.sum_comm]

/-- Some phase carries at least the average of the selected finite cell mass. -/
theorem exists_phaseMassOn_ge_average {m k : ℕ} (hk : 0 < k)
    (phase : Fin m → Fin k) (cells : Finset (Fin m)) (mass : Fin m → ℝ) :
    ∃ j, (∑ c ∈ cells, mass c) / (k : ℝ) ≤ phaseMassOn phase cells mass j := by
  apply exists_phase_mass_ge_average hk (∑ c ∈ cells, mass c) (phaseMassOn phase cells mass)
  rw [sum_phaseMassOn_eq]

/-- Combining local density filtering with a finite phase map yields one phase retaining its
average share of the good-cell carrier mass. -/
theorem exists_phase_goodMass_carrier {m k : ℕ} (hk : 0 < k) (τ : ℝ)
    (carrier shade : Fin m → ℝ) (phase : Fin m → Fin k)
    (hτ : 0 ≤ τ) (hcarrier : ∀ c, 0 ≤ carrier c)
    (hshade_le_carrier : ∀ c, shade c ≤ carrier c)
    (hglobal : τ * (∑ c, carrier c) ≤ ∑ c, shade c) :
    ∃ j, (τ / 2 * (∑ c, carrier c)) / (k : ℝ) ≤
      phaseMassOn phase (goodMassCells τ carrier shade) carrier j := by
  have hgood := sum_carrier_goodMassCells_ge_half τ carrier shade hτ hcarrier
    hshade_le_carrier hglobal
  obtain ⟨j, hj⟩ := exists_phaseMassOn_ge_average hk phase
    (goodMassCells τ carrier shade) carrier
  refine ⟨j, le_trans ?_ hj⟩
  exact div_le_div_of_nonneg_right hgood (by positivity)

/-- Transfer an indexed fullness lower bound through a parent-tube map while retaining every
original index, including repeated parents. Here `shadeScale` is the lower factor by which each
original shade measure survives the geometric rescaling, while `parentCarrierScale` bounds each
parent carrier measure by the corresponding original carrier measure. The conclusion is the
exact finite-sum fullness ledger needed before invoking a local estimate on the indexed parent
family; the geometric scaling inequalities remain explicit hypotheses. -/
theorem sum_parentFullness_transfer
    {ι : Type*} (indices : Finset ι)
     (fullness shadeScale parentCarrierScale : NNReal)
     (carrierMass shadeMass parentCarrierMass parentShadeMass : ι → NNReal)
    (hfull : fullness * (∑ i ∈ indices, carrierMass i) ≤
      ∑ i ∈ indices, shadeMass i)
    (hcarrier : ∀ i ∈ indices,
      parentCarrierMass i ≤ parentCarrierScale * carrierMass i)
    (hshade : ∀ i ∈ indices,
      shadeScale * shadeMass i ≤ parentShadeMass i) :
    (fullness * shadeScale) * (∑ i ∈ indices, parentCarrierMass i) ≤
      parentCarrierScale * (∑ i ∈ indices, parentShadeMass i) := by
  have hcarrierSum : (∑ i ∈ indices, parentCarrierMass i) ≤
      parentCarrierScale * (∑ i ∈ indices, carrierMass i) := by
    calc
      (∑ i ∈ indices, parentCarrierMass i) ≤
          ∑ i ∈ indices, parentCarrierScale * carrierMass i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hcarrier i hi
      _ = parentCarrierScale * (∑ i ∈ indices, carrierMass i) := by
        rw [Finset.mul_sum]
  have hshadeSum : shadeScale * (∑ i ∈ indices, shadeMass i) ≤
      ∑ i ∈ indices, parentShadeMass i := by
    calc
      shadeScale * (∑ i ∈ indices, shadeMass i) =
          ∑ i ∈ indices, shadeScale * shadeMass i := by rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ indices, parentShadeMass i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hshade i hi
  calc
    (fullness * shadeScale) * (∑ i ∈ indices, parentCarrierMass i) ≤
        (fullness * shadeScale) *
          (parentCarrierScale * (∑ i ∈ indices, carrierMass i)) :=
      mul_le_mul_of_nonneg_left hcarrierSum (by positivity)
    _ = (parentCarrierScale * shadeScale) *
        (fullness * (∑ i ∈ indices, carrierMass i)) := by ring
    _ ≤ (parentCarrierScale * shadeScale) *
        (∑ i ∈ indices, shadeMass i) :=
      mul_le_mul_of_nonneg_left hfull (by positivity)
    _ = parentCarrierScale *
        (shadeScale * (∑ i ∈ indices, shadeMass i)) := by ring
    _ ≤ parentCarrierScale * (∑ i ∈ indices, parentShadeMass i) :=
      mul_le_mul_of_nonneg_left hshadeSum (by positivity)

/-- Ratio form of `sum_parentFullness_transfer`, for callers whose parent carriers have
positive total-volume scale factor. This states directly that the parent-indexed fullness is at
least `fullness * shadeScale / parentCarrierScale`. -/
theorem parentFullness_transfer_ratio
    {ι : Type*} (indices : Finset ι)
    (fullness shadeScale parentCarrierScale : NNReal)
    (carrierMass shadeMass parentCarrierMass parentShadeMass : ι → NNReal)
    (hfull : fullness * (∑ i ∈ indices, carrierMass i) ≤
      ∑ i ∈ indices, shadeMass i)
    (hcarrier : ∀ i ∈ indices,
      parentCarrierMass i ≤ parentCarrierScale * carrierMass i)
    (hshade : ∀ i ∈ indices,
      shadeScale * shadeMass i ≤ parentShadeMass i)
    (hscale : 0 < parentCarrierScale) :
    ((fullness * shadeScale) / parentCarrierScale) *
        (∑ i ∈ indices, parentCarrierMass i) ≤
      ∑ i ∈ indices, parentShadeMass i := by
  have hledger := sum_parentFullness_transfer indices fullness shadeScale
    parentCarrierScale carrierMass shadeMass parentCarrierMass parentShadeMass
    hfull hcarrier hshade
  rw [show ((fullness * shadeScale) / parentCarrierScale) *
      (∑ i ∈ indices, parentCarrierMass i) =
      ((fullness * shadeScale) *
        (∑ i ∈ indices, parentCarrierMass i)) / parentCarrierScale by
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]]
  apply (div_le_iff₀ hscale).2
  simpa [mul_comm] using hledger

/-- A bounded parent fiber can merge indexed measurable masses without losing more than the
fiber multiplicity. The sum on the left counts every original index, including indices sharing a
parent; the sum on the right counts each parent once and uses the union of its fiber's sets. This
is the finite measure step used by the centering-shading construction. -/
theorem sum_parentFiber_shade_le
    {α ι κ : Type*} [MeasurableSpace α] [DecidableEq ι] [DecidableEq κ]
    (μ : Measure α) (originals : Finset ι) (parents : Finset κ)
    (parent : ι → κ) (shade : ι → Set α) (fiberBound : ℝ≥0∞)
    (hmap : ∀ i ∈ originals, parent i ∈ parents)
    (hfiber : ∀ j ∈ parents,
      ((originals.filter fun i => parent i = j).card : ℝ≥0∞) ≤ fiberBound) :
    (∑ i ∈ originals, μ (shade i)) ≤
      fiberBound * (∑ j ∈ parents,
        μ (⋃ i ∈ originals.filter (fun i => parent i = j), shade i)) := by
  classical
  have hfiber_sum : (∑ i ∈ originals, μ (shade i)) =
      ∑ j ∈ parents, ∑ i ∈ originals.filter (fun i => parent i = j), μ (shade i) :=
    (Finset.sum_fiberwise_of_maps_to hmap _).symm
  rw [hfiber_sum]
  calc
    (∑ j ∈ parents, ∑ i ∈ originals.filter (fun i => parent i = j), μ (shade i)) ≤
        ∑ j ∈ parents,
          ((originals.filter (fun i => parent i = j)).card : ℝ≥0∞) *
            μ (⋃ i ∈ originals.filter (fun i => parent i = j), shade i) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        (∑ i ∈ originals.filter (fun i => parent i = j), μ (shade i)) ≤
            ∑ i ∈ originals.filter (fun i => parent i = j),
              μ (⋃ i ∈ originals.filter (fun i => parent i = j), shade i) := by
          apply Finset.sum_le_sum
          intro i hi
          exact measure_mono (Set.subset_biUnion_of_mem hi)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ parents,
        fiberBound *
          μ (⋃ i ∈ originals.filter (fun i => parent i = j), shade i) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hfiber j hj) (by positivity)
    _ = fiberBound * (∑ j ∈ parents,
        μ (⋃ i ∈ originals.filter (fun i => parent i = j), shade i)) := by
      rw [Finset.mul_sum]

/-- The union of the complete parent fibers recovers the union of the original family, provided
every original index maps into the chosen finite parent set. -/
theorem parentFiber_union_eq
    {α ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (originals : Finset ι) (parents : Finset κ)
    (parent : ι → κ) (shade : ι → Set α)
    (hmap : ∀ i ∈ originals, parent i ∈ parents) :
    (⋃ j ∈ parents, ⋃ i ∈ originals.filter (fun i => parent i = j), shade i) =
      ⋃ i ∈ originals, shade i := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxj
    exact Set.mem_iUnion₂.mpr ⟨i, (Finset.mem_filter.mp hi).1, hxi⟩
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    refine Set.mem_iUnion₂.mpr ⟨parent i, hmap i hi, ?_⟩
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, hxi⟩

/-- In a three-dimensional real inner product space, a scalar homothety scales
Lebesgue measure by the absolute cube of the scalar. This is Mathlib's Haar-measure
homothety formula specialized to dimension three. -/
theorem volume_homothety_image
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) (c : ℝ) (A : Set E) :
    volume ((fun x : E => c • x) '' A) = ENNReal.ofReal (|c| ^ 3) * volume A := by
  have himage : (fun x : E => c • x) '' A =
      AffineMap.homothety (0 : E) c '' A := by
    congr 1
    funext x
    simp [AffineMap.homothety_apply]
  rw [himage, Measure.addHaar_image_homothety]
  rw [hdim]
  rw [abs_pow]

/-- In dimension three, the centering dilation by `1/8` retains exactly `1/512` of
Lebesgue measure. -/
theorem volume_eighth_homothety_image
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) (A : Set E) :
    volume ((fun x : E => (1 / 8 : ℝ) • x) '' A) =
      (1 / 512 : ℝ≥0∞) * volume A := by
  rw [volume_homothety_image hdim (1 / 8) A]
  have hcoeff : ENNReal.ofReal ((1 : ℝ) / 512) = (1 : ℝ≥0∞) / 512 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 512)]
    norm_num
  have hpow : (|(1 : ℝ) / 8|) ^ 3 = (1 : ℝ) / 512 := by norm_num
  rw [hpow, hcoeff]

end Kakeya4.Construction
