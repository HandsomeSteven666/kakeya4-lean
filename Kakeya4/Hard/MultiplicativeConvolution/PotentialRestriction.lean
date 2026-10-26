import Kakeya4.Hard.MultiplicativeConvolution.SmallBallEnergy
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# A genuine nonconcentrated restriction from the original energy

A single capped-potential sublevel set controls every radius simultaneously.
Markov pays for the removed mass. No Frostman condition is an extra input.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Actual capped potential of the original input law. -/
def cappedPotential (μ : Measure ℝ) (s r x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, cappedKernel s r x y ∂μ

/-- The potential threshold selects an actual Borel subset. -/
def potentialGoodSet (μ : Measure ℝ) (s r : ℝ) (L : ℝ≥0∞) : Set ℝ :=
  {x | cappedPotential μ s r x ≤ L}

/-- Parameter integration makes the capped potential measurable. -/
theorem measurable_cappedPotential (μ : Measure ℝ) [SFinite μ] (s r : ℝ) :
    Measurable (cappedPotential μ s r) :=
  (measurable_cappedKernel s r).lintegral_prod_right'

/-- The good restriction is Borel, before any energy finiteness assumption. -/
theorem measurableSet_potentialGoodSet (μ : Measure ℝ) [SFinite μ] (s r : ℝ) (L : ℝ≥0∞) :
    MeasurableSet (potentialGoodSet μ s r L) :=
  measurableSet_le (measurable_cappedPotential μ s r) measurable_const

/-- The discarded mass is paid by the actual capped energy. -/
theorem potentialGoodSet_compl_mass (μ : Measure ℝ) [SFinite μ]
    (s r : ℝ) (L : ℝ≥0∞) :
    L * μ (potentialGoodSet μ s r L)ᶜ ≤ cappedEnergy s r μ := by
  have hm : μ (potentialGoodSet μ s r L)ᶜ ≤ μ {x | L ≤ cappedPotential μ s r x} := by
    apply measure_mono
    intro x hx
    change ¬ cappedPotential μ s r x ≤ L at hx
    exact (lt_of_not_ge hx).le
  exact (mul_le_mul_right hm L).trans
    (mul_meas_ge_le_lintegral (measurable_cappedPotential μ s r) L)

/-- Every good center controls all balls at radii above the cap simultaneously. -/
theorem ball_mass_le_of_potential_le (μ : Measure ℝ) {s r R x : ℝ} {L : ℝ≥0∞}
    (hs : 0 ≤ s) (hR : 0 < R) (hrR : r ≤ R) (hx : cappedPotential μ s r x ≤ L) :
    μ (closedBall x R) ≤ ENNReal.ofReal (R^s) * L := by
  have hb := (ballMass_le_cappedPotential hs hrR μ x).trans hx
  have hcancel : ENNReal.ofReal (R^s) * ENNReal.ofReal R ^ (-s) = 1 := by
    rw [← ENNReal.ofReal_rpow_of_pos hR,
      ← ENNReal.rpow_add s (-s) (ENNReal.ofReal_ne_zero_iff.mpr hR) ENNReal.ofReal_ne_top]
    simp
  simpa only [← mul_assoc, hcancel, one_mul] using mul_le_mul_right hb (ENNReal.ofReal (R^s))

/-- The restriction controls balls at arbitrary centers, with the exact radius-doubling payment. -/
theorem restricted_ball_mass_le_potential (μ : Measure ℝ) [SFinite μ]
    {s r R : ℝ} (hs : 0 ≤ s) (hR : 0 < R) (hrR : r ≤ 2*R)
    (L : ℝ≥0∞) (z : ℝ) :
    (μ.restrict (potentialGoodSet μ s r L)) (closedBall z R) ≤
      ENNReal.ofReal ((2*R)^s) * L := by
  rw [Measure.restrict_apply measurableSet_closedBall]
  by_cases hne : (closedBall z R ∩ potentialGoodSet μ s r L).Nonempty
  · obtain ⟨x,hxz,hx⟩ := hne
    have hsub : closedBall z R ∩ potentialGoodSet μ s r L ⊆ closedBall x (2*R) := by
      intro y hy
      change dist y x ≤ 2*R
      have hyz : dist y z ≤ R := hy.1
      have hzx : dist z x ≤ R := by simpa only [mem_closedBall, dist_comm] using hxz
      calc
        _ ≤ dist y z + dist z x := dist_triangle _ _ _
        _ ≤ R+R := add_le_add hyz hzx
        _ = _ := by ring
    exact (measure_mono hsub).trans
      (ball_mass_le_of_potential_le μ hs (by positivity) hrR hx)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]
    exact bot_le

end Kakeya4.Hard.MultiplicativeConvolution
