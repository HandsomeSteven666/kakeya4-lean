import Kakeya4.Hard.MultilinearKakeya.ConvexDeterminant
import Kakeya4.Hard.MultilinearKakeya.SmoothEnergy

/-! The actual truncated unit body of a directional seminorm and its determinant comparison.
Using p(v) alone as budget requires the stated directional lower bound. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Kakeya4.Hard.MultilinearKakeya

def visibilityBody {n : ℕ} (p : Seminorm ℝ (E n)) : Set (E n) :=
  Metric.closedBall 0 1 ∩ {v | p v ≤ 1}

theorem mem_visibilityBody {n : ℕ} (p : Seminorm ℝ (E n)) (v : E n) :
    v ∈ visibilityBody p ↔ ‖v‖ ≤ 1 ∧ p v ≤ 1 := by
  simp only [visibilityBody, mem_inter_iff, Metric.mem_closedBall, dist_zero_right, mem_ofPred_eq]

theorem convex_visibilityBody {n : ℕ} (p : Seminorm ℝ (E n)) :
    Convex ℝ (visibilityBody p) := by
  have heq : {v : E n | p v ≤ 1} = p.closedBall 0 1 := p.closedBall_zero_eq.symm
  rw [visibilityBody, heq]
  exact (convex_closedBall (0 : E n) 1).inter (p.convex_closedBall 0 1)

theorem neg_mem_visibilityBody {n : ℕ} (p : Seminorm ℝ (E n)) {v : E n}
    (hv : v ∈ visibilityBody p) : -v ∈ visibilityBody p := by
  simp only [mem_visibilityBody, norm_neg, map_neg_eq_map] at hv ⊢
  exact hv

theorem isCompact_visibilityBody {n : ℕ} (p : Seminorm ℝ (E n)) (hp : Continuous p) :
    IsCompact (visibilityBody p) :=
  (isCompact_closedBall (0 : E n) 1).inter_right (isClosed_le hp continuous_const)

theorem zero_mem_interior_visibilityBody {n : ℕ} (p : Seminorm ℝ (E n)) (hp : Continuous p) :
    (0 : E n) ∈ interior (visibilityBody p) := by
  let U : Set (E n) := {v | ‖v‖ < 1 ∧ p v < 1}
  have hU : IsOpen U := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt hp continuous_const)
  have hz : (0 : E n) ∈ U := by simp [U]
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hU.mem_nhds hz)
  intro v hv
  exact (mem_visibilityBody p v).mpr ⟨hv.1.le, hv.2.le⟩

theorem volume_visibilityBody_pos {n : ℕ} (p : Seminorm ℝ (E n)) (hp : Continuous p) :
    0 < volume (visibilityBody p) :=
  Measure.measure_pos_of_nonempty_interior volume ⟨0, zero_mem_interior_visibilityBody p hp⟩

theorem volume_visibilityBody_lt_top {n : ℕ} (p : Seminorm ℝ (E n)) (hp : Continuous p) :
    volume (visibilityBody p) < ⊤ := (isCompact_visibilityBody p hp).measure_lt_top

theorem visibilityBody_antitone {n : ℕ} {p q : Seminorm ℝ (E n)} (hpq : p ≤ q) :
    visibilityBody q ⊆ visibilityBody p := by
  intro v hv
  rw [mem_visibilityBody] at hv ⊢
  exact ⟨hv.1, (hpq v).trans hv.2⟩

theorem normalized_mem_visibilityBody {n : ℕ} (p : Seminorm ℝ (E n)) {v : E n}
    (hv : ‖v‖ = 1) : (max 1 (p v))⁻¹ • v ∈ visibilityBody p := by
  have hs : 0 < max 1 (p v) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [mem_visibilityBody]
  constructor
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le), hv, mul_one]
    exact inv_le_one_of_one_le₀ (le_max_left _ _)
  · rw [map_smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
    calc
      _ ≤ (max 1 (p v))⁻¹ * max 1 (p v) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.mpr hs.le)
      _ = 1 := inv_mul_cancel₀ hs.ne'

theorem determinant_visibilityBody_le {n : ℕ} (hn : 0 < n) (p : Seminorm ℝ (E n))
    (hp : Continuous p) (v : Fin n → E n) (hv : ∀ i, ‖v i‖ = 1) :
    ENNReal.ofReal (((2 : ℝ)/(n : ℝ))^n * |Matrix.det (fun i j => v j i)|) ≤
      volume (visibilityBody p) * ENNReal.ofReal (∏ i, max 1 (p (v i))) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  let K : Set (Fin n → ℝ) := e ⁻¹' visibilityBody p
  have hK : Convex ℝ K := (convex_visibilityBody p).linear_preimage e.toLinearMap
  have hsymm : ∀ x ∈ K, -x ∈ K := by
    intro x hx
    change e (-x) ∈ visibilityBody p
    rw [map_neg]
    exact neg_mem_visibilityBody p hx
  have hcol (i : Fin n) : (max 1 (p (v i)))⁻¹ • WithLp.ofLp (v i) ∈ K := by
    change e ((max 1 (p (v i)))⁻¹ • WithLp.ofLp (v i)) ∈ visibilityBody p
    rw [map_smul]
    exact normalized_mem_visibilityBody p (hv i)
  have h := determinant_volume_le_of_scaled_vectors hn (fun i => WithLp.ofLp (v i))
    (fun i => max 1 (p (v i))) (fun i => lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    hK hsymm hcol
  have hvol : volume K = volume (visibilityBody p) :=
    (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
      (isCompact_visibilityBody p hp).measurableSet.nullMeasurableSet
  rwa [hvol] at h

theorem determinant_visibilityBody_le_of_lower_bound {n : ℕ} (hn : 0 < n)
    (p : Seminorm ℝ (E n)) (hp : Continuous p) (v : Fin n → E n)
    (hv : ∀ i, ‖v i‖ = 1) (hlower : ∀ i, 1 ≤ p (v i)) :
    ENNReal.ofReal (((2 : ℝ)/(n : ℝ))^n * |Matrix.det (fun i j => v j i)|) ≤
      volume (visibilityBody p) * ENNReal.ofReal (∏ i, p (v i)) := by
  simpa only [max_eq_right (hlower _)] using determinant_visibilityBody_le hn p hp v hv

end Kakeya4.Hard.MultilinearKakeya
