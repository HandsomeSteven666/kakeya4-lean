import Kakeya4.Hard.MultilinearKakeya.CylinderBudget

/-! Borel parameters for complete affine lines and their actual tube incidence.
Anchors are unrestricted, and no quotient or injective parametrization is needed:
different parameters may describe the same geometric line. -/

noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal RealInnerProductSpace BigOperators

namespace Kakeya4.Hard.MultilinearKakeya

/-- An arbitrary anchor and a unit vector, with the inherited product Borel structure. -/
abbrev LineParameter (n : ℕ) := E n × {v : E n // ‖v‖ = 1}

def LineParameter.toLine {n : ℕ} (p : LineParameter n) : Line n :=
  ⟨p.1,p.2.val,p.2.property⟩

def Line.toParameter {n : ℕ} (L : Line n) : LineParameter n :=
  (L.anchor,⟨L.direction,L.norm_direction⟩)

theorem Line.toParameter_toLine {n : ℕ} (L : Line n) : L.toParameter.toLine = L := by
  cases L
  rfl

theorem LineParameter.toLine_toParameter {n : ℕ} (p : LineParameter n) :
    p.toLine.toParameter = p := by
  rcases p with ⟨a,⟨v,hv⟩⟩
  rfl

/-- Orthogonal distance to the full line, expressed continuously in all parameters. -/
def parameterLineDistance {n : ℕ} (p : LineParameter n) (x : E n) : ℝ :=
  ‖(x-p.1) - (inner ℝ (x-p.1) p.2.val) • p.2.val‖

theorem parameterLineDistance_eq_infDist {n : ℕ} (p : LineParameter n) (x : E n) :
    parameterLineDistance p x = Metric.infDist x p.toLine.carrier := by
  apply le_antisymm
  · have h := transverse_norm_le_infDist p.toLine x
    rw [axialMeasurableEquiv_apply,Construction.axialCoordinates_snd_norm] at h
    exact h
  · let t := inner ℝ (x-p.1) p.2.val
    have hmem : p.1 + t • p.2.val ∈ p.toLine.carrier := ⟨t,rfl⟩
    have h := Metric.infDist_le_dist_of_mem (x := x) hmem
    have he : dist x (p.1+t • p.2.val) = parameterLineDistance p x := by
      unfold parameterLineDistance
      rw [dist_eq_norm]
      congr 1
      dsimp only [t]
      abel
    exact h.trans_eq he

theorem continuous_parameterLineDistance (n : ℕ) :
    Continuous (fun z : LineParameter n × E n => parameterLineDistance z.1 z.2) := by
  unfold parameterLineDistance
  fun_prop

def parameterTubeIncidence (n : ℕ) (r : ℝ) : Set (LineParameter n × E n) :=
  {z | parameterLineDistance z.1 z.2 ≤ r}

theorem mem_parameterTubeIncidence {n : ℕ} (r : ℝ) (p : LineParameter n) (x : E n) :
    (p,x) ∈ parameterTubeIncidence n r ↔ x ∈ p.toLine.tube r := by
  change parameterLineDistance p x ≤ r ↔ Metric.infDist x p.toLine.carrier ≤ r
  rw [parameterLineDistance_eq_infDist]

theorem isClosed_parameterTubeIncidence (n : ℕ) (r : ℝ) :
    IsClosed (parameterTubeIncidence n r) :=
  isClosed_le (continuous_parameterLineDistance n) continuous_const

theorem measurableSet_parameterTubeIncidence (n : ℕ) (r : ℝ) :
    MeasurableSet (parameterTubeIncidence n r) := (isClosed_parameterTubeIncidence n r).measurableSet

end Kakeya4.Hard.MultilinearKakeya
