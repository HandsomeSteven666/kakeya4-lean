import Kakeya4.Hard.MultilinearKakeya.TopologicalInput
import Kakeya4.Hard.AlgebraicGeometry.PolynomialNull

/-! Simultaneous polynomial bisection for finite measures absolutely continuous
with respect to volume, using a genuinely independent polynomial coefficient family. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace Kakeya4.Hard.MultilinearKakeya

def coefficientPolynomial {n k : ℕ} (B : Fin k → MvPolynomial (Fin n) ℝ) (u : E k) :
    MvPolynomial (Fin n) ℝ := Fintype.linearCombination ℝ B (WithLp.ofLp u)

theorem coefficientPolynomial_neg {n k : ℕ} (B : Fin k → MvPolynomial (Fin n) ℝ)
    (u : E k) : coefficientPolynomial B (-u) = -coefficientPolynomial B u := by
  exact map_neg (Fintype.linearCombination ℝ B) (WithLp.ofLp u)

theorem coefficientPolynomial_ne_zero {n k : ℕ} (B : Fin k → MvPolynomial (Fin n) ℝ)
    (hB : LinearIndependent ℝ B) (u : E k) (hu : u ≠ 0) :
    coefficientPolynomial B u ≠ 0 := by
  intro h
  have hc : (WithLp.ofLp u : Fin k → ℝ) = 0 :=
    hB.fintypeLinearCombination_injective (by simpa [coefficientPolynomial] using h)
  apply hu
  ext i
  exact congrFun hc i

theorem eval_coefficientPolynomial {n k : ℕ} (B : Fin k → MvPolynomial (Fin n) ℝ)
    (u : E k) (x : Fin n → ℝ) :
    MvPolynomial.eval x (coefficientPolynomial B u) =
      ∑ i, u i * MvPolynomial.eval x (B i) := by
  simp [coefficientPolynomial, Fintype.linearCombination_apply, MvPolynomial.smul_eq_C_mul]

theorem continuous_eval_coefficientPolynomial {n k : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    Continuous (fun u : E k => MvPolynomial.eval x (coefficientPolynomial B u)) := by
  simp only [eval_coefficientPolynomial]
  fun_prop

theorem continuousAt_polynomial_sublevel_measure {n k : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ]
    {α : Type*} [TopologicalSpace α] [FirstCountableTopology α]
    (g : α → E k) (hg : Continuous g) (a : α)
    (hnull : μ {x | MvPolynomial.eval x (coefficientPolynomial B (g a)) = 0} = 0) :
    ContinuousAt (fun b => μ {x | MvPolynomial.eval x (coefficientPolynomial B (g b)) ≤ 0}) a := by
  have hmeas (b : α) :
      MeasurableSet {x | MvPolynomial.eval x (coefficientPolynomial B (g b)) ≤ 0} :=
    isClosed_le (MvPolynomial.continuous_eval _) continuous_const |>.measurableSet
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (𝓝 a) (hmeas a) hmeas
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
  have hne : MvPolynomial.eval x (coefficientPolynomial B (g a)) ≠ 0 := hx
  have hc : ContinuousAt (fun b => MvPolynomial.eval x (coefficientPolynomial B (g b))) a :=
    ((continuous_eval_coefficientPolynomial B x).comp hg).continuousAt
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hevent := hc.eventually (Iio_mem_nhds hneg)
    filter_upwards [hevent] with b hb
    exact iff_of_true hb.le hneg.le
  · have hevent := hc.eventually (Ioi_mem_nhds hpos)
    filter_upwards [hevent] with b hb
    exact iff_of_false (not_le.mpr hb) (not_le.mpr hpos)

theorem coefficientPolynomial_sphere_ne_zero {n m : ℕ}
    (B : Fin (m+1) → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (u : Metric.sphere (0 : E (m+1)) 1) : coefficientPolynomial B u ≠ 0 := by
  apply coefficientPolynomial_ne_zero B hB
  intro hu
  have hnorm : ‖(u : E (m+1))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  rw [hu, norm_zero] at hnorm
  norm_num at hnorm

def polynomialBisectionMap {n m : ℕ} (B : Fin (m+1) → MvPolynomial (Fin n) ℝ)
    (μ : Fin m → Measure (Fin n → ℝ)) (u : Metric.sphere (0 : E (m+1)) 1) : E m :=
  WithLp.toLp 2 (fun i => (μ i {x | MvPolynomial.eval x (coefficientPolynomial B u) ≤ 0}).toReal)

theorem continuous_polynomialBisectionMap {n m : ℕ}
    (B : Fin (m+1) → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (μ : Fin m → Measure (Fin n → ℝ)) (hfin : ∀ i, IsFiniteMeasure (μ i))
    (hac : ∀ i, μ i ≪ volume) : Continuous (polynomialBisectionMap B μ) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  letI := hfin i
  rw [continuous_iff_continuousAt]
  intro u
  have hnull : μ i {x | MvPolynomial.eval x (coefficientPolynomial B u) = 0} = 0 :=
    hac i (real_polynomial_zero_volume _ (coefficientPolynomial_sphere_ne_zero B hB u))
  have hcont := continuousAt_polynomial_sublevel_measure B (μ i)
    Subtype.val continuous_subtype_val u hnull
  have hfinite : μ i {x | MvPolynomial.eval x (coefficientPolynomial B u) ≤ 0} ≠ ⊤ :=
    measure_ne_top _ _
  exact ContinuousAt.comp
    (f := fun v : Metric.sphere (0 : E (m+1)) 1 =>
      μ i {x | MvPolynomial.eval x (coefficientPolynomial B v) ≤ 0})
    (g := ENNReal.toReal) (x := u) (ENNReal.continuousAt_toReal hfinite) hcont

/-- Simultaneous bisection in an arbitrary independent polynomial coefficient
space. Absolute continuity is used on the original physical space only. -/
theorem exists_polynomial_bisection {n m : ℕ}
    (B : Fin (m+1) → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (μ : Fin m → Measure (Fin n → ℝ)) (hfin : ∀ i, IsFiniteMeasure (μ i))
    (hac : ∀ i, μ i ≪ volume) :
    ∃ u : Metric.sphere (0 : E (m+1)) 1,
      coefficientPolynomial B u ≠ 0 ∧ ∀ i,
        μ i {x | MvPolynomial.eval x (coefficientPolynomial B u) ≤ 0} = μ i univ / 2 ∧
        μ i {x | 0 ≤ MvPolynomial.eval x (coefficientPolynomial B u)} = μ i univ / 2 := by
  obtain ⟨u,hu⟩ := MathlibExt.Topology.Homotopy.BorsukUlamWanted.borsukUlam
    (polynomialBisectionMap B μ) (continuous_polynomialBisectionMap B hB μ hfin hac)
  refine ⟨u,coefficientPolynomial_sphere_ne_zero B hB u,fun i => ?_⟩
  letI := hfin i
  let P := coefficientPolynomial B u
  have hnull : μ i {x | MvPolynomial.eval x P = 0} = 0 :=
    hac i (real_polynomial_zero_volume P (coefficientPolynomial_sphere_ne_zero B hB u))
  have hcoord := congrArg (fun z : E m => z i) hu
  have heqReal : (μ i {x | MvPolynomial.eval x P ≤ 0}).toReal =
      (μ i {x | 0 ≤ MvPolynomial.eval x P}).toReal := by
    simpa [polynomialBisectionMap, coefficientPolynomial_neg, P] using hcoord
  have heq := (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (μ i) _)
    (measure_ne_top (μ i) _)).mp heqReal
  have hunion : {x | MvPolynomial.eval x P ≤ 0} ∪ {x | 0 ≤ MvPolynomial.eval x P} = univ := by
    ext x
    simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]
    exact le_total _ _
  have hinter : {x | MvPolynomial.eval x P ≤ 0} ∩ {x | 0 ≤ MvPolynomial.eval x P} =
      {x | MvPolynomial.eval x P = 0} := by
    ext x
    simp only [mem_inter_iff, mem_setOf_eq]
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le,h.ge⟩⟩
  have hmeasPos : MeasurableSet {x | 0 ≤ MvPolynomial.eval x P} :=
    (isClosed_le continuous_const (MvPolynomial.continuous_eval P)).measurableSet
  have hsum := measure_union_add_inter (μ := μ i) {x | MvPolynomial.eval x P ≤ 0} hmeasPos
  rw [hunion,hinter,hnull,add_zero] at hsum
  have hhalf : μ i {x | MvPolynomial.eval x P ≤ 0} = μ i univ / 2 := by
    apply (ENNReal.eq_div_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mpr
    rw [two_mul]
    simpa only [← heq] using hsum.symm
  exact ⟨hhalf,heq.symm.trans hhalf⟩

theorem totalDegree_coefficientPolynomial_le {n k D : ℕ}
    (B : Fin k → MvPolynomial (Fin n) ℝ) (hD : ∀ i, (B i).totalDegree ≤ D)
    (u : E k) : (coefficientPolynomial B u).totalDegree ≤ D := by
  unfold coefficientPolynomial
  rw [Fintype.linearCombination_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_smul_le (u i) (B i)).trans (hD i)

/-- Polynomial ham-sandwich with a proved degree bound, once an independent
family of m+1 degree-D polynomials is supplied. No singular Veronese pushforward
is assumed absolutely continuous. -/
theorem exists_polynomial_bisection_degree_le {n m D : ℕ}
    (B : Fin (m+1) → MvPolynomial (Fin n) ℝ) (hB : LinearIndependent ℝ B)
    (hD : ∀ i, (B i).totalDegree ≤ D)
    (μ : Fin m → Measure (Fin n → ℝ)) (hfin : ∀ i, IsFiniteMeasure (μ i))
    (hac : ∀ i, μ i ≪ volume) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ P.totalDegree ≤ D ∧ ∀ i,
      μ i {x | MvPolynomial.eval x P ≤ 0} = μ i univ / 2 ∧
      μ i {x | 0 ≤ MvPolynomial.eval x P} = μ i univ / 2 := by
  obtain ⟨u,hP,hu⟩ := exists_polynomial_bisection B hB μ hfin hac
  exact ⟨coefficientPolynomial B u,hP,totalDegree_coefficientPolynomial_le B hD u,hu⟩

end Kakeya4.Hard.MultilinearKakeya
