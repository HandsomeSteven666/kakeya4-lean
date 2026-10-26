import Kakeya4.Hard.MultilinearKakeya.RelativeOperatorGeometry

/-! Dimensional bounds for a disjoint family of relative operator neighborhoods.
The proof normalizes at one center and uses ordinary Haar ball volumes in the
endomorphism space; it does not use the condition number of that center. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology

namespace Kakeya4.Hard.MultilinearKakeya

theorem finite_disjoint_ball_card_mul_pow_le {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] {ι : Type*} [Fintype ι] (x : ι → V)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hd : Pairwise (fun i j => Disjoint (Metric.ball (x i) r) (Metric.ball (x j) r)))
    (hsub : ∀ i, Metric.ball (x i) r ⊆ Metric.ball 0 R) :
    (Fintype.card ι : ℝ) * r^(Module.finrank ℝ V) ≤ R^(Module.finrank ℝ V) := by
  have hfin (a : V) (s : ℝ) : μ (Metric.ball a s) ≠ ⊤ :=
    ne_of_lt ((measure_mono Metric.ball_subset_closedBall).trans_lt
      (isCompact_closedBall a s).measure_lt_top)
  have hunit : 0 < (μ (Metric.ball (0 : V) 1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos μ 0 zero_lt_one)) (hfin 0 1)
  have hv (a : V) {s : ℝ} (hs : 0 < s) :
      μ.real (Metric.ball a s) = s^(Module.finrank ℝ V) * (μ (Metric.ball (0 : V) 1)).toReal := by
    rw [measureReal_def, μ.addHaar_ball_of_pos a hs, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_pos hs _).le]
  have hm : (∑ i, μ.real (Metric.ball (x i) r)) ≤ μ.real (Metric.ball (0 : V) R) := by
    rw [← measureReal_iUnion_fintype hd (fun _ => Metric.isOpen_ball.measurableSet) (fun i => hfin (x i) r)]
    exact measureReal_mono (iUnion_subset hsub) (hfin 0 R)
  simp_rw [hv _ hr] at hm
  rw [hv 0 hR, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hm
  apply (mul_le_mul_iff_right₀ hunit).mp
  convert hm using 1 <;> ring

theorem finite_disjoint_ball_card_le {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] {ι : Type*} [Fintype ι] (x : ι → V)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hd : Pairwise (fun i j => Disjoint (Metric.ball (x i) r) (Metric.ball (x j) r)))
    (hsub : ∀ i, Metric.ball (x i) r ⊆ Metric.ball 0 R) :
    (Fintype.card ι : ℝ) ≤ (R/r)^(Module.finrank ℝ V) := by
  rw [div_pow]
  apply (le_div_iff₀ (pow_pos hr _)).mpr
  exact finite_disjoint_ball_card_mul_pow_le μ x hr hR hd hsub

theorem finrank_operator (n : ℕ) : Module.finrank ℝ (Operator n) = n*n := by
  rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E n) (F' := E n)).finrank_eq,
    Module.finrank_linearMap]
  simp only [E, finrank_euclideanSpace, Fintype.card_fin]

theorem relativeOperator_neighbour_card_bound {n : ℕ} {ι : Type*} [Fintype ι]
    (T₀ : E n ≃L[ℝ] E n) (T : ι → E n ≃L[ℝ] E n)
    {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hfor : ∀ i, ‖T₀.symm.toContinuousLinearMap.comp (T i).toContinuousLinearMap‖ ≤ C)
    (hback : ∀ i, ‖(T i).symm.toContinuousLinearMap.comp T₀.toContinuousLinearMap‖ ≤ C)
    (hd : Pairwise (fun i j => Disjoint (relativeOperatorBall (T i) δ) (relativeOperatorBall (T j) δ))) :
    (Fintype.card ι : ℝ) ≤ (C*(1+δ)/(δ/C))^(n*n) := by
  let F := fun i => (T i).trans T₀.symm
  have hFn (i : ι) : ‖(F i).toContinuousLinearMap‖ ≤ C := hfor i
  have hFi (i : ι) : ‖(F i).symm.toContinuousLinearMap‖ ≤ C := hback i
  have hsmall (i : ι) := ordinary_ball_subset_relativeOperatorBall (F i) hC hδ (hFi i)
  have hpre (i : ι) (A : Operator n) :
      A ∈ relativeOperatorBall (F i) δ ↔
        T₀.toContinuousLinearMap.comp A ∈ relativeOperatorBall (T i) δ := by
    have he : T₀.symm.toContinuousLinearMap.comp (T₀.toContinuousLinearMap.comp A) = A := by
      ext x
      simp
    have h := normalize_relativeOperatorBall_iff T₀ (T i) (T₀.toContinuousLinearMap.comp A) δ
    rwa [he] at h
  have hdisj : Pairwise (fun i j => Disjoint
      (Metric.ball (F i).toContinuousLinearMap (δ/C))
      (Metric.ball (F j).toContinuousLinearMap (δ/C))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro A hi hj
    exact Set.disjoint_left.mp (hd hij)
      ((hpre i A).mp (hsmall i hi)) ((hpre j A).mp (hsmall j hj))
  have hsub (i : ι) : Metric.ball (F i).toContinuousLinearMap (δ/C) ⊆
      Metric.ball (0 : Operator n) (C*(1+δ)) :=
    (hsmall i).trans (relativeOperatorBall_subset_ordinary_ball (F i) hC (hFn i))
  let : MeasurableSpace (Operator n) := borel (Operator n)
  let μ := (Module.finBasis ℝ (Operator n)).addHaar
  have h := finite_disjoint_ball_card_le μ (fun i => (F i).toContinuousLinearMap)
    (div_pos hδ hC) (mul_pos hC (by linarith)) hdisj hsub
  rwa [finrank_operator] at h

end Kakeya4.Hard.MultilinearKakeya
