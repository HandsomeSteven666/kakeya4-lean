import OAI.MeasureTheory.Falconer.Recursion.UniformFrostmanProfiles

/-!
Adapted from OpenAI math, Apache-2.0, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/MeasureTheory/Falconer/Recursion/UniformFrostmanProfiles.lean.
The fixed-C absorption threshold is replaced by an explicit scale-dependent
budget. H and N0 now precede C, which may grow with the current depth N.
See the probe root COPYING and PROVENANCE.json. Compilation/audit pending.
-/

namespace OAI.Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

/-- All profile constants precede C; C may grow by the allowed small power at the current scale. -/
theorem scale_frostman_profile_envelope (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    {s lam : ℝ} (hlam : 0 < lam) :
    ∃ H N₀ : ℕ, 0 < H ∧
      (∀ N ≥ N₀, 0 < N ∧ 0 < N/H ∧ N/(N/H)+1 ≤ 2*H ∧
        ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) ∧ (2:ℝ)^(N/(N/H)+2) ≤ ((2:ℝ)^N)^lam) ∧
      ∀ N ≥ N₀, ∀ C : ℝ, 0 ≤ C → C ≤ ((2:ℝ)^N)^(lam/2) →
      ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ],
      (∀ x : Space d, ∀ r > 0, μ (Metric.ball x r) ≤ ENNReal.ofReal (C*r^s)) →
      ∀ p ∈ regularizationLeaves Q μ N,
        regularizationLabel Q μ N (N/H) p ∈ regularizationIndex Q μ N (N/H)
          (ENNReal.ofReal (((2:ℝ)^N)^(-lam))) →
        ∀ j ≤ N, s*(j:ℝ)/(N:ℝ)-((d:ℝ)+3)*lam ≤ sourceProfile Q μ N (N/H) p j := by
  obtain ⟨H,N₁,hH,hscales⟩ := PlanarFalconer.exists_regularization_block_control hlam
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed (by positivity : 0 < lam/2)
    ((2*Real.sqrt d*Q.side)^s)
  refine ⟨H,max N₁ N₂,hH,fun N hN ↦ hscales N ((le_max_left _ _).trans hN),?_⟩
  intro N hN C hC hCscale μ _ hball p hp hret j hj
  have hs := hscales N ((le_max_left _ _).trans hN)
  have hbudget : C*(2*Real.sqrt d*Q.side)^s ≤ ((2:ℝ)^N)^lam := by
    calc
      _ ≤ ((2:ℝ)^N)^(lam/2)*((2:ℝ)^N)^(lam/2) :=
        mul_le_mul hCscale (hconst N ((le_max_right _ _).trans hN))
          (Real.rpow_nonneg (by positivity) _) (by positivity)
      _ = _ := by
        rw [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
        congr 1
        ring
  apply sourceProfile_frostman_lower Q hQ μ hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2 hp
    (retained_label_real_mass_lower Q μ hret) _ hj
  intro k hk P hP
  have hh := dyadic_cell_frostman_profile_bound hd Q hQ μ hC hball hs.1 P
  rw [hP] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hbudget (by positivity))

end OAI.Falconer.Regularization
