import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialSignSetProjection

/-!
Uniform bounds for one-dimensional semialgebraic fibers with empty interior.
The finite sign description and specialization identity are reused from OpenAI math;
the bound is chosen before the parameter, including all coefficient values.
-/

noncomputable section
open Set Filter Polynomial
open scoped Topology Classical BigOperators
open OAI.Release061

namespace Kakeya4.Hard

/-- A fixed polynomial sign formula has a common finite bound for all of its
one-dimensional fibers whose interior is empty. Parameters need no topology. -/
theorem uniform_line_fiber_bound {X ι : Type*} {c : X → ι → ℝ}
    {S : Set (X × ℝ)}
    (hS : PolynomialSignSet
      (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) S) :
    ∃ N : ℕ, ∀ x, interior {y : ℝ | (x,y) ∈ S} = ∅ →
      ∃ F : Finset ℝ, F.card ≤ N ∧ {y : ℝ | (x,y) ∈ S} ⊆ F := by
  obtain ⟨s,W,hW⟩ := hS.finite_sign_description
  let Q : s → X → ℝ[X] := fun p x =>
    ((MvPolynomial.optionEquivLeft ℝ ι p.val).map (MvPolynomial.eval (c x)))
  let d : s → ℕ := fun p => (MvPolynomial.optionEquivLeft ℝ ι p.val).natDegree
  refine ⟨∑ p, d p, fun x hx => ?_⟩
  let F : Finset ℝ := Finset.univ.biUnion (fun p : s => (Q p x).roots.toFinset)
  refine ⟨F, ?_, ?_⟩
  · exact Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun p _ =>
      (Multiset.toFinset_card_le _).trans ((card_roots' _).trans natDegree_map_le)))
  · intro y hy
    by_contra hF
    have hroot (p : s) (hp : Q p x ≠ 0) : (Q p x).eval y ≠ 0 := by
      intro hz
      apply hF
      exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _,
        Multiset.mem_toFinset.mpr ((mem_roots hp).mpr hz)⟩
    have hloc (p : s) : ∀ᶠ z in 𝓝 y,
        SignType.sign ((Q p x).eval z) = SignType.sign ((Q p x).eval y) := by
      by_cases hp : Q p x = 0
      · simp [hp]
      · exact ((continuousAt_sign_of_ne_zero (hroot p hp)).comp
          (f := fun z : ℝ => (Q p x).eval z)
          (Q p x).continuous.continuousAt).eventually
          ((isOpen_discrete {SignType.sign ((Q p x).eval y)}).mem_nhds (by simp))
    have hnhds : {z : ℝ | (x,z) ∈ S} ∈ 𝓝 y := by
      filter_upwards [Filter.eventually_all.mpr hloc] with z hz
      apply (hW (x,z)).mpr
      have he : (fun p : s => SignType.sign
          (MvPolynomial.eval (fun o => Option.elim o z (c x)) p.val)) =
          (fun p : s => SignType.sign
          (MvPolynomial.eval (fun o => Option.elim o y (c x)) p.val)) := by
        funext p
        simpa only [Q, OAI.Release061.SignElimination.eval_optionEquivLeft] using hz p
      rw [he]
      exact (hW (x,y)).mp hy
    have hi := mem_interior_iff_mem_nhds.mpr hnhds
    simpa only [hx, mem_empty_iff_false] using hi

end Kakeya4.Hard
