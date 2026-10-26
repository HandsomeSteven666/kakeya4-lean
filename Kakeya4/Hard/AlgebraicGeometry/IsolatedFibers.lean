import Kakeya4.Hard.AlgebraicGeometry.UniformDiscreteFibers

/-! Isolated points of full fibers form a semialgebraic family with uniform cardinal bound. -/

noncomputable section
open Set Filter
open scoped Topology Classical BigOperators
open OAI.Release061 OAI.Release061.SignElimination

namespace Kakeya4.Hard

/-- Isolation is tested against the entire fiber, using coordinate neighborhoods. -/
def isolatedFiberPoints {X κ : Type*} (S : Set (X × (κ → ℝ))) : Set (X × (κ → ℝ)) :=
  {z | z ∈ S ∧ ∃ r : ℝ, 0 < r ∧ ∀ w : κ → ℝ,
    (z.1,w) ∈ S → (∀ j, w j - z.2 j < r ∧ z.2 j - w j < r) → w = z.2}

/-- Quantifier elimination applies to isolation; derivatives are not required to
be semialgebraic in order to bound regular preimages. -/
theorem polynomialSignSet_isolatedFiberPoints {X ι κ : Type*} [Fintype κ]
    {c : X → ι → ℝ} {S : Set (X × (κ → ℝ))}
    (hS : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) S) :
    PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      (isolatedFiberPoints S) := by
  let d := fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2
  let e := fun z : (X × (κ → ℝ)) × ℝ => fun o => Option.elim o z.2 (d z.1)
  let b := fun z : ((X × (κ → ℝ)) × ℝ) × (κ → ℝ) => Sum.elim (e z.1) z.2
  have hs : PolynomialSignSet b {z | (z.1.1.1,z.2) ∈ S} :=
    hS.coordinate_preimage (fun z : ((X × (κ → ℝ)) × ℝ) × (κ → ℝ) => (z.1.1.1,z.2))
      (Sum.elim (fun i => Sum.inl (some (Sum.inl i))) Sum.inr)
      (by intro z i; cases i <;> rfl)
  have hnear : PolynomialSignSet b
      {z | ∀ j, z.2 j - z.1.1.2 j < z.1.2 ∧ z.1.1.2 j - z.2 j < z.1.2} := by
    apply PolynomialSignSet.forall_finite
    intro j
    have h₁ := PolynomialSignSet.positive (c := b)
      (MvPolynomial.X (Sum.inl none) -
        (MvPolynomial.X (Sum.inr j) - MvPolynomial.X (Sum.inl (some (Sum.inr j)))))
    have h₂ := PolynomialSignSet.positive (c := b)
      (MvPolynomial.X (Sum.inl none) -
        (MvPolynomial.X (Sum.inl (some (Sum.inr j))) - MvPolynomial.X (Sum.inr j)))
    convert h₁.inter h₂ using 1
    ext z
    simp [b,e,d,sub_pos]
  have heq : PolynomialSignSet b {z | z.2 = z.1.1.2} := by
    have hh := PolynomialSignSet.forall_finite (c := b)
      (fun j z => z.2 j = z.1.1.2 j) (fun j => by
        convert PolynomialSignSet.zero (c := b)
          (MvPolynomial.X (Sum.inr j) - MvPolynomial.X (Sum.inl (some (Sum.inr j)))) using 1
        ext z
        simp [b,e,d,sub_eq_zero])
    simpa only [funext_iff] using hh
  have hall : PolynomialSignSet e {z | ∀ w : κ → ℝ,
      (z.1.1,w) ∈ S → (∀ j, w j - z.1.2 j < z.2 ∧ z.1.2 j - w j < z.2) → w = z.1.2} := by
    have hbad := (hs.inter hnear).inter heq.compl
    have hp := (polynomialSignSet_projection_finite hbad).compl
    convert hp using 1
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, not_exists, not_and]
    aesop
  have hr : PolynomialSignSet e {z | 0 < z.2} := by
    simpa only [MvPolynomial.eval_X, e, Option.elim_none] using
      (PolynomialSignSet.positive (c := e) (MvPolynomial.X none))
  have hex := polynomialSignSet_projection_one (hr.inter hall)
  exact hS.inter hex

/-- Isolation in the full fiber implies isolation in any subfamily of it. -/
theorem isolatedFiberPoints_discrete {X κ : Type*} [Fintype κ]
    (S : Set (X × (κ → ℝ))) (x : X) (v : κ → ℝ)
    (hv : (x,v) ∈ isolatedFiberPoints S) :
    ∃ U : Set (κ → ℝ), IsOpen U ∧ v ∈ U ∧
      ∀ w, (x,w) ∈ isolatedFiberPoints S → w ∈ U → w = v := by
  obtain ⟨_,r,hr,hiso⟩ := hv
  let U := {w : κ → ℝ | ∀ j, w j - v j < r ∧ v j - w j < r}
  refine ⟨U, ?_, by intro j; simp [hr], fun w hw hU => hiso w hw.1 hU⟩
  have he : U = ⋂ j, {w : κ → ℝ | w j - v j < r ∧ v j - w j < r} := by
    ext w
    simp [U]
  rw [he]
  apply isOpen_iInter_of_finite
  intro j
  exact (isOpen_lt ((continuous_apply j).sub continuous_const) continuous_const).inter
    (isOpen_lt (continuous_const.sub (continuous_apply j)) continuous_const)

/-- A common finite bound for all isolated points of all full fibers. -/
theorem uniform_isolated_fiber_bound {X ι κ : Type*} [Fintype κ]
    {c : X → ι → ℝ} {S : Set (X × (κ → ℝ))}
    (hS : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) S) :
    ∃ N : ℕ, ∀ x, {v | (x,v) ∈ isolatedFiberPoints S}.encard ≤ N := by
  obtain ⟨N,hN⟩ := uniform_discrete_fiber_bound (polynomialSignSet_isolatedFiberPoints hS)
  exact ⟨N,fun x => hN x (isolatedFiberPoints_discrete S x)⟩

/-- A genuine isolating open neighborhood yields the polynomial coordinate-box
certificate used in quantifier elimination. -/
theorem mem_isolatedFiberPoints_of_local {X κ : Type*} [Fintype κ]
    (S : Set (X × (κ → ℝ))) (x : X) (v : κ → ℝ) (hv : (x,v) ∈ S)
    (hlocal : ∃ U : Set (κ → ℝ), IsOpen U ∧ v ∈ U ∧
      ∀ w, (x,w) ∈ S → w ∈ U → w = v) :
    (x,v) ∈ isolatedFiberPoints S := by
  obtain ⟨U,hU,hvU,hiso⟩ := hlocal
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hvU)
  refine ⟨hv,r,hr,fun w hw hnear => hiso w hw (hball ?_)⟩
  rw [Metric.mem_ball,dist_eq_norm]
  apply (pi_norm_lt_iff hr).mpr
  intro j
  change |w j - v j| < r
  exact abs_lt.mpr ⟨by linarith [(hnear j).2],(hnear j).1⟩

/-- Uniform bounds apply to any chosen collection of locally isolated points,
while the isolation test continues to use the entire original fiber. -/
theorem uniform_locally_isolated_fiber_bound {X ι κ : Type*} [Fintype κ]
    {c : X → ι → ℝ} {S : Set (X × (κ → ℝ))}
    (hS : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) S) :
    ∃ N : ℕ, ∀ x (R : Set (κ → ℝ)),
      (∀ v ∈ R, (x,v) ∈ S ∧ ∃ U : Set (κ → ℝ), IsOpen U ∧ v ∈ U ∧
        ∀ w, (x,w) ∈ S → w ∈ U → w = v) → R.encard ≤ N := by
  obtain ⟨N,hN⟩ := uniform_isolated_fiber_bound hS
  refine ⟨N,fun x R hR => (Set.encard_mono ?_).trans (hN x)⟩
  intro v hv
  exact mem_isolatedFiberPoints_of_local S x v (hR v hv).1 (hR v hv).2

end Kakeya4.Hard
