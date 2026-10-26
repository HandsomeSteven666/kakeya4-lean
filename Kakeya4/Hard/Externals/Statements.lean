import Kakeya4.Foundation.Defs.Kakeya
import Kakeya4.Foundation.Defs.Plank
import Kakeya4.Construction.Combinatorics.GraphBSG
import Kakeya4.Hard.DeterminantKakeya

/-!
# External published inputs

The manuscript's proof uses five results whose formal status is tracked below. The graph-BSG item now has a curated proof in the Construction zone; unresolved inputs are *not* introduced as `axiom`s.

Status is tracked in `ir/dependencies.json` and checked by `scripts/check_dependencies.py`:

* `WeightedPlanks` is **`stated`**: a real proposition defined in `Kakeya4/Foundation/Defs/Plank.lean`
  (no `sorry`), but not proved. It remains an explicit hypothesis of the main theorem.
* `DeterminantMultilinearKakeya` and graph BSG have real statements and complete proofs.
  The determinant input includes both finite families and arbitrary finite Borel line laws
  in the manuscript's dimensional range, with exact radius scaling.
* The restricted-triple and multiplicative-convolution items remain **`opaque`**:
  their statements are still `def ... : Prop := by sorry`.

Do not replace any body by `True`: `scripts/check_no_forbidden.py` rejects it.
-/

set_option autoImplicit false

namespace Kakeya4

/-- **Weighted full-time plank estimate** (manuscript `lem:weighted-planks`, §2).

Source: the 4D manuscript cites this as `[Lemma 2.3]{ThreeDimensional}`, where
`ThreeDimensional` is **OpenAI's own 3D preprint** *The Kakeya maximal conjecture in three
dimensions* (2026-09-23), lemma `lem:weighted-set`. It is **not** a peer-reviewed
Wang–Zahl result; its proof is conditional on the plank cap hypothesis and uses the
preprint's `lem:weighted-convex-set`. Neither is formalized. See `docs/LANDSCAPE.md`.

The proposition is formalized in `Kakeya4.Plank.WeightedPlanks`; see that module for the
statement, the modelling conventions and the quantifier ledger. It is **not proved**:
this alias only records that the dependency now has a real statement.

Manuscript statement (verbatim excerpt):

> Fix a bounded affine-line chart in `ℝ²`, and a fixed permitted enlargement of mesh cells.
> For every `ε > 0`, there are `η_ε > 0` and `C_ε < ∞` with the following property.
> Let `M_i(t) = b_i + t u_i`, `0 ≤ t ≤ 1`, be finitely many indexed traces, with
> `b_i, u_i` in the fixed bounded chart, and arbitrary positive weights `ω_i`.
> Repeated traces are allowed. Let `D ≥ 1`, `ρ = D⁻¹`, and suppose that every full-time
> plank `P = {(t,x) : 0 ≤ t ≤ 1, |⟨x - c - t v, e₁⟩| ≤ aρ, |⟨x - c - t v, e₂⟩| ≤ bρ}`,
> `1 ≤ a ≤ b ≤ D`, where `(e₁,e₂)` is an arbitrary orthonormal spatial frame and
> `c, v ∈ ℝ²`, satisfies `∑_{i : M_i ⊂ P} ω_i ≤ A a b`. Fixed dilations of these plank
> tests are permitted. Mark time bins `J_i`, each of length `ρ`, with `#J_i ≥ D^{1-η_ε}`.
> If `E_vis` is the union of the spatial–time mesh cells visited at their bin centers, or
> fixed enlargements of those cells, then `∑_i ω_i #J_i ≤ C_ε A D^ε #E_vis`.

STATUS: `stated` (real statement, no proof). -/
abbrev WeightedPlanks : Prop := Plank.WeightedPlanks

/-- The external-input alias is definitionally the curated statement. This `rfl` proof makes
it impossible to replace the alias by `True` without breaking the build. -/
theorem weightedPlanks_eq_plank : (WeightedPlanks : Prop) = Plank.WeightedPlanks := rfl

/-- **Determinant multilinear Kakeya** (Carbery–Valdimarsson).

Source: A. Carbery and S. I. Valdimarsson, *The endpoint multilinear Kakeya theorem via the
Borsuk–Ulam theorem*, J. Funct. Anal. 264 (2013), 1643–1663.

The equal ambient/wedge dimension specialization used in §6: dimensions `2 ≤ n ≤ 4`,
full affine lines with arbitrary anchors and unit directions, determinant weights,
nonnegative finite-family weights and arbitrary finite nonnegative Borel line laws.
The positive dimensional constant precedes the families/measures and every positive radius;
the scaling factor is exactly `r^n`. Repeated line parameters and zero weights/masses are allowed.
No fixed transversality, atomicity, bounded-anchor or finite-cardinality hypothesis is added.

The line laws use anchored unit-direction parameters; measurable source-family pushforwards
and actual successful-tuple determinant-threshold mass are handled by
`Hard.MultilinearKakeya.LineMeasureConsumers`. This input does not assert the remaining
physical velocity graph, other isotropic arguments, or the four-dimensional main theorem.

STATUS: `proved`, via the independently verified Hard finite/measure endpoint closure. -/
def DeterminantMultilinearKakeya : Prop :=
  Hard.MultilinearKakeya.ManuscriptBound ∧ Hard.MultilinearKakeya.LineMeasureManuscriptBound

/-- The external input is exactly the real finite-family and line-law statements. -/
theorem determinantMultilinearKakeya_eq_finite_and_measure :
    DeterminantMultilinearKakeya =
      (Hard.MultilinearKakeya.ManuscriptBound ∧ Hard.MultilinearKakeya.LineMeasureManuscriptBound) := rfl

/-- The determinant input has a complete proof, independent of ExternalInputs. -/
theorem determinantMultilinearKakeya_proof : DeterminantMultilinearKakeya :=
  Hard.finite_and_measure_determinantKakeya

/-- **Restricted-triple dot-product theorem** (Wang–Zahl).

Source: H. Wang and J. Zahl, *Sticky Kakeya sets and the sticky Kakeya conjecture*,
J. Amer. Math. Soc. 39 (2026), 515–585.

Used in the manuscript for planar rigidity in the finite-narrowness regime.

TODO(statement): formalize the restricted-triple configuration and the dot-product estimate.

STATUS: `opaque` (statement not yet formalized). -/
def RestrictedTripleDotProduct : Prop := by
  sorry

/-- **Multiplicative-convolution estimate** (Orponen–de Saxcé–Shmerkin).

Source: T. Orponen, N. de Saxcé and P. Shmerkin, multiplicative convolution estimates for
Furstenberg-type problems.

Used in `re:retained-edge-rigidity` to construct scalar coefficients with small interval
probabilities.

TODO(statement): formalize the convolution inequality and its admissibility hypotheses.

STATUS: `opaque` (statement not yet formalized). -/
def MultiplicativeConvolution : Prop := by
  sorry

/-- **Graph Balog–Szemerédi–Gowers theorem** (Sudakov–Szemerédi–Vu; Tao–Vu).

Source: Sudakov–Szemerédi–Vu, *On a question of Erdős and Moser*, Duke Math. J. 129 (2005);
Tao–Vu, *Additive Combinatorics* (2006), Theorem 2.29. The manuscript uses the graph form
recorded as `re:graph-bsg`: a dense bipartite graph contains large vertex sets whose
induced subgraph is dense and whose sumset is small.

The statement is formalized here and proved below from the retained-edge witness in the Construction zone.

Manuscript form: for finite nonempty `A, B` in an abelian group and `E ⊆ A × B` with
`|E| ≥ θ |A| |B|`, there exist `A' ⊆ A`, `B' ⊆ B` with
`|A'| ≥ c θ |A|`, `|B'| ≥ c θ |B|`, `|E ∩ (A' × B')| ≥ c θ² |A| |B|`, and
`|A' + B'| ≤ C₀ θ⁻⁵ |C|³ / (|A| |B|)`, where `C = {x + y : (x,y) ∈ E}`. -/
def GraphBalogSzemerediGowers : Prop := by
  classical
  exact
    ∃ c C₀ : ℝ, 0 < c ∧ 0 < C₀ ∧
    ∀ (G : Type) [AddCommGroup G] [DecidableEq G]
      (A B : Finset G), A.Nonempty → B.Nonempty →
      ∀ (E : Finset (G × G)), E ⊆ A.product B →
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      θ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ) →
      ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
        c * θ * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
        c * θ * (B.card : ℝ) ≤ (B'.card : ℝ) ∧
        c * θ ^ 2 * (A.card : ℝ) * (B.card : ℝ) ≤
          ((E.filter (fun p => p.1 ∈ A' ∧ p.2 ∈ B')).card : ℝ) ∧
        (((A'.product B').image (fun p => p.1 + p.2)).card : ℝ) ≤
          C₀ * (((E.image (fun p => p.1 + p.2)).card : ℝ) ^ 3) /
            (θ ^ 5 * (A.card : ℝ) * (B.card : ℝ))

/-- The manuscript graph-BSG statement, proved from the Construction retained-edge witness.
The witness has stronger endpoint constants (`1/8` and `1/4`), and its induced-edge constant
is exactly the uniform `1/32`; the original edge-sumset is definitionally the retained image. -/
theorem graphBalogSzemerediGowers_proof : GraphBalogSzemerediGowers := by
  classical
  unfold GraphBalogSzemerediGowers
  refine ⟨1 / 32, 32768, by norm_num, by norm_num, ?_⟩
  intro G _ _ A B hA hB E hE θ hθ hθle hdense
  obtain ⟨A', B', hA'sub, hB'sub, hA'size, hB'size, hEdges, hSumset⟩ :=
    GraphBSG.exists_graphBSG_sumset_witness A B E θ hθ hA hB hE hdense
  have hAc : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hBc : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
  refine ⟨A', B', hA'sub, hB'sub, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith [hEdges]
  · simpa [GraphBSG.retainedGraphSumSet] using hSumset

end Kakeya4
