import Kakeya4.Hard.Externals.Statements

/-!
# The external input bundle

`ExternalInputs` collects the five published inputs used by the manuscript. It is a
`Prop`-valued structure: every field is a proposition, so the structure is a `Subsingleton`
and carries no data.

The main theorem retains `ExternalInputs → IsKakeya 4 K → dimH K = 4`, but its proof still
has a gap: this is not a completed conditional proof. Determinant Kakeya and graph BSG are
proved independently and their fields remain for interface compatibility. The five-field
bundle is not the complete dependency closure; BPR, area-formula and section-10 transfer
obligations remain separately tracked.
-/

set_option autoImplicit false

namespace Kakeya4

/-- The five external published inputs used by the four-dimensional argument. -/
structure ExternalInputs : Prop where
  /-- Weighted full-time plank estimate (manuscript `lem:weighted-planks`). -/
  weightedPlanks : WeightedPlanks
  /-- Carbery–Valdimarsson determinant multilinear Kakeya. -/
  determinantMultilinearKakeya : DeterminantMultilinearKakeya
  /-- Wang–Zahl restricted-triple dot-product theorem. -/
  restrictedTripleDotProduct : RestrictedTripleDotProduct
  /-- Orponen–de Saxcé–Shmerkin multiplicative-convolution estimate. -/
  multiplicativeConvolution : MultiplicativeConvolution
  /-- Graph Balog–Szemerédi–Gowers theorem. -/
  graphBalogSzemerediGowers : GraphBalogSzemerediGowers

end Kakeya4
