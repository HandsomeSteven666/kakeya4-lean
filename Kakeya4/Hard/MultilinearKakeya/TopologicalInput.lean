import Kakeya4.Hard.MultilinearKakeya.Imported.BorsukUlam
import Kakeya4.Foundation.Basic

/-! The proven topological input for CV: odd Euclidean sphere maps have a zero.
This does not assert the existence of polynomial visibility or CV factorization. -/

noncomputable section

namespace Kakeya4.Hard.MultilinearKakeya

theorem odd_sphere_map_has_zero {n : ℕ}
    (f : Metric.sphere (0 : E (n+1)) 1 → E n) (hf : Continuous f)
    (hodd : ∀ x, f (-x) = -f x) : ∃ x, f x = 0 := by
  obtain ⟨x,hx⟩ := MathlibExt.Topology.Homotopy.BorsukUlamWanted.borsukUlam f hf
  refine ⟨x, ?_⟩
  have heq : f x = -f x := hx.trans (hodd x)
  ext i
  have hi := congrArg (fun v : E n => v i) heq
  change (f x) i = -(f x) i at hi
  change (f x) i = 0
  linarith

end Kakeya4.Hard.MultilinearKakeya
