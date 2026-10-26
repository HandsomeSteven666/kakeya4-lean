import Kakeya4.Hard.RestrictedTriple.PrunedInput

set_option autoImplicit false
noncomputable section
open Set

namespace Kakeya4.Hard.RestrictedTriple

/-- Scale the first class about the origin and translate both endpoint classes together.
Their scale factors may differ; the actual dot-difference is multiplied by c*d. -/
def endpointNormalization (c d : ℝ) (z : Plane) (t : Triple) : Triple :=
  (c • t.1,z+d • t.2.1,z+d • t.2.2)

theorem endpointNormalization_injective {c d : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) (z : Plane) :
    Function.Injective (endpointNormalization c d z) := by
  intro t u h
  have h0 := congrArg (fun v : Triple ↦ v.1) h
  have h1 := congrArg (fun v : Triple ↦ v.2.1) h
  have h2 := congrArg (fun v : Triple ↦ v.2.2) h
  change c • t.1 = c • u.1 at h0
  change z+d • t.2.1 = z+d • u.2.1 at h1
  change z+d • t.2.2 = z+d • u.2.2 at h2
  have ht0 := congrArg (fun v : Plane ↦ c⁻¹ • v) h0
  have ht1 := congrArg (fun v : Plane ↦ d⁻¹ • v) (add_left_cancel h1)
  have ht2 := congrArg (fun v : Plane ↦ d⁻¹ • v) (add_left_cancel h2)
  simp only [smul_smul,inv_mul_cancel₀ hc,inv_mul_cancel₀ hd,one_smul] at ht0 ht1 ht2
  exact Prod.ext ht0 (Prod.ext ht1 ht2)

theorem endpointNormalization_encard {c d : ℝ} (hc : c ≠ 0) (hd : d ≠ 0)
    (z : Plane) (Q : Set Triple) :
    (endpointNormalization c d z '' Q).encard = Q.encard :=
  (endpointNormalization_injective hc hd z).encard_image Q

theorem dotDifference_endpointNormalization (c d : ℝ) (z : Plane) (t : Triple) :
    dotDifference (endpointNormalization c d z t) = (c*d)*dotDifference t := by
  have heq : (z+d • t.2.1)-(z+d • t.2.2) = d • (t.2.1-t.2.2) := by module
  simp only [dotDifference,endpointNormalization,heq,inner_smul_left,inner_smul_right]
  simp
  ring

theorem dotDifferenceImage_endpointNormalization (c d : ℝ) (z : Plane) (Q : Set Triple) :
    dotDifferenceImage (endpointNormalization c d z '' Q) =
      (fun x : ℝ ↦ (c*d)*x) '' dotDifferenceImage Q := by
  simp only [dotDifferenceImage,image_image,Function.comp_def,dotDifference_endpointNormalization]

/-- Translating the first class adds a genuine endpoint-linear term. -/
theorem dotDifference_translate_first (z : Plane) (t : Triple) :
    dotDifference (t.1+z,t.2.1,t.2.2) = dotDifference t+inner ℝ z (t.2.1-t.2.2) := by
  simp only [dotDifference,inner_add_left]

end Kakeya4.Hard.RestrictedTriple
