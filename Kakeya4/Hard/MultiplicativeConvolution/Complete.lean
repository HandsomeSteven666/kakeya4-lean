import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FourierAllFactors

/-! Complete original finite-scale OSS Fourier decay, independent of ExternalInputs.
The proof and its actual fixed-kernel consumer are packaged from the audited Hard closure.
This module does not claim that the remaining four-dimensional proof is complete. -/
set_option autoImplicit false
namespace Kakeya4.Hard.MultiplicativeConvolution

theorem finiteScaleDecay_proof (kernel : SmoothKernel) : FiniteScaleDecay kernel :=
  OAI.Falconer.finiteScaleDecay_all kernel

theorem manuscriptDecay_proof : ManuscriptDecay := OAI.Falconer.manuscriptDecay_proof

#print axioms finiteScaleDecay_proof
#print axioms manuscriptDecay_proof
end Kakeya4.Hard.MultiplicativeConvolution
