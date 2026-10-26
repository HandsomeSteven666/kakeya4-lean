import Kakeya4.Hard.MultilinearKakeya.LineMeasureConsumers

/-! The finite-family and finite Borel line-law determinant Kakeya input
needed in manuscript section6. Other isotropic inputs are not asserted here. -/

namespace Kakeya4.Hard

theorem finite_and_measure_determinantKakeya :
    MultilinearKakeya.ManuscriptBound ∧ MultilinearKakeya.LineMeasureManuscriptBound :=
  ⟨MultilinearKakeya.manuscriptBound,MultilinearKakeya.lineMeasureManuscriptBound⟩

end Kakeya4.Hard
