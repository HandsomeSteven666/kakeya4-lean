import Kakeya4.Hard.Analysis.SlopeJacobian
import Kakeya4.Hard.Analysis.MonicGoodTimes
import Kakeya4.Hard.Analysis.AffineGoodTimes
import Kakeya4.Hard.Analysis.TimeSliceVolume
import Kakeya4.Hard.Analysis.SelectorVolume
import Kakeya4.Hard.Analysis.QuadraticSliceVolume
import Kakeya4.Hard.Analysis.RegularFibers
import Kakeya4.Hard.Analysis.RegularSlopeFibers

/-! All theorem declarations of the current selector-volume chain. -/

#print axioms Kakeya4.Hard.hasFDerivAt_slopeMap
#print axioms Kakeya4.Hard.contDiffAt_slopeMap
#print axioms Kakeya4.Hard.jacobianPolynomial_monic
#print axioms Kakeya4.Hard.jacobianPolynomial_natDegree
#print axioms Kakeya4.Hard.eval_jacobianPolynomial
#print axioms Kakeya4.Hard.det_slopeDerivative
#print axioms Kakeya4.Hard.slope_volume_le_of_jacobian_lower
#print axioms Kakeya4.Hard.measurableSet_badRootTimes
#print axioms Kakeya4.Hard.volume_badRootTimes_le
#print axioms Kakeya4.Hard.radius_le_norm_sub_root
#print axioms Kakeya4.Hard.pow_natDegree_le_abs_eval_of_not_mem_badRootTimes
#print axioms Kakeya4.Hard.volume_interval_sdiff_badRootTimes_ge
#print axioms Kakeya4.Hard.cubic_good_times
#print axioms Kakeya4.Hard.measurableSet_affineBadTimes
#print axioms Kakeya4.Hard.volume_affineBadTimes_le
#print axioms Kakeya4.Hard.simultaneous_cubic_affine_good_times
#print axioms Kakeya4.Hard.lintegral_measure_sections_swap
#print axioms Kakeya4.Hard.good_time_mass_le_integrated_sections
#print axioms Kakeya4.Hard.integrated_slice_volume_bound
#print axioms Kakeya4.Hard.measurableSet_selectorGoodSet
#print axioms Kakeya4.Hard.selector_good_time_mass
#print axioms Kakeya4.Hard.integrated_selector_volume_bound
#print axioms Kakeya4.Hard.selector_mass_bound_of_scaled
#print axioms Kakeya4.Hard.selector_volume_bound
#print axioms Kakeya4.Hard.measurableSet_quadraticStrip
#print axioms Kakeya4.Hard.measure_quadraticStrip_le
#print axioms Kakeya4.Hard.injOn_connectedComponents_of_isolated
#print axioms Kakeya4.Hard.encard_isolated_le_components
#print axioms Kakeya4.Hard.isOpen_singleton_in_fiber
#print axioms Kakeya4.Hard.encard_regular_fiber_le_components
#print axioms Kakeya4.Hard.encard_regular_fiber_le_of_components_bound
#print axioms Kakeya4.Hard.exists_open_injOn_of_regular_derivative
#print axioms Kakeya4.Hard.regular_slope_fiber_bound_of_components
#print axioms Kakeya4.Hard.selector_volume_bound_of_components
