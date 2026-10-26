import Kakeya4.Hard.AlgebraicGeometry.AffineDerivative
import Kakeya4.Hard.AlgebraicGeometry.AllowedRegion
import Kakeya4.Hard.AlgebraicGeometry.CompactTimeTests
import Kakeya4.Hard.AlgebraicGeometry.DiscreteProjection
import Kakeya4.Hard.AlgebraicGeometry.EligibleFormula
import Kakeya4.Hard.AlgebraicGeometry.EligibleSelector
import Kakeya4.Hard.AlgebraicGeometry.EligibleSubpowerVolume
import Kakeya4.Hard.AlgebraicGeometry.EligibleVolume
import Kakeya4.Hard.AlgebraicGeometry.HiddenQuadratic
import Kakeya4.Hard.AlgebraicGeometry.Imported.AlgebraicGraphPolynomial
import Kakeya4.Hard.AlgebraicGeometry.Imported.AnalyticZeroNull
import Kakeya4.Hard.AlgebraicGeometry.Imported.DecayWeightDeriv
import Kakeya4.Hard.AlgebraicGeometry.Imported.HermiteSignature
import Kakeya4.Hard.AlgebraicGeometry.Imported.InterpolateRealUpper
import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialCoordinateRay
import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialEmptyInterior
import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialLineDegree
import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialSignSetChoice
import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialSignSetChoice2
import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialSignSetFinite
import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialSignSetFinite2
import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialSignSetProjection
import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialSignSetProjection2
import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialSignSetQuery
import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialSignSetRoot
import Kakeya4.Hard.AlgebraicGeometry.Imported.PolynomialSignSetSigns
import Kakeya4.Hard.AlgebraicGeometry.Imported.RealPolynomialAnalyticRoot
import Kakeya4.Hard.AlgebraicGeometry.Imported.RegularSimpleSheet
import Kakeya4.Hard.AlgebraicGeometry.Imported.RootEvaluationSurjective
import Kakeya4.Hard.AlgebraicGeometry.Imported.RootMomentCoefficients
import Kakeya4.Hard.AlgebraicGeometry.Imported.RootSignPattern
import Kakeya4.Hard.AlgebraicGeometry.Imported.SampleAllChambers
import Kakeya4.Hard.AlgebraicGeometry.Imported.SemialgebraicAnalytic
import Kakeya4.Hard.AlgebraicGeometry.Imported.SeparableSpecialization
import Kakeya4.Hard.AlgebraicGeometry.Imported.SignatureRootValues
import Kakeya4.Hard.AlgebraicGeometry.Imported.SignVariationsPositiveRoots
import Kakeya4.Hard.AlgebraicGeometry.Imported.SquarefreeRelationOffDenominator
import Kakeya4.Hard.AlgebraicGeometry.Imported.TarskiQueryCharpoly
import Kakeya4.Hard.AlgebraicGeometry.Imported.VectorGraphCoordinate
import Kakeya4.Hard.AlgebraicGeometry.IsolatedFibers
import Kakeya4.Hard.AlgebraicGeometry.ManuscriptEligibility
import Kakeya4.Hard.AlgebraicGeometry.MeasurableSelector
import Kakeya4.Hard.AlgebraicGeometry.PhysicalChartData
import Kakeya4.Hard.AlgebraicGeometry.PhysicalRegionVolume
import Kakeya4.Hard.AlgebraicGeometry.PolynomialNull
import Kakeya4.Hard.AlgebraicGeometry.QuadraticPolynomial
import Kakeya4.Hard.AlgebraicGeometry.QuadraticRepresentation
import Kakeya4.Hard.AlgebraicGeometry.RegularFiberBound
import Kakeya4.Hard.AlgebraicGeometry.SelectorFamily
import Kakeya4.Hard.AlgebraicGeometry.SignFormula
import Kakeya4.Hard.AlgebraicGeometry.SlopeFiberFamily
import Kakeya4.Hard.AlgebraicGeometry.SpatialRegionVolume
import Kakeya4.Hard.AlgebraicGeometry.UniformDiscreteFibers
import Kakeya4.Hard.AlgebraicGeometry.UniformLineFibers
import Kakeya4.Hard.AlgebraicGeometry.VectorAnalytic
import Kakeya4.Hard.Analysis.PlanarRegionVolume
import Kakeya4.Hard.Analysis.SubpowerAbsorption
import Kakeya4.Hard.SlopeVolume

/-! Dedicated axiom audit for the full manuscript slope-volume dependency closure. -/

#print axioms Kakeya4.Hard.EligibleFormula.derivativeValue_affine
#print axioms Kakeya4.Hard.EligibleFormula.measurable_derivativeValue
#print axioms Kakeya4.Hard.EligibleFormula.measurable_derivativeSlope
#print axioms Kakeya4.Hard.EligibleFormula.measurable_derivativeOffset
#print axioms Kakeya4.Hard.EligibleFormula.eligible_derivative_witness
#print axioms Kakeya4.Hard.EligibleFormula.eval_spatialEnergy
#print axioms Kakeya4.Hard.EligibleFormula.lineCoordinates_eq
#print axioms Kakeya4.Hard.EligibleFormula.measurableSet_allowedRegion
#print axioms Kakeya4.Hard.EligibleFormula.eligible_image_mem_allowedRegion
#print axioms Kakeya4.Hard.EligibleFormula.compact_interval_sSup_le_iff
#print axioms Kakeya4.Hard.EligibleFormula.compact_interval_le_sSup_iff
#print axioms Kakeya4.Hard.EligibleFormula.derivative_sup_iff_time_witness
#print axioms Kakeya4.Hard.discrete_semialgebraic_projection_empty_interior
#print axioms Kakeya4.Hard.discrete_semialgebraic_scalar_projection_empty_interior
#print axioms Kakeya4.Hard.EligibleFormula.intervalTest_signSet
#print axioms Kakeya4.Hard.EligibleFormula.pointTest_signSet
#print axioms Kakeya4.Hard.EligibleFormula.lowerDerivativeTest_signSet
#print axioms Kakeya4.Hard.EligibleFormula.boxTest_signSet
#print axioms Kakeya4.Hard.EligibleFormula.eligible_signSet
#print axioms Kakeya4.Hard.EligibleFormula.exists_selectorData
#print axioms Kakeya4.Hard.EligibleFormula.SelectorData.volume_domain_eq
#print axioms Kakeya4.Hard.EligibleFormula.eligible_slope_volume_subpower
#print axioms Kakeya4.Hard.EligibleFormula.SelectorData.eligible_volume_of_region_bound
#print axioms Kakeya4.Hard.EligibleFormula.eligible_slope_volume_of_region_bound
#print axioms Kakeya4.Hard.EligibleFormula.hiddenPolynomial_degree
#print axioms Kakeya4.Hard.EligibleFormula.hiddenBase_update
#print axioms Kakeya4.Hard.EligibleFormula.hiddenPolynomial_eval
#print axioms Kakeya4.Hard.EligibleFormula.hiddenPolynomial_derivative_eval
#print axioms Kakeya4.Hard.EligibleFormula.hiddenPolynomial_eval_quadratic
#print axioms Kakeya4.Hard.EligibleFormula.hiddenPolynomial_derivative_affine
#print axioms OAI.Release061.real_graph_empty_interior
#print axioms OAI.Release061.semialgebraic_graph_polynomial
#print axioms OAI.Release061.algebraic_of_graph_polynomial
#print axioms OAI.Release061.analytic_real_zero_null
#print axioms OAI.Release061.radialPlane_analytic
#print axioms OAI.Release061.radialLine_analytic
#print axioms OAI.Release061.analytic_zero_null_convex
#print axioms OAI.Release061.analytic_zero_null_connected
#print axioms OAI.Release061.analytic_zero_null
#print axioms OAI.Release061.SignElimination.X_derivative_coeff
#print axioms OAI.Release061.SignElimination.criticalSampler_top_coeff
#print axioms OAI.Release061.SignElimination.criticalSampler_ne_zero
#print axioms OAI.Release061.SignElimination.decayWeight_continuous
#print axioms OAI.Release061.SignElimination.decayWeight_tendsto
#print axioms OAI.Release061.SignElimination.decayWeight_deriv
#print axioms OAI.Release061.SignElimination.complexEvaluation_apply
#print axioms OAI.Release061.SignElimination.rootSquare_apply
#print axioms OAI.Release061.SignElimination.hermiteForm_apply
#print axioms OAI.Release061.SignElimination.rootEvaluation_real
#print axioms OAI.Release061.SignElimination.rootEvaluation_upper
#print axioms OAI.Release061.SignElimination.hermiteForm_root_values
#print axioms OAI.Release061.SignElimination.hermite_signature
#print axioms OAI.Release061.SignElimination.realPartPolynomial_coeff
#print axioms OAI.Release061.SignElimination.realPartPolynomial_degree_lt
#print axioms OAI.Release061.SignElimination.realPartPolynomial_map
#print axioms OAI.Release061.SignElimination.real_interpolation
#print axioms OAI.Release061.SignElimination.real_interpolation_indexed
#print axioms OAI.Release061.SignElimination.realComplexNodes_conj
#print axioms OAI.Release061.SignElimination.realComplexNodes_injective
#print axioms OAI.Release061.SignElimination.interpolate_real_and_upper
#print axioms OAI.StrongThinTree.MSS.ray_eval
#print axioms OAI.StrongThinTree.MSS.ray_derivative
#print axioms OAI.Release061.PolynomialSignSet.exists_regular_polynomial
#print axioms OAI.Release061.PolynomialSignSet.frontier_polynomial
#print axioms OAI.Release061.PolynomialSignSet.polynomial_of_empty_interior
#print axioms OAI.QuarticPowerFree.pderiv_totalDegree_lt
#print axioms OAI.Nagata.W02.natDegree_eval₂_le_totalDegree
#print axioms OAI.Release061.SignElimination.polynomialSignSet_choice_relation_one
#print axioms OAI.Release061.SignElimination.polynomialSignSet_choice_one
#print axioms OAI.Release061.SignElimination.polynomialSignSet_choice_relation_finite
#print axioms OAI.Release061.SignElimination.polynomialSignSet_choice_finite
#print axioms OAI.Release061.PolynomialSignSet.univ
#print axioms OAI.Release061.PolynomialSignSet.empty
#print axioms OAI.Release061.PolynomialSignSet.inter
#print axioms OAI.Release061.PolynomialSignSet.const
#print axioms OAI.Release061.PolynomialSignSet.exists_finset
#print axioms OAI.Release061.PolynomialSignSet.exists_finite
#print axioms OAI.Release061.PolynomialSignSet.forall_finite
#print axioms OAI.Release061.PolynomialSignSet.sign
#print axioms OAI.Release061.SignElimination.RationalOn.congr
#print axioms OAI.Release061.SignElimination.RationalOn.mono
#print axioms OAI.Release061.SignElimination.RationalOn.polynomial
#print axioms OAI.Release061.SignElimination.RationalOn.const
#print axioms OAI.Release061.SignElimination.RationalOn.add
#print axioms OAI.Release061.SignElimination.RationalOn.neg
#print axioms OAI.Release061.SignElimination.RationalOn.sub
#print axioms OAI.Release061.SignElimination.RationalOn.mul
#print axioms OAI.Release061.SignElimination.RationalOn.pow
#print axioms OAI.Release061.SignElimination.RationalOn.inv
#print axioms OAI.Release061.SignElimination.RationalOn.div
#print axioms OAI.Release061.SignElimination.RationalOn.sum
#print axioms OAI.Release061.SignElimination.RationalOn.eval
#print axioms OAI.Release061.SignElimination.RationalOn.sign_inv_real
#print axioms OAI.Release061.SignElimination.RationalOn.sign_set
#print axioms OAI.Release061.SignElimination.polynomialSignSet_finite_signs
#print axioms OAI.Release061.SignElimination.RationalOn.polynomial_preimage
#print axioms OAI.Release061.SignElimination.RationalOn.coordinate_preimage
#print axioms OAI.Release061.SignElimination.eval_eq_sum_range_of_natDegree_le
#print axioms OAI.Release061.SignElimination.polynomialSignSet_root_relation
#print axioms OAI.Release061.SignElimination.polynomialSignSet_finite_subrelation
#print axioms OAI.Release061.PolynomialSignSet.finite_sign_description
#print axioms OAI.Release061.SignElimination.eval_optionEquivLeft
#print axioms OAI.Release061.SignElimination.polynomialSignSet_projection_one
#print axioms OAI.Release061.PolynomialSignSet.eval_substitution
#print axioms OAI.Release061.PolynomialSignSet.polynomial_preimage
#print axioms OAI.Release061.PolynomialSignSet.coordinate_preimage
#print axioms OAI.Release061.SignElimination.polynomialSignSet_projection_finite
#print axioms OAI.Release061.SignElimination.signVariations_congr_coeff
#print axioms OAI.Release061.SignElimination.signVariations_neg_congr_coeff
#print axioms OAI.Release061.SignElimination.eval_charpolyCoefficient
#print axioms OAI.Release061.SignElimination.rationalOn_charpoly_coefficient
#print axioms OAI.Release061.SignElimination.polynomialSignSet_of_sign_invariant
#print axioms OAI.Release061.SignElimination.coefficientHermiteMatrix_eq
#print axioms OAI.Release061.SignElimination.rationalOn_coefficientHermite
#print axioms OAI.Release061.SignElimination.tarskiQuery_coefficient_charpoly
#print axioms OAI.Release061.SignElimination.polynomialSignSet_query_predicate
#print axioms OAI.Release061.SignElimination.finite_polynomial_sign_sampler
#print axioms OAI.Release061.SignElimination.support_eq_of_coeff_sign_eq
#print axioms OAI.Release061.SignElimination.degree_data_of_coeff_sign_eq
#print axioms OAI.Release061.SignElimination.coeff_sign_ext_of_bound
#print axioms OAI.Release061.SignElimination.degree_stratum_signSet
#print axioms OAI.Release061.SignElimination.zero_stratum_signSet
#print axioms OAI.Release061.SignElimination.polynomialSignSet_query_bounded
#print axioms OAI.Release061.SignElimination.RationalPolynomialOn.mono
#print axioms OAI.Release061.SignElimination.RationalPolynomialOn.congr
#print axioms OAI.Release061.SignElimination.RationalPolynomialOn.const
#print axioms OAI.Release061.SignElimination.RationalPolynomialOn.add
#print axioms OAI.Release061.SignElimination.RationalPolynomialOn.neg
#print axioms OAI.Release061.SignElimination.RationalPolynomialOn.sub
#print axioms OAI.Release061.SignElimination.RationalPolynomialOn.mul
#print axioms OAI.Release061.SignElimination.RationalPolynomialOn.pow
#print axioms OAI.Release061.SignElimination.RationalPolynomialOn.prod
#print axioms OAI.Release061.SignElimination.RationalPolynomialOn.derivative
#print axioms OAI.Release061.SignElimination.RationalPolynomialOn.criticalSampler
#print axioms OAI.Release061.SignElimination.degree_lt_bound
#print axioms OAI.Release061.SignElimination.polynomialSignSet_root_signs
#print axioms OAI.Release061.SignElimination.criticalSampler_natDegree_le
#print axioms OAI.Release061.SignElimination.polynomialSignSet_nonzero_mask
#print axioms OAI.Release061.SignElimination.polynomialSignSet_exists_signs
#print axioms OAI.Release061.polynomial_gcd_specialization_data
#print axioms OAI.Release061.real_analytic_local_inverse
#print axioms OAI.Release061.real_triangularDifferentialEquiv_apply
#print axioms OAI.Release061.real_analytic_implicit_scalar
#print axioms OAI.Release061.real_polynomial_analytic_root
#print axioms OAI.Release061.continuousAt_real_parameter_eval
#print axioms OAI.Release061.polynomial_zero_persists_on_simple_sheet
#print axioms OAI.Release061.PolynomialSignSet.regular_on_simple_sheet
#print axioms OAI.Release061.SignElimination.complexify_conj
#print axioms OAI.Release061.SignElimination.complexify_ne_zero
#print axioms OAI.Release061.SignElimination.complexify_eval_conj
#print axioms OAI.Release061.SignElimination.complexify_real_eval
#print axioms OAI.Release061.SignElimination.complex_root_conj
#print axioms OAI.Release061.SignElimination.count_complex_root_conj
#print axioms OAI.Release061.SignElimination.count_complex_root_real
#print axioms OAI.Release061.SignElimination.realRoot_mem_complex
#print axioms OAI.Release061.SignElimination.rootNodes_bijective
#print axioms OAI.Release061.SignElimination.root_dimension_le
#print axioms OAI.Release061.SignElimination.rootEvaluation_surjective
#print axioms OAI.Release061.SignElimination.powerSumPolynomial_spec
#print axioms OAI.Release061.SignElimination.powerSumPolynomial_eval
#print axioms OAI.Release061.SignElimination.multiset_enumerate
#print axioms OAI.Release061.SignElimination.roots_esymm_eq_rootCoefficient
#print axioms OAI.Release061.SignElimination.root_moment_coefficients
#print axioms OAI.Release061.SignElimination.sign_indicator
#print axioms OAI.Release061.SignElimination.sign_pattern_count
#print axioms OAI.Release061.SignElimination.exists_root_sign_pattern_iff
#print axioms OAI.Release061.SignElimination.same_sign_of_mul_pos
#print axioms OAI.Release061.SignElimination.sample_nonzero_chamber
#print axioms OAI.Release061.SignElimination.sample_all_chambers
#print axioms OAI.Release061.semialgebraic_function_analytic_off_polynomial
#print axioms OAI.Release061.separable_map_of_leading_resultant_ne_zero
#print axioms OAI.Release061.resultant_derivative_ne_zero_of_generic_separable
#print axioms OAI.Release061.SignElimination.sigPos_comp_le
#print axioms OAI.Release061.SignElimination.sigPos_comp_surjective
#print axioms OAI.Release061.SignElimination.sigNeg_comp_surjective
#print axioms OAI.Release061.SignElimination.signature_weightedSumSquares
#print axioms OAI.Release061.SignElimination.squareRootOrOne_sq
#print axioms OAI.Release061.SignElimination.squareRootOrOne_ne_zero
#print axioms OAI.Release061.SignElimination.signature_of_root_values
#print axioms OAI.Release061.SignElimination.coeff_comp_neg
#print axioms OAI.Release061.SignElimination.natDegree_comp_neg
#print axioms OAI.Release061.SignElimination.eraseLead_comp_neg
#print axioms OAI.Release061.SignElimination.sign_pair_indicator
#print axioms OAI.Release061.SignElimination.signVariations_pair_le
#print axioms OAI.Release061.SignElimination.coeffList_mul_X
#print axioms OAI.Release061.SignElimination.signVariations_mul_X
#print axioms OAI.Release061.SignElimination.positive_negative_roots_card
#print axioms OAI.Release061.SignElimination.signVariations_eq_positive_roots
#print axioms OAI.Release061.polynomial_clear_denominators
#print axioms OAI.Release061.squarefree_relation_off_denominator
#print axioms OAI.Release061.SignElimination.quadratic_matrix_apply
#print axioms OAI.Release061.SignElimination.quadratic_matrix_comp
#print axioms OAI.Release061.SignElimination.diagonal_quadratic
#print axioms OAI.Release061.SignElimination.quadratic_signature_eigenvalues
#print axioms OAI.Release061.SignElimination.signature_matrix_charpoly
#print axioms OAI.Release061.SignElimination.hermiteMatrix_isHermitian
#print axioms OAI.Release061.SignElimination.root_matrix_identity
#print axioms OAI.Release061.SignElimination.complexify_eval_degreeLT
#print axioms OAI.Release061.SignElimination.hermiteMatrix_quadratic
#print axioms OAI.Release061.SignElimination.hermiteMatrix_signature
#print axioms OAI.Release061.SignElimination.hermiteMatrix_coefficients
#print axioms OAI.Release061.SignElimination.tarskiQuery_charpoly
#print axioms OAI.Release061.SignElimination.polynomialSignSet_vector_graph_coordinate
#print axioms Kakeya4.Hard.polynomialSignSet_isolatedFiberPoints
#print axioms Kakeya4.Hard.isolatedFiberPoints_discrete
#print axioms Kakeya4.Hard.uniform_isolated_fiber_bound
#print axioms Kakeya4.Hard.mem_isolatedFiberPoints_of_local
#print axioms Kakeya4.Hard.uniform_locally_isolated_fiber_bound
#print axioms Kakeya4.Hard.EligibleFormula.PhysicalChart.spatialRadius_eq_euclidean_norm
#print axioms Kakeya4.Hard.EligibleFormula.PhysicalChart.energy_parameters
#print axioms Kakeya4.Hard.EligibleFormula.PhysicalChart.pointTest_parameters
#print axioms Kakeya4.Hard.EligibleFormula.PhysicalChart.continuous_spatialRadius
#print axioms Kakeya4.Hard.EligibleFormula.PhysicalChart.continuous_testOnLine
#print axioms Kakeya4.Hard.EligibleFormula.PhysicalChart.continuous_derivativeOnLine
#print axioms Kakeya4.Hard.EligibleFormula.PhysicalChart.eligible_iff_supEligible
#print axioms Kakeya4.Hard.EligibleFormula.PhysicalChart.manuscriptSlopes_eq
#print axioms Kakeya4.Hard.EligibleFormula.SelectorData.measurable_measurableIntercept
#print axioms Kakeya4.Hard.EligibleFormula.SelectorData.measurableIntercept_eventuallyEq
#print axioms Kakeya4.Hard.EligibleFormula.SelectorData.contDiffAt_measurableIntercept
#print axioms Kakeya4.Hard.EligibleFormula.SelectorData.measurableIntercept_eligible
#print axioms Kakeya4.Hard.EligibleFormula.SelectorData.measurable_interceptDerivative
#print axioms Kakeya4.Hard.EligibleFormula.SelectorData.measurableIntercept_regular_fiber_bound
#print axioms Kakeya4.Hard.EligibleFormula.PhysicalChart.inverseSpatialMap_parameters
#print axioms Kakeya4.Hard.EligibleFormula.PhysicalChart.quadraticPolynomial_parameters
#print axioms Kakeya4.Hard.EligibleFormula.PhysicalChart.test_parameters
#print axioms Kakeya4.Hard.EligibleFormula.PhysicalChart.derivative_parameters
#print axioms Kakeya4.Hard.EligibleFormula.physicalChart_eligible_volume
#print axioms Kakeya4.Hard.EligibleFormula.spatialEnergyValue_base
#print axioms Kakeya4.Hard.EligibleFormula.volume_baseRegion_le
#print axioms Kakeya4.Hard.EligibleFormula.volume_allowedRegion_physical_le
#print axioms Kakeya4.Hard.EligibleFormula.physical_eligible_slope_volume
#print axioms Kakeya4.Hard.real_polynomial_zero_volume
#print axioms Kakeya4.Hard.vector_graph_open_analytic_locus
#print axioms Kakeya4.Hard.semialgebraic_sdiff_interior_volume
#print axioms Kakeya4.Hard.semialgebraic_selector_open_full_measure
#print axioms Kakeya4.Hard.EligibleFormula.quadraticPolynomial_totalDegree
#print axioms Kakeya4.Hard.EligibleFormula.linePolynomials_degree
#print axioms Kakeya4.Hard.EligibleFormula.derivative_on_line_degree
#print axioms Kakeya4.Hard.EligibleFormula.eval_spacetime
#print axioms Kakeya4.Hard.EligibleFormula.eval_test_eq
#print axioms Kakeya4.Hard.EligibleFormula.eval_derivativeW_eq
#print axioms Kakeya4.Hard.EligibleFormula.eval_line_restriction
#print axioms Kakeya4.Hard.EligibleFormula.derivativeW_affine
#print axioms Kakeya4.Hard.EligibleFormula.exponent_injective
#print axioms Kakeya4.Hard.EligibleFormula.exists_exponent_of_degree_le
#print axioms Kakeya4.Hard.EligibleFormula.quadraticPolynomial_withQuadratic
#print axioms Kakeya4.Hard.EligibleFormula.eval_test_withQuadratic
#print axioms Kakeya4.Hard.EligibleFormula.eval_derivativeW_withQuadratic
#print axioms Kakeya4.Hard.uniform_regular_fiber_bound
#print axioms Kakeya4.Hard.vector_graph_full_measure_analytic_locus
#print axioms Kakeya4.Hard.polynomialSignSet_graph_parameter_slice
#print axioms Kakeya4.Hard.semialgebraic_selector_family
#print axioms Kakeya4.Hard.polynomialSignSet_eval_le
#print axioms Kakeya4.Hard.polynomialSignSet_abs_eval_le
#print axioms Kakeya4.Hard.polynomialSignSet_forall_real
#print axioms Kakeya4.Hard.polynomialSignSet_eval_le_abs
#print axioms Kakeya4.Hard.polynomialSignSet_slope_fiber_family
#print axioms Kakeya4.Hard.uniform_regular_slope_fiber_family_bound
#print axioms Kakeya4.Hard.EligibleFormula.spatialEnergyValue_snoc
#print axioms Kakeya4.Hard.EligibleFormula.continuous_snoc
#print axioms Kakeya4.Hard.EligibleFormula.measurePreserving_snoc
#print axioms Kakeya4.Hard.EligibleFormula.measurableSet_baseRegion
#print axioms Kakeya4.Hard.EligibleFormula.volume_allowedRegion_le_base
#print axioms Kakeya4.Hard.uniform_discrete_fiber_bound
#print axioms Kakeya4.Hard.uniform_line_fiber_bound
#print axioms Kakeya4.Hard.vector_graph_analytic_off_polynomial
#print axioms Kakeya4.Hard.semialgebraic_analytic_selector
#print axioms Kakeya4.Hard.normalizedPlanarRegion_subset_box_image
#print axioms Kakeya4.Hard.volume_normalizedPlanarRegion_le
#print axioms Kakeya4.Hard.tendsto_log_const_mul_pow_div
#print axioms Kakeya4.Hard.le_const_mul_pow_of_one_le
#print axioms Kakeya4.Hard.SlopeVolume.eligible_slope_volume
#print axioms Kakeya4.Hard.SlopeVolume.selector_volume
#print axioms Kakeya4.Hard.SlopeVolume.eligible_slope_volume_subpower
#print axioms Kakeya4.Hard.SlopeVolume.slope_volume_bounds_subpower
