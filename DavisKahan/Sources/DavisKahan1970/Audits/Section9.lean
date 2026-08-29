/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Sources.DavisKahan1970.Section9.All

/-!
# Dependency audit for the Section 9 numerical example

Compile this module after repairing any elaboration issues, then inspect the
printed dependency sets before promoting the certificate bridge to exact source
coverage.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section9

/-! ## Paper-facing real source-model audit -/

#check real_freeBeam_operator_source
#check real_freeBeam_spectrum_source
#check real_freeBeam_positive_spectrum_source
#check real_freeBeam_trial_le_domain
#check real_freeBeam_operator_apply_trial
#check real_freeBeam_zero_mode_source
#check real_freeBeam_finiteData_source
#check real_freeBeam_trial_and_perturbation_source

#print axioms real_freeBeam_operator_source
#print axioms real_freeBeam_spectrum_source
#print axioms real_freeBeam_positive_spectrum_source
#print axioms real_freeBeam_trial_le_domain
#print axioms real_freeBeam_operator_apply_trial
#print axioms real_freeBeam_zero_mode_source
#print axioms real_freeBeam_finiteData_source
#print axioms real_freeBeam_trial_and_perturbation_source

/-! ## Real analytic implementation audit -/

#check DavisKahan.FreeBeam.Model.Real.beamOperator_is_closure_of_classical_freeBeam_fourthDerivative
#check DavisKahan.FreeBeam.Model.Real.classicalFreeBeamCoreGraph_has_classical_representative
#check DavisKahan.FreeBeam.Model.Real.classicalFreeBeamGraph_subset_graph
#check DavisKahan.FreeBeam.Model.Real.closure_classicalFreeBeamGraph_eq_graph
#check DavisKahan.FreeBeam.Model.Real.realSpectrum_beamOperator_eq_insert_zero
#check DavisKahan.FreeBeam.Model.Real.exists_strictMono_range_eq_beamEigenvalues
#check DavisKahan.FreeBeam.Model.Real.exists_eigenpair_of_characteristic
#check DavisKahan.FreeBeam.Model.Real.beamEigenvalues_eq_characteristicFourthPowers
#check DavisKahan.FreeBeam.Model.Real.beamRealPositiveSpectrum_sourceFacts
#check DavisKahan.FreeBeam.Model.Real.beamRealZeroMode_sourceFacts
#check DavisKahan.FreeBeam.Model.Real.beamPerturbation_isSelfAdjoint
#check DavisKahan.FreeBeam.Model.Real.beamTrial_orthonormal
#check DavisKahan.FreeBeam.Model.Real.beamRitz_matrix
#check DavisKahan.FreeBeam.Model.Real.beamResidualGram_matrix
#check DavisKahan.FreeBeam.Model.Real.beamFiniteDataCertificate
#check DavisKahan.FreeBeam.Model.Real.beamRealModel_sourceFacts
#check DavisKahan.FreeBeam.Model.Real.beamRealFiniteData_sourceFacts

#print axioms DavisKahan.FreeBeam.Model.Real.beamOperator_is_closure_of_classical_freeBeam_fourthDerivative
#print axioms DavisKahan.FreeBeam.Model.Real.classicalFreeBeamGraph_subset_graph
#print axioms DavisKahan.FreeBeam.Model.Real.realSpectrum_beamOperator_eq_insert_zero
#print axioms DavisKahan.FreeBeam.Model.Real.exists_strictMono_range_eq_beamEigenvalues
#print axioms DavisKahan.FreeBeam.Model.Real.exists_eigenpair_of_characteristic
#print axioms DavisKahan.FreeBeam.Model.Real.beamEigenvalues_eq_characteristicFourthPowers
#print axioms DavisKahan.FreeBeam.Model.Real.beamRealPositiveSpectrum_sourceFacts
#print axioms DavisKahan.FreeBeam.Model.Real.beamRealZeroMode_sourceFacts
#print axioms DavisKahan.FreeBeam.Model.Real.beamFiniteDataCertificate
#print axioms DavisKahan.FreeBeam.Model.Real.beamRealModel_sourceFacts

#check initial_residual_gram_from_affine_moments
#check recentered_residual_gram_from_affine_moments
#check residualGram_eigenvalueLow_charAt
#check residualGram_eigenvalueHigh_charAt
#check equation_9_1
#check equation_9_2
#check equation_9_3
#check equation_9_4
#check equation_9_5_low
#check equation_9_5_high
#check equation_9_6
#check equation_9_7
#check equation_9_8_lower
#check equation_9_8_upper
#check block_eigenproblem_iff
#check schur_complement_reduction
#check half_tanTwoPsi_ratio_lt_of_eigenvalue_upper
#check individual_angle_le_exact_envelope
#check final_lower_individual_angle_bound
#check final_upper_individual_angle_bound
#check NumericalExampleCertificate.printedConclusions

#print axioms initial_residual_gram_from_affine_moments
#print axioms recentered_residual_gram_from_affine_moments
#print axioms block_eigenproblem_iff
#print axioms schur_complement_reduction
#print axioms half_tanTwoPsi_ratio_lt_of_eigenvalue_upper
#print axioms NumericalExampleCertificate.printedConclusions

end Section9
end DavisKahan1970
end TauCeti