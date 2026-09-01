/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.Sources.DavisKahan1970.SinTwoTheta
import DavisKahan.Sources.DavisKahan1970.TanTheta
import DavisKahan.Sources.DavisKahan1970.TanTwoTheta

/-!
# Focused audit for the Section 7 and Theorem 6.3 source surfaces

Dependency audit for the sine-double-angle, generalized-tangent, and
tangent-double-angle source facades.  Every `#print axioms` below must report
only the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace TauCeti
namespace DavisKahan1970

/-! ## Section 7, equations (7.1)--(7.5): sine double angle -/

#check @sinTwoTheta_mirrorDefect_eq_perturbationDefect
#check @sinTwoTheta_mirrorDefect_le_two_mul
#check @sinTwoTheta_reflectedOverlap_norm
#check @norm_sinTwoThetaBlock_complex
#check @sinTwoTheta_unbounded_perturbation_opNorm_complex
#check @sinTwoTheta_unbounded_reflectionResidual_opNorm_complex
#check @sinTwoTheta_unbounded_perturbation_blockRepresentative_idealFamily_complex
#check @sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_complex
#check @sinTwoTheta_unbounded_reflectionResidual_arbitraryRepresentative_complex

#print axioms sinTwoTheta_unbounded_perturbation_blockRepresentative_idealFamily_complex
#print axioms sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_complex
#print axioms sinTwoTheta_unbounded_reflectionResidual_arbitraryRepresentative_complex
#print axioms sinTwoTheta_unbounded_perturbation_opNorm_complex

/-! ## Theorem 6.3: generalized tangent -/

#check @Theorem6_3
#check @Theorem6_3_equalRank
#check @Theorem6_3_kyFan
#check @Theorem6_3_transversality
#check @Theorem6_3_unbounded_graphAngle_opNorm
#check @Theorem6_3_unbounded_vector
#check @Theorem6_3_bounded_vector
#check @Theorem6_3_bounded_vector_oneSided

#print axioms Theorem6_3
#print axioms Theorem6_3_unbounded_graphAngle_opNorm
#print axioms Theorem6_3_bounded_vector
#print axioms Theorem6_3_bounded_vector_oneSided

/-! ## Section 7, equation (7.6): tangent double angle -/

#check @tanTwoTheta_principalBranch_finiteDimensional_uiNorm_rclike
#check @tanTwoTheta_principalBranch_finiteDimensional_kyFan_rclike
#check @tanTwoTheta_pairedSingularVector_scalar
#check @tanTwoTheta_sharpness_opNorm_rclike
#check @tanTwoTheta_spectral_repulsion
#check @tanTwoTheta_unbounded_opNorm_complex
#check @tanTwoTheta_unbounded_blockRepresentative_idealFamily_complex
#check @tanTwoTheta_principalBranch_finiteSubspace_idealFamily_rclike
#check @tanTwoTheta_principalBranch_finiteSubspace_kyFan_rclike
#check @tanTwoTheta_doubleAngleTangent_finiteSubspace_kyFan_rclike
#check @kyFanApproximationGauge_orthonormal_bound

#print axioms tanTwoTheta_principalBranch_finiteDimensional_uiNorm_rclike
#print axioms tanTwoTheta_principalBranch_finiteDimensional_kyFan_rclike
#print axioms tanTwoTheta_sharpness_opNorm_rclike
#print axioms tanTwoTheta_unbounded_blockRepresentative_idealFamily_complex
#print axioms tanTwoTheta_principalBranch_finiteSubspace_idealFamily_rclike
#print axioms tanTwoTheta_principalBranch_finiteSubspace_kyFan_rclike
#print axioms kyFanApproximationGauge_orthonormal_bound

end DavisKahan1970
end TauCeti