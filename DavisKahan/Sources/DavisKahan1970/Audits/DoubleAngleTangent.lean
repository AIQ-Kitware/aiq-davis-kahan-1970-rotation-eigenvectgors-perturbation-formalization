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
#check @norm_sinTwoThetaBlock
#check @unbounded_sinTwoTheta_opNorm
#check @unbounded_sinTwoTheta_reflectionResidual_opNorm
#check @unbounded_sinTwoTheta_uiNorm
#check @unbounded_sinTwoTheta_uiNorm_representative
#check @unbounded_sinTwoTheta_residual_uiNorm_representative

#print axioms unbounded_sinTwoTheta_uiNorm
#print axioms unbounded_sinTwoTheta_uiNorm_representative
#print axioms unbounded_sinTwoTheta_residual_uiNorm_representative
#print axioms unbounded_sinTwoTheta_opNorm

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

#check @tanTwoTheta_uiNorm
#check @tanTwoTheta_kyFan
#check @tanTwoTheta_pairedSingularVector_scalar
#check @tanTwoTheta_sharp_opNorm
#check @tanTwoTheta_spectral_repulsion
#check @unbounded_tanTwoTheta_opNorm
#check @unbounded_tanTwoTheta_uiNorm
#check @tanTwoTheta_uiIdeal_infinite
#check @tanTwoTheta_kyFan_infinite
#check @tanTwoTheta_kyFan_doubleAngleTangent_infinite
#check @kyFanApproximationGauge_orthonormal_bound

#print axioms tanTwoTheta_uiNorm
#print axioms tanTwoTheta_kyFan
#print axioms tanTwoTheta_sharp_opNorm
#print axioms unbounded_tanTwoTheta_uiNorm
#print axioms tanTwoTheta_uiIdeal_infinite
#print axioms tanTwoTheta_kyFan_infinite
#print axioms kyFanApproximationGauge_orthonormal_bound

end DavisKahan1970
end TauCeti