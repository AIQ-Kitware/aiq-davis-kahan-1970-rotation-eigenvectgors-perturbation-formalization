/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.Section8.Presentation
import DavisKahan.Sources.DavisKahan1970.Section8.Theorem81MajorizationReal

/-!
# Dependency audit for Davis--Kahan 1970 Section 8

This is the audit leaf for the **actual final capstones** of Section 8.  It
lives downstream of the analytic layer because that is where Section 8's
analytic content lives; the upstream leaf
`DavisKahan/Sources/DavisKahan1970/Audits/Section8.lean` continues to audit the
internal infrastructure, which is no longer evidence about the printed
theorems.

Every target below should report exactly

```
[propext, Classical.choice, Quot.sound]
```

and nothing project-local.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

/-! ## Theorem 8.1: the branch, its characterization, its uniqueness -/

#check theorem8_1
#check theorem8_1_characterization
#check theorem8_1_uniqueness

#print axioms theorem8_1
#print axioms theorem8_1_characterization
#print axioms theorem8_1_uniqueness

/-! ## Theorem 8.1(i), both blocks -/

#check theorem8_1_upperCompressionRepulsion
#check theorem8_1_lowerCompressionRepulsion

#print axioms theorem8_1_upperCompressionRepulsion
#print axioms theorem8_1_lowerCompressionRepulsion

/-! ## Theorem 8.1(ii), both blocks

The shared Weyl step, the dimension-free approximation-number statements, and
the printed angle form. -/

#check theorem8_1_upperSandwichApproximation
#check theorem8_1_lowerSandwichApproximation
#check theorem8_1_upperApproximationRepulsion
#check theorem8_1_lowerApproximationRepulsion
#check theorem8_1_upperApproximationRepulsion_angle
#check theorem8_1_lowerApproximationRepulsion_angle

#print axioms theorem8_1_upperSandwichApproximation
#print axioms theorem8_1_lowerSandwichApproximation
#print axioms theorem8_1_upperApproximationRepulsion
#print axioms theorem8_1_lowerApproximationRepulsion
#print axioms theorem8_1_upperApproximationRepulsion_angle
#print axioms theorem8_1_lowerApproximationRepulsion_angle

/-! ## Theorem 8.1(iii), both blocks

The weak-majorization cores, the every-symmetric-gauge forms, the printed angle
forms, and the paper's increasing index order. -/

#check theorem8_1_upperWeightedWeakMajorization
#check theorem8_1_lowerWeightedWeakMajorization
#check theorem8_1_upperSymmetricGaugeRepulsion
#check theorem8_1_lowerSymmetricGaugeRepulsion
#check theorem8_1_upperSymmetricGaugeRepulsion_angle
#check theorem8_1_lowerSymmetricGaugeRepulsion_angle
#check theorem8_1_upperSymmetricGaugeRepulsion_angle_rev
#check theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev

#print axioms theorem8_1_upperWeightedWeakMajorization
#print axioms theorem8_1_lowerWeightedWeakMajorization
#print axioms theorem8_1_upperSymmetricGaugeRepulsion
#print axioms theorem8_1_lowerSymmetricGaugeRepulsion
#print axioms theorem8_1_upperSymmetricGaugeRepulsion_angle
#print axioms theorem8_1_lowerSymmetricGaugeRepulsion_angle
#print axioms theorem8_1_upperSymmetricGaugeRepulsion_angle_rev
#print axioms theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev

/-! ## Theorem 8.1(ii) and 8.1(iii) over a REAL Hilbert space, both blocks

The real branch, its sharp form bounds, the dimension-free part (ii) endpoints
and the finite-dimensional part (iii) endpoints. -/

#check canonicalLowBranchReal
#check theorem8_1_spectralRepulsion_real
#check canonicalLowBranchReal_form_low
#check canonicalLowBranchReal_form_high
#check theorem8_1_upperSandwichApproximation_real
#check theorem8_1_lowerSandwichApproximation_real
#check theorem8_1_upperApproximationRepulsion_real
#check theorem8_1_lowerApproximationRepulsion_real
#check theorem8_1_upperWeightedWeakMajorization_real
#check theorem8_1_lowerWeightedWeakMajorization_real
#check theorem8_1_upperSymmetricGaugeRepulsion_real
#check theorem8_1_lowerSymmetricGaugeRepulsion_real

#print axioms canonicalLowBranchReal
#print axioms theorem8_1_spectralRepulsion_real
#print axioms canonicalLowBranchReal_form_low
#print axioms canonicalLowBranchReal_form_high
#print axioms theorem8_1_upperSandwichApproximation_real
#print axioms theorem8_1_lowerSandwichApproximation_real
#print axioms theorem8_1_upperApproximationRepulsion_real
#print axioms theorem8_1_lowerApproximationRepulsion_real
#print axioms theorem8_1_upperWeightedWeakMajorization_real
#print axioms theorem8_1_lowerWeightedWeakMajorization_real
#print axioms theorem8_1_upperSymmetricGaugeRepulsion_real
#print axioms theorem8_1_lowerSymmetricGaugeRepulsion_real

/-! ## The eigenvalue/angle source dictionary -/

#check approximationNumber_eq_eigenvalues_of_isPositive
#check approximationNumber_upperBlockShift_eq_zero_of_le
#check approximationNumber_lowerBlockShift_eq_zero_of_le
#check approximationNumber_cosineBlock_eq_principalCosines
#check approximationNumber_lowerCosineBlock_eq_principalCosines
#check norm_cosineBlock_eq_principalCosines_zero
#check norm_lowerCosineBlock_eq_principalCosines_zero
#check cos_arccos_approximationNumber_cosineBlock
#check arcsin_one_div_two
#check maximalAngle_le_pi_div_six_iff

#print axioms approximationNumber_eq_eigenvalues_of_isPositive
#print axioms approximationNumber_upperBlockShift_eq_zero_of_le
#print axioms approximationNumber_lowerBlockShift_eq_zero_of_le
#print axioms approximationNumber_cosineBlock_eq_principalCosines
#print axioms approximationNumber_lowerCosineBlock_eq_principalCosines
#print axioms norm_cosineBlock_eq_principalCosines_zero
#print axioms norm_lowerCosineBlock_eq_principalCosines_zero
#print axioms cos_arccos_approximationNumber_cosineBlock
#print axioms arcsin_one_div_two
#print axioms maximalAngle_le_pi_div_six_iff

/-! ## The generic sandwich majorization behind part (iii) -/

#check TauCeti.singularValues_adjoint_sandwich_weaklyMajorized
#check TauCeti.approximationNumber_adjoint_sandwich_weaklyMajorized

#print axioms TauCeti.singularValues_adjoint_sandwich_weaklyMajorized
#print axioms TauCeti.approximationNumber_adjoint_sandwich_weaklyMajorized

/-! ## Theorem 8.2

Both alternatives from the printed hypotheses, the inherited `sin 2Θ`
estimates, the Krein completion, equation (1.5), and the printed `Θ < π/4`. -/

#check theorem8_2_perturbationHalfGap_complex
#check theorem8_2_residualHalfGap_complex
#check theorem8_2_branch_directed_complex
#check theorem8_2_krein_completion
#check theorem8_2_sinTwoTheta_perturbation_complex
#check theorem8_2_sinTwoTheta_residual_complex
#check subspaceGap_eq_directedGap_of_finrank_eq
#check theorem8_2_perturbationHalfGap_maximalAngle_lt
#check theorem8_2_residualHalfGap_maximalAngle_lt
#check theorem8_2_branch_maximalAngle_lt
#check theorem8_2_complex
#check theorem8_2_sinTwoTheta_perturbation_symmetricNorming
#check theorem8_2_sinTwoTheta_residual_symmetricNorming
#check theorem8_2_sinTwoTheta_residual_all_kyFan
#check theorem8_2_branch_maximalAngle_lt_of_crossedDefects
#check theorem8_2_perturbationHalfGap_real
#check theorem8_2_residualHalfGap_real
#check theorem8_2_branch_directed_real
#check theorem8_2_perturbationHalfGap_real_maximalAngle_lt
#check theorem8_2_branch_real_maximalAngle_lt_of_crossedDefects
#check theorem8_2_branch_real_maximalAngle_lt
#check theorem8_2_sinTwoTheta_perturbation_real
#check theorem8_2_sinTwoTheta_residual_real
#check theorem8_2_sinTwoTheta_perturbation_real_symmetricNorming
#check theorem8_2_sinTwoTheta_residual_real_symmetricNorming
#check theorem8_2_real

#print axioms theorem8_2_perturbationHalfGap_complex
#print axioms theorem8_2_residualHalfGap_complex
#print axioms theorem8_2_branch_directed_complex
#print axioms theorem8_2_krein_completion
#print axioms theorem8_2_sinTwoTheta_perturbation_complex
#print axioms theorem8_2_sinTwoTheta_residual_complex
#print axioms subspaceGap_eq_directedGap_of_finrank_eq
#print axioms theorem8_2_perturbationHalfGap_maximalAngle_lt
#print axioms theorem8_2_residualHalfGap_maximalAngle_lt
#print axioms theorem8_2_branch_maximalAngle_lt
#print axioms theorem8_2_complex
#print axioms theorem8_2_sinTwoTheta_perturbation_symmetricNorming
#print axioms theorem8_2_sinTwoTheta_residual_symmetricNorming
#print axioms theorem8_2_sinTwoTheta_residual_all_kyFan
#print axioms theorem8_2_branch_maximalAngle_lt_of_crossedDefects
#print axioms theorem8_2_perturbationHalfGap_real
#print axioms theorem8_2_residualHalfGap_real
#print axioms theorem8_2_branch_directed_real
#print axioms theorem8_2_perturbationHalfGap_real_maximalAngle_lt
#print axioms theorem8_2_branch_real_maximalAngle_lt_of_crossedDefects
#print axioms theorem8_2_branch_real_maximalAngle_lt
#print axioms theorem8_2_sinTwoTheta_perturbation_real
#print axioms theorem8_2_sinTwoTheta_residual_real
#print axioms theorem8_2_sinTwoTheta_perturbation_real_symmetricNorming
#print axioms theorem8_2_sinTwoTheta_residual_real_symmetricNorming
#print axioms theorem8_2_real

end Section8
end DavisKahan1970
end TauCeti
