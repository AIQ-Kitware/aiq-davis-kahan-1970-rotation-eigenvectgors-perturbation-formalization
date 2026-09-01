/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.All

/-!
# Davis--Kahan 1970 result semantic audit surface

This file is intentionally outside `DavisKahan.All`.  It gives a hostile reviewer a
single compiler-checkable surface for the Lean declarations selected by the maintained
29-result Davis--Kahan 1970 completion inventory.

Each `#check` below is evidence only: the semantic correspondence to the printed source
is recorded in `dev/davis-kahan-1970-formalization-result-inventory.json` and the
human-readable result audit.  The maintained result inventory is terminal; this surface
keeps source-facing headline declarations and their scope companions compiler-visible.

Run:

```bash
lake env lean DavisKahan/Sources/DavisKahan1970/Audits/ResultSemanticSurface.lean
```
-/

namespace TauCeti.DavisKahan1970.Audits

/-! ### Exact audit wrappers for stronger reusable theorem surfaces

These two declarations are intentionally tiny.  They make the semantic specialization
visible in Lean itself when the maintained reusable theorem is stronger or more general
than the paper-facing result.
-/

universe u v

/-- **Theorem 5.1, scalar-generic exact audit wrapper.**

The reusable theorem only needs the left-inverse half of the printed inverse hypothesis.
This wrapper retains both inverse equations and is generic over the scalar field, making
it compiler-visible that the printed Banach-space theorem is covered over both real and
complex scalars. -/
theorem theorem5_1_scalarGeneric_sourceAudit
    {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {N : (F →L[𝕜] E) → ℝ}
    (hadd : ∀ S T, N (S + T) ≤ N S + N T)
    (hidealL : ∀ (L : E →L[𝕜] E) (T : F →L[𝕜] E),
      N (L ∘L T) ≤ ‖L‖ * N T)
    (hidealR : ∀ (T : F →L[𝕜] E) (R : F →L[𝕜] F),
      N (T ∘L R) ≤ N T * ‖R‖)
    (hNnonneg : ∀ T, 0 ≤ N T)
    {A Ainv : E →L[𝕜] E} {B : F →L[𝕜] F} {X C : F →L[𝕜] E}
    {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hB : ‖B‖ ≤ ρ)
    (hAinv_left : Ainv ∘L A = ContinuousLinearMap.id 𝕜 E)
    (_hAinv_right : A ∘L Ainv = ContinuousLinearMap.id 𝕜 E)
    (hAinv_norm : ‖Ainv‖ ≤ (ρ + δ)⁻¹)
    (hEq : A ∘L X - X ∘L B = C) :
    δ * N X ≤ N C := by
  exact TauCeti.ContinuousLinearMap.opNorm_le_of_sylvester_of_leftInverse
    hadd hidealL hidealR hNnonneg hAinv_left hρ hδ hAinv_norm hB hEq

/-- **Theorem 5.2, real ordered exact audit wrapper.**

The maintained real theorem accepts the more general `FormBoundedSylvesterGap`.
This wrapper constructs its ordered `A ≥ c + δ > c ≥ B` branch explicitly, so a
reviewer can compare the printed real theorem without mentally specializing the gap sum. -/
theorem theorem5_2_real_ordered_sourceAudit
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (N : TauCeti.DavisKahan.ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℝ))
    {A : E →ₗ.[ℝ] E}
    {B : F →ₗ.[ℝ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X C : F →L[ℝ] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBc : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge C := by
  exact TauCeti.DavisKahan.ExactSinTheta.davisKahan1970_sylvester_real
    N hA hB hδ
      (TauCeti.DavisKahan.ExactSinTheta.FormBoundedSylvesterGap.leftAboveRightBelow
        c hAc hBc)
      hEq hC

end TauCeti.DavisKahan1970.Audits

/-! ## S2-sin-theta: Single-angle sine theorem

Status: **TERMINAL EXACT**.

The first two are the canonical Section 2 inventory names; the two after them are
the declarations they alias, with the full `FormBoundedSylvesterGap`, both
conclusions and no capability class.  The rest are the presentation declaration,
the engine, and the scope companions. -/

#check @TauCeti.DavisKahan1970.SectionTwo.sinTheta_complex
#check @TauCeti.DavisKahan1970.SectionTwo.sinTheta_real
#check @DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_complex
#check @DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_real
#check @DavisKahan1970.sinTheta_unbounded_intervalExterior_paperUINorm_complex
#check @DavisKahan1970.sinTheta_unbounded_intervalExterior_paperUINorm_real
#check @DavisKahan1970.sinTheta_unbounded_intervalExterior_characterizedWitness_rclike
#check @DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike
#check @TauCeti.DavisKahan1970.sinTheta_unbounded_intervalExterior_paperUINorm_rclike
#check @TauCeti.DavisKahan1970.sinTheta_bundled_complex
#check @TauCeti.DavisKahan1970.sinTheta_paperData_real
#check @TauCeti.DavisKahan1970.sinTheta_generalized_bundled_complex
#check @TauCeti.DavisKahan1970.sinTheta_generalized_paperData_real

/-! ## S2-tan-theta: Single-angle tangent theorem

Status: **TERMINAL EXACT** under the accepted nonlocal source interpretation.

The printed Section 2 statement is not locally self-contained: it does not state the
crossed-defect condition (3.5), which the source introduces in Section 3 and then
assumes as standing before proving this theorem in Section 6.  The source-shaped
ambient declarations therefore carry a crossed-defect hypothesis and *conclude*
membership of the tangent operator in the norm's ideal, which is the explicit form of
the paper's own convention that a result is vacuous when a displayed norm fails to
exist.  The reading, its evidence, and the competing literal reading are recorded in
`dev/davis-kahan-1970-formalization-result-inventory.json` under
`nonlocal_source_interpretation`.

The transversality-form declarations assume `‖sin Θ‖ < 1`, which is strictly stronger
than (3.5); they are registered as specializations, not as the source-shaped form.
-/

#check @TauCeti.DavisKahan1970.SectionTwo.tanTheta_complex
#check @TauCeti.DavisKahan1970.SectionTwo.tanTheta_real
#check @TauCeti.DavisKahan1970.tanTheta_directed_finiteDimensional_paperUINorm_rclike
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_paperUINorm_complex
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_paperUINorm_real
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_paperUINorm_complex
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_paperUINorm_real
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedTrial_paperUINorm_complex
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedTrial_paperUINorm_real
#check @TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal
#check @TauCeti.DavisKahan.ExactTanTheta.UnboundedCompressionTrialData.ideal_of_formBounds
#check @TauCeti.DavisKahan1970.theorem6_3_unboundedCompression_ideal_real
#check @TauCeti.DavisKahan.UnboundedRitzPair
#check @TauCeti.DavisKahan.ReducingComplement
#check @TauCeti.DavisKahan.UnboundedRitzPair.ofTrialBlock
#check @TauCeti.DavisKahan.ReducingComplement.ofReducesSubspace
#check @TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm
#check @TauCeti.DavisKahan.Section2.theorem6_3_perturbation_infiniteTrial
#check @TauCeti.DavisKahan1970.tanTheta_ambient_bounded_paperUINorm_complex_of_transversality
#check @TauCeti.DavisKahan1970.tanTheta_ambient_bounded_paperUINorm_real_of_transversality
#check @TauCeti.DavisKahan1970.tanTheta_ambient_bounded_paperUINorm_complex_of_crossedDefects
#check @TauCeti.DavisKahan1970.tanTheta_ambient_bounded_paperUINorm_real_of_crossedDefects
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedOperator_boundedRitz_paperUINorm_complex
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedOperator_boundedRitz_paperUINorm_real
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_raw_paperUINorm_complex
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_raw_paperUINorm_real
#check @TauCeti.DavisKahan.directedGap_asymmetric_coordinateHalfSpace
#check @TauCeti.DavisKahan1970.remark3_2_bilateralShift_separates_dimensionHypotheses
#check @TauCeti.DavisKahan1970.tanTheta_directed_bounded_spectralGap_paperUINorm_complex
#check @TauCeti.DavisKahan1970.tanTheta_directed_bounded_spectralGap_paperUINorm_real
#check @TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists
#check @TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real

/-! ## S2-sin-two-theta: Double-angle sine theorem

Status: **TERMINAL EXACT**.  Both fixed-field endpoints take
`FormBoundedSylvesterGap`, so the printed half-infinite gap scope is covered on
both.  The two `spectrumGap` declarations are the earlier complex route, at a
bounded separating interval only; they are supporting evidence, not the
result's canonical witness.

The **ambient** clause is discharged by
`sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_complex` and its real
sibling, at the same unbounded scope as the directed clause.  The bounded ambient
endpoints below them are their specializations, retained as an alternative proof.
-/

#check @TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta_complex
#check @TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_finiteDimensional_paperUINorm_rclike
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_blockRepresentative_paperUINorm_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_paperUINorm_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_blockRepresentative_spectrumGap_paperUINorm_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_spectrumGap_paperUINorm_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_paperUINorm_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_unequalDimension_paperUINorm_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_unequalDimension_paperUINorm_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_unequalDimension_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_reflectionResidual_arbitraryRepresentative_unequalDimension_complex
#check @TauCeti.DavisKahan.sinTwoTheta_addBounded_gauge_of_formGap
#check @TauCeti.DavisKahan.sinTwoTheta_reflectionResidual_gauge_of_formGap
#check @TauCeti.DavisKahan.sinTheta_addBounded_gauge_complex_block_of_formGap
#check @TauCeti.DavisKahan.ExactSinTheta.sinTheta_unbounded_complex_block
#check @TauCeti.DavisKahan.sinAngleOperatorDirectedC_reflected_eq_sinTwoAngleOperatorC
#check @TauCeti.DavisKahan.sinTwoThetaIdealBlock_hasSameApproximationNumbers
#check @TauCeti.DavisKahan.extendedGauge_sinTwoThetaIdealBlock_complex
#check @TauCeti.DavisKahan.approximationSingularValue_sinTwoThetaIdealBlock_real
#check @TauCeti.DavisKahan.extendedGauge_sinTwoThetaIdealBlock_real
#check @TauCeti.DavisKahan.mem_sinTwoAngleOperatorC_iff
#check @TauCeti.DavisKahan.gauge_sinTwoAngleOperatorC
#check @TauCeti.DavisKahan.mem_sinTwoAngleOperatorRC_iff
#check @TauCeti.DavisKahan.gauge_sinTwoAngleOperatorRC
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_real
#check @TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta_ambient_complex
#check @TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta_ambient_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_reflection_projectorDifference_paperUINorm
#check @TauCeti.DavisKahan1970.sinTheta_ambient_unitaryConj_projectorDifference_paperUINorm
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_bounded_paperUINorm_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_bounded_paperUINorm_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_reflectionResidual_arbitraryRepresentative_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_reflectionResidual_arbitraryRepresentative_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_spectrumGap_paperUINorm_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_intervalExterior_paperUINorm_real

/-! ## S2-tan-two-theta: Double-angle tangent theorem

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.SectionTwo.tanTwoTheta_complex
#check @TauCeti.DavisKahan1970.SectionTwo.tanTwoTheta_real
#check @TauCeti.DavisKahan1970.tanTwoTheta_branchFree_bounded_finiteSubspace_paperUINorm_rclike
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_blockRepresentative_derivedReflection_paperUINorm_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_blockRepresentative_derivedReflection_paperUINorm_real
#check @TauCeti.DavisKahan.ReflectionIntertwines
#check @TauCeti.DavisKahan.ReflectionIntertwines.ofReducesSubspace
#check @TauCeti.DavisKahan.reflection_commutes_of_reducesSubspace
#check @TauCeti.DavisKahan.diagonalPart_sq_add_offDiagonalPart_sq
#check @TauCeti.DavisKahan.diagonalPart_anticommute_offDiagonalPart
#check @TauCeti.DavisKahan.corner_offDiagonalPart_sq
#check @TauCeti.DavisKahan.gram_unboundedReflectionTangent
#check @TauCeti.DavisKahan.gram_unboundedReflectionTangent_eq_offDiagonal
#check @TauCeti.DavisKahan.starProjection_offDiagonal_sq_reflection
#check @TauCeti.DavisKahan.unboundedReflectionTangent_reflection_eq
#check @TauCeti.DavisKahan.paperTanTwoBlockRepresentative_mul_signedCosTwo
#check @TauCeti.DavisKahan.sameApproximationSingularValues_unboundedReflectionTangent
#check @TauCeti.DavisKahan.extendedGauge_unboundedReflectionTangent_complex
#check @TauCeti.DavisKahan.extendedGauge_unboundedReflectionTangent_real
#check @TauCeti.DavisKahan.isUnit_signedCosTwo_of_isUnit_diagonalPart_sq
#check @TauCeti.DavisKahan.cos_two_ne_zero_of_isUnit_diagonalPart_reflection_sq
#check @TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorR
#check @TauCeti.DavisKahanExt.complexify_paperAbsTanTwoAngleOperatorR
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_paperUINorm_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_paperUINorm_real
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_paperUINorm_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_paperUINorm_real
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_bounded_spectralGap_paperUINorm_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_bounded_spectralGap_paperUINorm_real
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_real
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_blockRepresentative_paperUINorm_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_blockRepresentative_paperUINorm_real

/-! ## DK-3.1-prop: Acute direct rotation existence and uniqueness

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.proposition3_1_source

/-! ## DK-3.2-prop: Nonacute existence criterion

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.proposition3_2_exists_iff_crossedDefectsEquivalent
#check @TauCeti.DavisKahan1970.proposition3_2_not_unique
#check @TauCeti.DavisKahan1970.proposition3_2_exists_iff_crossedDefectsEquivalent_real
#check @TauCeti.DavisKahan1970.proposition3_2_not_unique_real

/-! ## DK-3.3-prop: Principal square-root characterization

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.proposition3_3_complex_forward_source
#check @TauCeti.DavisKahan1970.proposition3_3_complex_converse_source
#check @TauCeti.DavisKahan1970.proposition3_3_real_forward_source
#check @TauCeti.DavisKahan1970.proposition3_3_real_converse_source

/-! ## DK-3.4-prop: Square as a direct rotation

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.proposition3_4_source_full_complex
#check @TauCeti.DavisKahan1970.proposition3_4_source_full_real
#check @TauCeti.DavisKahan1970.proposition3_4_source_full_bundled_complex
#check @TauCeti.DavisKahan1970.proposition3_4_source_eq_directRotation

/-! ## DK-3.1-thm: Classification of pairs of subspaces

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification_complex
#check @TauCeti.DavisKahan1970.theorem3_1_realization
#check @TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification_real

/-! ## DK-3.1-cor: Compact classification by angle eigenvalues

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.corollary3_1_compact_defectBlock_angleList_classification
#check @TauCeti.DavisKahan1970.corollary3_1_compact_classification_real
#check @TauCeti.DavisKahan1970.corollary3_1_realization

/-! ## DK-3.5-prop: Angle commutation and eigenspace geometry

Status: **TERMINAL EXACT**.

The three printed clauses do not share a scope, and the signatures below show it.  The source
attaches "in the acute case" to the maximal-eigenspace clause only, so the commutation and
eigenvector-angle clauses are stated for the completed direct rotation selected by a
crossed-defect isometry and carry no acuteness hypothesis; the maximality clause keeps it.
-/

#check @TauCeti.DavisKahan1970.proposition3_5_commutations
#check @TauCeti.DavisKahan1970.proposition3_5_eigenvector_angle
#check @TauCeti.DavisKahan1970.proposition3_5_commutations_acute
#check @TauCeti.DavisKahan1970.proposition3_5_eigenvector_angle_acute
#check @TauCeti.DavisKahan.Proposition35.vectorAngle_nonacuteDirectRotation_eq_of_angleOperator_apply
#check @TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_eq_fixedCosineSubspace
#check @TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_uniqueMaximal

/-! ## DK-3.2-cor: Reversal symmetry

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.corollary3_2_source
#check @TauCeti.DavisKahan1970.corollary3_2_paperQuarterTurn_symm
#check @TauCeti.DavisKahan1970.corollary3_2_nonacute_directRotation_resolution
#check @TauCeti.DavisKahan1970.complex_directRotation_reversal
#check @TauCeti.DavisKahan1970.real_directRotation_reversal
#check @TauCeti.DavisKahan1970.corollary3_2_reversal_source_form

/-! ## DK-4.1-prop: Pointwise and singular-value extremality of the direct rotation

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_complex
#check @TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_real
#check @TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_directRotationValues_complex
#check @TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_directRotationValues_real

/-! ## DK-4.1-cor: UI-norm minimality of direct rotation displacement

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute_paperUINorm_complex
#check @TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute_paperUINorm_real
#check @TauCeti.DavisKahan1970.paperUINorm_of_kyFanDominant
#check @TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute_complex
#check @TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute_real
#check @TauCeti.DavisKahan1970.Corollary4_1_infiniteDimensional_nonacute

/-! ## DK-4.2-prop: Basis-angle square-sum extremality

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.Proposition4_2_infiniteDimensional
#check @TauCeti.DavisKahan1970.tsum_displacementAngleSineSqR_ge_tsum_sq_sin_principalAngleSequence

/-! ## DK-4.3-prop: Squared displacement UI-norm minimality

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.Proposition4_3_compact_nonacute_paperUINorm_complex
#check @TauCeti.DavisKahan1970.Proposition4_3_compact_nonacute_paperUINorm_real
#check @TauCeti.DavisKahan1970.Proposition4_3_compact_nonacute_idealGauge
#check @TauCeti.DavisKahan1970.Proposition4_3_compact_nonacute_real_idealGauge

/-! ## DK-4.4-prop: Full-displacement counterexamples and Proposition 4.4 as printed

Status: **TERMINAL REFUTED + REPAIR**.
-/

#check @TauCeti.DavisKahanTheory.DavisKahanProposition4_4_Finite
#check @TauCeti.DavisKahanTheory.not_davisKahanProposition4_4_Finite
#check @TauCeti.DavisKahanTheory.shortRotation_fullDisplacement_refuted
#check @TauCeti.DavisKahanTheory.directRotation_fullDisplacement_qnorm

/-! ## DK-5.1-thm: Banach-space Sylvester lower bound

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.banach_sylvester_lower_bound_uiNorm
#check @TauCeti.DavisKahan1970.banach_sylvester_lower_bound_exact
#check @TauCeti.DavisKahan1970.banach_sylvester_lower_bound_interchanged
#check @TauCeti.DavisKahan1970.banach_sylvester_lower_bound_interchanged_exact
#check @TauCeti.DavisKahan1970.banach_sylvester_lower_bound_unboundedA
#check @TauCeti.DavisKahan1970.Audits.theorem5_1_scalarGeneric_sourceAudit

/-! ## DK-5.2-thm: Semibounded self-adjoint Sylvester theorem

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.theorem5_2_paperUINorm_complex
#check @TauCeti.DavisKahan1970.theorem5_2_paperUINorm_real
#check @TauCeti.DavisKahan1970.Theorem5_2
#check @TauCeti.DavisKahan.ExactSinTheta.davisKahan1970_sylvester_real
#check @TauCeti.DavisKahan1970.Audits.theorem5_2_real_ordered_sourceAudit

/-! ## DK-5.1-lem: Strong-cutoff convergence of singular values

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.Lemma5_1

/-! ## DK-6.1-lem: Direct-sum UI-norm comparison and converse

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.lemma6_1
#check @TauCeti.DavisKahan1970.lemma6_1_converse

/-! ## DK-6.2-lem: Reflection-pinch contraction

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.lemma6_2

/-! ## DK-6.1-prop: Sine proof, ambient limitation, and symmetric sine theorem

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.proposition6_1_source_complex
#check @TauCeti.DavisKahan1970.proposition6_1_source_projectorDifference_complex
#check @TauCeti.DavisKahan1970.proposition6_1_source_real
#check @TauCeti.DavisKahan1970.proposition6_1_commonDomain_source_complex
#check @TauCeti.DavisKahan1970.proposition6_1_commonDomain_source_real
#check @TauCeti.DavisKahan1970.Proposition6_1_commonDomain
#check @TauCeti.DavisKahan1970.Proposition6_1_real_commonDomain
#check @TauCeti.DavisKahan1970.Proposition6_1_complex
#check @TauCeti.DavisKahan1970.Proposition6_1_real
#check @TauCeti.DavisKahan1970.Proposition6_1_real_representative
#check @TauCeti.DavisKahan1970.Proposition6_1_real_sinTheta_singularValues

/-! ## DK-6.1-thm: Generalized sine theorem

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.theorem6_1_source_complex
#check @TauCeti.DavisKahan1970.theorem6_1_source_real
#check @TauCeti.DavisKahan1970.Theorem6_1_commonDomain
#check @DavisKahan1970.IsTrialResidualEquation
#check @DavisKahan1970.isTrialResidual_iff_equation_and_isometry
#check @TauCeti.DavisKahan1970.lowerFrameBound_iff_source_operator_inequality
#check @TauCeti.DavisKahan1970.lowerFrameBound_of_source_operator_inequality
#check @TauCeti.DavisKahan1970.Theorem6_1_complex
#check @TauCeti.DavisKahan1970.Theorem6_1_real
#check @TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain
#check @TauCeti.DavisKahan1970.Theorem6_1_real_commonCore

/-! ## DK-6.2-thm: Pairwise-gap square-norm sine theorem

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.theorem6_2_source_complex
#check @TauCeti.DavisKahan1970.theorem6_2_source_real
#check @TauCeti.DavisKahan1970.Theorem6_2_complex
#check @TauCeti.DavisKahan1970.Theorem6_2_real

/-! ## DK-6.3-thm: Tangent proof machinery, Example 6.1, and generalized tangent theorem

Status: **TERMINAL EXACT**.  The canonical witnesses are the two paper-norm
endpoints: Theorem 6.3 is printed "for every unitary-invariant norm", and the
representative is a parameter characterised by its approximation numbers, so one
theorem serves every norm.  The existential ideal-gauge forms below select a
representative per Ky Fan index and are supporting evidence.
-/

#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_paperUINorm_complex
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_paperUINorm_real
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedTrial_paperUINorm_complex
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedTrial_paperUINorm_real
#check @TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal
#check @TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists
#check @TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real
#check @TauCeti.DavisKahan1970.tanTheta_directed_bounded_spectralGap_paperUINorm_complex
#check @TauCeti.DavisKahan1970.tanTheta_directed_bounded_spectralGap_paperUINorm_real

/-! ## DK-6.3-lem: Finite-rank near-maximizer leakage estimate

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.Section6Appendix.lemma6_3_approximationNumber_leakage_complex
#check @TauCeti.DavisKahan1970.Section6Appendix.lemma6_3_singularValue_leakage_complex
#check @TauCeti.DavisKahan1970.Section6Appendix.lemma6_3_approximationNumber_leakage_real

/-! ## DK-8.1-thm: Branch selection and spectral repulsion

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_source
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_source
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_source
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_source
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_real
#check @TauCeti.DavisKahan1970.Section8.approximationNumber_eq_eigenvalues_of_isPositive
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_source
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_source
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_real

/-! ## DK-8.2-thm: Smallness selects the acute branch

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_paperUINorm
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_paperUINorm
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_real_paperUINorm
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_real_paperUINorm
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_maximalAngle_lt_of_crossedDefects
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_real_maximalAngle_lt_of_crossedDefects

