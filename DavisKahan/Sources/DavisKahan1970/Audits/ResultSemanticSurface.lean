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
    (hAc : TauCeti.DavisKahan.ExactSinTheta.SemiboundedBelow A (c + δ))
    (hBc : TauCeti.DavisKahan.ExactSinTheta.SemiboundedAbove B c)
    (hEq : TauCeti.DavisKahan.ExactSinTheta.HasClosedSylvesterEquation A B X C)
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
-/

#check @DavisKahan1970.sinTheta_headline
#check @TauCeti.DavisKahan1970.sinTheta_headline_generic
#check @TauCeti.DavisKahan1970.sinTheta
#check @TauCeti.DavisKahan1970.sinTheta_real_exactPaper
#check @TauCeti.DavisKahan1970.generalizedSinTheta
#check @TauCeti.DavisKahan1970.generalizedSinTheta_real_exactPaper

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

#check @TauCeti.DavisKahan1970.tanTheta_headline_generic_directed
#check @TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm
#check @TauCeti.DavisKahan.Section2.theorem6_3_perturbation_infiniteTrial
#check @TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm
#check @TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real
#check @TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent
#check @TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real_of_crossedDefectsEquivalent
#check @TauCeti.DavisKahan1970.tanTheta_unbounded_ambient_paperUINorm_exact
#check @TauCeti.DavisKahan1970.tanTheta_unbounded_ambient_paperUINorm_real_exact
#check @TauCeti.DavisKahan1970.tanTheta_unboundedCompression_ambient_paperUINorm_exact
#check @TauCeti.DavisKahan1970.tanTheta_unboundedCompression_ambient_paperUINorm_real_exact
#check @TauCeti.DavisKahan.directedGap_asymmetric_coordinateHalfSpace
#check @TauCeti.DavisKahan1970.remark3_2_bilateralShift_separates_dimensionHypotheses
#check @TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_spectral
#check @TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real_spectral
#check @TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists
#check @TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real

/-! ## S2-sin-two-theta: Double-angle sine theorem

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.sinTwoTheta_headline_generic_directed
#check @TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm
#check @TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real
#check @TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative
#check @TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative
#check @TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative_real
#check @TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_directedResidual_paperUINorm
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_directedResidual_paperUINorm_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_directedResidual_paperUINorm_real_of_intervalExterior

/-! ## S2-tan-two-theta: Double-angle tangent theorem

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.tanTwoTheta_headline_generic
#check @TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_exact
#check @TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_real_exact
#check @TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_exact
#check @TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real_exact
#check @TauCeti.DavisKahan1970.tanTwoTheta_unbounded_directedResidual_paperUINorm_exact
#check @TauCeti.DavisKahan1970.tanTwoTheta_unbounded_directedResidual_paperUINorm_real_exact
#check @TauCeti.DavisKahan1970.tanTwoTheta_unbounded_ambient_paperUINorm_exact
#check @TauCeti.DavisKahan1970.tanTwoTheta_unbounded_ambient_paperUINorm_real_exact

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
#check @TauCeti.DavisKahan1970.proposition3_4_source_full
#check @TauCeti.DavisKahan1970.proposition3_4_source_eq_directRotation

/-! ## DK-3.1-thm: Classification of pairs of subspaces

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification
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

#check @TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute
#check @TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_real
#check @TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_directRotationValues
#check @TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_directRotationValues_real

/-! ## DK-4.1-cor: UI-norm minimality of direct rotation displacement

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute
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
#check @TauCeti.DavisKahan1970.Audits.theorem5_1_scalarGeneric_sourceAudit

/-! ## DK-5.2-thm: Semibounded self-adjoint Sylvester theorem

Status: **TERMINAL EXACT**.
-/

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

#check @TauCeti.DavisKahan1970.Proposition6_1
#check @TauCeti.DavisKahan1970.Proposition6_1_real

/-! ## DK-6.1-thm: Generalized sine theorem

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.Theorem6_1
#check @TauCeti.DavisKahan1970.Theorem6_1_real
#check @TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain
#check @TauCeti.DavisKahan1970.Theorem6_1_real_commonCore

/-! ## DK-6.2-thm: Pairwise-gap square-norm sine theorem

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.Theorem6_2
#check @TauCeti.DavisKahan1970.Theorem6_2_real

/-! ## DK-6.3-thm: Tangent proof machinery, Example 6.1, and generalized tangent theorem

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists
#check @TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real
#check @TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_spectral
#check @TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real_spectral

/-! ## DK-6.3-lem: Finite-rank near-maximizer leakage estimate

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.Section6Appendix.lemma6_3_approximationNumber_leakage
#check @TauCeti.DavisKahan1970.Section6Appendix.lemma6_3_singularValue_leakage
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

#check @TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_paperUINorm
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_paperUINorm
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_real_paperUINorm
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_real_paperUINorm
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_maximalAngle_lt_of_crossedDefects
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_real_maximalAngle_lt_of_crossedDefects

