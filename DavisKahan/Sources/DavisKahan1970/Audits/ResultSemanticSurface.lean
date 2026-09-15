/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.All

open TauCeti.DavisKahan.Sylvester

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
  exact TauCeti.DavisKahan1970.theorem5_2_kyFanDominant_real
    N hA hB hδ
      (TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap.leftAboveRightBelow
        c hAc hBc)
      hEq hC


/-! ## Source-exact Section 2 façades

Each of these states its Section 2 clause at the PRINTED scope.  For the
sine-theta façade that means a separable ambient Hilbert space and
`NormalizedSymmetricOperatorIdealFamily`, with the source-wide vacuity convention
spelled directly in the theorem type as `N.Mem sinTheta₀ → N.Mem R → ...`.
The stronger arbitrary-Hilbert `SymmetricNormingFunction` theorem remains
registered separately as a generalization.  The discharge is the source's own
Fan-dominance reduction at (1.11)-(1.13). -/

#check @TauCeti.DavisKahan1970.corollary4_1_compact_nonacute_sourceExact_complex
#check @TauCeti.DavisKahan1970.corollary4_1_compact_nonacute_sourceExact_real
#check @TauCeti.DavisKahan1970.proposition4_3_compact_nonacute_sourceExact_complex
#check @TauCeti.DavisKahan1970.proposition4_3_compact_nonacute_sourceExact_real
#check @TauCeti.DavisKahan1970.proposition4_3_compact_nonacute_sourceExact_ofCrossedDefects_complex
#check @TauCeti.DavisKahan1970.proposition4_3_compact_nonacute_sourceExact_ofCrossedDefects_real
#check @TauCeti.DavisKahan1970.theorem5_2_sourceExact_complex
#check @TauCeti.DavisKahan1970.theorem5_2_sourceExact_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_sourceExact
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_directedAngle_sourceExact
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_real_sourceExact
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_directedAngle_real_sourceExact
#check @TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_whereDefinedUIN_rclike
#check @TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_whereDefinedUIN_complex
#check @TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_whereDefinedUIN_real
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_definedTangent_normalizedUIN_complex
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_definedTangent_normalizedUIN_real
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_normalizedUIN_complex
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_normalizedUIN_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_whereDefinedUIN_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_whereDefinedUIN_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_perturbedGap_whereDefinedUIN_rclike
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_reducing_whereDefinedUIN_rclike
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_rclike
#check @TauCeti.DavisKahan1970.sinTwoTheta_reflectionResidual_block_gauge_reducing_rclike
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_kyFan_rclike
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_symmetricNorming_rclike
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_rclike
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_perturbedGap_whereDefinedUIN_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_normalizedUIN_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_normalizedUIN_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_perturbedGap_normalizedUIN_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_perturbedGap_normalizedUIN_real
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_normalizedUIN_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_normalizedUIN_real
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_normalizedUIN_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_normalizedUIN_real
#check @TauCeti.DavisKahan1970.normalizedUnitaryInvariant_of_symmetricNorming
#check @TauCeti.DavisKahan1970.normalizedUnitaryInvariant_of_symmetricNorming_mul
#check @TauCeti.DavisKahan.ExactSinTheta.NormalizedUnitaryInvariantNorm
end TauCeti.DavisKahan1970.Audits

/-! ## The source's norm class: the two Lean quantifiers are equivalent

Section 1 fixes `‖·‖` as an arbitrary normalized unitarily invariant norm and then
declares the criterion it will use: "Fan dominance is used in the strong form:
`‖K‖ ≤ ‖L‖` for every unitary-invariant norm iff the inequality holds for every Ky
Fan norm."

Two Lean objects model that class in this development.  `SymmetricNormingFunction`
is the Gohberg--Krein reading -- a dimension-coherent symmetric gauge, extended to
infinite dimension as the supremum of its singular-value prefixes.
`KyFanDominantIdealFamily` is the axiomatic reading -- a symmetric operator ideal
family with Fan dominance as a field.  Neither exhausts the other as a *type*: the
Calkin-augmented norm `T ↦ ‖T‖ + ‖π(T)‖` is a Fan-dominant unitarily invariant norm
on `B(H)` that agrees with the operator norm on finite-rank operators, so no
symmetric gauge generates it.

The two theorems below show the *estimates* do not care.  Each quantifier is
equivalent to weak Ky Fan majorization, so a bound proved over one holds over the
other -- and a source-facing endpoint stated over `SymmetricNormingFunction`
therefore delivers the printed "for every unitary-invariant norm", including at
norms outside the symmetrically normed ideals. -/

#check @TauCeti.DavisKahan1970.symmetricNorming_of_kyFanDominant
#check @TauCeti.DavisKahan1970.kyFanDominant_of_symmetricNorming
#check @TauCeti.DavisKahan1970.symmetricNorming_iff_kyFanDominant

/-! ## S2-sin-theta: Single-angle sine theorem

Status: **TERMINAL EXACT**.

The first name is the public Section 2 short name, now aliasing the ledger-selected
where-defined RClike theorem. The fixed-field aliases are thin specializations; the older
`SymmetricNormingFunction` declarations remain stronger implementation APIs. -/

#check @TauCeti.DavisKahan1970.SectionTwo.sinTheta
#check @TauCeti.DavisKahan1970.SectionTwo.sinTheta_complex
#check @TauCeti.DavisKahan1970.SectionTwo.sinTheta_real
#check @TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_real
#check @TauCeti.DavisKahan1970.sinTheta_unbounded_intervalExterior_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.sinTheta_unbounded_intervalExterior_symmetricNorming_real
#check @TauCeti.DavisKahan1970.sinTheta_unbounded_intervalExterior_characterizedWitness_rclike
#check @TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_rclike
#check @TauCeti.DavisKahan1970.sinTheta_unbounded_intervalExterior_symmetricNorming_rclike
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

#check @TauCeti.DavisKahan1970.SectionTwo.tanTheta_directed
#check @TauCeti.DavisKahan1970.SectionTwo.tanTheta_ambient
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_rclike
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_exists_rclike
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_definedTangent_symmetricNorming_rclike
#check @TauCeti.DavisKahan1970.SectionTwo.tanTheta_ambient_complex
#check @TauCeti.DavisKahan1970.SectionTwo.tanTheta_ambient_real
#check @TauCeti.DavisKahan1970.tanTheta_directed_finiteDimensional_symmetricNorming_rclike
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_definedTangent_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_definedTangent_symmetricNorming_real
#check @TauCeti.DavisKahan1970.HasDefinedAmbientTangent
#check @TauCeti.DavisKahan1970.HasDefinedAmbientTangentReal
#check @TauCeti.DavisKahan1970.crossedDefectsEquivalent_of_hasDefinedAmbientTangent
#check @TauCeti.DavisKahan1970.crossedDefectsEquivalent_of_hasDefinedAmbientTangentReal
#check @TauCeti.DavisKahan1970.spectrum_angleOperator_lt_pi_div_two_of_hasDefinedAmbientTangent
#check @TauCeti.DavisKahan1970.continuousOn_tan_spectrum_of_hasDefinedAmbientTangent
#check @TauCeti.DavisKahan1970.hasDefinedAmbientTangent_iff_pi_div_two_notMem_spectrum
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_symmetricNorming_real
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_real
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedTrial_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedTrial_symmetricNorming_real
#check @TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal
#check @TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.ideal_of_formBounds
#check @TauCeti.DavisKahan1970.theorem6_3_unboundedCompression_ideal_real
#check @TauCeti.DavisKahan.UnboundedRitzPair
#check @TauCeti.DavisKahan.ReducingComplement
#check @TauCeti.DavisKahan.UnboundedRitzPair.ofTrialBlock
#check @TauCeti.DavisKahan.ReducingComplement.ofReducesSubspace
#check @TauCeti.DavisKahan.FiniteDimensional.partIII_tanTheta_ritzResidual_uiNorm
#check @TauCeti.DavisKahan1970.theorem6_3_perturbation_infiniteTrial
#check @TauCeti.DavisKahan1970.tanTheta_ambient_bounded_symmetricNorming_complex_of_transversality
#check @TauCeti.DavisKahan1970.tanTheta_ambient_bounded_symmetricNorming_real_of_transversality
#check @TauCeti.DavisKahan1970.tanTheta_ambient_bounded_symmetricNorming_complex_of_crossedDefects
#check @TauCeti.DavisKahan1970.tanTheta_ambient_bounded_symmetricNorming_real_of_crossedDefects
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedOperator_boundedRitz_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedOperator_boundedRitz_symmetricNorming_real
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_explicitCompatibility_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_explicitCompatibility_symmetricNorming_real
#check @TauCeti.DavisKahan.directedGap_asymmetric_coordinateHalfSpace
#check @TauCeti.DavisKahan1970.remark3_2_bilateralShift_separates_dimensionHypotheses
#check @TauCeti.DavisKahan1970.tanTheta_directed_bounded_spectralGap_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTheta_directed_bounded_spectralGap_symmetricNorming_real
#check @TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists
#check @TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_exists_complex
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_exists_real
#check @TauCeti.DavisKahan1970.approximationSingularValue_directedSineBlock_lt_one_unboundedRitz_complex
#check @TauCeti.DavisKahan1970.approximationSingularValue_directedSineBlock_lt_one_unboundedRitz_real

/-! ## S2-sin-two-theta: Double-angle sine theorem

Status: **TERMINAL EXACT**.  Both fixed-field endpoints take
`FormBoundedSylvesterGap`, so the printed half-infinite gap scope is covered on
both.  The two `spectrumGap` declarations are the earlier complex route, at a
bounded separating interval only; they are supporting evidence, not the
result's canonical witness.

The **ambient** clause is discharged by
`sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_complex` and its real
sibling, at the same unbounded scope as the directed clause.  The bounded ambient
endpoints below them are their specializations, retained as an alternative proof.

`sinTwoTheta_ambient_unbounded_reflectionPair_symmetricNorming_rclike` is the same
ambient bound at an **arbitrary `RCLike` field**, on the paper's own ambient
double-angle sine.  It is supporting rather than canonical evidence because it
hypothesises `U` and `V` as a reducing subspace and a reflected pair instead of
naming the printed spectral subspaces, whose construction in this tree is
field-specific.  Its signature carries no capability class and no functional
calculus: the real calculus on `E →L[𝕜] E` is a theorem at every `RCLike` field.
-/

#check @TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta
#check @TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta_directed
#check @TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta_directed_complex
#check @TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta_directed_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_finiteDimensional_symmetricNorming_rclike
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_blockRepresentative_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_blockRepresentative_spectrumGap_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_spectrumGap_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_unequalDimension_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_unequalDimension_symmetricNorming_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_unequalDimension_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_reflectionResidual_arbitraryRepresentative_unequalDimension_complex
#check @TauCeti.DavisKahan.sinTwoTheta_addBounded_gauge_of_formGap
#check @TauCeti.DavisKahan.sinTwoTheta_reflectionResidual_gauge_of_formGap
#check @TauCeti.DavisKahan.sinTheta_addBounded_gauge_complex_block_of_formGap
#check @TauCeti.DavisKahan.ExactSinTheta.sinTheta_unbounded_complex_block
#check @TauCeti.DavisKahan.directedSinAngleOperatorC_reflected_eq_directedSinTwoAngleOperatorC
#check @TauCeti.DavisKahan.sinTwoThetaIdealBlock_hasSameApproximationNumbers
#check @TauCeti.DavisKahan.extendedGauge_sinTwoThetaIdealBlock_complex
#check @TauCeti.DavisKahan.approximationSingularValue_sinTwoThetaIdealBlock_real
#check @TauCeti.DavisKahan.extendedGauge_sinTwoThetaIdealBlock_real
#check @TauCeti.DavisKahan.mem_directedSinTwoAngleOperatorC_iff
#check @TauCeti.DavisKahan.gauge_directedSinTwoAngleOperatorC
#check @TauCeti.DavisKahan.mem_directedSinTwoAngleOperatorRC_iff
#check @TauCeti.DavisKahan.gauge_directedSinTwoAngleOperatorRC
-- The canonical ambient witnesses: the gap is on the blocks of the PERTURBED
-- operator relative to `Q`, which is where Section 2 states it.
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_rclike
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_real
-- The unperturbed-gap reading, retained as supporting evidence.
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_reducing_symmetricNorming_rclike
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_reducing_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_reducing_symmetricNorming_real
-- The four steps of the role reversal.
#check @TauCeti.LinearPMap.addBounded_neg_cancel
#check @TauCeti.DavisKahan.Angle.sinTwoAngleOperator_comm
#check @TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge_neg
#check @TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.mem_neg
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_reflectionPair_symmetricNorming_rclike
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_real
#check @TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta_ambient
#check @TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta_ambient_complex
#check @TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta_ambient_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_reflection_projectorDifference_symmetricNorming
#check @TauCeti.DavisKahan1970.sinTheta_ambient_unitaryConj_projectorDifference_symmetricNorming
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_bounded_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_ambient_bounded_symmetricNorming_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_reflectionResidual_arbitraryRepresentative_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_unbounded_reflectionResidual_arbitraryRepresentative_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_spectrumGap_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_intervalExterior_symmetricNorming_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_symmetricNorming_real
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_real
#check @TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator_hasSameApproximationNumbers_swap
#check @TauCeti.DavisKahan.Angle.sinTwoThetaIdealBlock_hasSameApproximationNumbers_trialSide
#check @TauCeti.DavisKahan.Angle.mem_directedSinTwoAngleOperator_trialSide_iff
#check @TauCeti.DavisKahan.Angle.gauge_directedSinTwoAngleOperator_trialSide
#check @TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta_directed_blockRepresentative_complex
#check @TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta_directed_blockRepresentative_real

/-! ### The directed `sin 2Θ` orientation, pinned

`Angle.directedSinTwoAngleOperator` is an **ordered** object, and the directed
Section 2 clause is about one of the two orderings.  A `#check` cannot see that: the
type of `sinTwoTheta_directed_complex` mentions both subspaces, and swapping them
leaves a well-typed theorem with the same name and the same declaration signature
shape.  The audit below fixes the semantic names and states the intended conclusion
literally, so that a later argument swap fails to elaborate here rather than passing
silently.

`trial` is the subspace carrying the printed residual `R = A E₀ - E₀ A₀`; `gapCarrier`
is the subspace whose two reducing restrictions the printed separation `δ` separates.
The paper's `sin Θ₀` is `Q^⊥ E₀` -- the cross-projection with the trial subspace on
the right -- so the conclusion must be on
`directedSinTwoAngleOperator trial gapCarrier`, in that order. -/

open TauCeti.DavisKahan.Sylvester in
/-- **Orientation audit for the directed `sin 2Θ` clause, over `ℂ`.**

Discharged by a bare application of the source theorem with no adapter and no
rewriting, so it holds exactly when that theorem's conclusion is on the trial-side
ordering. -/
theorem sinTwoTheta_directed_orientation_sourceAudit_complex
    {Hc : Type*} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction)
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    {trial : Submodule ℂ Hc} [trial.HasOrthogonalProjection]
    [CompleteSpace trial]
    {ritz : trial →L[ℂ] trial} {residual : trial →L[ℂ] Hc}
    {gapCarrier : Submodule ℂ Hc} [gapCarrier.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A gapCarrier)
    (hVdom : ∀ v : trial, (v : Hc) ∈ A.domain)
    (hres : ∀ v : trial, A ⟨(v : Hc), hVdom v⟩ = residual v + ((ritz v : trial) : Hc))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A gapCarrier hred)
      (TauCeti.LinearPMap.reducingRestriction A gapCarrierᗮ hred.orthogonal) δ)
    (hRmem : N.Mem residual) :
    N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator trial gapCarrier) ∧
      δ * N.gauge
          (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator trial gapCarrier) ≤
        2 * N.gauge residual :=
  TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_complex
    N hA hred hVdom hres hδ hgap hRmem

open TauCeti.DavisKahan.Sylvester in
/-- **Orientation audit for the directed `sin 2Θ` clause, over `ℝ`.** -/
theorem sinTwoTheta_directed_orientation_sourceAudit_real
    {Er : Type*} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction)
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    {trial : Submodule ℝ Er} [trial.HasOrthogonalProjection]
    [CompleteSpace trial]
    {ritz : trial →L[ℝ] trial} {residual : trial →L[ℝ] Er}
    {gapCarrier : Submodule ℝ Er} [gapCarrier.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A gapCarrier)
    (hVdom : ∀ v : trial, (v : Er) ∈ A.domain)
    (hres : ∀ v : trial, A ⟨(v : Er), hVdom v⟩ = residual v + ((ritz v : trial) : Er))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A gapCarrier hred)
      (TauCeti.LinearPMap.reducingRestriction A gapCarrierᗮ hred.orthogonal) δ)
    (hRmem : N.Mem residual) :
    N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator trial gapCarrier) ∧
      δ * N.gauge
          (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator trial gapCarrier) ≤
        2 * N.gauge residual :=
  TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_real
    N hA hred hVdom hres hδ hgap hRmem

/-- **The two orderings are not the same operator.**

Recorded so that the orientation audits above are read as content rather than
bookkeeping: what makes them necessary is that the *sines* differ.  The doubled
sines agree only at the level of the approximation-number sequence, which is
`directedSinTwoAngleOperator_hasSameApproximationNumbers_swap`, and that is a
theorem about the doubling. -/
example {Hc : Type*} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    (U V : Submodule ℂ Hc) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator U V).HasSameApproximationNumbers
      (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator V U) :=
  TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator_hasSameApproximationNumbers_swap U V

/-! ## S2-tan-two-theta: Double-angle tangent theorem

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.SectionTwo.tanTwoTheta_directed
#check @TauCeti.DavisKahan1970.SectionTwo.tanTwoTheta_ambient
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_rclike
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_reducing_symmetricNorming_rclike
#check @TauCeti.DavisKahan1970.SectionTwo.tanTwoTheta_ambient_complex
#check @TauCeti.DavisKahan1970.SectionTwo.tanTwoTheta_ambient_real
#check @TauCeti.DavisKahan1970.tanTwoTheta_branchFree_bounded_finiteSubspace_symmetricNorming_rclike
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_blockRepresentative_derivedReflection_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_blockRepresentative_derivedReflection_symmetricNorming_real
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
#check @TauCeti.DavisKahan.tanTwoBlockRepresentative_mul_signedCosTwo
#check @TauCeti.DavisKahan.sameApproximationSingularValues_unboundedReflectionTangent
#check @TauCeti.DavisKahan.extendedGauge_unboundedReflectionTangent_complex
#check @TauCeti.DavisKahan.extendedGauge_unboundedReflectionTangent_real
#check @TauCeti.DavisKahan.isUnit_signedCosTwo_of_isUnit_diagonalPart_sq
#check @TauCeti.DavisKahan.cos_two_ne_zero_of_isUnit_diagonalPart_reflection_sq
#check @TauCeti.DavisKahan.Angle.absTanTwoAngleOperatorR
#check @TauCeti.DavisKahan.Angle.complexify_absTanTwoAngleOperatorR
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.cos_two_ne_zero_of_isUnit_diagonalPart_reflection_sq_real
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_symmetricNorming_real
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_symmetricNorming_real
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_bounded_spectralGap_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_bounded_spectralGap_symmetricNorming_real
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_blockRepresentative_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_blockRepresentative_symmetricNorming_real

/-! ## DK-3.1-prop: Acute direct rotation existence and uniqueness

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.proposition3_1

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

#check @TauCeti.DavisKahan1970.proposition3_3_complex_forward
#check @TauCeti.DavisKahan1970.proposition3_3_complex_converse
#check @TauCeti.DavisKahan1970.proposition3_3_real_forward
#check @TauCeti.DavisKahan1970.proposition3_3_real_converse

/-! ## DK-3.4-prop: Square as a direct rotation

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.proposition3_4_full_complex
#check @TauCeti.DavisKahan1970.proposition3_4_full_real
#check @TauCeti.DavisKahan1970.proposition3_4_isDirectRotation_complex
#check @TauCeti.DavisKahan1970.proposition3_4_eq_directRotation
#check @TauCeti.DavisKahan1970.proposition3_4_crossedDefectsEquivalent_complex
#check @TauCeti.DavisKahan1970.proposition3_4_crossedDefectsEquivalent_real

/-! ## DK-3.1-thm: Classification of pairs of subspaces

Status: **TERMINAL EXACT**.
-/

-- The canonical witness: the invariant on the SOURCE'S OWN angle operators.
#check @TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification_sourceAngle_complex
#check @TauCeti.DavisKahan1970.genericAngleBlock
#check @TauCeti.DavisKahan1970.spectrum_genericCosineBlock_subset_Icc
#check @TauCeti.sameSpectralMultiplicity_cfc_iff
#check @TauCeti.OperatorUnitaryEquiv.cfc_real
#check @TauCeti.continuous_conjStarAlgEquiv
#check @TauCeti.DavisKahan1970.genericCosineBlock_nonneg
#check @TauCeti.DavisKahan1970.genericCosineBlock_le_one
-- The same, over a real Hilbert space, on the source's own angle operator.
#check @TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification_sourceAngle_real
#check @TauCeti.DavisKahan1970.genericAngleBlockReal
#check @TauCeti.DavisKahan1970.spectrum_genericCosineBlock_subset_Icc_real
#check @TauCeti.DavisKahan.RealSpectralRestriction.sameSpectralMultiplicity_cfc_iff_real
#check @TauCeti.DavisKahan1970.genericCosineBlock_nonneg_real
#check @TauCeti.DavisKahan1970.genericCosineBlock_le_one_real
#check @TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification_real
-- The printed dimension clause as a proposition, and the realizations it produces.
#check @TauCeti.DavisKahan1970.SameHilbertDimensionSum
#check @TauCeti.DavisKahan1970.theorem3_1_realization_inAmbient_ofSameHilbertDimension_complex
#check @TauCeti.DavisKahan1970.theorem3_1_realization_inAmbient_ofSameHilbertDimension_real
-- The structural cos^2 Theta classification beneath the source-facing statement.
#check @TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification_complex
#check @TauCeti.DavisKahan1970.theorem3_1_realization
#check @TauCeti.DavisKahan1970.theorem3_1_realization_ofSpectralMultiplicity_complex
#check @TauCeti.DavisKahan1970.theorem3_1_realization_inAmbient_ofSpectralMultiplicityAwayFromZero_complex
#check @TauCeti.DavisKahan1970.theorem3_1_realization_inAmbient_ofSpectralMultiplicityAwayFromZero_real
#check @TauCeti.nonempty_linearIsometryEquiv_of_hilbertBasis
#check @TauCeti.DavisKahan1970.theorem3_1_realization_ofSpectralMultiplicityAwayFromZero_complex
#check @TauCeti.DavisKahan1970.theorem3_1_intertwiner_of_nonzeroPartsUnitaryEquiv
#check @TauCeti.DavisKahan1970.theorem3_1_realization_ofNonzeroPartsUnitaryEquiv
#check @TauCeti.DavisKahan1970.NonzeroPartsUnitaryEquiv
#check @TauCeti.DavisKahan1970.theorem3_1_realization_ofSpectralMultiplicityAwayFromZero_real
#check @TauCeti.DavisKahan1970.SameSpectralMultiplicityAwayFromZero
#check @TauCeti.DavisKahan1970.nonzeroPart
#check @TauCeti.DavisKahan1970.invariantFor_nonzeroPart
#check @TauCeti.DavisKahan1970.theorem3_1_intertwiner_of_sameSpectralMultiplicity_complex
#check @TauCeti.DavisKahan1970.theorem3_1_realization_ofAngles
#check @TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification_real

/-! ## DK-3.1-cor: Compact classification by angle eigenvalues

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.corollary3_1_compact_defectBlock_angleList_classification
#check @TauCeti.DavisKahan1970.corollary3_1_compact_classification_real
#check @TauCeti.DavisKahan1970.corollary3_1_realization
#check @TauCeti.DavisKahan1970.corollary3_1_realization_zeroMultiplicity
#check @TauCeti.DavisKahan1970.corollary3_1_prescribedAngleSequence_classification
#check @TauCeti.DavisKahan1970.corollary3_1_prescribedAngleSequence_classification_real
-- The canonical Corollary 3.1 witness: the invariant on the source's own ANGLES.
#check @TauCeti.DavisKahan1970.corollary3_1_compact_defectBlock_sourceAngleList_classification
#check @TauCeti.DavisKahan1970.norm_genericCosineBlock_le_one
#check @TauCeti.DavisKahan1970.compactAngleList
#check @TauCeti.DavisKahan1970.compactAngleList_mem_Icc
#check @TauCeti.DavisKahan1970.compactAngleList_inj_iff
#check @TauCeti.DavisKahan1970.compactAngleEigenvalueList_genericCosineBlock_le_one
#check @TauCeti.DavisKahan1970.angleSequence_eq_of_angleList_eq
#check @TauCeti.DavisKahan1970.angle_eq_of_sin_sq_eq

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

#check @TauCeti.DavisKahan1970.corollary3_2
#check @TauCeti.DavisKahan1970.corollary3_2_nonacuteQuarterTurn_symm
#check @TauCeti.DavisKahan1970.corollary3_2_nonacute_directRotation_resolution
#check @TauCeti.DavisKahan1970.complex_directRotation_reversal
#check @TauCeti.DavisKahan1970.real_directRotation_reversal
#check @TauCeti.DavisKahan1970.corollary3_2_reversal_form

/-! ## DK-4.1-prop: Pointwise and singular-value extremality of the direct rotation

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.proposition4_1_compact_nonacute_complex
#check @TauCeti.DavisKahan1970.proposition4_1_compact_nonacute_real
#check @TauCeti.DavisKahan1970.proposition4_1_directRotation_sourceExact_complex
#check @TauCeti.DavisKahan1970.proposition4_1_directRotation_sourceExact_real
#check @TauCeti.DavisKahan1970.corollary4_1_directRotation_sourceExact_complex
#check @TauCeti.DavisKahan1970.corollary4_1_directRotation_sourceExact_real
#check @TauCeti.DavisKahan1970.proposition4_3_directRotation_sourceExact_complex
#check @TauCeti.DavisKahan1970.proposition4_3_directRotation_sourceExact_real
#check @TauCeti.DavisKahan1970.proposition4_1_compact_nonacute_directRotationValues_complex
#check @TauCeti.DavisKahan1970.proposition4_1_compact_nonacute_directRotationValues_real

/-! ## DK-4.1-cor: UI-norm minimality of direct rotation displacement

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.corollary4_1_compact_nonacute_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.corollary4_1_compact_nonacute_symmetricNorming_real
#check @TauCeti.DavisKahan1970.symmetricNorming_of_kyFanDominant
#check @TauCeti.DavisKahan1970.corollary4_1_compact_nonacute_complex
#check @TauCeti.DavisKahan1970.corollary4_1_compact_nonacute_real
#check @TauCeti.DavisKahan1970.corollary4_1_infiniteDimensional_nonacute

/-! ## DK-4.2-prop: Basis-angle square-sum extremality

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.proposition4_2_infiniteDimensional
#check @TauCeti.DavisKahan1970.proposition4_2_compact_nonacute
#check @TauCeti.DavisKahan1970.proposition4_2_compact_nonacute_real
#check @TauCeti.DavisKahan1970.tsum_displacementAngleSineSqR_ge_tsum_sq_sin_principalAngleSequence

/-! ## DK-4.3-prop: Squared displacement UI-norm minimality

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.proposition4_3_compact_nonacute_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.proposition4_3_compact_nonacute_symmetricNorming_real
#check @TauCeti.DavisKahan1970.proposition4_3_compact_nonacute_idealGauge
#check @TauCeti.DavisKahan1970.proposition4_3_compact_nonacute_real_idealGauge

/-! ## DK-4.4-prop: Full-displacement counterexamples and Proposition 4.4 as printed

Status: **TERMINAL REFUTED + REPAIR**.
-/

#check @TauCeti.DavisKahan1970.proposition4_4_printedStatement
#check @TauCeti.DavisKahan1970.proposition4_4_refuted
#check @TauCeti.DavisKahan.crossedDefectsEquivalent_of_isAcute
#check @TauCeti.DavisKahan.crossedDefectsEquivalent_iff_finrank_eq
#check @TauCeti.DavisKahan.CrossedDefectsSameDimension
#check @TauCeti.DavisKahan.crossedDefectsEquivalent_iff_sameDimension
#check @TauCeti.nonempty_linearIsometryEquiv_of_separable_of_infiniteDimensional
#check @TauCeti.nonempty_linearIsometryEquiv_of_countable_infinite_hilbertBasis
#check @TauCeti.nonempty_linearIsometryEquiv_of_hilbertBasis
#check @TauCeti.exists_countable_hilbertBasis
#check @TauCeti.finiteDimensional_of_finite_hilbertBasis
#check @TauCeti.lpIndexCongr
#check @TauCeti.countable_of_orthonormal
#check @TauCeti.DavisKahan1970.approximationNumber_reflectionTangentCorner
#check @TauCeti.DavisKahan1970.reflectionTangentCorner_reflection_eq_tanTwoBlockCompression
#check @TauCeti.DavisKahan1970.tanTwoDirectedCornerC_sameApproximationSingularSequence_reflectionTangentCorner
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_reducing_blockCompression_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_reducing_derivedReflection_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_reducing_sineSequence_symmetricNorming_real
#check @TauCeti.DavisKahan1970.blockCompression_diagonalPair
#check @TauCeti.DavisKahan1970.blockCompression_mul_reflectionOperator
#check @TauCeti.DavisKahan1970.extendedGauge_projectionBlock_eq_blockCompression
#check @TauCeti.DavisKahan1970.mem_projectionBlock_iff_mem_blockCompression
#check @TauCeti.DavisKahan1970.gauge_projectionBlock_eq_blockCompression
#check @TauCeti.DavisKahan1970.approximationNumber_tanTwoDirectedCorner
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_symmetricNorming_real
#check @TauCeti.DavisKahan1970.approximationNumber_tanTwoDirectedCornerR
#check @TauCeti.DavisKahan1970.norm_offDiagonalPart_reflectionOperator_complexifySubmodule
#check @TauCeti.DavisKahan1970.complexifyReal_addBounded
#check @TauCeti.DavisKahan1970.reducesSubspace_addBounded_complexifyReal
#check @TauCeti.DavisKahan1970.re_inner_complexifyReal_le_of_forall_mem
#check @TauCeti.DavisKahan1970.le_re_inner_complexifyReal_of_forall_mem_orthogonal
#check @TauCeti.DavisKahan1970.reducesSubspace_complexifyReal
#check @TauCeti.DavisKahan1970.isOddFor_complexifySubmodule
#check @TauCeti.DavisKahan1970.projectionBlock_complexifySubmodule
#check @TauCeti.LinearPMap.isSelfAdjoint_complexifyReal
#check @TauCeti.DavisKahan.complexify_sinTwoThetaIdealBlock
#check @TauCeti.DavisKahan.ExactSinTheta.ComplexificationApproximation.approximationSingularValue_complexify
#check @TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge_complexify
#check @TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.mem_complexify_iff
#check @TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge_eq_of_hasSameApproximationNumbers
#check @TauCeti.DavisKahan.ExactSinTheta.projectionBlock_same_compression
#check @TauCeti.DavisKahan1970.hasSameApproximationNumbers_reflectionSineCorner_sinTwoThetaIdealBlock
#check @TauCeti.DavisKahan1970.tanTwoDirectedCornerR
#check @TauCeti.DavisKahan1970.proposition4_4_refutingPair
#check @TauCeti.DavisKahan.FiniteDimensional.directRotation_fullDisplacement_qnorm

/-! ## DK-5.1-thm: Banach-space Sylvester lower bound

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.banach_sylvester_lower_bound_uiNorm
#check @TauCeti.DavisKahan1970.banach_sylvester_lower_bound_exact
#check @TauCeti.DavisKahan1970.theorem5_1_banach_sylvester_banachScope
#check @TauCeti.DavisKahan1970.theorem5_1_banach_sylvester_banachScope_ofProperties
#check @TauCeti.DavisKahan1970.banach_sylvester_lower_bound_interchanged
#check @TauCeti.DavisKahan1970.banach_sylvester_lower_bound_interchanged_exact
#check @TauCeti.DavisKahan1970.banach_sylvester_lower_bound_unboundedA
#check @TauCeti.DavisKahan1970.Audits.theorem5_1_scalarGeneric_sourceAudit

/-! ## DK-5.2-thm: Semibounded self-adjoint Sylvester theorem

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.theorem5_2_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.theorem5_2_symmetricNorming_real
#check @TauCeti.DavisKahan1970.theorem5_2_orderedGap_symmetricNorming_real
#check @TauCeti.DavisKahan1970.theorem5_2
#check @TauCeti.DavisKahan1970.theorem5_2_kyFanDominant_real
#check @TauCeti.DavisKahan1970.Audits.theorem5_2_real_ordered_sourceAudit

/-! ## DK-5.1-lem: Strong-cutoff convergence of singular values

Status: **TERMINAL EXACT**.

The canonical witnesses are the two fixed-field statements.  `lemma5_1` is generic
over `RCLike 𝕜` and carries `HasApproximationNumberStrongCutoff 𝕜`, a capability
class whose single field is Lemma 5.1 itself; it is a facade over the two proofs
below and is kept as supporting evidence so the generic development can cite one
name.  A registered witness for a printed lemma should not assume that lemma.
-/

#check @TauCeti.DavisKahan1970.lemma5_1_complex
#check @TauCeti.DavisKahan1970.lemma5_1_real
#check @TauCeti.DavisKahan1970.lemma5_1

/-! ## DK-6.1-lem: Direct-sum UI-norm comparison and converse

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.lemma6_1
#check @TauCeti.DavisKahan1970.lemma6_1_converse
#check @TauCeti.DavisKahan1970.lemma6_2_sourceExact
#check @TauCeti.DavisKahan1970.lemma6_1_sourceExact_complex
#check @TauCeti.DavisKahan1970.lemma6_1_sourceExact_real
#check @TauCeti.DavisKahan1970.lemma6_1_converse_sourceExact_complex
#check @TauCeti.DavisKahan1970.lemma6_1_converse_sourceExact_real
#check @TauCeti.DavisKahan1970.lemma6_1_sourceExact
#check @TauCeti.DavisKahan1970.lemma6_1_converse_sourceExact

/-! ## DK-6.2-lem: Reflection-pinch contraction

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.lemma6_2

/-! ## DK-6.1-prop: Sine proof, ambient limitation, and symmetric sine theorem

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.proposition6_1_complex
#check @TauCeti.DavisKahan1970.proposition6_1_projectorDifference_complex
#check @TauCeti.DavisKahan1970.proposition6_1_real
#check @TauCeti.DavisKahan1970.proposition6_1_sourceExact_complex
#check @TauCeti.DavisKahan1970.proposition6_1_sourceExact_real
#check @TauCeti.DavisKahan1970.proposition6_1_commonDomain_complex
#check @TauCeti.DavisKahan1970.proposition6_1_commonDomain_real
#check @TauCeti.DavisKahan1970.proposition6_1_commonDomain
#check @TauCeti.DavisKahan1970.proposition6_1_real_commonDomain
#check @TauCeti.DavisKahan1970.proposition6_1_complex
#check @TauCeti.DavisKahan1970.proposition6_1_real
#check @TauCeti.DavisKahan1970.proposition6_1_real_representative
#check @TauCeti.DavisKahan1970.proposition6_1_real_sinTheta_singularValues

/-! ## DK-6.1-thm: Generalized sine theorem

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.theorem6_1_complex
#check @TauCeti.DavisKahan1970.theorem6_1_real
#check @TauCeti.DavisKahan1970.theorem6_1_sourceExact_complex
#check @TauCeti.DavisKahan1970.theorem6_1_sourceExact_real
#check @TauCeti.DavisKahan1970.theorem6_1_commonDomain
#check @TauCeti.DavisKahan1970.IsTrialResidualEquation
#check @TauCeti.DavisKahan1970.isTrialResidual_iff_equation_and_isometry
#check @TauCeti.DavisKahan1970.lowerFrameBound_iff_operator_inequality
#check @TauCeti.DavisKahan1970.lowerFrameBound_of_operator_inequality
#check @TauCeti.DavisKahan1970.theorem6_1_complex
#check @TauCeti.DavisKahan1970.theorem6_1_real
#check @TauCeti.DavisKahan1970.theorem6_1_real_commonDomain
#check @TauCeti.DavisKahan1970.theorem6_1_real_commonCore

/-! ## DK-6.2-thm: Pairwise-gap square-norm sine theorem

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.theorem6_2_complex
#check @TauCeti.DavisKahan1970.theorem6_2_real
#check @TauCeti.DavisKahan1970.theorem6_2_complex
#check @TauCeti.DavisKahan1970.theorem6_2_real

/-! ## DK-6.3-thm: Tangent proof machinery, Example 6.1, and generalized tangent theorem

Status: **TERMINAL EXACT**.  The canonical witnesses are the two `_exists_`
unbounded-Ritz paper-norm endpoints.  They ask the caller for nothing the printed
theorem does not: an unbounded Ritz pair, an arbitrary reducing complement, the two
ordered form bounds, and a bounded residual.  From those they *derive* the pole
exclusion (no principal angle is right), *construct* a representative with the
paper's approximation numbers `tan θⱼ`, and bound it in every source norm.

The parameterized `_unboundedRitz_` pair below is the same estimate with the
representative and its characterisation supplied by the caller; it is the
implementation the `_exists_` form composes, and remains registered as
correspondence evidence.  The `_unboundedTrial_` pair adds a spectral-gap
hypothesis the printed theorem does not have -- it assumes the perturbed operator
has no spectrum in `(α, α + δ)`, equivalently that the reducing subspace *is* the
spectral subspace below `α` -- and is a specialization, not a witness.
-/

#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_exists_complex
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_exists_real
#check @TauCeti.DavisKahan1970.approximationSingularValue_directedSineBlock_lt_one_unboundedRitz_complex
#check @TauCeti.DavisKahan1970.approximationSingularValue_directedSineBlock_lt_one_unboundedRitz_real
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_real
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedTrial_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTheta_directed_unboundedTrial_symmetricNorming_real
#check @TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal
#check @TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists
#check @TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real
#check @TauCeti.DavisKahan1970.tanTheta_directed_bounded_spectralGap_symmetricNorming_complex
#check @TauCeti.DavisKahan1970.tanTheta_directed_bounded_spectralGap_symmetricNorming_real

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
#check @TauCeti.DavisKahan.maximalAngle_le_pi_div_four_of_orderedFormGap_unbounded
#check @TauCeti.DavisKahan.maximalAngle_le_pi_div_four_of_orderedFormGap_unbounded_printed
#check @TauCeti.DavisKahan.reflectionProduct_form_nonneg_of_orderedFormGap_unbounded
#check @TauCeti.DavisKahan.subspaceGap_le_of_orderedFormGap_unbounded
#check @TauCeti.DavisKahan.subspaceGap_le_of_orderedFormGap_unbounded_printed
#check @TauCeti.DavisKahan1970.Section8.canonicalLowBranchUnbounded
#check @TauCeti.DavisKahan1970.Section8.canonicalLowBranchUnbounded_reduces
#check @TauCeti.DavisKahan1970.Section8.canonicalLowBranchUnbounded_orthogonal
#check @TauCeti.DavisKahan1970.Section8.re_inner_le_of_mem_canonicalLowBranchUnbounded
#check @TauCeti.DavisKahan1970.Section8.le_re_inner_of_mem_canonicalLowBranchUnbounded_orthogonal
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranchUnbounded_form
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranchUnbounded_printed
#check @TauCeti.DavisKahan.re_inner_le_of_realSpectrum_subset_Iic
#check @TauCeti.DavisKahan.le_re_inner_of_realSpectrum_subset_Ici
#check @TauCeti.DavisKahan.re_inner_le_of_reducingRestriction_realSpectrum_subset_Iic
#check @TauCeti.DavisKahan.le_re_inner_of_reducingRestriction_realSpectrum_subset_Ici
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_of_spectrumIn_unbounded
#check @TauCeti.LinearPMap.specProjection_eq_specProjC
#check @TauCeti.LinearPMap.specProjection_apply_of_unitary_intertwines
#check @TauCeti.DavisKahan.reflectionProduct_form_pos_of_orderedFormGap_unbounded
#check @TauCeti.DavisKahan.norm_starProjection_sub_sq_lt_of_reflectionProduct_form_pos
#check @TauCeti.DavisKahan.norm_starProjection_sub_sq_lt_of_orderedFormGap_unbounded
#check @TauCeti.DavisKahan.norm_starProjection_sub_sq_lt_of_orderedFormGap_unbounded_printed
#check @TauCeti.DavisKahan1970.Section8.starProjection_specProjection_comm_of_reduces
#check @TauCeti.DavisKahan1970.Section8.eq_of_starProjection_comm_of_crossed_trivial
#check @TauCeti.DavisKahan1970.Section8.norm_starProjection_lt_of_mem_orthogonal_of_sq_lt
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_eq_canonicalBranchUnbounded_of_maximalAngle_le
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_orderedFormGap_unbounded
#check @TauCeti.DavisKahan1970.Section8.re_inner_le_of_complexifyReal_le
#check @TauCeti.DavisKahan1970.Section8.le_re_inner_of_le_complexifyReal
#check @TauCeti.DavisKahan1970.Section8.maximalAngle_complexifySubmodule
#check @TauCeti.DavisKahan1970.Section8.canonicalLowBranchUnboundedReal
#check @TauCeti.DavisKahan1970.Section8.canonicalLowBranchUnboundedReal_reduces
#check @TauCeti.DavisKahan1970.Section8.complexifySubmodule_canonicalLowBranchUnboundedReal
#check @TauCeti.DavisKahan1970.Section8.canonicalLowBranchUnbounded_congr
#check @TauCeti.DavisKahan1970.Section8.re_inner_le_of_complexifyReal_le_of_eq
#check @TauCeti.DavisKahan1970.Section8.le_re_inner_of_le_complexifyReal_of_eq
#check @TauCeti.DavisKahan1970.Section8.maximalAngle_le_of_complexifySubmodule_le
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranchUnbounded_printed_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_orderedFormGap_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_eq_canonicalBranchUnbounded_of_maximalAngle_le_real
#check @TauCeti.DavisKahan1970.Section8.re_inner_split_of_reduces_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.semiboundedAbove_reducingRestriction_iff
#check @TauCeti.DavisKahan1970.Section8.semiboundedBelow_reducingRestriction_iff
#check @TauCeti.DavisKahan1970.Section8.semiboundedAbove_reducingRestriction_real_iff
#check @TauCeti.DavisKahan1970.Section8.semiboundedBelow_reducingRestriction_real_iff
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_blockPlacement_unbounded_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_blockPlacement_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_exists_branch_blockPlacement_unbounded_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_exists_branch_blockPlacement_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_sourceExact_unbounded_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_sourceExact_unbounded_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_sourceExact_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_sourceExact_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_ofBlockPlacement_unbounded_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_ofBlockPlacement_unbounded_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_ofBlockPlacement_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_ofBlockPlacement_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperEigenvalueRepulsion_sourceExact
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerEigenvalueRepulsion_sourceExact
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperEigenvalueRepulsion_sourceExact_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerEigenvalueRepulsion_sourceExact_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeEigenvalue_sourceExact
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeEigenvalue_sourceExact
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeEigenvalue_sourceExact_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeEigenvalue_sourceExact_real
#check @TauCeti.DavisKahan1970.Section8.re_inner_split_of_reduces
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_unbounded
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_unbounded
#check @TauCeti.DavisKahan.subspaceGap_le_of_reflectionProduct_form_nonneg
#check @TauCeti.DavisKahan.maximalAngle_le_pi_div_four_of_reflectionProduct_form_nonneg
#check @TauCeti.DavisKahan.reflectionProduct_add_swap_eq
#check @TauCeti.ContinuousLinearMap.nonneg_of_lyapunov_nonneg
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_real
#check @TauCeti.DavisKahan1970.Section8.approximationNumber_eq_eigenvalues_of_isPositive
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_real

/-! ## DK-8.2-thm: Smallness selects the acute branch

Status: **TERMINAL EXACT**.
-/

#check @TauCeti.DavisKahan1970.Section8.theorem8_2_branch_directed_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_symmetricNorming
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_symmetricNorming
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_directedAngle_symmetricNorming
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_directedAngle_real_symmetricNorming
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_branch_directed_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_real_symmetricNorming
#check @TauCeti.DavisKahan1970.Section8.directedGap_le_of_reducingGap_unbounded_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_branch_maximalAngle_lt_unbounded_smallPerturbation_complex
#check @TauCeti.DavisKahan.CrossedDefectsEquivalent.symm
#check @TauCeti.DavisKahan.notMem_spectrum_addBounded_of_spectrum_gap
#check @TauCeti.DavisKahan.spectrum_addBounded_subset_of_gap
#check @TauCeti.DavisKahan.realSpectrum_addBounded_subset_of_gap
#check @TauCeti.DavisKahan.specRange_bandExterior_eq_orthogonal
#check @TauCeti.DavisKahan.formBoundedSylvesterGap_band_exterior
#check @TauCeti.DavisKahan.subspaceGap_bandSubspace_le
#check @TauCeti.DavisKahan.abs_directedGap_sub_directedGap_le
#check @TauCeti.DavisKahan.le_of_band_exterior_spectra
#check @TauCeti.DavisKahan.realSpectrum_subset_union_of_reduces
#check @TauCeti.DavisKahan.reducesSubspace_of_isSelfAdjoint_of_invariant
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_unbounded_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_maximalAngle_lt_unbounded_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_residualHalfGap_unbounded_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_residualHalfGap_maximalAngle_lt_unbounded_complex
#check @TauCeti.DavisKahan.Foundation.RealComplexification.unitaryConj_complexifyReal_reducingRestriction
#check @TauCeti.DavisKahan.Foundation.RealComplexification.realSpectrum_reducingRestriction_complexifyReal
#check @TauCeti.DavisKahan.Foundation.RealComplexification.realSpectrum_reducingRestriction_complexifyReal_of_eq
#check @TauCeti.DavisKahan.Foundation.RealComplexification.norm_complexify_comp_subtypeL
#check @TauCeti.DavisKahan.Foundation.RealComplexification.separableSpace_realComplexification
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_residualHalfGap_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_maximalAngle_lt_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_residualHalfGap_maximalAngle_lt_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_branch_maximalAngle_lt_unbounded_source_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_branch_maximalAngle_lt_unbounded_source_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_perturbation_sourceExact_unbounded_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_perturbation_sourceExact_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_residual_sourceExact_unbounded_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_residual_sourceExact_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.sourceResidual
#check @TauCeti.DavisKahan1970.Section8.sourceResidual_eq_sub_ritzBlock
#check @TauCeti.DavisKahan1970.Section8.exists_ritzBlock_of_realSpectrum_subset_Icc_complex
#check @TauCeti.DavisKahan1970.Section8.exists_ritzBlock_of_realSpectrum_subset_Icc_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_real_symmetricNorming
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_branch_maximalAngle_lt_of_crossedDefects
#check @TauCeti.DavisKahan1970.Section8.theorem8_2_branch_real_maximalAngle_lt_of_crossedDefects
#check @TauCeti.DavisKahan1970.isTrialResidual_iff
#check @TauCeti.DavisKahan1970.isExactSpectralDecomposition_iff

/-! ## 2026-09-06 source-surface façades and the separability sweep -/

#check @TauCeti.DavisKahan1970.proposition3_1_separable
#check @TauCeti.DavisKahan1970.proposition3_2_exists_iff_crossedDefectsEquivalent_separable
#check @TauCeti.DavisKahan1970.proposition3_2_not_unique_separable
#check @TauCeti.DavisKahan1970.proposition3_3_complex_forward_separable
#check @TauCeti.DavisKahan1970.proposition3_3_complex_converse_separable
#check @TauCeti.DavisKahan1970.proposition3_3_real_forward_separable
#check @TauCeti.DavisKahan1970.proposition3_3_real_converse_separable
#check @TauCeti.DavisKahan1970.proposition3_4_full_complex_separable
#check @TauCeti.DavisKahan1970.proposition3_4_full_real_separable
#check @TauCeti.DavisKahan1970.corollary3_1_compact_defectBlock_sourceAngleList_classification_separable
#check @TauCeti.DavisKahan1970.proposition3_5_commutations_separable
#check @TauCeti.DavisKahan1970.proposition3_5_eigenvector_angle_separable
#check @TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_uniqueMaximal_separable
#check @TauCeti.DavisKahan1970.corollary3_2_separable
#check @TauCeti.DavisKahan1970.proposition4_2_compact_nonacute_separable
#check @TauCeti.DavisKahan1970.proposition4_2_compact_nonacute_real_separable

/-! ## 2026-09-07 fourth-hostile-review source-scope façades

Theorem 8.1's existence-with-part-(i) clause and the derived block symmetry;
Section 4 on Davis--Kahan's Definition 3.1 direct rotation; Theorem 3.1's
converse and Corollary 3.1's realization at the paper's separable scope; and
Section 6 on the printed separation, the paper's ambient scope, and the
source's definedness convention. -/

#check @TauCeti.DavisKahan1970.Section8.theorem8_1_exists_branch_withCompression_unbounded_complex
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_exists_branch_withCompression_unbounded_real
#check @TauCeti.DavisKahan1970.Section8.isSymmetric_upperBlockShift
#check @TauCeti.DavisKahan1970.Section8.isSymmetric_lowerBlockShift

#check @TauCeti.DavisKahan.IsSourceDirectRotation
#check @TauCeti.DavisKahan.IsSourceDirectRotation.add_star_eq_two_absoluteValue
#check @TauCeti.DavisKahan.norm_one_sub_apply_eq_of_isSourceDirectRotation
#check @TauCeti.DavisKahan.sq_eq_reflectionProduct
#check @TauCeti.DavisKahan1970.crossedDefectsEquivalent_of_isSourceDirectRotation

#check @TauCeti.DavisKahan1970.theorem3_1_realization_sourceExact_complex
#check @TauCeti.DavisKahan1970.theorem3_1_realization_sourceExact_real
#check @TauCeti.DavisKahan1970.corollary3_1_realization_zeroMultiplicity_sourceScope

#check @TauCeti.DavisKahan1970.lemma6_1_separable_complex
#check @TauCeti.DavisKahan1970.lemma6_1_separable_real
#check @TauCeti.DavisKahan1970.lemma6_1_converse_separable_complex
#check @TauCeti.DavisKahan1970.lemma6_1_converse_separable_real
#check @TauCeti.DavisKahan1970.lemma6_2_separable
#check @TauCeti.DavisKahan1970.proposition6_1_printedGap_sourceExact_complex
#check @TauCeti.DavisKahan1970.proposition6_1_printedGap_sourceExact_real
#check @TauCeti.DavisKahan1970.theorem6_1_printedGap_sourceExact_complex
#check @TauCeti.DavisKahan1970.theorem6_1_printedGap_sourceExact_real
#check @TauCeti.DavisKahan1970.theorem6_2_vacuity_sourceExact_complex
#check @TauCeti.DavisKahan1970.theorem6_2_vacuity_sourceExact_real
#check @TauCeti.DavisKahan1970.lemma6_3_leakage_separable_complex
#check @TauCeti.DavisKahan1970.lemma6_3_leakage_separable_real

#check @TauCeti.DavisKahan.ExactSinTheta.NormalizedSymmetricOperatorIdealFamily
#check @TauCeti.DavisKahan.ExactSinTheta.NormalizedSymmetricOperatorIdealFamily.HasFanDominance
#check @TauCeti.DavisKahan.ExactSinTheta.NormalizedSymmetricOperatorIdealFamily.HasFanDominanceWhereDefined
#check @TauCeti.DavisKahan.ExactSinTheta.NormalizedSymmetricOperatorIdealFamily.ScaledGaugeLEWhereDefined
#check @TauCeti.DavisKahan.ExactSinTheta.NormalizedSymmetricOperatorIdealFamily.withFanDominance
#check @TauCeti.DavisKahan.ExactSinTheta.NormalizedUnitaryInvariantNorm.toNormalizedSymmetricOperatorIdealFamily_withFanDominance

/-! ## 2026-09-07 fifth-hostile-review repairs

Lemma 6.1 on the source's own two operators; Theorem 8.1's existence clause and
part (i) as one printed sentence; and parts (ii) and (iii) on the blocks
themselves, with the symmetric gauge at the block dimension. -/

#check @TauCeti.DavisKahan1970.lemma6_1_sourceOperators_separable_complex
#check @TauCeti.DavisKahan1970.lemma6_1_sourceOperators_separable_real
#check @TauCeti.DavisKahan1970.lemma6_1_converse_sourceOperators_separable_complex
#check @TauCeti.DavisKahan1970.lemma6_1_converse_sourceOperators_separable_real

#check @TauCeti.DavisKahan1970.Section8.upperBlockCompression
#check @TauCeti.DavisKahan1970.Section8.lowerBlockCompression
#check @TauCeti.DavisKahan1970.Section8.approximationNumber_upperBlockCompression
#check @TauCeti.DavisKahan1970.Section8.approximationNumber_lowerBlockCompression
#check @TauCeti.DavisKahan1970.Section8.finrank_eq_of_isAcute
#check @TauCeti.DavisKahan1970.Section8.finrank_orthogonal_eq_of_isAcute
#check @TauCeti.DavisKahan1970.Section8.weaklyMajorized_comp_castLE
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_finrank_orthogonal_branch_eq
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_finrank_branch_eq
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_finrank_orthogonal_branch_eq_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_finrank_branch_eq_real

#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperEigenvalueRepulsion_blockSourceExact
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerEigenvalueRepulsion_blockSourceExact
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperEigenvalueRepulsion_blockSourceExact_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerEigenvalueRepulsion_blockSourceExact_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeEigenvalue_blockSourceExact
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeEigenvalue_blockSourceExact
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeEigenvalue_blockSourceExact_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeEigenvalue_blockSourceExact_real

/-! ## An approximation-number extension of Theorem 8.1 (ii)

Part (ii) is printed with "natural infinite-dimensional extensions"; part (iii)
is not.  The phrase does not identify a unique formal proposition -- Section 1
offers both the minimax sequence and spectral-multiplicity language and does not
choose -- so these are registered as generalizations, not as source evidence for
the phrase. -/

#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_blockExtension
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_blockExtension
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_blockExtension_real
#check @TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_blockExtension_real
