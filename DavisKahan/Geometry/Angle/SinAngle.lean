/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.BoundedOperator.Compat
import DavisKahan.Geometry.Polar.OperatorAbsoluteValue

/-!
# Spectra-backed sine of the operator angle

This module gives a proof-complete complex Hilbert-space branch for the most
primitive operator-angle object needed by Davis--Kahan: the modulus of the
difference of the two orthogonal projections.

It is deliberately parallel to the independent scalar-generic construction in
`Core.OperatorAngle`.  No existing declaration is replaced, and no claim is
made yet that the two definitions agree.  The bridge nevertheless provides an
immediately usable sine operator whose norm is definitionally tied to the
existing DKPS subspace gap.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The Spectra-backed sine-angle operator, defined as the modulus of the
orthogonal-projector difference. -/
noncomputable def spectraSinAngleOperator
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : H →L[ℂ] H :=
  spectraOperatorAbsoluteValue (projection U - projection V)

/-- The bridge definition is exactly the Spectra modulus of the projector
difference. -/
@[simp]
theorem spectraSinAngleOperator_eq_absoluteValue
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraSinAngleOperator U V =
      spectraOperatorAbsoluteValue (projection U - projection V) :=
  rfl

/-- The Spectra-backed sine-angle operator is positive. -/
theorem spectraSinAngleOperator_nonneg
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ spectraSinAngleOperator U V := by
  simpa [spectraSinAngleOperator] using
    spectraOperatorAbsoluteValue_nonneg (projection U - projection V)

/-- The Spectra-backed sine-angle operator is self-adjoint. -/
theorem spectraSinAngleOperator_isSelfAdjoint
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (spectraSinAngleOperator U V) := by
  simpa [spectraSinAngleOperator] using
    spectraOperatorAbsoluteValue_isSelfAdjoint (projection U - projection V)

/-- Squaring the Spectra-backed sine-angle operator gives the positive product
of the projector difference with its adjoint. -/
theorem spectraSinAngleOperator_mul_self
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraSinAngleOperator U V * spectraSinAngleOperator U V =
      star (projection U - projection V) *
        (projection U - projection V) := by
  simpa [spectraSinAngleOperator] using
    spectraOperatorAbsoluteValue_mul_self (projection U - projection V)

/-- Pointwise norms of the sine-angle operator and projector difference agree. -/
theorem norm_spectraSinAngleOperator_apply
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (x : H) :
    ‖spectraSinAngleOperator U V x‖ =
      ‖(projection U - projection V) x‖ := by
  simp [spectraSinAngleOperator]

/-- The operator norm of the Spectra-backed sine-angle operator is exactly the
existing DKPS symmetric subspace gap. -/
theorem norm_spectraSinAngleOperator
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖spectraSinAngleOperator U V‖ = subspaceGap U V := by
  change ‖spectraOperatorAbsoluteValue
      (U.starProjection - V.starProjection)‖ =
    ‖U.starProjection - V.starProjection‖
  exact norm_spectraOperatorAbsoluteValue
    (U.starProjection - V.starProjection)

end DavisKahan
end TauCeti