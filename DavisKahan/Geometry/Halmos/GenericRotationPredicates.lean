/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Geometry.Halmos.TwoProjections
import DavisKahan.SpectralTheory.SpectralRestriction
-- supplies `compressOperator`
import DavisKahan.Sylvester.Spectrum
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic

/-!
# Grounded generic direct-rotation predicates for Davis--Kahan 1970

This module collects the fully proved Section-3 predicate declarations underlying
the generic direct-rotation analysis: the paper-style direct-rotation predicate,
the crossed-defect equivalence, and the compressions of the Halmos cosine and
sine squares to the reducing generic summand (together with their Pythagorean
identity).

These declarations were promoted out of the experimental frontier module once
they became grounded.  The namespace stack `TauCeti.DavisKahan`
is retained verbatim so that the fully-qualified names are unchanged; only the
module path has moved.  De-experimentalizing the namespace is a deliberately
deferred later pass.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan


universe u v

section UnitaryGeometry

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- A bounded operator is a paper-style direct rotation when it is unitary,
intertwines the two orthogonal projections, has nonnegative diagonal
compressions, and has skew-adjoint crossed blocks. -/
structure IsPaperDirectRotation
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (T : H →L[𝕜] H) : Prop where
  unitary_mem : T ∈ unitary (H →L[𝕜] H)
  intertwines : T * projection U = projection V * T
  source_compression_nonnegative :
    ∀ x : H, 0 ≤ RCLike.re
      ⟪x, (projection U * T * projection U) x⟫_𝕜
  complement_compression_nonnegative :
    ∀ x : H, 0 ≤ RCLike.re
      ⟪x, (complementaryProjection U * T * complementaryProjection U) x⟫_𝕜
  crossed_blocks :
    complementaryProjection U * T * projection U =
      -star (projection U * T * complementaryProjection U)

/-- The source and target crossed intersections admit a unitary
identification.  This is the constructive form of equality of their Hilbert
space dimensions. -/
def CrossedDefectsEquivalent
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] : Prop :=
  Nonempty
    (halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V)

/-- Restriction of the Halmos cosine square to the reducing generic summand,
realized as the compression to the generic part.  The generic part reduces
both projections, hence every word in them, so the compression is the honest
restriction. -/
noncomputable def genericHalmosCosineSq
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosGenericPart U V →L[𝕜] halmosGenericPart U V :=
  DavisKahanExt.compressOperator (halmosGenericPart U V) (halmosCosineSq U V)

/-- Restriction of the Halmos sine square to the reducing generic summand. -/
noncomputable def genericHalmosSineSq
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosGenericPart U V →L[𝕜] halmosGenericPart U V :=
  DavisKahanExt.compressOperator (halmosGenericPart U V) (halmosSineSq U V)

/-- The restricted generic cosine and sine squares retain the Pythagorean
identity. -/
theorem genericHalmosCosineSq_add_sineSq
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    genericHalmosCosineSq U V + genericHalmosSineSq U V = 1 := by
  ext x
  have hsum : halmosCosineSq U V (x : H) + halmosSineSq U V (x : H) =
      (x : H) := by
    have h := congrArg
      (fun T : H →L[𝕜] H => T (x : H)) (halmosCosineSq_add_sineSq U V)
    simpa using h
  simp only [add_apply, one_apply_eq_self,
    genericHalmosCosineSq, genericHalmosSineSq, DavisKahanExt.compressOperator,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  simp only [Submodule.coe_add, Submodule.coe_orthogonalProjectionOnto_apply]
  rw [← map_add, hsum, Submodule.starProjection_eq_self_iff.mpr x.2]

end UnitaryGeometry

end DavisKahan
end TauCeti