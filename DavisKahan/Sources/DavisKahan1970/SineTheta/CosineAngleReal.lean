/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.CosineAngle
import DavisKahan.SpectralTheory.Complexification.Subspace

/-!
# Literal directed angle for real subspaces

For real Hilbert spaces the source angle is defined on the canonical
complexification.  This loses no geometric information: the real orthogonal
projections complexify exactly, and the complexified subspaces have the same
principal-angle data as the original real subspaces.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Literal directed real angle, represented faithfully on the canonical
complexification of the trial subspace. -/
noncomputable def paperSourceDirectedAngleR
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :=
  paperSourceDirectedAngleC (complexifySubmodule U) (complexifySubmodule V)

/-- Literal cosine of the directed real angle. -/
noncomputable def paperSourceDirectedCosR
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :=
  paperSourceDirectedCosC (complexifySubmodule U) (complexifySubmodule V)

/-- Literal sine of the directed real angle. -/
noncomputable def paperSourceDirectedSinR
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :=
  paperSourceDirectedSinC (complexifySubmodule U) (complexifySubmodule V)

/-- The paper's real directed cosine agrees with the canonical one. -/
@[simp]
theorem paperSourceDirectedCosR_eq
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSourceDirectedCosR U V =
      paperCosineModulusC (complexifySubmodule U) (complexifySubmodule V) :=
  paperSourceDirectedCosC_eq _ _

/-- The paper's real directed sine agrees with the canonical one. -/
@[simp]
theorem paperSourceDirectedSinR_eq
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSourceDirectedSinR U V =
      paperSineModulusC (complexifySubmodule U) (complexifySubmodule V) :=
  paperSourceDirectedSinC_eq_paperSineModulusC _ _

end

end ExactSinTheta
end DavisKahan
end TauCeti