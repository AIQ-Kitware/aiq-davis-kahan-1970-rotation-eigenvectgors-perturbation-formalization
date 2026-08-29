/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.Complexification.Subspace
import DavisKahan.Geometry.Angle.OperatorAngleComplex

/-!
# Real operator angles through complexification

The complex operator-angle calculus is complete.  This file specializes it to real Hilbert subspaces by applying that calculus to their
canonical complexifications.  It avoids a second Halmos decomposition and
keeps every norm, gap, acuteness threshold, and projection identity tied to
the original real subspaces.

The operators in this file act on the complexified Hilbert space.  A later,
strictly smaller descent seam may show that the conjugation-invariant
operators preserve the canonical real copy and therefore bundle as real
operators.  All norm-level and projection-geometric content is already exact
here.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan
namespace Real

open scoped InnerProductSpace

noncomputable section

open TauCeti.DavisKahan.Foundation
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Symmetric sine-angle operator for real subspaces, evaluated in their
canonical complexification. -/
noncomputable def sinAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    RealComplexification E →L[ℂ] RealComplexification E :=
  sinAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)

/-- Directed sine-angle operator for real subspaces in the complexification. -/
noncomputable def sinAngleOperatorDirectedRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    RealComplexification E →L[ℂ] RealComplexification E :=
  sinAngleOperatorDirectedC (complexifySubmodule U) (complexifySubmodule V)

/-- Cosine-angle operator for real subspaces in the complexification. -/
noncomputable def cosAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    RealComplexification E →L[ℂ] RealComplexification E :=
  cosAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)

/-- Sine of twice the real operator angle in the complexification. -/
noncomputable def sinTwoAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    RealComplexification E →L[ℂ] RealComplexification E :=
  sinTwoAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)

/-- Tangent-angle operator for acute real subspaces, in the complexification. -/
noncomputable def tanAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : TauCeti.DavisKahan.IsUniformlyAcute U V) :
    RealComplexification E →L[ℂ] RealComplexification E :=
  tanAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)
    ((isUniformlyAcute_complexifySubmodule_iff U V).2 hacute)

/-- Tangent of twice the angle for quarter-acute real subspaces. -/
noncomputable def tanTwoAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : TauCeti.DavisKahan.IsQuarterAcute U V) :
    RealComplexification E →L[ℂ] RealComplexification E :=
  tanTwoAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)
    ((isQuarterAcute_complexifySubmodule_iff U V).2 hquarter)

/-- The real-subspace sine operator is positive. -/
theorem sinAngleOperatorRC_nonneg (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ sinAngleOperatorRC U V :=
  sinAngleOperatorC_nonneg _ _

/-- The real-subspace sine operator is self-adjoint. -/
theorem isSelfAdjoint_sinAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (sinAngleOperatorRC U V) :=
  isSelfAdjoint_sinAngleOperatorC _ _

/-- The operator norm of the complexified real sine angle is exactly the
original real projection gap. -/
theorem norm_sinAngleOperatorRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinAngleOperatorRC U V‖ = TauCeti.DavisKahan.subspaceGap U V := by
  rw [sinAngleOperatorRC, norm_sinAngleOperatorC]
  exact subspaceGap_complexifySubmodule U V

/-- Pointwise real-copy form of the sine-angle norm identity. -/
theorem norm_sinAngleOperatorRC_ofReal (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (x : E) :
    ‖sinAngleOperatorRC U V (ofReal x)‖ =
      ‖(U.starProjection - V.starProjection) x‖ := by
  rw [sinAngleOperatorRC, norm_sinAngleOperatorC_apply]
  rw [starProjection_complexifySubmodule,
    starProjection_complexifySubmodule, ← complexify_sub,
    complexify_ofReal, LinearIsometry.norm_map]

/-- The directed sine norm is the original real directed gap. -/
theorem norm_sinAngleOperatorDirectedRC (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinAngleOperatorDirectedRC U V‖ =
      TauCeti.DavisKahan.directedGap U V := by
  rw [sinAngleOperatorDirectedRC, norm_sinAngleOperatorDirectedC]
  exact directedGap_complexifySubmodule U V

/-- The cosine operator remains contractive for real subspaces. -/
theorem norm_cosAngleOperatorRC_le_one (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖cosAngleOperatorRC U V‖ ≤ 1 :=
  norm_cosAngleOperatorC_le_one _ _

/-- Operator Pythagoras for real subspaces, with the right side identified as
the complexification of the original real projection. -/
theorem sinAngleOperatorDirectedRC_sq_add_cosAngleOperatorRC_sq
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    sinAngleOperatorDirectedRC U V * sinAngleOperatorDirectedRC U V +
        cosAngleOperatorRC U V * cosAngleOperatorRC U V =
      complexify U.starProjection := by
  rw [sinAngleOperatorDirectedRC, cosAngleOperatorRC,
    sinAngleOperatorDirectedC_sq_add_cosAngleOperatorC_sq,
    starProjection_complexifySubmodule]

/-- The directed sine and cosine operators commute for real subspaces. -/
theorem commute_sinAngleOperatorDirectedRC_cosAngleOperatorRC
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    Commute (sinAngleOperatorDirectedRC U V) (cosAngleOperatorRC U V) :=
  commute_sinAngleOperatorDirectedC_cosAngleOperatorC _ _

/-- The complexified double-angle sine satisfies the sharp available bound in
terms of the original real directed gap. -/
theorem norm_sinTwoAngleOperatorRC_le (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinTwoAngleOperatorRC U V‖ ≤
      2 * TauCeti.DavisKahan.directedGap U V := by
  rw [sinTwoAngleOperatorRC]
  have h := norm_sinTwoAngleOperatorC_le
    (complexifySubmodule U) (complexifySubmodule V)
  change ‖sinTwoAngleOperatorC (complexifySubmodule U)
      (complexifySubmodule V)‖ ≤
    2 * TauCeti.DavisKahan.directedGap U V
  change ‖sinTwoAngleOperatorC (complexifySubmodule U)
      (complexifySubmodule V)‖ ≤
    2 * TauCeti.DavisKahan.directedGap (complexifySubmodule U)
      (complexifySubmodule V) at h
  rw [directedGap_complexifySubmodule] at h
  exact h

/-- Defining tangent identity for acute real subspaces after complexification. -/
theorem tanAngleOperatorRC_comp_cosAngleExtended
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hacute : TauCeti.DavisKahan.IsUniformlyAcute U V) :
    tanAngleOperatorRC U V hacute ∘L
        cosAngleExtendedC (complexifySubmodule U) (complexifySubmodule V) =
      sinAngleOperatorDirectedRC U V := by
  exact tanAngleOperatorC_comp_cosAngleExtendedC
    (complexifySubmodule U) (complexifySubmodule V)
    ((isUniformlyAcute_complexifySubmodule_iff U V).2 hacute)

/-- Defining double-tangent identity below the real quarter-angle threshold. -/
theorem tanTwoAngleOperatorRC_comp_cosTwoAngleExtended
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hquarter : TauCeti.DavisKahan.IsQuarterAcute U V) :
    tanTwoAngleOperatorRC U V hquarter ∘L
        cosTwoAngleExtendedC (complexifySubmodule U) (complexifySubmodule V) =
      sinTwoAngleOperatorRC U V := by
  exact tanTwoAngleOperatorC_comp_cosTwoAngleExtendedC
    (complexifySubmodule U) (complexifySubmodule V)
    ((isQuarterAcute_complexifySubmodule_iff U V).2 hquarter)

end

end Real
end DavisKahanExt
end TauCeti