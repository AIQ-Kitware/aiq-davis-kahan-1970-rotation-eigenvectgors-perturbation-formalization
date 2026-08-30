/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Geometry.Angle.PaperTanAngle
import DavisKahan.Geometry.Angle.PaperDoubleAngle
import DavisKahan.SpectralTheory.Complexification.FormTransport

/-!
# The paper's operator angle between two **real** subspaces

Standing assumption 1 of Davis--Kahan 1970 is that the Hilbert space is "real or
complex".  The paper's angle `Θ = arcsin |P_U - P_V|` and its trigonometric
functions are built here over `ℂ`, because Mathlib registers the continuous
functional calculus on Hilbert-space operators only over `ℂ`.  That is a
*representation* restriction, not a mathematical one, and this module removes it.

`DavisKahan/Geometry/Angle/OperatorAngleReal.lean` already evaluates the complex
calculus at the complexification of a real pair; its operators, however, act on
`RealComplexification E`, so a statement about them is not literally a statement
about `E`.  This module supplies the missing descent, which its module docstring
anticipated: every one of these operators is a continuous functional calculus of
`|P_U - P_V|`, hence lies in the fixed-point algebra of the canonical
conjugation, hence **is** the complexification of a bounded operator on `E`.

## What makes this honest

The real objects are not defined by a formula that happens to complexify
correctly; they are defined as the real restrictions, and the identity

  `complexify (paperTanAngleOperatorR U V) = paperTanAngleOperatorC (Uᶜ) (Vᶜ)`

is proved.  Their real content is then pinned down without reference to the
complexification:

* `paperSinAngleOperatorR_mul_self`: `sin Θ · sin Θ = (P_U - P_V)²`;
* `paperSinAngleOperatorR_nonneg` and `isSelfAdjoint_paperSinAngleOperatorR`:
  together with the previous item this *characterises* `sin Θ` as the
  nonnegative square root, i.e. as `|P_U - P_V|` in the real sense;
* `norm_paperSinAngleOperatorR`: `‖sin Θ‖` is the real subspace gap.

## Main definitions

* `TauCeti.DavisKahanExt.paperSinAngleOperatorR`, `paperAngleOperatorR`,
  `paperSinTwoAngleOperatorR`, `paperTanAngleOperatorR`,
  `paperTanTwoAngleOperatorR`: the five paper angle operators of a real pair, as
  bounded operators on the real space.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: standing assumption 1, and the
  angle operators of Sections 1 and 2.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

variable (U V : Submodule ℝ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-! ### The complexified angle operators are conjugation-fixed -/

/-- The sine-angle operator of a complexified pair is fixed by the canonical
conjugation: it is the modulus of a complexified operator. -/
theorem conjugateOperator_sinAngleOperatorC_complexifySubmodule :
    conjugateOperator
        (sinAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)) =
      sinAngleOperatorC (complexifySubmodule U) (complexifySubmodule V) := by
  rw [sinAngleOperatorC, starProjection_complexifySubmodule,
    starProjection_complexifySubmodule, ← complexify_sub]
  exact conjugateOperator_modulus_of_fixed (conjugateOperator_complexify _)

/-- The operator angle of a complexified pair is conjugation-fixed. -/
theorem conjugateOperator_paperAngleOperatorC_complexifySubmodule :
    conjugateOperator
        (paperAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)) =
      paperAngleOperatorC (complexifySubmodule U) (complexifySubmodule V) :=
  conjugateOperator_cfc _ (isSelfAdjoint_sinAngleOperatorC _ _)
    (conjugateOperator_sinAngleOperatorC_complexifySubmodule U V) Real.arcsin

/-- **Every** continuous functional calculus of the complexified operator angle
is conjugation-fixed.  This is the single fact that makes all five real angle
operators below descend, with no per-symbol argument. -/
theorem conjugateOperator_cfc_paperAngleOperatorC_complexifySubmodule
    (f : ℝ → ℝ) :
    conjugateOperator
        (cfc f (paperAngleOperatorC (complexifySubmodule U)
          (complexifySubmodule V))) =
      cfc f (paperAngleOperatorC (complexifySubmodule U)
        (complexifySubmodule V)) :=
  conjugateOperator_cfc _ (isSelfAdjoint_paperAngleOperatorC _ _)
    (conjugateOperator_paperAngleOperatorC_complexifySubmodule U V) f

/-! ### The real angle operators -/

/-- The paper's `sin Θ` for a pair of **real** closed subspaces: a bounded
operator on the real space. -/
def paperSinAngleOperatorR : E →L[ℝ] E :=
  realPartOperator
    (sinAngleOperatorC (complexifySubmodule U) (complexifySubmodule V))

/-- The paper's Hermitian operator angle `Θ = arcsin |P_U - P_V|` for a pair of
**real** closed subspaces. -/
def paperAngleOperatorR : E →L[ℝ] E :=
  realPartOperator
    (paperAngleOperatorC (complexifySubmodule U) (complexifySubmodule V))

/-- The paper's ambient `sin 2Θ` for a pair of **real** closed subspaces. -/
def paperSinTwoAngleOperatorR : E →L[ℝ] E :=
  realPartOperator
    (paperSinTwoAngleOperatorC (complexifySubmodule U) (complexifySubmodule V))

/-- The paper's ambient `tan Θ` for a pair of **real** closed subspaces. -/
def paperTanAngleOperatorR : E →L[ℝ] E :=
  realPartOperator
    (paperTanAngleOperatorC (complexifySubmodule U) (complexifySubmodule V))

/-- The paper's ambient `tan 2Θ` for a pair of **real** closed subspaces. -/
def paperTanTwoAngleOperatorR : E →L[ℝ] E :=
  realPartOperator
    (paperTanTwoAngleOperatorC (complexifySubmodule U) (complexifySubmodule V))

/-- The paper's branch-free ambient `|tan 2Θ|` for a pair of **real** closed
subspaces.

The real counterpart of `paperAbsTanTwoAngleOperatorC`, and the object the real
double-angle tangent theorem concludes on: a unitarily invariant norm sees a
self-adjoint operator through its singular values, so it cannot tell `tan 2Θ`
from `|tan 2Θ|`, and only the latter is defined without a quarter-acute branch
hypothesis. -/
def paperAbsTanTwoAngleOperatorR : E →L[ℝ] E :=
  realPartOperator
    (paperAbsTanTwoAngleOperatorC (complexifySubmodule U) (complexifySubmodule V))

/-! ### The descent identities -/

/-- Complexifying the real sine-angle operator recovers the complex one. -/
@[simp]
theorem complexify_paperSinAngleOperatorR :
    complexify (paperSinAngleOperatorR U V) =
      sinAngleOperatorC (complexifySubmodule U) (complexifySubmodule V) :=
  complexify_realPartOperator
    (conjugateOperator_sinAngleOperatorC_complexifySubmodule U V)

/-- Complexifying the real operator angle recovers the complex one. -/
@[simp]
theorem complexify_paperAngleOperatorR :
    complexify (paperAngleOperatorR U V) =
      paperAngleOperatorC (complexifySubmodule U) (complexifySubmodule V) :=
  complexify_realPartOperator
    (conjugateOperator_paperAngleOperatorC_complexifySubmodule U V)

/-- Complexifying the real `sin 2Θ` recovers the complex one. -/
@[simp]
theorem complexify_paperSinTwoAngleOperatorR :
    complexify (paperSinTwoAngleOperatorR U V) =
      paperSinTwoAngleOperatorC (complexifySubmodule U) (complexifySubmodule V) :=
  complexify_realPartOperator
    (conjugateOperator_cfc_paperAngleOperatorC_complexifySubmodule U V _)

/-- Complexifying the real `tan Θ` recovers the complex one. -/
@[simp]
theorem complexify_paperTanAngleOperatorR :
    complexify (paperTanAngleOperatorR U V) =
      paperTanAngleOperatorC (complexifySubmodule U) (complexifySubmodule V) :=
  complexify_realPartOperator
    (conjugateOperator_cfc_paperAngleOperatorC_complexifySubmodule U V _)

/-- Complexifying the real `tan 2Θ` recovers the complex one. -/
@[simp]
theorem complexify_paperTanTwoAngleOperatorR :
    complexify (paperTanTwoAngleOperatorR U V) =
      paperTanTwoAngleOperatorC (complexifySubmodule U) (complexifySubmodule V) :=
  complexify_realPartOperator
    (conjugateOperator_cfc_paperAngleOperatorC_complexifySubmodule U V _)

/-- Complexifying the real `|tan 2Θ|` recovers the complex one. -/
@[simp]
theorem complexify_paperAbsTanTwoAngleOperatorR :
    complexify (paperAbsTanTwoAngleOperatorR U V) =
      paperAbsTanTwoAngleOperatorC (complexifySubmodule U) (complexifySubmodule V) :=
  complexify_realPartOperator
    (conjugateOperator_cfc_paperAngleOperatorC_complexifySubmodule U V _)

/-! ### Real content of the real sine-angle operator

The three results below hold in `E` and never mention the complexification.
Together they say `paperSinAngleOperatorR U V` is *the* nonnegative square root
of `(P_U - P_V)²`, which is the paper's `sin Θ = |P_U - P_V|`. -/

/-- A conjugation-fixed self-adjoint complex operator restricts to a
self-adjoint real operator; applied to the real angle operators. -/
private theorem isSelfAdjoint_realPartOperator_of_fixed
    {A : RealComplexification E →L[ℂ] RealComplexification E}
    (hfix : conjugateOperator A = A) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (realPartOperator A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  apply complexify_injective
  rw [complexify_adjoint, complexify_realPartOperator hfix, hA.adjoint_eq]

/-- The real sine-angle operator is self-adjoint. -/
theorem isSelfAdjoint_paperSinAngleOperatorR :
    IsSelfAdjoint (paperSinAngleOperatorR U V) :=
  isSelfAdjoint_realPartOperator_of_fixed
    (conjugateOperator_sinAngleOperatorC_complexifySubmodule U V)
    (isSelfAdjoint_sinAngleOperatorC _ _)

/-- The real operator angle is self-adjoint. -/
theorem isSelfAdjoint_paperAngleOperatorR :
    IsSelfAdjoint (paperAngleOperatorR U V) :=
  isSelfAdjoint_realPartOperator_of_fixed
    (conjugateOperator_paperAngleOperatorC_complexifySubmodule U V)
    (isSelfAdjoint_paperAngleOperatorC _ _)

/-- The real ambient `sin 2Θ` is self-adjoint. -/
theorem isSelfAdjoint_paperSinTwoAngleOperatorR :
    IsSelfAdjoint (paperSinTwoAngleOperatorR U V) :=
  isSelfAdjoint_realPartOperator_of_fixed
    (conjugateOperator_cfc_paperAngleOperatorC_complexifySubmodule U V _)
    (isSelfAdjoint_paperSinTwoAngleOperatorC _ _)

/-- The real ambient `tan Θ` is self-adjoint. -/
theorem isSelfAdjoint_paperTanAngleOperatorR :
    IsSelfAdjoint (paperTanAngleOperatorR U V) :=
  isSelfAdjoint_realPartOperator_of_fixed
    (conjugateOperator_cfc_paperAngleOperatorC_complexifySubmodule U V _)
    (isSelfAdjoint_paperTanAngleOperatorC _ _)

/-- The real ambient `tan 2Θ` is self-adjoint. -/
theorem isSelfAdjoint_paperTanTwoAngleOperatorR :
    IsSelfAdjoint (paperTanTwoAngleOperatorR U V) :=
  isSelfAdjoint_realPartOperator_of_fixed
    (conjugateOperator_cfc_paperAngleOperatorC_complexifySubmodule U V _)
    (isSelfAdjoint_paperTanTwoAngleOperatorC _ _)

/-- **The real sine-angle operator squares to the squared projection
difference**, entirely inside `E`. -/
theorem paperSinAngleOperatorR_mul_self :
    paperSinAngleOperatorR U V ∘L paperSinAngleOperatorR U V =
      (U.starProjection - V.starProjection) ∘L
        (U.starProjection - V.starProjection) := by
  apply complexify_injective
  rw [complexify_comp, complexify_comp, complexify_paperSinAngleOperatorR,
    complexify_sub, ← starProjection_complexifySubmodule U,
    ← starProjection_complexifySubmodule V]
  have hsa : IsSelfAdjoint ((complexifySubmodule U).starProjection -
      (complexifySubmodule V).starProjection) :=
    (isSelfAdjoint_starProjection _).sub (isSelfAdjoint_starProjection _)
  have h := ContinuousLinearMap.modulus_mul_self
    ((complexifySubmodule U).starProjection -
      (complexifySubmodule V).starProjection)
  rw [hsa.adjoint_eq] at h
  exact h

/-- **The real sine-angle operator is nonnegative.**  With
`paperSinAngleOperatorR_mul_self` this identifies it as the real
`|P_U - P_V|`. -/
theorem paperSinAngleOperatorR_nonneg :
    0 ≤ paperSinAngleOperatorR U V := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
    (isSelfAdjoint_paperSinAngleOperatorR U V), fun x => ?_⟩
  have hpos : (0 : ℝ) ≤ RCLike.re
      ⟪complexify (paperSinAngleOperatorR U V) (ofReal x), ofReal x⟫_ℂ := by
    rw [complexify_paperSinAngleOperatorR]
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).1
      (sinAngleOperatorC_nonneg _ _)).2 _
  have hval : RCLike.re
      ⟪complexify (paperSinAngleOperatorR U V) (ofReal x), ofReal x⟫_ℂ =
      ⟪paperSinAngleOperatorR U V x, x⟫_ℝ + ⟪paperSinAngleOperatorR U V 0, 0⟫_ℝ :=
    re_inner_complexify _ _
  simp only [map_zero, inner_zero_left, add_zero] at hval
  simpa [ContinuousLinearMap.reApplyInnerSelf_apply, hval] using hval ▸ hpos

/-- **The norm of the real sine-angle operator is the real subspace gap**,
`‖sin Θ‖ = ‖P_U - P_V‖`. -/
theorem norm_paperSinAngleOperatorR :
    ‖paperSinAngleOperatorR U V‖ = DavisKahan.subspaceGap U V := by
  rw [← norm_complexify, complexify_paperSinAngleOperatorR,
    norm_sinAngleOperatorC]
  exact subspaceGap_complexifySubmodule U V

end

end DavisKahanExt
end TauCeti
