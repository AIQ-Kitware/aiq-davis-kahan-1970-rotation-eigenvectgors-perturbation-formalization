/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
import ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks

/-!
# The bounded Davis--Kahan vocabulary

The paper library's names for the bounded operator geometry it uses: `projection`
for an orthogonal projector, `Reduces` for a reducing subspace, `subspaceGap` for
the projection gap, and so on.  **Every declaration here is a forwarding name.**
Nothing is proved in this file; each line points at the general statement in
`ForTauCeti`, in Mathlib, or in one of `ForTauCeti`'s own generic modules.

## Why this file exists, and why it is here rather than in `ForTauCeti`

It was `ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/Basic.lean` until
2026-07-30, when lane `RUB-NS-PAPER` measured what that module contained: all
twenty-one of its declarations were one-line forwards, and they opened the
namespace `TauCeti.DavisKahan` — a paper's name — inside the *generic* library.

Both halves of that are wrong for `ForTauCeti`, and they are wrong in opposite
directions, which is why the fix is a move and not a rename:

* A compatibility alias is not generic mathematics.  `ForTauCeti` is staged for
  Tau Ceti, and Tau Ceti has no use for a second spelling of `starProjection`.
* The mathematics the aliases pointed at **is** generic, and it stayed behind: it
  now lives in `Submodule` and `ContinuousLinearMap`, next to the objects it is
  about.

So the vocabulary comes back to the paper library that wanted it, keeping its
namespace and every name, and the two real theorems of the former
`BoundedOperator/{Projector,SinTheta}.lean` — the dimension-free directed `sin Θ`
bound and the sharp factor-one projector bound — stay in `ForTauCeti` under
`Submodule` and are re-exported below.  No consumer in `DavisKahan/**` changes.

**Do not add mathematics to this file.**  A new bounded-operator result belongs
in `ForTauCeti` under the namespace of the object it is about; if the paper
library wants a shorter name for it, add one `export` line here.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/BoundedOperator/Basic.lean`, moved into
  `ForTauCeti` by lane Y3(b3) on 2026-07-29 and returned here by lane
  `RUB-NS-PAPER` on 2026-07-30.
* Extraction class: **not for extraction** — this is paper-library vocabulary.
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-! ### Names that differ from the canonical one -/

/-- Compatibility-friendly name for symmetry of a bounded operator. -/
abbrev IsSelfAdjointOperator (A : E →L[𝕜] E) : Prop := A.IsSymmetric

/-- Orthogonal projection onto a subspace. -/
noncomputable abbrev projection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →L[𝕜] E := U.starProjection

/-- Orthogonal projection onto the orthogonal complement. -/
noncomputable abbrev complementaryProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →L[𝕜] E := Uᗮ.starProjection

/-- Symmetric projection gap. -/
noncomputable abbrev subspaceGap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  U.projectionGap V

/-- Directed projection gap. -/
noncomputable abbrev directedGap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  U.directedProjectionGap V

/-- **The quantitative acute case: the projection gap is strictly below one.**

This is *not* Davis--Kahan's printed Definition 3.2, and it used to be called
`IsAcute`, which said it was.  The printed definition — both crossed
intersections `U ⊓ Vᗮ` and `Uᗮ ⊓ V` vanish — is `TauCeti.IsAcute`, in
`ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean`.

The two agree in finite dimension (`TauCeti.isAcute_iff_projectionGap_lt_one`)
and only there: `‖P_U - P_V‖ < 1` is uniform, so it also excludes principal
angles that merely accumulate at `π/2`, and `TauCeti.isAcute_of_projectionGap_lt_one`
is the one implication that survives in general.  Hence the qualifier: a
statement carrying this hypothesis is narrower than the printed one whenever the
ambient space is infinite dimensional. -/
def IsUniformlyAcute (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  subspaceGap U V < 1

/-- The projection gap lies below the quarter-angle threshold. -/
def IsQuarterAcute (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  subspaceGap U V < Real.sqrt 2 / 2

/-- An isometric bounded embedding. -/
def IsometricEmbedding (X : F →L[𝕜] E) : Prop := ∀ x, ‖X x‖ = ‖x‖

/-- Residual of an approximate invariant pair. -/
def residual (A : E →L[𝕜] E) (X : F →L[𝕜] E)
    (M : F →L[𝕜] F) : F →L[𝕜] E := A ∘L X - X ∘L M

/-- Directed sine block for an approximate subspace embedding. -/
noncomputable def sinThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →L[𝕜] E) : F →L[𝕜] E :=
  Uᗮ.starProjection ∘L X

/-- A symmetric invariant subspace is reducing. -/
theorem reduces_orthogonalComplement {A : E →L[𝕜] E}
    (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    (hU : ∀ x ∈ U, A x ∈ U) : A.Reduces U :=
  ContinuousLinearMap.IsSymmetric.reduces_of_invariant hA hU

/-- Projection commutation for a reducing subspace. -/
theorem projection_comp_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : A.Reduces U) :
    projection U ∘L A = A ∘L projection U :=
  ContinuousLinearMap.starProjection_comp_comm_of_reduces A U hU

/-- Pointwise projection commutation for a reducing subspace. -/
theorem projection_apply_comm_of_isInvariant
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : A.Reduces U) (x : E) :
    projection U (A x) = A (projection U x) :=
  ContinuousLinearMap.starProjection_apply_comm_of_reduces A U hU x

/-- Constant-one separated-form Sylvester estimate. -/
theorem norm_sylvester_le_of_coercive
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {c g : ℝ} (hg : 0 < g)
    (hAc : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hEq : ContinuousLinearMap.sylvesterOperator A B X = C) :
    ‖X‖ ≤ ‖C‖ / g :=
  TauCeti.ContinuousLinearMap.opNorm_le_div_of_comp_sub_comp_eq hA hB hg hAc hBc hEq

/-! ### Names that are already canonical

These are the same name in a different namespace, so an `export` is the whole
content.  Reaching for `TauCeti.DavisKahan.reflectionOperator` and reaching for
`Submodule.reflectionOperator` gives the same declaration. -/

export _root_.ContinuousLinearMap (Reduces)

export _root_.Submodule
  (reflectionOperator diagonalPart offDiagonalPart IsOffDiagonal
   reflectionOperator_comm_of_reduces
   reflectionOperator_involutive norm_reflectionOperator_le_one
   reflectionOperator_norm_map reflectionOperator_surjective reflectionOperator_apply
   projectionGap_comm starProjection_orthogonal_apply
   two_smul_diagonalPart_eq_add_reflectionConjugate
   two_smul_offDiagonalPart_eq_sub_reflectionConjugate
   norm_starProjection_sub_eq_max directedProjectionGap_le_projectionGap
   projectionGap_eq_max_directedProjectionGap sinTheta_directed_coercive
   sinTheta_directed_of_formBounds opNorm_starProjection_sub_le_of_coercive
   opNorm_starProjection_sub_le_of_formBounds)

export _root_.ContinuousLinearMap (norm_add_eq_max_of_block)

end DavisKahan
end TauCeti
