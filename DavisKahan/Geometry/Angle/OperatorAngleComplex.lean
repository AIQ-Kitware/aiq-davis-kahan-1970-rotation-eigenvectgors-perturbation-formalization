/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import ForTauCeti.Analysis.InnerProductSpace.OperatorModulus
import DavisKahan.BoundedOperator.Compat

/-!
# The complex operator angle calculus: honest first rungs

The scalar-generic ladder in `Core/OperatorAngle.lean` is blocked on an
`RCLike`-generic positive operator square root.  Per the route decision
recorded in `docs/planning/davis-kahan-full-paper-goal.md`, this module
specializes to `ℂ`, where the continuous-functional-calculus square root is
available (`ForMathlib/Analysis/InnerProductSpace/OperatorAbsoluteValue.lean`),
with a real-scalar bridge by complexification expected later.

* `sinAngleOperatorC U V = |P_U - P_V|`: the sine of the operator angle as
  the absolute value of the projector difference — the definition the
  generic ladder reaches only after the Halmos decomposition.
* `norm_sinAngleOperatorC`: `‖sin Θ(U, V)‖ = subspaceGap U V`, immediate
  from the absolute-value norm identity.
* `norm_sinAngleOperatorC_apply`: the pointwise identity
  `‖sin Θ(U, V) x‖ = ‖(P_U - P_V) x‖`.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Sine of the operator angle between two subspaces at complex scalars:
the absolute value of the projector difference. -/
noncomputable def sinAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  ContinuousLinearMap.modulus (U.starProjection - V.starProjection)

/-- The sine operator is nonnegative. -/
theorem sinAngleOperatorC_nonneg (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ sinAngleOperatorC U V :=
  ContinuousLinearMap.modulus_nonneg _

/-- The sine operator is self-adjoint. -/
theorem isSelfAdjoint_sinAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (sinAngleOperatorC U V) :=
  ContinuousLinearMap.modulus_isSelfAdjoint _

/-- **The norm of the sine operator is the subspace gap.** -/
theorem norm_sinAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinAngleOperatorC U V‖ = subspaceGap U V :=
  ContinuousLinearMap.norm_modulus _

/-- Pointwise identity: the sine operator is a pointwise isometry of the
projector difference. -/
theorem norm_sinAngleOperatorC_apply (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (x : E) :
    ‖sinAngleOperatorC U V x‖ =
      ‖(U.starProjection - V.starProjection) x‖ :=
  ContinuousLinearMap.norm_modulus_apply _ x

/-- Cosine of the directed operator angle at complex scalars: the absolute
value of the projection composition `P_V P_U`.  Its singular values are the
cosines of the principal angles of `U` against `V`. -/
noncomputable def cosAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  ContinuousLinearMap.modulus (V.starProjection ∘L U.starProjection)

/-- The cosine operator is nonnegative. -/
theorem cosAngleOperatorC_nonneg (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ cosAngleOperatorC U V :=
  ContinuousLinearMap.modulus_nonneg _

/-- The cosine operator is self-adjoint. -/
theorem isSelfAdjoint_cosAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (cosAngleOperatorC U V) :=
  ContinuousLinearMap.modulus_isSelfAdjoint _

/-- The norm of the cosine operator is the norm of the directed projection
composition — the largest principal cosine. -/
theorem norm_cosAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖cosAngleOperatorC U V‖ = ‖V.starProjection ∘L U.starProjection‖ :=
  ContinuousLinearMap.norm_modulus _

/-- The cosine operator is a contraction. -/
theorem norm_cosAngleOperatorC_le_one (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖cosAngleOperatorC U V‖ ≤ 1 := by
  rw [norm_cosAngleOperatorC]
  calc ‖V.starProjection ∘L U.starProjection‖
      ≤ ‖V.starProjection‖ * ‖U.starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 :=
        mul_le_mul V.starProjection_norm_le U.starProjection_norm_le
          (norm_nonneg _) zero_le_one
    _ = 1 := by ring

/-- Directed sine of the operator angle at complex scalars: the absolute
value of the cross projection composition `P_{Vᗮ} P_U`.  Its norm is the
directed gap. -/
noncomputable def sinAngleOperatorDirectedC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  ContinuousLinearMap.modulus (Vᗮ.starProjection ∘L U.starProjection)

/-- The directed sine operator is nonnegative. -/
theorem sinAngleOperatorDirectedC_nonneg (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ sinAngleOperatorDirectedC U V :=
  ContinuousLinearMap.modulus_nonneg _

/-- The directed sine operator is self-adjoint. -/
theorem isSelfAdjoint_sinAngleOperatorDirectedC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (sinAngleOperatorDirectedC U V) :=
  ContinuousLinearMap.modulus_isSelfAdjoint _

/-- **The norm of the directed sine operator is the directed gap.** -/
theorem norm_sinAngleOperatorDirectedC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinAngleOperatorDirectedC U V‖ = directedGap U V :=
  ContinuousLinearMap.norm_modulus _

/-- Square of the compressed cross block: `(P_W P_U)⋆ (P_W P_U) = P_U P_W P_U`
for any orthogonally complemented `W`. -/
theorem adjoint_cross_mul_cross (U W : Submodule ℂ E)
    [U.HasOrthogonalProjection] [W.HasOrthogonalProjection] :
    star (W.starProjection ∘L U.starProjection) *
        (W.starProjection ∘L U.starProjection) =
      U.starProjection ∘L W.starProjection ∘L U.starProjection := by
  -- Left as a `rw` chain on purpose: `simp only` with this same list breaks the enclosing `calc`:
  -- it normalises the left-hand side past the form the next step declares.
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
    (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection W).star_eq, ContinuousLinearMap.mul_def]
  calc (U.starProjection ∘L W.starProjection) ∘L
        (W.starProjection ∘L U.starProjection)
      = U.starProjection ∘L (W.starProjection ∘L W.starProjection) ∘L
          U.starProjection := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = U.starProjection ∘L W.starProjection ∘L U.starProjection := by
        rw [show W.starProjection ∘L W.starProjection = W.starProjection from
          W.isIdempotentElem_starProjection]

/-- **Operator-level Pythagoras.**  The squares of the directed sine and
cosine operators sum to the source projection:
`sin Θ(U,V)² + cos Θ(U,V)² = P_U`. -/
theorem sinAngleOperatorDirectedC_sq_add_cosAngleOperatorC_sq
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinAngleOperatorDirectedC U V * sinAngleOperatorDirectedC U V +
      cosAngleOperatorC U V * cosAngleOperatorC U V = U.starProjection := by
  rw [sinAngleOperatorDirectedC, cosAngleOperatorC,
    ContinuousLinearMap.modulus_mul_self_eq_star_mul_self, ContinuousLinearMap.modulus_mul_self_eq_star_mul_self,
    adjoint_cross_mul_cross, adjoint_cross_mul_cross]
  calc U.starProjection ∘L Vᗮ.starProjection ∘L U.starProjection +
        U.starProjection ∘L V.starProjection ∘L U.starProjection
      = U.starProjection ∘L (Vᗮ.starProjection + V.starProjection) ∘L
          U.starProjection := by
        rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    _ = U.starProjection ∘L ContinuousLinearMap.id ℂ E ∘L
          U.starProjection := by
        rw [show Vᗮ.starProjection + V.starProjection =
          ContinuousLinearMap.id ℂ E from by
            rw [Submodule.starProjection_orthogonal' V]
            ext x
            simp]
    _ = U.starProjection := by
        rw [ContinuousLinearMap.id_comp,
          show U.starProjection ∘L U.starProjection = U.starProjection from
            U.isIdempotentElem_starProjection]

omit [CompleteSpace E] in
/-- Any two-sided compression by `P_U` commutes with `P_U`. -/
theorem commute_compress_starProjection (U : Submodule ℂ E)
    [U.HasOrthogonalProjection] (T : E →L[ℂ] E) :
    Commute (U.starProjection ∘L T ∘L U.starProjection) U.starProjection := by
  have hidem : U.starProjection ∘L U.starProjection = U.starProjection :=
    U.isIdempotentElem_starProjection
  show (U.starProjection ∘L T ∘L U.starProjection) * U.starProjection =
    U.starProjection * (U.starProjection ∘L T ∘L U.starProjection)
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
  calc (U.starProjection ∘L T ∘L U.starProjection) ∘L U.starProjection
      = U.starProjection ∘L T ∘L
          (U.starProjection ∘L U.starProjection) := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = U.starProjection ∘L T ∘L U.starProjection := by rw [hidem]
    _ = (U.starProjection ∘L U.starProjection) ∘L T ∘L
          U.starProjection := by rw [hidem]
    _ = U.starProjection ∘L
          ((U.starProjection ∘L T ∘L U.starProjection)) := by
        simp only [ContinuousLinearMap.comp_assoc]

omit [CompleteSpace E] in
/-- The two compressed cross squares sum to the source projection. -/
theorem cross_sq_add_cross_sq (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.starProjection ∘L Vᗮ.starProjection ∘L U.starProjection +
      U.starProjection ∘L V.starProjection ∘L U.starProjection =
    U.starProjection := by
  calc U.starProjection ∘L Vᗮ.starProjection ∘L U.starProjection +
        U.starProjection ∘L V.starProjection ∘L U.starProjection
      = U.starProjection ∘L (Vᗮ.starProjection + V.starProjection) ∘L
          U.starProjection := by
        rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    _ = U.starProjection ∘L ContinuousLinearMap.id ℂ E ∘L
          U.starProjection := by
        rw [show Vᗮ.starProjection + V.starProjection =
          ContinuousLinearMap.id ℂ E from by
            rw [Submodule.starProjection_orthogonal' V]
            ext x
            simp]
    _ = U.starProjection := by
        rw [ContinuousLinearMap.id_comp,
          show U.starProjection ∘L U.starProjection = U.starProjection from
            U.isIdempotentElem_starProjection]

/-- The two compressed cross squares commute. -/
theorem commute_cross_sq (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute
      (star (Vᗮ.starProjection ∘L U.starProjection) *
        (Vᗮ.starProjection ∘L U.starProjection))
      (star (V.starProjection ∘L U.starProjection) *
        (V.starProjection ∘L U.starProjection)) := by
  rw [adjoint_cross_mul_cross, adjoint_cross_mul_cross]
  have hb : U.starProjection ∘L V.starProjection ∘L U.starProjection =
      U.starProjection -
        U.starProjection ∘L Vᗮ.starProjection ∘L U.starProjection :=
    eq_sub_of_add_eq' (cross_sq_add_cross_sq U V)
  rw [hb]
  exact (commute_compress_starProjection U Vᗮ.starProjection).sub_right
    (Commute.refl _)

/-- **The directed sine and cosine operators commute** — the compressed
cross squares commute by the Pythagoras identity, and commutation passes
to the continuous-functional-calculus square roots. -/
theorem commute_sinAngleOperatorDirectedC_cosAngleOperatorC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (sinAngleOperatorDirectedC U V) (cosAngleOperatorC U V) :=
  ContinuousLinearMap.modulus_commute_modulus (commute_cross_sq U V)

/-- Sine of twice the directed operator angle at complex scalars:
`2 sin Θ cos Θ` through the commuting directed sine and cosine. -/
noncomputable def sinTwoAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  (2 : ℝ) • (sinAngleOperatorDirectedC U V * cosAngleOperatorC U V)

/-- The double-angle sine operator is self-adjoint: the commuting product
of the self-adjoint sine and cosine is self-adjoint, and the real scalar
preserves it. -/
theorem isSelfAdjoint_sinTwoAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (sinTwoAngleOperatorC U V) := by
  have hmul : IsSelfAdjoint
      (sinAngleOperatorDirectedC U V * cosAngleOperatorC U V) := by
    rw [IsSelfAdjoint, star_mul,
      (isSelfAdjoint_cosAngleOperatorC U V).star_eq,
      (isSelfAdjoint_sinAngleOperatorDirectedC U V).star_eq]
    exact (commute_sinAngleOperatorDirectedC_cosAngleOperatorC U V).symm
  exact (IsSelfAdjoint.all (2 : ℝ)).smul hmul

/-- Norm bound for the double-angle sine: at most twice the directed gap. -/
theorem norm_sinTwoAngleOperatorC_le (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinTwoAngleOperatorC U V‖ ≤ 2 * directedGap U V := by
  calc ‖sinTwoAngleOperatorC U V‖
      = 2 * ‖sinAngleOperatorDirectedC U V * cosAngleOperatorC U V‖ := by
        rw [sinTwoAngleOperatorC, norm_smul]
        norm_num
    _ ≤ 2 * (‖sinAngleOperatorDirectedC U V‖ * ‖cosAngleOperatorC U V‖) := by
        have := norm_mul_le (sinAngleOperatorDirectedC U V)
          (cosAngleOperatorC U V)
        linarith
    _ ≤ 2 * (directedGap U V * 1) := by
        have h1 : ‖sinAngleOperatorDirectedC U V‖ = directedGap U V :=
          norm_sinAngleOperatorDirectedC U V
        have h2 := norm_cosAngleOperatorC_le_one U V
        have h3 : (0 : ℝ) ≤ directedGap U V := by
          rw [← h1]; exact norm_nonneg _
        nlinarith [norm_nonneg (cosAngleOperatorC U V)]
    _ = 2 * directedGap U V := by ring

/-- **Exact norm of the double-angle sine.**
`‖sin 2Θ(U, V)‖ = 2 ‖P_{Vᗮ} P_U P_V‖`: the absolute values drop out of
the norm of the product by the C⋆-composition identities
`‖|S| D‖ = ‖S D‖` and `‖D |T|‖ = ‖D T⋆‖`, leaving the compressed cross
block. -/
theorem norm_sinTwoAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinTwoAngleOperatorC U V‖ =
      2 * ‖Vᗮ.starProjection ∘L U.starProjection ∘L V.starProjection‖ := by
  -- The canonical modulus laws are stated with `adjoint` and `∘L`, which on an
  -- endomorphism algebra are `star` and `*` only up to unfolding; both local
  -- facts are therefore phrased in the canonical form and proved in the
  -- algebra form.
  have hstar : ContinuousLinearMap.adjoint
      (V.starProjection ∘L U.starProjection) =
      U.starProjection ∘L V.starProjection := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    show star (V.starProjection * U.starProjection) =
      U.starProjection * V.starProjection
    rw [star_mul, (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection V).star_eq]
  have hcomp : (Vᗮ.starProjection ∘L U.starProjection) ∘L
      (U.starProjection ∘L V.starProjection) =
      Vᗮ.starProjection ∘L U.starProjection ∘L V.starProjection := by
    show Vᗮ.starProjection * U.starProjection *
        (U.starProjection * V.starProjection) =
      Vᗮ.starProjection * (U.starProjection * V.starProjection)
    rw [mul_assoc, ← mul_assoc U.starProjection,
      (U.isIdempotentElem_starProjection).eq]
  have hprod : ‖sinAngleOperatorDirectedC U V * cosAngleOperatorC U V‖ =
      ‖Vᗮ.starProjection ∘L U.starProjection ∘L V.starProjection‖ := by
    -- `‖|S| ∘L D‖ = ‖S ∘L D‖` and `‖D ∘L |T|‖ = ‖D ∘L T⋆‖` are stated with
    -- `∘L`; on an endomorphism algebra that is `*`, but only up to unfolding,
    -- so say so once and rewrite in the composite form.
    show ‖sinAngleOperatorDirectedC U V ∘L cosAngleOperatorC U V‖ = _
    rw [sinAngleOperatorDirectedC, cosAngleOperatorC,
      ContinuousLinearMap.norm_modulus_comp, ContinuousLinearMap.norm_comp_modulus,
      hstar, hcomp]
  rw [sinTwoAngleOperatorC, norm_smul, hprod]
  norm_num

omit [CompleteSpace E] in
/-- **Pointwise Pythagoras for the directed sine and cosine.**  On vectors
of `U`, the squared norms of the directed sine (`P_{Vᗮ} x`) and cosine
(`P_V x`) data add to `‖x‖²` — the operator-level `sin² + cos² = 1` on the
source subspace. -/
theorem sq_norm_sin_add_sq_norm_cos (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : x ∈ U) :
    ‖(Vᗮ.starProjection ∘L U.starProjection) x‖ ^ 2 +
      ‖(V.starProjection ∘L U.starProjection) x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hP : U.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have hVc : Vᗮ.starProjection x = x - V.starProjection x :=
    V.starProjection_orthogonal_apply x
  have horth : ⟪V.starProjection x, x - V.starProjection x⟫_ℂ = 0 := by
    have h1 : x - V.starProjection x ∈ Vᗮ := by
      rw [← hVc]
      exact Vᗮ.starProjection_apply_mem x
    have h2 : V.starProjection x ∈ V := V.starProjection_apply_mem x
    exact (Submodule.mem_orthogonal V _).mp h1 _ h2
  have hpyth : ‖V.starProjection x‖ ^ 2 + ‖x - V.starProjection x‖ ^ 2 =
      ‖x‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (V.starProjection x) (x - V.starProjection x) horth
    rw [show V.starProjection x + (x - V.starProjection x) = x from by abel]
      at h
    rw [sq, sq, sq]
    linarith
  simp only [ContinuousLinearMap.comp_apply, hP]
  rw [hVc]
  linarith

/-- The directed cosine vanishes on the orthogonal complement of the
source. -/
theorem cosAngleOperatorC_apply_eq_zero_of_mem_orthogonal
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {y : E} (hy : y ∈ Uᗮ) : cosAngleOperatorC U V y = 0 := by
  rw [cosAngleOperatorC, ContinuousLinearMap.modulus_apply_eq_zero_iff]
  have hPU : U.starProjection y = 0 := by
    rw [Submodule.starProjection_apply, Submodule.coe_eq_zero,
      Submodule.orthogonalProjectionOnto_eq_zero_iff]
    exact hy
  simp [hPU]

/-- **Acute coercivity of the directed cosine.**  On the source subspace,
`‖cos Θ(U,V) x‖ ≥ √(1 - directedGap²) ‖x‖` — the quantitative content of
acuteness, by the pointwise Pythagoras identity. -/
theorem norm_cosAngleOperatorC_apply_ge (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : x ∈ U) :
    Real.sqrt (1 - directedGap U V ^ 2) * ‖x‖ ≤
      ‖cosAngleOperatorC U V x‖ := by
  have hg : directedGap U V = ‖Vᗮ.starProjection ∘L U.starProjection‖ :=
    rfl
  have hg1 : directedGap U V ≤ 1 := by
    rw [hg]
    calc ‖Vᗮ.starProjection ∘L U.starProjection‖
        ≤ ‖Vᗮ.starProjection‖ * ‖U.starProjection‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 :=
          mul_le_mul Vᗮ.starProjection_norm_le U.starProjection_norm_le
            (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  have hg0 : 0 ≤ directedGap U V := by
    rw [hg]; exact norm_nonneg _
  have hcos : ‖cosAngleOperatorC U V x‖ =
      ‖(V.starProjection ∘L U.starProjection) x‖ :=
    ContinuousLinearMap.norm_modulus_apply _ x
  have hsin_le : ‖(Vᗮ.starProjection ∘L U.starProjection) x‖ ≤
      directedGap U V * ‖x‖ := by
    rw [hg]
    exact (Vᗮ.starProjection ∘L U.starProjection).le_opNorm x
  have hpyth := sq_norm_sin_add_sq_norm_cos U V hx
  have hsq : (1 - directedGap U V ^ 2) * ‖x‖ ^ 2 ≤
      ‖cosAngleOperatorC U V x‖ ^ 2 := by
    rw [hcos]
    nlinarith [hsin_le, norm_nonneg ((Vᗮ.starProjection ∘L
      U.starProjection) x), norm_nonneg x]
  have hs := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_mul (by nlinarith : (0:ℝ) ≤ 1 - directedGap U V ^ 2),
    Real.sqrt_sq (norm_nonneg x), Real.sqrt_sq (norm_nonneg _)] at hs

/-- In the acute regime the directed cosine is injective on the source
subspace. -/
theorem cosAngleOperatorC_eq_zero_imp_of_acute (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) {x : E} (hx : x ∈ U)
    (h0 : cosAngleOperatorC U V x = 0) : x = 0 := by
  have hglt : directedGap U V < 1 :=
    lt_of_le_of_lt (directedProjectionGap_le_projectionGap U V) hacute
  have hg0 : 0 ≤ directedGap U V := by
    rw [show directedGap U V =
      ‖Vᗮ.starProjection ∘L U.starProjection‖ from rfl]
    exact norm_nonneg _
  have hcoer := norm_cosAngleOperatorC_apply_ge U V hx
  rw [h0, norm_zero] at hcoer
  have hpos : 0 < Real.sqrt (1 - directedGap U V ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  have hxle : ‖x‖ ≤ 0 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  exact norm_eq_zero.mp (le_antisymm hxle (norm_nonneg x))


section Tangent

/-- The directed cosine commutes with the source projection. -/
theorem commute_cosAngleOperatorC_starProjection (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (cosAngleOperatorC U V) U.starProjection := by
  have hb : Commute (star (V.starProjection ∘L U.starProjection) *
      (V.starProjection ∘L U.starProjection)) U.starProjection := by
    rw [adjoint_cross_mul_cross]
    exact commute_compress_starProjection U V.starProjection
  exact hb.cfcₙ_nnreal _

/-- The directed cosine maps the source subspace into itself. -/
theorem cosAngleOperatorC_apply_mem (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : x ∈ U) : cosAngleOperatorC U V x ∈ U := by
  have h := commute_cosAngleOperatorC_starProjection U V
  have hx' : U.starProjection x = x :=
    Submodule.starProjection_eq_self_iff.mpr hx
  rw [← Submodule.starProjection_eq_self_iff]
  calc U.starProjection (cosAngleOperatorC U V x)
      = (U.starProjection * cosAngleOperatorC U V) x := rfl
    _ = (cosAngleOperatorC U V * U.starProjection) x := by rw [← h.eq]
    _ = cosAngleOperatorC U V x := by
        show cosAngleOperatorC U V (U.starProjection x) = _
        rw [hx']

/-- The extended cosine: the directed cosine on the source, the identity on
its orthogonal complement. -/
noncomputable def cosAngleExtendedC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  cosAngleOperatorC U V + Uᗮ.starProjection

/-- The extended cosine is self-adjoint. -/
theorem isSelfAdjoint_cosAngleExtendedC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (cosAngleExtendedC U V) :=
  (isSelfAdjoint_cosAngleOperatorC U V).add (isSelfAdjoint_starProjection _)

omit [CompleteSpace E] in
/-- **Pythagoras across a subspace and its orthogonal complement.** -/
private theorem norm_sq_eq_starProjection_add_orthogonal (U : Submodule ℂ E)
    [U.HasOrthogonalProjection] (x : E) :
    ‖x‖ ^ 2 = ‖U.starProjection x‖ ^ 2 + ‖Uᗮ.starProjection x‖ ^ 2 := by
  have horth' : ⟪U.starProjection x, Uᗮ.starProjection x⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal U _).mp
      (Uᗮ.starProjection_apply_mem x) _ (U.starProjection_apply_mem x)
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (U.starProjection x) (Uᗮ.starProjection x) horth'
  rw [U.starProjection_add_starProjection_orthogonal x] at h
  rw [sq, sq, sq]
  linarith

/-- **Global coercivity of the extended cosine in the acute regime.** -/
theorem norm_cosAngleExtendedC_apply_ge (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (x : E) :
    min (Real.sqrt (1 - directedGap U V ^ 2)) 1 * ‖x‖ ≤
      ‖cosAngleExtendedC U V x‖ := by
  set c : ℝ := min (Real.sqrt (1 - directedGap U V ^ 2)) 1 with hc
  have hc0 : 0 ≤ c := le_min (Real.sqrt_nonneg _) zero_le_one
  -- decompose and compute the image
  have hdecomp : x = U.starProjection x + Uᗮ.starProjection x :=
    (U.starProjection_add_starProjection_orthogonal x).symm
  have hcos0 : cosAngleOperatorC U V (Uᗮ.starProjection x) = 0 :=
    cosAngleOperatorC_apply_eq_zero_of_mem_orthogonal U V
      (Uᗮ.starProjection_apply_mem x)
  have himg : cosAngleExtendedC U V x =
      cosAngleOperatorC U V (U.starProjection x) + Uᗮ.starProjection x := by
    calc cosAngleExtendedC U V x
        = cosAngleOperatorC U V x + Uᗮ.starProjection x := rfl
      _ = cosAngleOperatorC U V (U.starProjection x + Uᗮ.starProjection x) +
            Uᗮ.starProjection x := by rw [← hdecomp]
      _ = cosAngleOperatorC U V (U.starProjection x) + Uᗮ.starProjection x := by
          rw [map_add, hcos0, add_zero]
  -- orthogonality of the two summands
  have hmemU : cosAngleOperatorC U V (U.starProjection x) ∈ U :=
    cosAngleOperatorC_apply_mem U V (U.starProjection_apply_mem x)
  have horth : ⟪cosAngleOperatorC U V (U.starProjection x),
      Uᗮ.starProjection x⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal U _).mp
      (Uᗮ.starProjection_apply_mem x) _ hmemU
  have horth' : ⟪U.starProjection x, Uᗮ.starProjection x⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal U _).mp
      (Uᗮ.starProjection_apply_mem x) _ (U.starProjection_apply_mem x)
  -- squared-norm computations
  have hsq1 : ‖cosAngleExtendedC U V x‖ ^ 2 =
      ‖cosAngleOperatorC U V (U.starProjection x)‖ ^ 2 +
        ‖Uᗮ.starProjection x‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (cosAngleOperatorC U V (U.starProjection x)) (Uᗮ.starProjection x)
      horth
    rw [himg, sq, sq, sq]
    linarith
  have hsq2 := norm_sq_eq_starProjection_add_orthogonal U x
  -- coercivity on the source component
  have hcoer := norm_cosAngleOperatorC_apply_ge U V
    (U.starProjection_apply_mem x)
  have hcle : c ≤ Real.sqrt (1 - directedGap U V ^ 2) := min_le_left _ _
  have hc1 : c ≤ 1 := min_le_right _ _
  have hlow1 : c * ‖U.starProjection x‖ ≤
      ‖cosAngleOperatorC U V (U.starProjection x)‖ :=
    le_trans (mul_le_mul_of_nonneg_right hcle (norm_nonneg _)) hcoer
  have hfinal : (c * ‖x‖) ^ 2 ≤ ‖cosAngleExtendedC U V x‖ ^ 2 := by
    rw [hsq1]
    have h1 : (c * ‖U.starProjection x‖) ^ 2 ≤
        ‖cosAngleOperatorC U V (U.starProjection x)‖ ^ 2 := by
      have h := mul_self_le_mul_self
        (mul_nonneg hc0 (norm_nonneg _)) hlow1
      rw [sq, sq]
      exact h
    have h2 : c ^ 2 ≤ 1 := by nlinarith
    have hb2 : (0:ℝ) ≤ ‖Uᗮ.starProjection x‖ ^ 2 := sq_nonneg _
    nlinarith [h1, h2, hb2, hsq2, sq_nonneg ‖x‖,
      sq_nonneg ‖U.starProjection x‖]
  have hs := Real.sqrt_le_sqrt hfinal
  rwa [Real.sqrt_sq (mul_nonneg hc0 (norm_nonneg x)),
    Real.sqrt_sq (norm_nonneg _)] at hs

/-- **The extended cosine is invertible in the acute regime.** -/
theorem cosAngleExtendedC_ker_bot_range_top (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    (cosAngleExtendedC U V).ker = ⊥ ∧
      (cosAngleExtendedC U V).range = ⊤ := by
  have hglt : directedGap U V < 1 :=
    lt_of_le_of_lt (directedProjectionGap_le_projectionGap U V) hacute
  have hg0 : 0 ≤ directedGap U V := by
    rw [show directedGap U V =
      ‖Vᗮ.starProjection ∘L U.starProjection‖ from rfl]
    exact norm_nonneg _
  set c : ℝ := min (Real.sqrt (1 - directedGap U V ^ 2)) 1 with hc
  have hcpos : 0 < c := by
    apply lt_min
    · exact Real.sqrt_pos.mpr (by nlinarith)
    · exact zero_lt_one
  have hlow : ∀ x, c * ‖x‖ ≤ ‖cosAngleExtendedC U V x‖ := fun x =>
    norm_cosAngleExtendedC_apply_ge U V x
  have hker : (cosAngleExtendedC U V).ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx0 : cosAngleExtendedC U V x = 0 := hx
    have h := hlow x
    rw [hx0, norm_zero] at h
    have : ‖x‖ ≤ 0 := by nlinarith
    exact norm_eq_zero.mp (le_antisymm this (norm_nonneg x))
  refine ⟨hker, ?_⟩
  -- closed range from the antilipschitz bound
  have hanti : AntilipschitzWith (⟨c, hcpos.le⟩ : NNReal)⁻¹
      (cosAngleExtendedC U V) := by
    refine ContinuousLinearMap.antilipschitz_of_bound _ fun x => ?_
    have h := hlow x
    have hcoe : ((((⟨c, hcpos.le⟩ : NNReal))⁻¹ : NNReal) : ℝ) = c⁻¹ := rfl
    rw [hcoe]
    calc ‖x‖ = c⁻¹ * (c * ‖x‖) :=
          (inv_mul_cancel_left₀ hcpos.ne' ‖x‖).symm
      _ ≤ c⁻¹ * ‖cosAngleExtendedC U V x‖ :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hcpos.le)
  have hclosed : IsClosed (Set.range (cosAngleExtendedC U V)) :=
    hanti.isClosed_range (cosAngleExtendedC U V).uniformContinuous
  -- dense range from self-adjointness and injectivity
  have hclosed' : IsClosed
      (((cosAngleExtendedC U V).range : Submodule ℂ E) : Set E) := by
    convert hclosed using 1
    ext y
    simp [SetLike.mem_coe, Set.mem_range, LinearMap.mem_range]
  have : CompleteSpace
      ((cosAngleExtendedC U V).range : Submodule ℂ E) :=
    hclosed'.completeSpace_coe
  have : ((cosAngleExtendedC U V).range :
      Submodule ℂ E).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace _
  rw [← Submodule.orthogonal_eq_bot_iff]
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hy' : ∀ x : E, ⟪cosAngleExtendedC U V x, y⟫_ℂ = 0 := by
    intro x
    exact (Submodule.mem_orthogonal _ y).mp hy _ ⟨x, rfl⟩
  have hTy : cosAngleExtendedC U V y = 0 := by
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_cosAngleExtendedC U V)
    have h := hy' (cosAngleExtendedC U V y)
    have hstep : ⟪cosAngleExtendedC U V (cosAngleExtendedC U V y), y⟫_ℂ =
        ⟪cosAngleExtendedC U V y, cosAngleExtendedC U V y⟫_ℂ :=
      hsym (cosAngleExtendedC U V y) y
    rw [hstep] at h
    exact inner_self_eq_zero.mp h
  have h := hlow y
  rw [hTy, norm_zero] at h
  have : ‖y‖ ≤ 0 := by nlinarith
  exact norm_eq_zero.mp (le_antisymm this (norm_nonneg y))

/-- The extended cosine as a continuous linear equivalence, in the acute
regime. -/
noncomputable def cosAngleExtendedCEquiv (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) : E ≃L[ℂ] E :=
  ContinuousLinearEquiv.ofBijective (cosAngleExtendedC U V)
    (cosAngleExtendedC_ker_bot_range_top U V hacute).1
    (cosAngleExtendedC_ker_bot_range_top U V hacute).2

/-- **Tangent of the directed operator angle** in the acute regime:
`tan Θ = sin Θ · (cos Θ + P_{Uᗮ})⁻¹`. -/
noncomputable def tanAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) : E →L[ℂ] E :=
  sinAngleOperatorDirectedC U V ∘L
    (cosAngleExtendedCEquiv U V hacute).symm.toContinuousLinearMap

/-- The defining identity: the tangent composed with the extended cosine is
the directed sine. -/
theorem tanAngleOperatorC_comp_cosAngleExtendedC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    tanAngleOperatorC U V hacute ∘L cosAngleExtendedC U V =
      sinAngleOperatorDirectedC U V := by
  ext x
  show sinAngleOperatorDirectedC U V
    ((cosAngleExtendedCEquiv U V hacute).symm
      (cosAngleExtendedC U V x)) = sinAngleOperatorDirectedC U V x
  congr 1
  exact (cosAngleExtendedCEquiv U V hacute).symm_apply_apply x

end Tangent

section DoubleAngleTangent

/-- A self-adjoint operator bounded below in norm is boundedly invertible:
trivial kernel, closed range, full range. -/
theorem ker_bot_range_top_of_isSelfAdjoint_of_bounded_below
    {T : E →L[ℂ] E} (hsa : IsSelfAdjoint T) {c : ℝ} (hcpos : 0 < c)
    (hlow : ∀ x, c * ‖x‖ ≤ ‖T x‖) :
    T.ker = ⊥ ∧ T.range = ⊤ := by
  have hker : T.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx0 : T x = 0 := hx
    have h := hlow x
    rw [hx0, norm_zero] at h
    have : ‖x‖ ≤ 0 := by nlinarith
    exact norm_eq_zero.mp (le_antisymm this (norm_nonneg x))
  refine ⟨hker, ?_⟩
  have hanti : AntilipschitzWith (⟨c, hcpos.le⟩ : NNReal)⁻¹ T := by
    refine ContinuousLinearMap.antilipschitz_of_bound _ fun x => ?_
    have h := hlow x
    have hcoe : ((((⟨c, hcpos.le⟩ : NNReal))⁻¹ : NNReal) : ℝ) = c⁻¹ := rfl
    rw [hcoe]
    calc ‖x‖ = c⁻¹ * (c * ‖x‖) :=
          (inv_mul_cancel_left₀ hcpos.ne' ‖x‖).symm
      _ ≤ c⁻¹ * ‖T x‖ :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hcpos.le)
  have hclosed : IsClosed (Set.range T) :=
    hanti.isClosed_range T.uniformContinuous
  have hclosed' : IsClosed ((T.range : Submodule ℂ E) : Set E) := by
    convert hclosed using 1
    ext y
    simp [SetLike.mem_coe, Set.mem_range, LinearMap.mem_range]
  have : CompleteSpace (T.range : Submodule ℂ E) :=
    hclosed'.completeSpace_coe
  have : (T.range : Submodule ℂ E).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace _
  rw [← Submodule.orthogonal_eq_bot_iff]
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hy' : ∀ x : E, ⟪T x, y⟫_ℂ = 0 := by
    intro x
    exact (Submodule.mem_orthogonal _ y).mp hy _ ⟨x, rfl⟩
  have hTy : T y = 0 := by
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
    have h := hy' (T y)
    have hstep : ⟪T (T y), y⟫_ℂ = ⟪T y, T y⟫_ℂ := hsym (T y) y
    rw [hstep] at h
    exact inner_self_eq_zero.mp h
  have h := hlow y
  rw [hTy, norm_zero] at h
  have : ‖y‖ ≤ 0 := by nlinarith
  exact norm_eq_zero.mp (le_antisymm this (norm_nonneg y))

omit [CompleteSpace E] in
/-- Coercivity of an operator supported on `U`, extended by the identity on
`Uᗮ`. -/
theorem norm_add_starProjection_orthogonal_apply_ge
    {S : E →L[ℂ] E} (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hmem : ∀ x ∈ U, S x ∈ U) (hzero : ∀ y ∈ Uᗮ, S y = 0)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hcoer : ∀ x ∈ U, c * ‖x‖ ≤ ‖S x‖) (x : E) :
    c * ‖x‖ ≤ ‖(S + Uᗮ.starProjection) x‖ := by
  have hdecomp : x = U.starProjection x + Uᗮ.starProjection x :=
    (U.starProjection_add_starProjection_orthogonal x).symm
  have hS0 : S (Uᗮ.starProjection x) = 0 :=
    hzero _ (Uᗮ.starProjection_apply_mem x)
  have himg : (S + Uᗮ.starProjection) x =
      S (U.starProjection x) + Uᗮ.starProjection x := by
    calc (S + Uᗮ.starProjection) x = S x + Uᗮ.starProjection x := rfl
      _ = S (U.starProjection x + Uᗮ.starProjection x) +
            Uᗮ.starProjection x := by rw [← hdecomp]
      _ = S (U.starProjection x) + Uᗮ.starProjection x := by
          rw [map_add, hS0, add_zero]
  have hmemU : S (U.starProjection x) ∈ U :=
    hmem _ (U.starProjection_apply_mem x)
  have horth : ⟪S (U.starProjection x), Uᗮ.starProjection x⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal U _).mp
      (Uᗮ.starProjection_apply_mem x) _ hmemU
  have horth' : ⟪U.starProjection x, Uᗮ.starProjection x⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal U _).mp
      (Uᗮ.starProjection_apply_mem x) _ (U.starProjection_apply_mem x)
  have hsq1 : ‖(S + Uᗮ.starProjection) x‖ ^ 2 =
      ‖S (U.starProjection x)‖ ^ 2 + ‖Uᗮ.starProjection x‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (S (U.starProjection x)) (Uᗮ.starProjection x) horth
    rw [himg, sq, sq, sq]
    linarith
  have hsq2 := norm_sq_eq_starProjection_add_orthogonal U x
  have hlow1 : c * ‖U.starProjection x‖ ≤ ‖S (U.starProjection x)‖ :=
    hcoer _ (U.starProjection_apply_mem x)
  have hfinal : (c * ‖x‖) ^ 2 ≤ ‖(S + Uᗮ.starProjection) x‖ ^ 2 := by
    rw [hsq1]
    have h1 : (c * ‖U.starProjection x‖) ^ 2 ≤
        ‖S (U.starProjection x)‖ ^ 2 := by
      have h := mul_self_le_mul_self
        (mul_nonneg hc0 (norm_nonneg _)) hlow1
      rw [sq, sq]
      exact h
    have h2 : c ^ 2 ≤ 1 := by nlinarith
    have hb2 : (0:ℝ) ≤ ‖Uᗮ.starProjection x‖ ^ 2 := sq_nonneg _
    nlinarith [h1, h2, hb2, hsq2, sq_nonneg ‖x‖,
      sq_nonneg ‖U.starProjection x‖]
  have hs := Real.sqrt_le_sqrt hfinal
  rwa [Real.sqrt_sq (mul_nonneg hc0 (norm_nonneg x)),
    Real.sqrt_sq (norm_nonneg _)] at hs

/-- Cosine of twice the directed operator angle: `cos 2Θ = cos² - sin²`. -/
noncomputable def cosTwoAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  cosAngleOperatorC U V * cosAngleOperatorC U V -
    sinAngleOperatorDirectedC U V * sinAngleOperatorDirectedC U V

/-- The double-angle cosine is self-adjoint. -/
theorem isSelfAdjoint_cosTwoAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (cosTwoAngleOperatorC U V) := by
  simp only [cosTwoAngleOperatorC, IsSelfAdjoint, star_sub, star_mul, star_mul,
    (isSelfAdjoint_cosAngleOperatorC U V).star_eq,
    (isSelfAdjoint_sinAngleOperatorDirectedC U V).star_eq]

/-- The directed sine vanishes on the orthogonal complement of the
source. -/
theorem sinAngleOperatorDirectedC_apply_eq_zero_of_mem_orthogonal
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {y : E} (hy : y ∈ Uᗮ) : sinAngleOperatorDirectedC U V y = 0 := by
  rw [sinAngleOperatorDirectedC, ContinuousLinearMap.modulus_apply_eq_zero_iff]
  have hPU : U.starProjection y = 0 := by
    rw [Submodule.starProjection_apply, Submodule.coe_eq_zero,
      Submodule.orthogonalProjectionOnto_eq_zero_iff]
    exact hy
  simp [hPU]

/-- The directed sine commutes with the source projection. -/
theorem commute_sinAngleOperatorDirectedC_starProjection
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (sinAngleOperatorDirectedC U V) U.starProjection := by
  have hb : Commute (star (Vᗮ.starProjection ∘L U.starProjection) *
      (Vᗮ.starProjection ∘L U.starProjection)) U.starProjection := by
    rw [adjoint_cross_mul_cross]
    exact commute_compress_starProjection U Vᗮ.starProjection
  exact hb.cfcₙ_nnreal _

/-- The directed sine maps the source subspace into itself. -/
theorem sinAngleOperatorDirectedC_apply_mem (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : x ∈ U) : sinAngleOperatorDirectedC U V x ∈ U := by
  have h := commute_sinAngleOperatorDirectedC_starProjection U V
  have hx' : U.starProjection x = x :=
    Submodule.starProjection_eq_self_iff.mpr hx
  rw [← Submodule.starProjection_eq_self_iff]
  calc U.starProjection (sinAngleOperatorDirectedC U V x)
      = (U.starProjection * sinAngleOperatorDirectedC U V) x := rfl
    _ = (sinAngleOperatorDirectedC U V * U.starProjection) x := by
        rw [← h.eq]
    _ = sinAngleOperatorDirectedC U V x := by
        show sinAngleOperatorDirectedC U V (U.starProjection x) = _
        rw [hx']

/-- **Quarter-acute coercivity of the double-angle cosine on the source.**
`‖cos 2Θ x‖ ≥ (1 - 2 · directedGap²) ‖x‖` on `U` — trivially true when the
constant is nonpositive, and by the form bound otherwise. -/
theorem norm_cosTwoAngleOperatorC_apply_ge (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : x ∈ U) :
    (1 - 2 * directedGap U V ^ 2) * ‖x‖ ≤
      ‖cosTwoAngleOperatorC U V x‖ := by
  rcases le_or_gt (1 - 2 * directedGap U V ^ 2) 0 with hneg | hpos
  · calc (1 - 2 * directedGap U V ^ 2) * ‖x‖ ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg (norm_nonneg x)
      _ ≤ ‖cosTwoAngleOperatorC U V x‖ := norm_nonneg _
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  -- the quadratic form of `cos 2Θ` on `U`
  have hsymc := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (isSelfAdjoint_cosAngleOperatorC U V)
  have hsyms := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (isSelfAdjoint_sinAngleOperatorDirectedC U V)
  have hform : (⟪cosTwoAngleOperatorC U V x, x⟫_ℂ : ℂ) =
      (((‖cosAngleOperatorC U V x‖ ^ 2 -
        ‖sinAngleOperatorDirectedC U V x‖ ^ 2 : ℝ)) : ℂ) := by
    calc (⟪cosTwoAngleOperatorC U V x, x⟫_ℂ : ℂ)
        = ⟪cosAngleOperatorC U V (cosAngleOperatorC U V x), x⟫_ℂ -
            ⟪sinAngleOperatorDirectedC U V
              (sinAngleOperatorDirectedC U V x), x⟫_ℂ := by
          rw [cosTwoAngleOperatorC]
          simp [sub_apply, inner_sub_left]
      _ = ⟪cosAngleOperatorC U V x, cosAngleOperatorC U V x⟫_ℂ -
            ⟪sinAngleOperatorDirectedC U V x,
              sinAngleOperatorDirectedC U V x⟫_ℂ := by
          have h1 : ⟪cosAngleOperatorC U V (cosAngleOperatorC U V x),
              x⟫_ℂ = ⟪cosAngleOperatorC U V x,
                cosAngleOperatorC U V x⟫_ℂ :=
            hsymc (cosAngleOperatorC U V x) x
          have h2 : ⟪sinAngleOperatorDirectedC U V
              (sinAngleOperatorDirectedC U V x), x⟫_ℂ =
              ⟪sinAngleOperatorDirectedC U V x,
                sinAngleOperatorDirectedC U V x⟫_ℂ :=
            hsyms (sinAngleOperatorDirectedC U V x) x
          rw [h1, h2]
      _ = _ := by
          rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
          norm_cast
  -- pointwise Pythagoras data
  have hcosn : ‖cosAngleOperatorC U V x‖ =
      ‖(V.starProjection ∘L U.starProjection) x‖ :=
    ContinuousLinearMap.norm_modulus_apply _ x
  have hsinn : ‖sinAngleOperatorDirectedC U V x‖ =
      ‖(Vᗮ.starProjection ∘L U.starProjection) x‖ :=
    ContinuousLinearMap.norm_modulus_apply _ x
  have hpyth := sq_norm_sin_add_sq_norm_cos U V hx
  have hsin_le : ‖(Vᗮ.starProjection ∘L U.starProjection) x‖ ≤
      directedGap U V * ‖x‖ := by
    rw [show directedGap U V =
      ‖Vᗮ.starProjection ∘L U.starProjection‖ from rfl]
    exact (Vᗮ.starProjection ∘L U.starProjection).le_opNorm x
  -- the form is bounded below
  have hform_ge : (1 - 2 * directedGap U V ^ 2) * ‖x‖ ^ 2 ≤
      ‖cosAngleOperatorC U V x‖ ^ 2 -
        ‖sinAngleOperatorDirectedC U V x‖ ^ 2 := by
    rw [hcosn, hsinn]
    nlinarith [hsin_le, norm_nonneg
      ((Vᗮ.starProjection ∘L U.starProjection) x), norm_nonneg x]
  -- Cauchy--Schwarz upgrade to a norm bound
  have hCS : ‖cosAngleOperatorC U V x‖ ^ 2 -
      ‖sinAngleOperatorDirectedC U V x‖ ^ 2 ≤
        ‖cosTwoAngleOperatorC U V x‖ * ‖x‖ := by
    have h1 : ((‖cosAngleOperatorC U V x‖ ^ 2 -
        ‖sinAngleOperatorDirectedC U V x‖ ^ 2 : ℝ)) =
        RCLike.re (⟪cosTwoAngleOperatorC U V x, x⟫_ℂ : ℂ) := by
      rw [hform]
      exact (RCLike.ofReal_re _).symm
    rw [h1]
    calc RCLike.re (⟪cosTwoAngleOperatorC U V x, x⟫_ℂ : ℂ)
        ≤ ‖(⟪cosTwoAngleOperatorC U V x, x⟫_ℂ : ℂ)‖ := RCLike.re_le_norm _
      _ ≤ ‖cosTwoAngleOperatorC U V x‖ * ‖x‖ := norm_inner_le_norm _ _
  have hx0' : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hkey : (1 - 2 * directedGap U V ^ 2) * ‖x‖ ^ 2 ≤
      ‖cosTwoAngleOperatorC U V x‖ * ‖x‖ := le_trans hform_ge hCS
  have hkey' : ((1 - 2 * directedGap U V ^ 2) * ‖x‖) * ‖x‖ ≤
      ‖cosTwoAngleOperatorC U V x‖ * ‖x‖ := by nlinarith [hkey]
  exact le_of_mul_le_mul_right hkey' hx0'

/-- The double-angle cosine vanishes on the orthogonal complement. -/
theorem cosTwoAngleOperatorC_apply_eq_zero_of_mem_orthogonal
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {y : E} (hy : y ∈ Uᗮ) : cosTwoAngleOperatorC U V y = 0 := by
  show cosAngleOperatorC U V (cosAngleOperatorC U V y) -
    sinAngleOperatorDirectedC U V (sinAngleOperatorDirectedC U V y) = 0
  rw [cosAngleOperatorC_apply_eq_zero_of_mem_orthogonal U V hy,
    sinAngleOperatorDirectedC_apply_eq_zero_of_mem_orthogonal U V hy,
    map_zero, map_zero, sub_zero]

/-- The double-angle cosine maps the source subspace into itself. -/
theorem cosTwoAngleOperatorC_apply_mem (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : x ∈ U) : cosTwoAngleOperatorC U V x ∈ U := by
  show cosAngleOperatorC U V (cosAngleOperatorC U V x) -
    sinAngleOperatorDirectedC U V (sinAngleOperatorDirectedC U V x) ∈ U
  exact U.sub_mem
    (cosAngleOperatorC_apply_mem U V (cosAngleOperatorC_apply_mem U V hx))
    (sinAngleOperatorDirectedC_apply_mem U V
      (sinAngleOperatorDirectedC_apply_mem U V hx))

/-- The extended double-angle cosine: `cos 2Θ` on the source, the identity
on its orthogonal complement. -/
noncomputable def cosTwoAngleExtendedC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  cosTwoAngleOperatorC U V + Uᗮ.starProjection

/-- The extended double-angle cosine is self-adjoint. -/
theorem isSelfAdjoint_cosTwoAngleExtendedC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (cosTwoAngleExtendedC U V) :=
  (isSelfAdjoint_cosTwoAngleOperatorC U V).add
    (isSelfAdjoint_starProjection _)

/-- **The extended double-angle cosine is invertible in the quarter-acute
regime.** -/
theorem cosTwoAngleExtendedC_ker_bot_range_top (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V) :
    (cosTwoAngleExtendedC U V).ker = ⊥ ∧
      (cosTwoAngleExtendedC U V).range = ⊤ := by
  have hg0 : 0 ≤ directedGap U V := by
    rw [show directedGap U V =
      ‖Vᗮ.starProjection ∘L U.starProjection‖ from rfl]
    exact norm_nonneg _
  have hglt : directedGap U V < Real.sqrt 2 / 2 :=
    lt_of_le_of_lt (directedProjectionGap_le_projectionGap U V) hquarter
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hgsq : 2 * directedGap U V ^ 2 < 1 := by nlinarith
  set c : ℝ := min (1 - 2 * directedGap U V ^ 2) 1 with hc
  have hcpos : 0 < c := lt_min (by nlinarith) one_pos
  have hcoerU : ∀ x ∈ U, c * ‖x‖ ≤ ‖cosTwoAngleOperatorC U V x‖ :=
    fun x hx =>
      le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (norm_nonneg x)) (norm_cosTwoAngleOperatorC_apply_ge U V hx)
  have hlow := norm_add_starProjection_orthogonal_apply_ge U
    (fun x hx => cosTwoAngleOperatorC_apply_mem U V hx)
    (fun y hy => cosTwoAngleOperatorC_apply_eq_zero_of_mem_orthogonal U V hy)
    hcpos.le (min_le_right _ _) hcoerU
  exact ker_bot_range_top_of_isSelfAdjoint_of_bounded_below
    (isSelfAdjoint_cosTwoAngleExtendedC U V) hcpos hlow

/-- The extended double-angle cosine as a continuous linear equivalence. -/
noncomputable def cosTwoAngleExtendedCEquiv (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V) : E ≃L[ℂ] E :=
  ContinuousLinearEquiv.ofBijective (cosTwoAngleExtendedC U V)
    (cosTwoAngleExtendedC_ker_bot_range_top U V hquarter).1
    (cosTwoAngleExtendedC_ker_bot_range_top U V hquarter).2

/-- **Tangent of twice the directed operator angle** in the quarter-acute
regime: `tan 2Θ = sin 2Θ · (cos 2Θ + P_{Uᗮ})⁻¹`. -/
noncomputable def tanTwoAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V) : E →L[ℂ] E :=
  sinTwoAngleOperatorC U V ∘L
    (cosTwoAngleExtendedCEquiv U V hquarter).symm.toContinuousLinearMap

/-- The defining identity: the double-angle tangent composed with the
extended double-angle cosine is the double-angle sine. -/
theorem tanTwoAngleOperatorC_comp_cosTwoAngleExtendedC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V) :
    tanTwoAngleOperatorC U V hquarter ∘L cosTwoAngleExtendedC U V =
      sinTwoAngleOperatorC U V := by
  ext x
  show sinTwoAngleOperatorC U V
    ((cosTwoAngleExtendedCEquiv U V hquarter).symm
      (cosTwoAngleExtendedC U V x)) = sinTwoAngleOperatorC U V x
  congr 1
  exact (cosTwoAngleExtendedCEquiv U V hquarter).symm_apply_apply x

section TangentNormBounds

/-- Norm bound for the inverse of the extended cosine: coercivity inverts
to `‖(cos Θ + P_{Uᗮ})⁻¹ y‖ ≤ c⁻¹ ‖y‖`. -/
theorem norm_cosAngleExtendedCEquiv_symm_apply_le (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) (y : E) :
    ‖(cosAngleExtendedCEquiv U V hacute).symm y‖ ≤
      (min (Real.sqrt (1 - directedGap U V ^ 2)) 1)⁻¹ * ‖y‖ := by
  set c : ℝ := min (Real.sqrt (1 - directedGap U V ^ 2)) 1 with hc
  have hglt : directedGap U V < 1 :=
    lt_of_le_of_lt (directedProjectionGap_le_projectionGap U V) hacute
  have hg0 : 0 ≤ directedGap U V := by
    rw [show directedGap U V =
      ‖Vᗮ.starProjection ∘L U.starProjection‖ from rfl]
    exact norm_nonneg _
  have hcpos : 0 < c := lt_min (Real.sqrt_pos.mpr (by nlinarith)) one_pos
  have hcoer := norm_cosAngleExtendedC_apply_ge U V
    ((cosAngleExtendedCEquiv U V hacute).symm y)
  have happ : cosAngleExtendedC U V
      ((cosAngleExtendedCEquiv U V hacute).symm y) = y :=
    (cosAngleExtendedCEquiv U V hacute).apply_symm_apply y
  rw [happ] at hcoer
  calc ‖(cosAngleExtendedCEquiv U V hacute).symm y‖
      = c⁻¹ * (c * ‖(cosAngleExtendedCEquiv U V hacute).symm y‖) :=
        (inv_mul_cancel_left₀ hcpos.ne' _).symm
    _ ≤ c⁻¹ * ‖y‖ :=
        mul_le_mul_of_nonneg_left hcoer (inv_nonneg.mpr hcpos.le)

/-- **Norm bound for the tangent operator**: `‖tan Θ‖` is at most the
directed gap over the acute coercivity constant —
`tan θ_max = sin θ_max / cos θ_max` as an inequality. -/
theorem norm_tanAngleOperatorC_le (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    ‖tanAngleOperatorC U V hacute‖ ≤
      directedGap U V *
        (min (Real.sqrt (1 - directedGap U V ^ 2)) 1)⁻¹ := by
  set c : ℝ := min (Real.sqrt (1 - directedGap U V ^ 2)) 1 with hc
  have hglt : directedGap U V < 1 :=
    lt_of_le_of_lt (directedProjectionGap_le_projectionGap U V) hacute
  have hg0 : 0 ≤ directedGap U V := by
    rw [show directedGap U V =
      ‖Vᗮ.starProjection ∘L U.starProjection‖ from rfl]
    exact norm_nonneg _
  have hcpos : 0 < c := lt_min (Real.sqrt_pos.mpr (by nlinarith)) one_pos
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hg0 (inv_nonneg.mpr hcpos.le)) fun y => ?_
  calc ‖tanAngleOperatorC U V hacute y‖
      = ‖sinAngleOperatorDirectedC U V
          ((cosAngleExtendedCEquiv U V hacute).symm y)‖ := rfl
    _ ≤ ‖sinAngleOperatorDirectedC U V‖ *
          ‖(cosAngleExtendedCEquiv U V hacute).symm y‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ directedGap U V * (c⁻¹ * ‖y‖) := by
        refine mul_le_mul ?_ ?_ (norm_nonneg _) hg0
        · rw [norm_sinAngleOperatorDirectedC]
        · exact norm_cosAngleExtendedCEquiv_symm_apply_le U V hacute y
    _ = directedGap U V * c⁻¹ * ‖y‖ := by ring

end TangentNormBounds

end DoubleAngleTangent

/-! ### Where the double-angle operator lives

**A recorded audit claim, refuted here.**  The source census carried a reasoned
-- not compiled -- counterexample asserting that in the two-dimensional
one-angle model `sinTwoAngleOperatorC U V` carries `sin 2θ` with multiplicity
two, "one from the `U` side and one from `Uᗮ`", while the directed ideal block
`sinTwoThetaIdealBlock U V` carries it once; and concluded from that that the
two objects are the paper's `Θ` and `Θ₀` and that any bridge between them pairs
the wrong two objects.

The multiplicity claim is false, and the reason is definitional.
`sinTwoAngleOperatorC` is built from `sinAngleOperatorDirectedC`, the modulus of
the *cross* product `P_{Vᗮ} P_U` -- not from the symmetric
`sinAngleOperatorC = |P_U - P_V|`.  The symmetric sine does have full rank in
that model, where it is `sin θ · 1`; the directed one annihilates `Uᗮ`
(`sinAngleOperatorDirectedC_apply_eq_zero_of_mem_orthogonal`, already in this
file), and so does every product with it on the left.

The two theorems below record the consequence in general, with no dimension
hypothesis: both the directed sine and the ambient double-angle operator have
range inside `U`, so the rank of either is at most `dim U` and no multiplicity
count separates them.  Whether the `Θ₀`/`Θ` bridge holds is therefore still
open; what is settled is that this argument does not refute it. -/

/-- **The directed sine operator is supported on `U`.** -/
theorem range_sinAngleOperatorDirectedC_le (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    LinearMap.range (sinAngleOperatorDirectedC U V : E →ₗ[ℂ] E) ≤ U := by
  rintro y ⟨x, rfl⟩
  have hmem : (sinAngleOperatorDirectedC U V : E →ₗ[ℂ] E) x ∈ Uᗮᗮ := by
    intro z hz
    simp only [ContinuousLinearMap.coe_coe]
    have hadj : ⟪z, sinAngleOperatorDirectedC U V x⟫_ℂ
        = ⟪sinAngleOperatorDirectedC U V z, x⟫_ℂ :=
      ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (isSelfAdjoint_sinAngleOperatorDirectedC U V)) z x).symm
    rw [hadj, sinAngleOperatorDirectedC_apply_eq_zero_of_mem_orthogonal U V hz,
      inner_zero_left]
  rwa [Submodule.orthogonal_orthogonal] at hmem

/-- **The ambient double-angle sine operator is supported on `U` too.**  In
particular its rank never exceeds `dim U`, so it cannot carry a singular value
with a multiplicity the directed block misses. -/
theorem range_sinTwoAngleOperatorC_le (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    LinearMap.range (sinTwoAngleOperatorC U V : E →ₗ[ℂ] E) ≤ U := by
  rintro y ⟨x, rfl⟩
  have hval : (sinTwoAngleOperatorC U V : E →ₗ[ℂ] E) x
      = (2 : ℝ) • sinAngleOperatorDirectedC U V (cosAngleOperatorC U V x) := rfl
  rw [hval]
  exact U.smul_mem _
    (range_sinAngleOperatorDirectedC_le U V ⟨cosAngleOperatorC U V x, rfl⟩)

end DavisKahanExt
end TauCeti
