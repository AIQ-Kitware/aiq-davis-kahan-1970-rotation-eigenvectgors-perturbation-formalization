/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.CosineAngle
import DavisKahan.OperatorIdeal.ApproximationNumbers.BlockSum
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.HeterogeneousRepresentative
import DavisKahan.Sources.DavisKahan1970.SineTheta.ProjectionBlocks

/-!
# The full operator angle printed in Davis--Kahan 1970

The paper defines two directed coordinate angles and then sets
`Theta = diag(Theta_0, Theta_1)`.  This file implements that literal block
operator on the orthogonal coordinate decomposition of the first subspace.
Its sine is the corresponding block sum.  A unitary coordinate change and the
cross-block identity show that its complete singular-value sequence is exactly
that of the projector difference.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A subspace admitting an orthogonal projection inside a complete ambient
space is itself complete.  `local instance` does not propagate through imports,
so it is reinstalled here. -/
local instance instCompleteSpaceCoeOfHasOrthogonalProjectionFullAngle
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-- `Theta = diag(Theta_0,Theta_1)` on the source orthogonal coordinates. -/
noncomputable def paperSourceFullAngleC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    WithLp 2 (U × Uᗮ) →L[ℂ] WithLp 2 (U × Uᗮ) :=
  continuousOrthogonalBlockSum
    (paperSourceDirectedAngleC U V)
    (paperSourceDirectedAngleC Uᗮ Vᗮ)

/-- The literal block-diagonal `sin Theta`. -/
noncomputable def paperSourceFullSinC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    WithLp 2 (U × Uᗮ) →L[ℂ] WithLp 2 (U × Uᗮ) :=
  continuousOrthogonalBlockSum
    (paperSourceDirectedSinC U V)
    (paperSourceDirectedSinC Uᗮ Vᗮ)

/-- The cross projection sum in coordinates of `U` and `V complement`. -/
noncomputable def paperSourceCrossBlockSumC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    WithLp 2 (U × Uᗮ) →L[ℂ] WithLp 2 (Vᗮ × (Vᗮ)ᗮ) :=
  continuousOrthogonalBlockSum
    (paperSineBlockC U V)
    (paperSineBlockC Uᗮ Vᗮ)

/-- The literal full sine and the coordinate cross-block sum have identical
complete singular-value sequences. -/
theorem paperSourceFullSin_same_coordinateCrossBlockSum
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularSequence
      (paperSourceFullSinC U V) (paperSourceCrossBlockSumC U V) := by
  exact sameApproximationSingularSequence_continuousOrthogonalBlockSum
    (paperSourceDirectedSin_same_paperSineBlock U V)
    (paperSourceDirectedSin_same_paperSineBlock Uᗮ Vᗮ)

/-- The coordinate cross-block sum is unitarily equivalent to the ambient
cross sum printed in the paper. -/
theorem paperSourceCrossBlockSum_same_ambientCrossSum
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularSequence
      (paperSourceCrossBlockSumC U V) (paperCrossSineSum V U) := by
  let Udom : E ≃ₗᵢ[ℂ] WithLp 2 (U × Uᗮ) := U.orthogonalDecomposition
  let Vcod : E ≃ₗᵢ[ℂ] WithLp 2 (Vᗮ × (Vᗮ)ᗮ) := Vᗮ.orthogonalDecomposition
  have hfactor :
      Vcod.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          paperCrossSineSum V U ∘L
          Udom.symm.toContinuousLinearEquiv.toContinuousLinearMap =
        paperSourceCrossBlockSumC U V := by
    ext x
    apply WithLp.ofLp_injective 2
    -- `orthogonalDecomposition` carries its own `simp` lemmas for application
    -- and inverse application; unfolding the definition would defeat them and
    -- expose the raw `prodEquivOfIsCompl`.
    -- The second coordinate lies in `Uᗮ`, so its `U`-projection vanishes, and
    -- anything already in `V` has vanishing `Vᗮ`-projection.
    have hUb : U.orthogonalProjectionOnto (↑x.snd : E) = 0 :=
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal x.snd.2
    have hUbStar : U.starProjection (↑x.snd : E) = 0 := by
      rw [Submodule.starProjection_apply, hUb, Submodule.coe_zero]
    -- Anything already in `V` is annihilated by the projection onto `Vᗮ`.
    have hV1 : ∀ z : E, Vᗮ.orthogonalProjectionOnto (V.starProjection z) = 0 := by
      intro z
      refine Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal ?_
      rw [Submodule.orthogonal_orthogonal]
      exact V.starProjection_apply_mem z
    -- On `Vᗮᗮ` the `V`-projection is invisible: the discarded part lies in `Vᗮ`.
    have hV2 : ∀ z : E,
        Vᗮᗮ.orthogonalProjectionOnto (V.starProjection z) =
          Vᗮᗮ.orthogonalProjectionOnto z := by
      intro z
      have hmem : z - V.starProjection z ∈ Vᗮᗮᗮ := by
        rw [Submodule.orthogonal_orthogonal]
        exact Submodule.sub_starProjection_mem_orthogonal z
      have hzero :=
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (K := Vᗮᗮ) hmem
      rw [map_sub] at hzero
      exact (sub_eq_zero.mp hzero).symm
    simp [paperSourceCrossBlockSumC, paperSineBlockC,
      paperCrossSineSum, Udom, Vcod, Submodule.adjoint_subtypeL,
      hUbStar, hV1, hV2]
  exact (SameApproximationSingularValues.of_isometricEquiv_comp
    Vcod Udom hfactor).symm

/-- The paper's literal full `sin Theta` has exactly the singular values of
`P_U-P_V`. -/
theorem paperSourceFullSin_same_projectionDifference
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularSequence
      (paperSourceFullSinC U V) (U.starProjection - V.starProjection) := by
  exact (paperSourceFullSin_same_coordinateCrossBlockSum U V).trans
    ((paperSourceCrossBlockSum_same_ambientCrossSum U V).trans
      (paperCrossSineSum_same_projectionDiff V U))

/-- Every source norm gives the same value to the literal full angle sine and
the projector difference. -/
theorem paperSourceFullSin_mem_iff_and_gauge_eq
    (N : PaperUnitaryInvariantNorm)
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (N.Mem (paperSourceFullSinC U V) ↔
      N.Mem (U.starProjection - V.starProjection)) ∧
    N.gauge (paperSourceFullSinC U V) =
      N.gauge (U.starProjection - V.starProjection) :=
  (paperSourceFullSin_same_projectionDifference U V).paperMem_iff_and_gauge_eq N

end

end ExactSinTheta
end DavisKahan
end TauCeti