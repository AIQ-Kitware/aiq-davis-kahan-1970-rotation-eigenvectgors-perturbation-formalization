/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
import DavisKahan.OperatorIdeal.CanonicalRealView
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm

/-!
# Projection-block lemmas from Davis--Kahan section 6

This file formalizes the two elementary projection lemmas used verbatim in the
paper's proof of the symmetric sine theorem.

* `paperDiagonalPair` is `Omega K Gamma + OmegaComplement K GammaComplement`.
  Its reflection identity is the displayed proof of Lemma 6.2.
* `paperCrossSineSum` is the sum of the two complementary cross projections.
  Right composition by the target reflection turns it into the projector
  difference.  Since the reflection is an involutive isometry, the two
  operators have identical complete approximation-singular-value sequences.

The results are proved both for the existing ideal-family interface and for the
literal paper norm represented by `PaperUnitaryInvariantNorm`.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The pair of diagonal projection blocks from Davis--Kahan Lemma 6.2. -/
def paperDiagonalPair (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (K : E →L[𝕜] E) : E →L[𝕜] E :=
  U.starProjection ∘L K ∘L V.starProjection +
    Uᗮ.starProjection ∘L K ∘L Vᗮ.starProjection

omit [CompleteSpace E] in
/-- The reflection identity displayed in the proof of Davis--Kahan Lemma 6.2. -/
theorem two_smul_paperDiagonalPair_eq_add_reflections
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    (2 : 𝕜) • paperDiagonalPair U V K =
      K + U.reflectionOperator ∘L K ∘L V.reflectionOperator := by
  ext x
  simp only [paperDiagonalPair, ContinuousLinearMap.comp_apply, add_apply,
    smul_apply]
  simp_rw [Submodule.starProjection_orthogonal_apply,
    Submodule.reflectionOperator_apply]
  simp only [map_sub, map_smul]
  module

/-- Ideal membership for the diagonal pair. -/
theorem paperDiagonalPair_mem
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {K : E →L[𝕜] E} (hK : N.Mem K) :
    N.Mem (paperDiagonalPair U V K) := by
  exact N.add_mem
    (N.comp_mem U.starProjection V.starProjection hK)
    (N.comp_mem Uᗮ.starProjection Vᗮ.starProjection hK)

/-- **Davis--Kahan Lemma 6.2 for an arbitrary rectangular symmetric ideal.** -/
theorem paperDiagonalPair_gauge_le
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {K : E →L[𝕜] E} (hK : N.Mem K) :
    N.gaugeReal (paperDiagonalPair U V K) ≤ N.gaugeReal K := by
  have hB : N.Mem (paperDiagonalPair U V K) :=
    paperDiagonalPair_mem N U V hK
  have hJ : N.Mem
      (U.reflectionOperator ∘L K ∘L V.reflectionOperator) :=
    N.comp_mem U.reflectionOperator V.reflectionOperator hK
  have hJle :
      N.gaugeReal (U.reflectionOperator ∘L K ∘L V.reflectionOperator) ≤
        N.gaugeReal K :=
    N.gaugeReal_comp_le_of_contractions _ _ hK
      (Submodule.norm_reflectionOperator_le_one U)
      (Submodule.norm_reflectionOperator_le_one V)
  have hsum : N.gaugeReal
      (K + U.reflectionOperator ∘L K ∘L V.reflectionOperator) ≤
        N.gaugeReal K + N.gaugeReal
          (U.reflectionOperator ∘L K ∘L V.reflectionOperator) :=
    N.gaugeReal_add_le hK hJ
  have htwo : N.gaugeReal ((2 : 𝕜) • paperDiagonalPair U V K) =
      2 * N.gaugeReal (paperDiagonalPair U V K) := by
    rw [N.gaugeReal_smul (2 : 𝕜) hB]
    norm_num
  rw [← two_smul_paperDiagonalPair_eq_add_reflections U V K, htwo] at hsum
  linarith

/-- Lemma 6.2 simultaneously for every finite Ky Fan approximation gauge. -/
theorem paperDiagonalPair_all_kyFan_le
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    ∀ k : ℕ,
      kyFanApproximationGauge k (paperDiagonalPair U V K) ≤
        kyFanApproximationGauge k K := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    let N := KyFanDominantIdealFamily.kyFan (𝕜 := 𝕜) k hk
    have h := paperDiagonalPair_gauge_le
      N.toSymmetricOperatorIdealFamily U V
      (KyFanDominantIdealFamily.kyFan_mem (𝕜 := 𝕜) k hk K)
    simpa only [N,
      KyFanDominantIdealFamily.kyFan_gauge] using h

/-- Literal source-norm form of Davis--Kahan Lemma 6.2. -/
theorem paperDiagonalPair_paperNorm_le
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    (N : PaperUnitaryInvariantNorm)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    N.extendedGauge (paperDiagonalPair U V K) ≤ N.extendedGauge K :=
  N.extendedGauge_le_of_all_kyFan_le
    (paperDiagonalPair_all_kyFan_le U V K)

/-- Real-valued source-norm form on the canonical ideal. -/
theorem paperDiagonalPair_paperGauge_le
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    (N : PaperUnitaryInvariantNorm)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {K : E →L[𝕜] E} (hK : N.Mem K) :
    N.Mem (paperDiagonalPair U V K) ∧
      N.gauge (paperDiagonalPair U V K) ≤ N.gauge K := by
  have hle := paperDiagonalPair_paperNorm_le N U V K
  have hB : N.Mem (paperDiagonalPair U V K) := by
    intro htop
    rw [htop] at hle
    exact hK (top_le_iff.mp hle)
  refine ⟨hB, ?_⟩
  show (N.extendedGauge (paperDiagonalPair U V K)).toReal ≤
    (N.extendedGauge K).toReal
  exact (ENNReal.toReal_le_toReal hB hK).mpr hle

/-- Right composition with a subspace reflection preserves every approximation
singular value. -/
theorem sameApproximationSingularValues_comp_reflection_right
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) :
    SameApproximationSingularValues
      (A ∘L U.reflectionOperator) A := by
  intro n
  have hnn : ‖(U.reflectionOperator : E →L[𝕜] E)‖ ≤ 1 := by
    exact_mod_cast Submodule.norm_reflectionOperator_le_one U
  have hright (T : E →L[𝕜] E) :
      (T ∘L U.reflectionOperator).approximationNumber n ≤
        T.approximationNumber n :=
    calc (T ∘L U.reflectionOperator).approximationNumber n
        ≤ T.approximationNumber n *
            ‖(U.reflectionOperator : E →L[𝕜] E)‖ :=
          T.approximationNumber_comp_le_mul_norm _ n
      _ ≤ T.approximationNumber n * 1 := by
        gcongr
        first
          | assumption
          | simpa using ContinuousLinearMap.approximationNumber_nonneg _ _
      _ = T.approximationNumber n := mul_one _
  have hcomp :
      (A ∘L U.reflectionOperator) ∘L U.reflectionOperator = A := by
    rw [ContinuousLinearMap.comp_assoc, U.reflectionOperator_involutive,
      ContinuousLinearMap.comp_id]
  have key : (A ∘L U.reflectionOperator).approximationNumber n
      = A.approximationNumber n := by
    refine le_antisymm (hright A) ?_
    calc A.approximationNumber n
        = ((A ∘L U.reflectionOperator) ∘L
            U.reflectionOperator).approximationNumber n := by rw [hcomp]
      _ ≤ (A ∘L U.reflectionOperator).approximationNumber n :=
          hright (A ∘L U.reflectionOperator)
  exact key

/-- Left composition with a subspace reflection preserves every approximation
singular value. -/
theorem sameApproximationSingularValues_comp_reflection_left
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) :
    SameApproximationSingularValues
      (U.reflectionOperator ∘L A) A := by
  intro n
  have hnn : ‖(U.reflectionOperator : E →L[𝕜] E)‖ ≤ 1 := by
    exact_mod_cast Submodule.norm_reflectionOperator_le_one U
  have hleft (T : E →L[𝕜] E) :
      (U.reflectionOperator ∘L T).approximationNumber n ≤
        T.approximationNumber n :=
    calc (U.reflectionOperator ∘L T).approximationNumber n
        ≤ ‖(U.reflectionOperator : E →L[𝕜] E)‖ *
            T.approximationNumber n :=
          ContinuousLinearMap.approximationNumber_comp_le_norm_mul _ T n
      _ ≤ 1 * T.approximationNumber n := by
        gcongr
        first
          | assumption
          | simpa using ContinuousLinearMap.approximationNumber_nonneg _ _
      _ = T.approximationNumber n := one_mul _
  have hcomp :
      U.reflectionOperator ∘L (U.reflectionOperator ∘L A) = A := by
    rw [← ContinuousLinearMap.comp_assoc, U.reflectionOperator_involutive,
      ContinuousLinearMap.id_comp]
  have key : (U.reflectionOperator ∘L A).approximationNumber n
      = A.approximationNumber n := by
    refine le_antisymm (hleft A) ?_
    calc A.approximationNumber n
        = (U.reflectionOperator ∘L
            (U.reflectionOperator ∘L A)).approximationNumber n := by rw [hcomp]
      _ ≤ (U.reflectionOperator ∘L A).approximationNumber n :=
          hleft (U.reflectionOperator ∘L A)
  exact key

/-- Sum of the two cross-projection blocks appearing in Proposition 6.1. -/
def paperCrossSineSum (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  Uᗮ.starProjection ∘L V.starProjection +
    U.starProjection ∘L Vᗮ.starProjection

omit [CompleteSpace E] in
/-- The cross-block sum is the projector difference followed by the target
reflection. -/
theorem paperCrossSineSum_eq_projectionDiff_comp_reflection
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperCrossSineSum U V =
      (V.starProjection - U.starProjection) ∘L V.reflectionOperator := by
  ext x
  simp only [paperCrossSineSum, ContinuousLinearMap.comp_apply, add_apply,
    sub_apply]
  rw [Submodule.reflectionOperator_apply]
  simp_rw [Submodule.starProjection_orthogonal_apply]
  simp only [map_sub, map_smul]
  have hVidem : V.starProjection (V.starProjection x) = V.starProjection x :=
    congrArg (fun T : E →L[𝕜] E => T x) V.isIdempotentElem_starProjection
  have hUadd := U.starProjection_add_starProjection_orthogonal
    (V.starProjection x)
  rw [hVidem]
  module

/-- The cross-block sum has exactly the complete singular-value sequence of the
projector difference. -/
theorem paperCrossSineSum_same_projectionDiff
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularValues
      (paperCrossSineSum U V) (V.starProjection - U.starProjection) := by
  rw [paperCrossSineSum_eq_projectionDiff_comp_reflection]
  exact sameApproximationSingularValues_comp_reflection_right V _

end

end ExactSinTheta
end DavisKahan
end TauCeti