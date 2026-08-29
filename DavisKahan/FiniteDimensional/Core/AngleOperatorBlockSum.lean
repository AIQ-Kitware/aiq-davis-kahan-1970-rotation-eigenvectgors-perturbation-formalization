/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/
import DavisKahan.FiniteDimensional.Core.AngleOperators
import ForTauCeti.Analysis.InnerProductSpace.AngleGeometryBlockSum

/-!
# Finite angle operators on orthogonal block sums

The canonical finite angle operator and its totalized tangent functions preserve orthogonal direct
sums.  The sine-angle statement lives in `ForTauCeti`; this file lifts that paper-independent
operator geometry through the Davis--Kahan finite functional-calculus definitions of `Theta`,
`tan Theta`, and `tan (2 Theta)`.
-/

namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The canonical finite angle operator preserves orthogonal direct sums. -/
theorem angleOperator_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ V₁ : Submodule 𝕜 E₁) (U₂ V₂ : Submodule 𝕜 E₂) :
    angleOperator
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum
        (angleOperator U₁ V₁) (angleOperator U₂ V₂) := by
  let S₁ := sinAngleOperator U₁ V₁
  let S₂ := sinAngleOperator U₂ V₂
  have hS₁ : S₁.IsSymmetric := by
    dsimp only [S₁]
    rw [TauCeti.sinAngleOperator_eq_operatorAbs]
    exact (TauCeti.isPositive_operatorAbs (projection U₁ - projection V₁)).isSymmetric
  have hS₂ : S₂.IsSymmetric := by
    dsimp only [S₂]
    rw [TauCeti.sinAngleOperator_eq_operatorAbs]
    exact (TauCeti.isPositive_operatorAbs (projection U₂ - projection V₂)).isSymmetric
  let hblock :=
    RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric hS₁ hS₂
  have hsin :
      sinAngleOperator
          (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
          (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
        RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum S₁ S₂ :=
    TauCeti.sinAngleOperator_orthogonalBlockSumSubmodule U₁ V₁ U₂ V₂
  have hsum : LinearMap.IsSymmetric
      (sinAngleOperator
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂)) := by
    rw [hsin]
    exact hblock
  calc
    angleOperator
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      TauCeti.selfAdjointFunctionalCalculus hblock Real.arcsin := by
        unfold angleOperator
        exact TauCeti.selfAdjointFunctionalCalculus_congr_op hsum hblock hsin Real.arcsin
    _ = RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum
          (TauCeti.selfAdjointFunctionalCalculus hS₁ Real.arcsin)
          (TauCeti.selfAdjointFunctionalCalculus hS₂ Real.arcsin) :=
      TauCeti.selfAdjointFunctionalCalculus_orthogonalBlockSum hS₁ hS₂ Real.arcsin
    _ = RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum
          (angleOperator U₁ V₁) (angleOperator U₂ V₂) := rfl

/-- The canonical finite `tan Theta` operator preserves orthogonal direct sums. -/
theorem tanAngleOperator_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ V₁ : Submodule 𝕜 E₁) (U₂ V₂ : Submodule 𝕜 E₂) :
    tanAngleOperator
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum
        (tanAngleOperator U₁ V₁) (tanAngleOperator U₂ V₂) := by
  have hangle := angleOperator_orthogonalBlockSumSubmodule U₁ V₁ U₂ V₂
  have hA₁ : (angleOperator U₁ V₁).IsSymmetric := by
    unfold angleOperator
    exact TauCeti.selfAdjointFunctionalCalculus_isSymmetric _ _
  have hA₂ : (angleOperator U₂ V₂).IsSymmetric := by
    unfold angleOperator
    exact TauCeti.selfAdjointFunctionalCalculus_isSymmetric _ _
  let hblock :=
    RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric hA₁ hA₂
  have hsum : LinearMap.IsSymmetric
      (angleOperator
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂)) := by
    unfold angleOperator
    exact TauCeti.selfAdjointFunctionalCalculus_isSymmetric _ _
  calc
    tanAngleOperator
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      TauCeti.selfAdjointFunctionalCalculus hblock safeTan := by
        unfold tanAngleOperator
        exact TauCeti.selfAdjointFunctionalCalculus_congr_op hsum hblock hangle safeTan
    _ = RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum
          (TauCeti.selfAdjointFunctionalCalculus hA₁ safeTan)
          (TauCeti.selfAdjointFunctionalCalculus hA₂ safeTan) :=
      TauCeti.selfAdjointFunctionalCalculus_orthogonalBlockSum hA₁ hA₂ safeTan
    _ = RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum
          (tanAngleOperator U₁ V₁) (tanAngleOperator U₂ V₂) := rfl

/-- The canonical finite `tan (2 Theta)` operator preserves orthogonal direct sums. -/
theorem tanTwoAngleOperator_orthogonalBlockSumSubmodule
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    (U₁ V₁ : Submodule 𝕜 E₁) (U₂ V₂ : Submodule 𝕜 E₂) :
    tanTwoAngleOperator
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum
        (tanTwoAngleOperator U₁ V₁) (tanTwoAngleOperator U₂ V₂) := by
  have hangle := angleOperator_orthogonalBlockSumSubmodule U₁ V₁ U₂ V₂
  have hA₁ : (angleOperator U₁ V₁).IsSymmetric := by
    unfold angleOperator
    exact TauCeti.selfAdjointFunctionalCalculus_isSymmetric _ _
  have hA₂ : (angleOperator U₂ V₂).IsSymmetric := by
    unfold angleOperator
    exact TauCeti.selfAdjointFunctionalCalculus_isSymmetric _ _
  let hblock :=
    RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric hA₁ hA₂
  have hsum : LinearMap.IsSymmetric
      (angleOperator
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂)) := by
    unfold angleOperator
    exact TauCeti.selfAdjointFunctionalCalculus_isSymmetric _ _
  calc
    tanTwoAngleOperator
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule U₁ U₂)
        (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule V₁ V₂) =
      TauCeti.selfAdjointFunctionalCalculus hblock safeTanTwo := by
        unfold tanTwoAngleOperator
        exact TauCeti.selfAdjointFunctionalCalculus_congr_op hsum hblock hangle safeTanTwo
    _ = RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum
          (TauCeti.selfAdjointFunctionalCalculus hA₁ safeTanTwo)
          (TauCeti.selfAdjointFunctionalCalculus hA₂ safeTanTwo) :=
      TauCeti.selfAdjointFunctionalCalculus_orthogonalBlockSum hA₁ hA₂ safeTanTwo
    _ = RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum
          (tanTwoAngleOperator U₁ V₁) (tanTwoAngleOperator U₂ V₂) := rfl

end DavisKahanTheory
end TauCeti
