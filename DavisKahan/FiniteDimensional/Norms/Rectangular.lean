/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import ForTauCeti.Analysis.InnerProductSpace.SchattenNorm
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Rectangular Schatten compatibility module

The finite-dimensional rectangular Schatten construction has moved to the
canonical reusable module
`ForMathlib.Analysis.InnerProductSpace.SchattenNorm`.

This import preserves the historical experimental module path while exposing
the same `RectangularUnitarilyInvariantSeminorm.schatten` and `mem_schatten`
interface to downstream files.
-/

namespace TauCeti
namespace RectangularUnitarilyInvariantSeminorm

open scoped InnerProductSpace BigOperators
open Module (finrank)

universe uE uF

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Extend a coherent square UI-norm family to rectangular maps by the
standard orthogonal zero extension.  This useful historical bridge is retained
alongside the intrinsic singular-value construction. -/
noncomputable def ofSquareFamily
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F]
    (Ns : ∀ (H : Type (max uE uF)) [NormedAddCommGroup H]
      [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H],
      UnitarilyInvariantSeminorm 𝕜 H) :
    RectangularUnitarilyInvariantSeminorm 𝕜 E F where
  toFun A := Ns (WithLp 2 (E × F)) (zeroExtension A)
  add_le' A B := by
    rw [zeroExtension_add]
    exact (Ns (WithLp 2 (E × F))).add_le _ _
  smul' a A := by
    rw [zeroExtension_smul]
    exact (Ns (WithLp 2 (E × F))).smul' a _
  invariant' U V A := by
    let UV : WithLp 2 (E × F) ≃ₗᵢ[𝕜] WithLp 2 (E × F) :=
      LinearIsometryEquiv.withLpProdCongr 2 V.symm U
    have hzero : zeroExtension
        (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) =
      UV.toLinearMap ∘ₗ zeroExtension A ∘ₗ UV.symm.toLinearMap := by
      ext z
      simp [UV]
    rw [hzero]
    exact (Ns (WithLp 2 (E × F))).invariant UV UV.symm _

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Historical finite-dimensional rectangular Schatten declaration.  Its
implementation is the canonical production construction. -/
noncomputable def schatten (p : ℝ) (hp : 1 ≤ p) :
    RectangularUnitarilyInvariantSeminorm 𝕜 E F where
  toFun A := schattenNorm (𝕜 := 𝕜) (E := E) (F := F) p hp A
  add_le' A B := schattenNorm_add_le p hp A B
  smul' a A := schattenNorm_smul p hp a A
  invariant' U V A := schattenNorm_invariant p hp U V A

/-- Historical name retained for the gated rectangular-norm target. -/
theorem mem_schatten (p : ℝ) (hp : 1 ≤ p) (A : E →ₗ[𝕜] F) :
    0 ≤ schatten (𝕜 := 𝕜) (E := E) (F := F) p hp A := by
  change 0 ≤ schattenNorm (𝕜 := 𝕜) (E := E) (F := F) p hp A
  exact schattenNorm_nonneg p hp A

end RectangularUnitarilyInvariantSeminorm
end TauCeti