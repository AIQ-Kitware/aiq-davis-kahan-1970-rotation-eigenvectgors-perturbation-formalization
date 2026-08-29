/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.OperatorIdeal.ApproximationNumbers.OperatorModulus
import DavisKahan.Sources.DavisKahan1970.SineTheta.OperatorAngleBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# The source definition of the directed Davis--Kahan angle

The paper defines `Theta_0` from the cosine block, not from a previously named
sine block.  If `U` is the trial subspace and `V` is the exact subspace, the
cosine block is the overlap map from `U` to `V`; its positive source modulus is
`cos Theta_0`.  The angle is `arccos (cos Theta_0)` on the coordinate Hilbert
space `U`.

This module keeps the coordinate space explicit.  In particular, it does not
extend the cosine modulus by zero to the ambient orthogonal complement, where
`arccos 0 = pi/2` would create spurious angles.  It then proves that applying
sine to the source-defined angle has the complete singular-value sequence of
the cross projection into `V`'s orthogonal complement.
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
so it is reinstalled here.

Every adjoint below is taken on a subspace coordinate space, so without this
the whole module fails to elaborate. -/
local instance instCompleteSpaceCoeOfHasOrthogonalProjectionCosineAngle
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-- The bounded operators on a subspace coordinate space, as a C⋆-algebra.

This is `inferInstance`, but stating it in the submodule shape is load-bearing.
Searching for `ContinuousFunctionalCalculus` on `↥U →L[ℂ] ↥U` does not find the
C⋆-algebra structure on its own, even though the very same search succeeds for
an abstract complete complex inner-product space and the C⋆-algebra instance is
found when requested directly.  Recording it here as a local instance lets the
functional calculus below elaborate; without it every `cfc` in this module
fails. -/
noncomputable local instance instCStarAlgebraSubspaceCoordinateCosineAngle
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] :
    CStarAlgebra (↥U →L[ℂ] ↥U) :=
  inferInstance

/-- The overlap block whose singular values are the principal cosines. -/
noncomputable def paperCosineBlockC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] V :=
  V.subtypeL.adjoint ∘L U.subtypeL

/-- The complementary overlap block whose singular values are the directed
principal sines. -/
noncomputable def paperSineBlockC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] Vᗮ :=
  Vᗮ.subtypeL.adjoint ∘L U.subtypeL

/-- The positive cosine operator on the trial coordinate space. -/
noncomputable def paperCosineModulusC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  ContinuousLinearMap.modulus (paperCosineBlockC U V)

/-- The positive directed sine modulus on the trial coordinate space. -/
noncomputable def paperSineModulusC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  ContinuousLinearMap.modulus (paperSineBlockC U V)

/-- The cosine modulus is a positive contraction. -/
theorem norm_paperCosineModulusC_le_one
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖paperCosineModulusC U V‖ ≤ 1 := by
  rw [paperCosineModulusC]
  calc
    ‖ContinuousLinearMap.modulus (paperCosineBlockC U V)‖ =
        ‖paperCosineBlockC U V‖ := ContinuousLinearMap.norm_modulus _
    _ ≤ ‖V.subtypeL.adjoint‖ * ‖U.subtypeL‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := by
      have hV : ‖V.subtypeL.adjoint‖ ≤ 1 := by
        rw [Submodule.adjoint_subtypeL]
        exact V.orthogonalProjectionOnto_norm_le
      exact mul_le_mul hV U.norm_subtypeL_le
        (norm_nonneg U.subtypeL) zero_le_one
    _ = 1 := by ring

/-- The real spectrum of the cosine modulus lies in `[0,1]`. -/
theorem spectrum_paperCosineModulusC_subset_Icc
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (paperCosineModulusC U V) ⊆ Set.Icc 0 1 := by
  intro x hx
  refine ⟨spectrum_nonneg_of_nonneg
    (ContinuousLinearMap.modulus_nonneg (paperCosineBlockC U V)) hx, ?_⟩
  -- `spectrum.norm_le_norm_of_mem` would need `NormOneClass`, i.e. `‖id‖ = 1`,
  -- which fails when `U` is the zero subspace.  The `mul` form carries no such
  -- instance, and `norm_id_le` bounds the unit without nontriviality.
  have hone : ‖(1 : ↥U →L[ℂ] ↥U)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have habs : ‖x‖ ≤ ‖paperCosineModulusC U V‖ * ‖(1 : ↥U →L[ℂ] ↥U)‖ :=
    spectrum.norm_le_norm_mul_of_mem hx
  rw [Real.norm_eq_abs] at habs
  refine (le_abs_self x).trans (habs.trans ?_)
  calc
    ‖paperCosineModulusC U V‖ * ‖(1 : ↥U →L[ℂ] ↥U)‖ ≤ 1 * 1 :=
      mul_le_mul (norm_paperCosineModulusC_le_one U V) hone
        (norm_nonneg _) zero_le_one
    _ = 1 := by ring

/-- The literal directed angle of Section 1 and Section 6 of the paper. -/
noncomputable def paperSourceDirectedAngleC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  cfc Real.arccos (paperCosineModulusC U V)

/-- The paper's literal `cos Theta_0`. -/
noncomputable def paperSourceDirectedCosC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  cfc Real.cos (paperSourceDirectedAngleC U V)

/-- The paper's literal `sin Theta_0`. -/
noncomputable def paperSourceDirectedSinC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  cfc Real.sin (paperSourceDirectedAngleC U V)

/-- Applying cosine to the source-defined angle recovers the overlap modulus. -/
theorem paperSourceDirectedCosC_eq
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSourceDirectedCosC U V = paperCosineModulusC U V := by
  have hsa : IsSelfAdjoint (paperCosineModulusC U V) :=
    ContinuousLinearMap.modulus_isSelfAdjoint _
  rw [paperSourceDirectedCosC, paperSourceDirectedAngleC,
    ← cfc_comp Real.cos Real.arccos (paperCosineModulusC U V)
      hsa Real.continuous_cos.continuousOn
      Real.continuous_arccos.continuousOn]
  calc
    cfc (Real.cos ∘ Real.arccos) (paperCosineModulusC U V) =
        cfc (fun x : ℝ => x) (paperCosineModulusC U V) := by
      apply cfc_congr
      intro x hx
      have hxi := spectrum_paperCosineModulusC_subset_Icc U V hx
      exact Real.cos_arccos (by linarith [hxi.1]) hxi.2
    _ = paperCosineModulusC U V := cfc_id' ℝ _

/-- Operator Pythagoras on the trial coordinate space. -/
theorem paperSineModulus_sq_add_paperCosineModulus_sq
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSineModulusC U V * paperSineModulusC U V +
      paperCosineModulusC U V * paperCosineModulusC U V =
        ContinuousLinearMap.id ℂ U := by
  rw [paperSineModulusC, paperCosineModulusC,
    ContinuousLinearMap.modulus_mul_self,
    ContinuousLinearMap.modulus_mul_self]
  ext x
  -- The adjoint of a projection onto the subtype is the inclusion.
  have hadjPerp : (Vᗮ.orthogonalProjectionOnto).adjoint = Vᗮ.subtypeL := by
    rw [← Submodule.adjoint_subtypeL, ContinuousLinearMap.adjoint_adjoint]
  have hadjV : (V.orthogonalProjectionOnto).adjoint = V.subtypeL := by
    rw [← Submodule.adjoint_subtypeL, ContinuousLinearMap.adjoint_adjoint]
  have hsplit : Vᗮ.starProjection (x : E) + V.starProjection (x : E) = (x : E) := by
    simp [add_comm]
  have hUx : U.starProjection (x : E) = (x : E) :=
    Submodule.starProjection_eq_self_iff.mpr x.2
  simp only [paperSineBlockC, paperCosineBlockC, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.id_apply, Submodule.adjoint_subtypeL,
    hadjPerp, hadjV, Submodule.coe_add]
  -- Both summands are `U`'s projection of a piece of the `V`/`Vᗮ` splitting.
  change U.starProjection (Vᗮ.starProjection (x : E)) +
      U.starProjection (V.starProjection (x : E)) = (x : E)
  rw [← map_add, hsplit, hUx]

set_option maxHeartbeats 1000000 in
/-- The source-defined sine is the positive square root complementary to the
cosine modulus. -/
theorem paperSourceDirectedSinC_eq_paperSineModulusC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSourceDirectedSinC U V = paperSineModulusC U V := by
  have hsaCos : IsSelfAdjoint (paperCosineModulusC U V) :=
    ContinuousLinearMap.modulus_isSelfAdjoint _
  -- The spectrum of the angle is the arccosine image of the modulus spectrum,
  -- by the spectral mapping theorem.
  have hspec : spectrum ℝ (paperSourceDirectedAngleC U V) =
      Real.arccos '' spectrum ℝ (paperCosineModulusC U V) := by
    rw [paperSourceDirectedAngleC]
    exact cfc_map_spectrum Real.arccos (paperCosineModulusC U V) hsaCos
      Real.continuous_arccos.continuousOn
  have hnonneg : 0 ≤ paperSourceDirectedSinC U V := by
    rw [paperSourceDirectedSinC]
    apply cfc_nonneg
    intro x hx
    rw [hspec] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact Real.sin_nonneg_of_nonneg_of_le_pi
      (Real.arccos_nonneg y) (Real.arccos_le_pi y)
  have hsquare :
      paperSourceDirectedSinC U V * paperSourceDirectedSinC U V =
        (paperSineBlockC U V).adjoint ∘L paperSineBlockC U V := by
    rw [paperSourceDirectedSinC, ← cfc_mul _ _ _
      Real.continuous_sin.continuousOn Real.continuous_sin.continuousOn]
    have htrig :
        cfc (fun x : ℝ => Real.sin x * Real.sin x)
            (paperSourceDirectedAngleC U V) =
          ContinuousLinearMap.id ℂ U -
            paperCosineModulusC U V * paperCosineModulusC U V := by
      have hangle : IsSelfAdjoint (paperSourceDirectedAngleC U V) :=
        cfc_predicate Real.arccos (paperCosineModulusC U V)
      -- Name both functions in eta-expanded form: supplying only the
      -- continuity proofs would pin `g` to `Real.cos * Real.cos`, which does
      -- not match the eta-expanded `fun x => Real.cos x * Real.cos x` in the
      -- goal, and the rewrite would not fire.
      have hcos : paperCosineModulusC U V * paperCosineModulusC U V =
          cfc (fun x : ℝ => Real.cos x * Real.cos x)
            (paperSourceDirectedAngleC U V) := by
        rw [← paperSourceDirectedCosC_eq U V, paperSourceDirectedCosC]
        exact (cfc_mul Real.cos Real.cos (paperSourceDirectedAngleC U V)
          Real.continuous_cos.continuousOn
          Real.continuous_cos.continuousOn).symm
      have hone : (ContinuousLinearMap.id ℂ U) =
          cfc (fun _ : ℝ => (1 : ℝ)) (paperSourceDirectedAngleC U V) :=
        (cfc_const_one ℝ (paperSourceDirectedAngleC U V) hangle).symm
      have hsplit :
          cfc (fun x : ℝ => (1 : ℝ) - Real.cos x * Real.cos x)
              (paperSourceDirectedAngleC U V) =
            cfc (fun _ : ℝ => (1 : ℝ)) (paperSourceDirectedAngleC U V) -
              cfc (fun x : ℝ => Real.cos x * Real.cos x)
                (paperSourceDirectedAngleC U V) :=
        cfc_sub (fun _ : ℝ => (1 : ℝ))
          (fun x : ℝ => Real.cos x * Real.cos x)
          (paperSourceDirectedAngleC U V)
          continuous_const.continuousOn
          (Real.continuous_cos.mul Real.continuous_cos).continuousOn
      rw [hcos, hone, ← hsplit]
      apply cfc_congr
      intro x _
      nlinarith [Real.sin_sq_add_cos_sq x]
    rw [htrig]
    have hp := paperSineModulus_sq_add_paperCosineModulus_sq U V
    have hs := ContinuousLinearMap.modulus_mul_self (paperSineBlockC U V)
    rw [← hs]
    exact (eq_sub_of_add_eq hp).symm
  show paperSourceDirectedSinC U V =
    CFC.sqrt ((paperSineBlockC U V).adjoint ∘L paperSineBlockC U V)
  exact (CFC.sqrt_unique hsquare hnonneg).symm

/-- The literal source `sin Theta_0` has exactly the singular values of the
cross projection printed in the paper.

The source sine acts on the trial coordinate space `U` while the cross block
maps `U` into `Vᗮ`, so this is the heterogeneous singular-sequence relation;
`SameApproximationSingularValues` is the special case of it in which the two
operators happen to share a codomain, and cannot be stated here. -/
theorem paperSourceDirectedSin_same_paperSineBlock
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularSequence
      (paperSourceDirectedSinC U V) (paperSineBlockC U V) := by
  rw [paperSourceDirectedSinC_eq_paperSineModulusC]
  exact modulus_hasSameApproximationNumbers _


end

end ExactSinTheta
end DavisKahan
end TauCeti