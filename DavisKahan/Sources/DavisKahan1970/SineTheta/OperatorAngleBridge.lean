/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Geometry.Angle.PaperOperatorAngle
import DavisKahan.OperatorIdeal.ApproximationNumbers.OperatorModulus
import DavisKahan.Sources.DavisKahan1970.SineTheta.ProjectionBlocks

/-!
# Literal paper angles and the accepted sine blocks

Davis and Kahan use two angle objects.

* `Theta` is the Hermitian angle of the whole ambient space.  Its sine has the
  singular values of the projector difference.
* `Theta0` is the directed angle from the trial subspace to the exact
  subspace.  Its sine has the singular values of the cross projection.

The existing complex angle calculus already supplies the two positive sine
operators.  This file defines the literal angle operators by applying arcsine
through continuous functional calculus and proves that applying sine recovers
those positive operators exactly.  The approximation-number modulus theorem
then identifies them with the raw projection blocks used in the paper.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The directed sine operator is a positive contraction. -/
theorem norm_sinAngleOperatorDirectedC_le_one
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V‖ ≤ 1 := by
  rw [TauCeti.DavisKahanExt.norm_sinAngleOperatorDirectedC]
  change ‖Vᗮ.starProjection ∘L U.starProjection‖ ≤ 1
  calc
    ‖Vᗮ.starProjection ∘L U.starProjection‖ ≤
        ‖Vᗮ.starProjection‖ * ‖U.starProjection‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 :=
      mul_le_mul Vᗮ.starProjection_norm_le U.starProjection_norm_le
        (norm_nonneg _) zero_le_one
    _ = 1 := by ring

/-- Spectrum of the directed positive sine lies in the canonical unit
interval. -/
theorem spectrum_sinAngleOperatorDirectedC_subset_Icc
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V) ⊆
      Set.Icc 0 1 := by
  intro x hx
  refine ⟨spectrum_nonneg_of_nonneg
    (TauCeti.DavisKahanExt.sinAngleOperatorDirectedC_nonneg U V) hx, ?_⟩
  -- `NormOneClass (E →L[ℂ] E)` fails for possibly trivial `E`, so the spectral
  -- radius bound is used in its `‖1‖`-corrected form.
  have hone : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have habs : |x| ≤
      ‖TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V‖ :=
    calc |x| = ‖x‖ := (Real.norm_eq_abs x).symm
      _ ≤ ‖TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V‖ *
            ‖(1 : E →L[ℂ] E)‖ := spectrum.norm_le_norm_mul_of_mem hx
      _ ≤ ‖TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V‖ * 1 :=
          mul_le_mul_of_nonneg_left hone (norm_nonneg _)
      _ = ‖TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V‖ := mul_one _
  exact (le_abs_self x).trans
    (habs.trans (norm_sinAngleOperatorDirectedC_le_one U V))

/-- The literal directed angle `Theta0`, extended by zero on the orthogonal
complement of the trial subspace. -/
noncomputable def paperDirectedAngleOperatorC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  cfc Real.arcsin
    (TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V)

/-- The literal directed angle is self-adjoint. -/
theorem isSelfAdjoint_paperDirectedAngleOperatorC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (paperDirectedAngleOperatorC U V) := by
  exact cfc_predicate Real.arcsin
    (TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V)

/-- The literal directed angle is nonnegative. -/
theorem paperDirectedAngleOperatorC_nonneg
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ paperDirectedAngleOperatorC U V := by
  apply cfc_nonneg
  intro x hx
  exact Real.arcsin_nonneg.mpr
    ((spectrum_sinAngleOperatorDirectedC_subset_Icc U V hx).1)

/-- Applying sine to `Theta0` recovers the positive directed sine exactly. -/
theorem cfc_sin_paperDirectedAngleOperatorC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    cfc Real.sin (paperDirectedAngleOperatorC U V) =
      TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V := by
  have hsa : IsSelfAdjoint
      (TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V) :=
    TauCeti.DavisKahanExt.isSelfAdjoint_sinAngleOperatorDirectedC U V
  have harcsin : ContinuousOn Real.arcsin
      (spectrum ℝ
        (TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V)) :=
    Real.continuous_arcsin.continuousOn
  have hsin : ContinuousOn Real.sin
      (Real.arcsin '' spectrum ℝ
        (TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V)) :=
    Real.continuous_sin.continuousOn
  rw [paperDirectedAngleOperatorC,
    ← cfc_comp Real.sin Real.arcsin
      (TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V)
      hsa hsin harcsin]
  calc
    cfc (Real.sin ∘ Real.arcsin)
        (TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V) =
      cfc (fun x : ℝ => x)
        (TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V) := by
      apply cfc_congr
      intro x hx
      have hxi := spectrum_sinAngleOperatorDirectedC_subset_Icc U V hx
      exact Real.sin_arcsin (by linarith [hxi.1]) hxi.2
    _ = TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V :=
      cfc_id' ℝ _

/-- Literal `sin Theta0`. -/
noncomputable def paperDirectedSinAngleOperatorC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  cfc Real.sin (paperDirectedAngleOperatorC U V)

/-- The paper's directed complex sine-angle operator agrees with the canonical one. -/
@[simp]
theorem paperDirectedSinAngleOperatorC_eq
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperDirectedSinAngleOperatorC U V =
      TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V :=
  cfc_sin_paperDirectedAngleOperatorC U V

/-- The directed literal sine has exactly the singular values of the cross
projection `P_(V complement) P_U`, as in the paper. -/
theorem paperDirectedSin_same_crossProjection
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularValues
      (paperDirectedSinAngleOperatorC U V)
      (Vᗮ.starProjection ∘L U.starProjection) := by
  rw [paperDirectedSinAngleOperatorC_eq,
    TauCeti.DavisKahanExt.sinAngleOperatorDirectedC]
  exact modulus_hasSameApproximationNumbers _

/-- The whole-space literal sine has exactly the singular values of the
projector difference. -/
theorem paperSin_same_projectionDiff
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularValues
      (TauCeti.DavisKahanExt.paperSinAngleOperatorC U V)
      (U.starProjection - V.starProjection) := by
  rw [TauCeti.DavisKahanExt.paperSinAngleOperatorC_eq,
    TauCeti.DavisKahanExt.sinAngleOperatorC]
  exact modulus_hasSameApproximationNumbers _

/-- Negation changes no approximation singular value. -/
theorem sameApproximationSingularValues_neg (A : E →L[ℂ] E) :
    SameApproximationSingularValues (-A) A := by
  intro n
  have h : ((-1 : ℂ) • A).approximationNumber n =
      ‖(-1 : ℂ)‖ * A.approximationNumber n :=
    ContinuousLinearMap.approximationNumber_smul (-1 : ℂ) A n
  simp only [neg_smul, one_smul, norm_neg, norm_one, one_mul] at h
  exact h

/-- The cross-block sum in Proposition 6.1 realizes the singular values of the
literal whole-space sine. -/
theorem paperCrossSineSum_same_literalSin
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularValues
      (paperCrossSineSum U V)
      (TauCeti.DavisKahanExt.paperSinAngleOperatorC U V) := by
  refine (paperCrossSineSum_same_projectionDiff U V).trans
    (SameApproximationSingularValues.trans ?_
      (paperSin_same_projectionDiff U V).symm)
  rw [← neg_sub U.starProjection V.starProjection]
  exact sameApproximationSingularValues_neg _

/-- The literal directed angle has spectrum in `[0, pi/2]`. -/
theorem spectrum_paperDirectedAngleOperatorC_subset_Icc
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (paperDirectedAngleOperatorC U V) ⊆
      Set.Icc 0 (Real.pi / 2) := by
  have hsa : IsSelfAdjoint
      (TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V) :=
    TauCeti.DavisKahanExt.isSelfAdjoint_sinAngleOperatorDirectedC U V
  have harcsin : ContinuousOn Real.arcsin
      (spectrum ℝ
        (TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V)) :=
    Real.continuous_arcsin.continuousOn
  intro y hy
  rw [paperDirectedAngleOperatorC,
    cfc_map_spectrum (R := ℝ) Real.arcsin
      (TauCeti.DavisKahanExt.sinAngleOperatorDirectedC U V) hsa harcsin] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxi := spectrum_sinAngleOperatorDirectedC_subset_Icc U V hx
  exact ⟨Real.arcsin_nonneg.mpr hxi.1,
    Real.arcsin_le_pi_div_two x⟩

end

end ExactSinTheta
end DavisKahan
end TauCeti