/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.CosineAngle
import DavisKahan.Sources.DavisKahan1970.SineTheta.CosineAngleReal

/-!
# Equality of the cosine-defined and sine-defined directed angles

Davis and Kahan define the directed angle from the positive cosine overlap.
A modern projection formulation often starts from the positive complementary
sine modulus.  On the canonical range `[0, pi/2]` these are not merely
operators with matching singular data: functional calculus shows that they
produce exactly the same angle operator.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A subspace admitting an orthogonal projection inside a complete ambient
space is itself complete.  `local instance` does not propagate through imports,
so it is reinstalled here. -/
local instance instCompleteSpaceCoeOfHasOrthogonalProjectionAngleIdentity
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-- The bounded operators on a subspace coordinate space, as a C⋆-algebra.

Recording this in the submodule shape is load-bearing: the functional-calculus
search does not find the C⋆-algebra structure on `↥U →L[ℂ] ↥U` by itself.  See
the companion instance in `PaperCosineAngle`. -/
noncomputable local instance instCStarAlgebraSubspaceCoordinateAngleIdentity
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] :
    CStarAlgebra (↥U →L[ℂ] ↥U) :=
  inferInstance

/-- The source cosine-defined directed angle has spectrum in `[0, pi/2]`. -/
theorem spectrum_paperSourceDirectedAngleC_subset_Icc
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (paperSourceDirectedAngleC U V) ⊆
      Set.Icc 0 (Real.pi / 2) := by
  have hsa : IsSelfAdjoint (paperCosineModulusC U V) :=
    ContinuousLinearMap.modulus_isSelfAdjoint _
  intro y hy
  rw [paperSourceDirectedAngleC,
    cfc_map_spectrum (R := ℝ) Real.arccos (paperCosineModulusC U V)
      hsa Real.continuous_arccos.continuousOn] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxi := spectrum_paperCosineModulusC_subset_Icc U V hx
  exact ⟨Real.arccos_nonneg x,
    (Real.arccos_le_pi_div_two).2 hxi.1⟩

/-- The angle reconstructed from the positive sine modulus. -/
noncomputable def paperSineDefinedDirectedAngleC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  cfc Real.arcsin (paperSineModulusC U V)

/-- The angle reconstructed from the sine modulus is exactly the source
cosine-defined angle. -/
theorem paperSineDefinedDirectedAngleC_eq_source
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSineDefinedDirectedAngleC U V = paperSourceDirectedAngleC U V := by
  have hangle : IsSelfAdjoint (paperSourceDirectedAngleC U V) :=
    cfc_predicate Real.arccos (paperCosineModulusC U V)
  rw [paperSineDefinedDirectedAngleC,
    ← paperSourceDirectedSinC_eq_paperSineModulusC U V,
    paperSourceDirectedSinC,
    ← cfc_comp Real.arcsin Real.sin (paperSourceDirectedAngleC U V)
      hangle Real.continuous_arcsin.continuousOn
      Real.continuous_sin.continuousOn]
  calc
    cfc (Real.arcsin ∘ Real.sin) (paperSourceDirectedAngleC U V) =
        cfc (fun x : ℝ => x) (paperSourceDirectedAngleC U V) := by
      apply cfc_congr
      intro x hx
      have hxi := spectrum_paperSourceDirectedAngleC_subset_Icc U V hx
      exact Real.arcsin_sin
        (by linarith [hxi.1, Real.pi_pos]) hxi.2
    _ = paperSourceDirectedAngleC U V := cfc_id' ℝ _

/-- Equivalent formulation with the source angle on the left. -/
theorem paperSourceDirectedAngleC_eq_arcsin_sineModulus
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSourceDirectedAngleC U V =
      cfc Real.arcsin (paperSineModulusC U V) :=
  (paperSineDefinedDirectedAngleC_eq_source U V).symm

section Real

variable {F : Type v}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- For real subspaces, the sine-reconstructed angle on the canonical
complexification equals the source cosine-defined angle.

The right-hand side is written through `paperSineDefinedDirectedAngleC`, which
is *by definition* `cfc Real.arcsin (paperSineModulusC ..)`, so this is the same
statement as the spelled-out functional calculus.  Writing it out here would not
elaborate: in statement position there is no way to pin the C⋆-algebra instance
on the complexified subspace coordinates, and the functional-calculus search
does not find it unaided even though the C⋆-algebra structure itself resolves. -/
theorem paperSourceDirectedAngleR_eq_arcsin_sineModulus
    (U V : Submodule ℝ F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSourceDirectedAngleR U V =
      paperSineDefinedDirectedAngleC
        (complexifySubmodule U)
        (complexifySubmodule V) :=
  (paperSineDefinedDirectedAngleC_eq_source _ _).symm

end Real

end

end ExactSinTheta
end DavisKahan
end TauCeti