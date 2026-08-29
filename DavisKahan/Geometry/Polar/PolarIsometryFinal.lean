/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/

import ForTauCeti.Analysis.InnerProductSpace.Polar.PartialIsometry

/-!
# Final-space identities for the bounded polar isometry

The nonacute direct-rotation development needs the *final* projection identity
`U U⋆ = P_(closure range T)` alongside the initial one `U⋆ U = P_(closure range |T|)`,
together with the unitary `polarPartialFinalEquiv` between the two spaces.

Both now come straight from
`ForTauCeti/Analysis/InnerProductSpace/Polar/PartialIsometry.lean`, which develops the
general bounded polar decomposition — rectangular, infinite-dimensional, no invertibility
hypothesis — over our own `ContinuousLinearMap.modulus`.  This module is the thin
square-case naming layer the Davis--Kahan geometry reads.

## History

Until 2026-07-28 this file obtained the polar decomposition from `vendor/Spectra`
(`Spectra.QuantumMechanics.Channels`) and, worse, **declared its own contents into that
vendored namespace**, so eight Davis--Kahan results were indistinguishable from Spectra's
own API.  Both problems are gone: the mathematics is ours, and the declarations live in the
Davis--Kahan namespace with the rest of the geometry development.

The replacement is a strict generalisation rather than a transcription.  The two
constructions coincide — both extend `|T| x ↦ T x` from the dense range of the modulus —
but the ForTauCeti one is stated for `E →L[ℂ] F` with independent source and target, and it
proves the uniqueness characterisation that makes `adjoint_polarIsometry` a three-line
consequence instead of a 140-line argument.  That characterisation is also what lets
`DavisKahan/Geometry/Polar/OperatorAbsoluteValue.lean` identify the Spectra-backed polar
isometry with ours, so nothing downstream had to choose between the two.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

noncomputable section

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-! The scalar-action and continuous-functional-calculus hypotheses carried by
`ForTauCeti/Analysis/InnerProductSpace/Polar/PartialIsometry.lean`; typeclass
inference discharges them at `𝕜 = ℂ` and at `𝕜 = ℝ`. -/
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
  [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

/-- The final space in the bounded polar decomposition, `closure (range T)`. -/
abbrev polarFinalRange (T : H →L[𝕜] H) : Submodule 𝕜 H := T.polarFinal

/-- The initial space in the bounded polar decomposition, `closure (range |T|)`. -/
abbrev polarRange (T : H →L[𝕜] H) : Submodule 𝕜 H := T.polarInitial

/-- The polar partial isometry `U : H →L[𝕜] H`. -/
abbrev polarIsometry (T : H →L[𝕜] H) : H →L[𝕜] H := T.polarPartial

/-- The isometry `K → H`, `|T| x ↦ T x`, on the initial space. -/
abbrev polarPartial (T : H →L[𝕜] H) : T.polarInitial →L[𝕜] H := T.polarPartialAux

/-- The modulus `|T|`. -/
abbrev absOp (T : H →L[𝕜] H) : H →L[𝕜] H := T.modulus

/-- The modulus, corestricted to the initial space. -/
abbrev absOpCorestrict (T : H →L[𝕜] H) : H →ₗ[𝕜] T.polarInitial := T.modulusCorestrict

/-- The operator modulus `|T|` is self-adjoint. -/
theorem absOp_isSelfAdjoint (T : H →L[𝕜] H) : IsSelfAdjoint (absOp T) :=
  T.modulus_isSelfAdjoint

/-- The operator modulus is a positive operator. -/
theorem absOp_nonneg (T : H →L[𝕜] H) : 0 ≤ absOp T := T.modulus_nonneg

/-- `|T|` maps into the polar initial subspace, which is why the polar partial
isometry is defined there. -/
theorem absOp_mem_polarRange (T : H →L[𝕜] H) (x : H) : absOp T x ∈ polarRange T :=
  T.modulus_apply_mem_polarInitial x

/-- The modulus preserves norms pointwise: `‖|T| x‖ = ‖T x‖`.  This is the identity
the whole polar factorization rests on. -/
theorem norm_absOp_apply (T : H →L[𝕜] H) (x : H) : ‖absOp T x‖ = ‖T x‖ :=
  T.norm_modulus_apply x

/-- The corestriction of `|T|` to the polar initial subspace has dense range, so the
partial isometry extends continuously from it. -/
theorem denseRange_absOpCorestrict (T : H →L[𝕜] H) : DenseRange (absOpCorestrict T) :=
  T.denseRange_modulusCorestrict

/-- The polar factorization: the partial isometry applied to `|T| x` returns `T x`. -/
theorem polarPartial_absOpCorestrict (T : H →L[𝕜] H) (x : H) :
    polarPartial T (absOpCorestrict T x) = T x :=
  T.polarPartialAux_modulusCorestrict x

/-- The polar partial isometry is isometric on the polar initial subspace. -/
theorem norm_polarPartial_eq (T : H →L[𝕜] H) (x : T.polarInitial) :
    ‖polarPartial T x‖ = ‖x‖ :=
  T.norm_polarPartialAux_apply x

/-- The polar isometry acts by first projecting onto the polar initial subspace and
then applying the partial isometry. -/
theorem polarIsometry_apply_eq (T : H →L[𝕜] H) (w : H) :
    polarIsometry T w = polarPartial T (T.polarInitial.orthogonalProjectionOnto w) := rfl

/-- The polar partial isometry recovers `T` from its modulus: `U (|T| x) = T x`. -/
@[simp] theorem polarIsometry_absOp (T : H →L[𝕜] H) (x : H) :
    polarIsometry T (absOp T x) = T x :=
  T.polarPartial_apply_modulus x

/-- The range of the polar partial isometry lies in the final polar space. -/
theorem polarPartial_mem_finalRange (T : H →L[𝕜] H) (x : T.polarInitial) :
    polarPartial T x ∈ polarFinalRange T := by
  have hx : T.polarPartialAux x = T.polarPartial (x : H) := by
    rw [ContinuousLinearMap.polarPartial_apply]
    congr 1
    exact (Subtype.ext (by
      simp [])).symm
  rw [polarFinalRange, T.polarFinal_eq_range_polarPartial, hx]
  exact ⟨(x : H), rfl⟩

/-- The polar partial isometry, restricted to its final space, is onto. -/
theorem polarPartial_final_surjective (T : H →L[𝕜] H) :
    Function.Surjective
      ((polarPartial T).codRestrict (polarFinalRange T)
        (polarPartial_mem_finalRange T)) := by
  rintro ⟨y, hy⟩
  rw [polarFinalRange, T.polarFinal_eq_range_polarPartial] at hy
  obtain ⟨z, rfl⟩ := hy
  have hz : T.polarPartial z = T.polarPartialAux (T.polarInitial.orthogonalProjectionOnto z) :=
    rfl
  exact ⟨T.polarInitial.orthogonalProjectionOnto z, Subtype.ext (by simpa using hz.symm)⟩

/-- The polar partial isometry as a unitary between its initial and final spaces. -/
def polarPartialFinalEquiv (T : H →L[𝕜] H) :
    T.polarInitial ≃ₗᵢ[𝕜] polarFinalRange T :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := ((polarPartial T).codRestrict (polarFinalRange T)
        (polarPartial_mem_finalRange T)).toLinearMap
      norm_map' := fun x => by
        change ‖polarPartial T x‖ = ‖x‖
        exact T.norm_polarPartialAux_apply x }
    (polarPartial_final_surjective T)

/-- **The final projection identity** `U U⋆ = P_(closure range T)`. -/
theorem polarIsometry_comp_adjoint_self (T : H →L[𝕜] H) :
    polarIsometry T ∘L (polarIsometry T).adjoint = (polarFinalRange T).starProjection :=
  T.polarPartial_comp_adjoint

/-- **The initial projection identity** `U⋆ U = P_(closure range |T|)`. -/
theorem polarIsometry_adjoint_comp_self (T : H →L[𝕜] H) :
    (polarIsometry T).adjoint ∘L polarIsometry T = (polarRange T).starProjection :=
  T.adjoint_comp_polarPartial

/-- `U⋆ T = |T|`, the initial-space identity. -/
theorem polarIsometry_adjoint_comp (T : H →L[𝕜] H) :
    (polarIsometry T).adjoint ∘L T = absOp T :=
  T.adjoint_polarPartial_comp_self

/-- The polar decomposition `U |T| = T`. -/
theorem polar_decomposition (T : H →L[𝕜] H) :
    polarIsometry T ∘L absOp T = T :=
  T.polarPartial_comp_modulus

/-- **The adjoint of the polar isometry is the polar isometry of the adjoint.** -/
theorem adjoint_polarIsometry (T : H →L[𝕜] H) :
    (polarIsometry T).adjoint = polarIsometry T.adjoint :=
  (T.polarPartial_adjoint).symm

end

end DavisKahan
end TauCeti
