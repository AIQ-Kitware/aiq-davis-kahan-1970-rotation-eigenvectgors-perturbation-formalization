/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Geometry.Polar.PolarIsometryFinal
import DavisKahan.Geometry.Polar.DirectRotation
import DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Polar factors and reducing projections

This file isolates the functional-analytic facts used by the nonacute
Davis--Kahan direct rotation.  The key principle is that an intertwining
relation `T P = Q T`, together with the adjoint relation, passes from `T` to
its polar partial isometry.  The proof is carried out first on `range |T|`,
then on its closure, and finally on the orthogonal complement, where the polar
factor vanishes.
-/

open scoped InnerProductSpace InnerProduct

namespace TauCeti
namespace DavisKahan

open DavisKahan.Foundation

noncomputable section

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
  [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

/-- A self-adjoint projection commuting with `|T|` preserves the initial polar
space. -/
theorem polarRange_invariant_of_commute_abs
    (T P : H →L[𝕜] H)
    (hcomm : absOp T ∘L P = P ∘L absOp T)
    {x : H} (hx : x ∈ polarRange T) : P x ∈ polarRange T := by
  let M : Submodule 𝕜 H := Submodule.comap (P : H →ₗ[𝕜] H) (polarRange T)
  have hMclosed : IsClosed (M : Set H) := by
    have hcl : IsClosed ((polarRange T : Set H)) := by
      rw [polarRange]; exact Submodule.isClosed_topologicalClosure _
    exact hcl.preimage P.continuous
  have hrange : LinearMap.range (absOp T).toLinearMap ≤ M := by
    rintro y ⟨z, rfl⟩
    change P (absOp T z) ∈ polarRange T
    have hpoint := DFunLike.congr_fun hcomm z
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hpoint
    rw [← hpoint]
    exact absOp_mem_polarRange T (P z)
  have hclosure : polarRange T ≤ M := by
    rw [polarRange]
    exact Submodule.topologicalClosure_minimal _ hrange hMclosed
  exact hclosure hx

/-- If a self-adjoint projection preserves the initial polar space, it also
preserves its orthogonal complement. -/
theorem polarRange_orthogonal_invariant_of_selfAdjoint
    (T P : H →L[𝕜] H) (hP : IsSelfAdjoint P)
    (hpres : ∀ x ∈ polarRange T, P x ∈ polarRange T)
    {x : H} (hx : x ∈ (polarRange T)ᗮ) : P x ∈ (polarRange T)ᗮ := by
  rw [Submodule.mem_orthogonal'] at hx ⊢
  intro y hy
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (ContinuousLinearMap.star_eq_adjoint P).symm.trans hP.star_eq
  rw [hPadj]
  exact hx (P y) (hpres y hy)

/-- The absolute value commutes with the initial projection whenever `T`
intertwines two orthogonal projections. -/
theorem absOp_commutes_of_projection_intertwining
    (T P Q : H →L[𝕜] H)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hTP : T ∘L P = Q ∘L T) :
    absOp T ∘L P = P ∘L absOp T := by
  have hPsa : IsSelfAdjoint P := LinearMap.IsSymmetric.isSelfAdjoint hP.2
  have hQsa : IsSelfAdjoint Q := LinearMap.IsSymmetric.isSelfAdjoint hQ.2
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (ContinuousLinearMap.star_eq_adjoint P).symm.trans hPsa.star_eq
  have hQadj : ContinuousLinearMap.adjoint Q = Q :=
    (ContinuousLinearMap.star_eq_adjoint Q).symm.trans hQsa.star_eq
  have hstar : P ∘L T† = T† ∘L Q := by
    have h := congrArg ContinuousLinearMap.adjoint hTP
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      hPadj, hQadj] at h
    exact h
  have hgram : (T† ∘L T) ∘L P = P ∘L (T† ∘L T) := by
    calc
      (T† ∘L T) ∘L P = T† ∘L (T ∘L P) := by
        ext x
        rfl
      _ = T† ∘L (Q ∘L T) := by rw [hTP]
      _ = (T† ∘L Q) ∘L T := by
        ext x
        rfl
      _ = (P ∘L T†) ∘L T := by rw [← hstar]
      _ = P ∘L (T† ∘L T) := by
        ext x
        rfl
  -- `|T| = √(T⋆T)` via the continuous functional calculus, so `P` commuting with
  -- `T⋆T` (the Gram operator) passes to the modulus by `Commute.cfcₙ_nnreal`.
  have hcomm : Commute (star T * T) P := by
    have hmul : (star T * T) * P = P * (star T * T) := by
      simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
      exact hgram
    exact hmul
  have h2 : Commute (absOp T) P := Commute.cfcₙ_nnreal hcomm NNReal.sqrt
  simpa [ContinuousLinearMap.mul_def] using h2.eq

/-- The polar partial isometry intertwines the same two projections as the
original operator. -/
theorem polarIsometry_intertwines_of_projection_intertwining
    (T P Q : H →L[𝕜] H)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hTP : T ∘L P = Q ∘L T) :
    polarIsometry T ∘L P = Q ∘L polarIsometry T := by
  have habs : absOp T ∘L P = P ∘L absOp T :=
    absOp_commutes_of_projection_intertwining T P Q hP hQ hTP
  have hpres : ∀ x ∈ polarRange T, P x ∈ polarRange T :=
    fun x hx => polarRange_invariant_of_commute_abs T P habs hx
  have hPsa : IsSelfAdjoint P := LinearMap.IsSymmetric.isSelfAdjoint hP.2
  have hpresOrth : ∀ x ∈ (polarRange T)ᗮ, P x ∈ (polarRange T)ᗮ :=
    fun x hx => polarRange_orthogonal_invariant_of_selfAdjoint T P hPsa hpres hx
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨m, hm, hmk⟩ :=
    Submodule.HasOrthogonalProjection.exists_orthogonal
      (K := polarRange T) x
  obtain ⟨k, hk, rfl⟩ : ∃ k ∈ (polarRange T)ᗮ, x = m + k :=
    ⟨x - m, hmk, by abel⟩
  have hUk : polarIsometry T k = 0 := by
    rw [polarIsometry_apply_eq]
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hk]
    simp
  have hUPk : polarIsometry T (P k) = 0 := by
    rw [polarIsometry_apply_eq]
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr (hpresOrth k hk)]
    simp
  simp only [ContinuousLinearMap.comp_apply, map_add, hUk, hUPk, map_zero,
    add_zero]
  have heqOnDense :
      polarPartial T ((polarRange T).orthogonalProjectionOnto (P m)) =
        Q (polarPartial T ((polarRange T).orthogonalProjectionOnto m)) := by
    let f : polarRange T →L[𝕜] H :=
      polarPartial T ∘L
        (P ∘L (polarRange T).subtypeL).codRestrict
          (polarRange T) (fun z => hpres z z.property)
    let g : polarRange T →L[𝕜] H := Q ∘L polarPartial T
    have hfg : f = g := by
      apply DFunLike.coe_injective
      apply DenseRange.equalizer (denseRange_absOpCorestrict T)
        f.continuous g.continuous
      funext z
      change polarPartial T
          ⟨P (absOp T z), hpres _ (absOp_mem_polarRange T z)⟩ =
        Q (polarPartial T (absOpCorestrict T z))
      have hpabs := DFunLike.congr_fun habs z
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hpabs
      have hleft :
          (⟨P (absOp T z), hpres _ (absOp_mem_polarRange T z)⟩ : polarRange T) =
            absOpCorestrict T (P z) := by
        apply Subtype.ext
        simpa using hpabs.symm
      rw [hleft, polarPartial_absOpCorestrict, polarPartial_absOpCorestrict]
      exact DFunLike.congr_fun hTP z
    have hmproj : (polarRange T).orthogonalProjectionOnto m = ⟨m, hm⟩ := by
      apply Subtype.ext
      exact Submodule.starProjection_eq_self_iff.mpr hm
    have hPm : P m ∈ polarRange T := hpres m hm
    have hPmproj : (polarRange T).orthogonalProjectionOnto (P m) = ⟨P m, hPm⟩ := by
      apply Subtype.ext
      exact Submodule.starProjection_eq_self_iff.mpr hPm
    have hcodeq :
        ((P ∘L (polarRange T).subtypeL).codRestrict (polarRange T)
            (fun z => hpres z z.property)) ⟨m, hm⟩ = (⟨P m, hPm⟩ : polarRange T) := by
      apply Subtype.ext
      -- `simp` no longer takes the `codRestrict` coercion step; it is definitional.
      rfl
    have hkey := DFunLike.congr_fun hfg ⟨m, hm⟩
    simp only [f, g, ContinuousLinearMap.comp_apply, hcodeq] at hkey
    rw [hmproj, hPmproj]
    exact hkey
  simpa [polarIsometry_apply_eq] using heqOnDense

/-- The polar factor of the canonical two-projection intertwiner intertwines
both projections without an acuteness assumption. -/
theorem canonicalPolarFactor_intertwines_from_polar
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraCanonicalPolarFactor U V ∘L projection U =
      projection V ∘L spectraCanonicalPolarFactor U V := by
  rw [spectraCanonicalPolarFactor, spectraPolarIsometry]
  apply polarIsometry_intertwines_of_projection_intertwining
  · exact ⟨U.isIdempotentElem_starProjection,
      (isSelfAdjoint_starProjection U).isSymmetric⟩
  · exact ⟨V.isIdempotentElem_starProjection,
      (isSelfAdjoint_starProjection V).isSymmetric⟩
  · simpa [ContinuousLinearMap.mul_def] using
      spectraCanonicalIntertwiner_mul_projection U V

/-- Taking adjoints exchanges the ordered pair of subspaces in the canonical
polar factor. -/
theorem canonicalPolarFactor_adjoint_swap_from_polar
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    star (spectraCanonicalPolarFactor U V) =
      spectraCanonicalPolarFactor V U := by
  rw [spectraCanonicalPolarFactor, spectraCanonicalPolarFactor,
    ContinuousLinearMap.star_eq_adjoint,
    adjoint_spectraPolarIsometry,
    ← ContinuousLinearMap.star_eq_adjoint, star_spectraCanonicalIntertwiner]

end

end DavisKahan
end TauCeti
