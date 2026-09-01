/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.Section4Real
import DavisKahan.Sources.DavisKahan1970.Section5
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNormLaws

/-!
# Reading the ideal-gauge results at the paper's own unitarily invariant norm

Several results Davis and Kahan state "for every unitary-invariant norm" are
proved here at an arbitrary `KyFanDominantIdealFamily`.  That is a genuine
theorem and, as a quantifier, it is not the printed one: `PaperUnitaryInvariantNorm`
is the repository's model of the source's norm object -- a normalized symmetric
gauge read on the complete approximation-singular-value sequence -- and a
reviewer comparing a Lean statement with the paper should see it.

The gap is bridgeable once and for all.  A `KyFanDominantIdealFamily`-quantified
estimate can be instantiated at the finite Ky Fan gauges themselves, which are
such families; that yields Ky Fan majorization, and Fan dominance
(`PaperUnitaryInvariantNorm.mul_gauge_le_of_all_mul_kyFan_le`) turns majorization
into the same estimate at every source norm.  `paperUINorm_of_kyFanDominant`
below is that bridge, and the endpoints after it are its instances.

This module adds no mathematics beyond the bridge: each endpoint is the already
proved ideal-gauge theorem, read at the source's norm.  The ideal-gauge forms are
retained -- they are stronger in their own quantifier -- and are recorded as
supporting evidence in the result inventory.

## Main results

* `paperUINorm_of_kyFanDominant`;
* `Corollary4_1_compact_nonacute_paperUINorm_complex` and `..._real`;
* `Proposition4_3_compact_nonacute_paperUINorm_complex` and `..._real`;
* `theorem5_2_paperUINorm_complex` and `theorem5_2_paperUINorm_real`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Corollary 4.1, Proposition 4.3,
  Theorem 5.2.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.ApproximationNumber

noncomputable section

universe u v

/-! ## The bridge -/

/-- **Fan dominance turns an ideal-gauge estimate into a source-norm estimate.**

If `d · gauge X ≤ gauge Y` holds in every Fan-dominant unitarily invariant ideal
gauge, then it holds at every normalized unitarily invariant norm in the source's
sense, and `X` lies in that norm's ideal whenever `Y` does.

The proof instantiates the hypothesis at the finite Ky Fan gauges, which are
themselves such families, and then applies Fan dominance. -/
theorem paperUINorm_of_kyFanDominant
    {𝕜 : Type u} [RCLike 𝕜]
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (N : PaperUnitaryInvariantNorm) {X Y : E →L[𝕜] F} {d : ℝ} (hd : 0 < d)
    (hY : N.Mem Y)
    (h : ∀ M : KyFanDominantIdealFamily.{u, v} 𝕜,
      M.Mem Y → M.Mem X ∧ d * M.gauge X ≤ M.gauge Y) :
    N.Mem X ∧ d * N.gauge X ≤ N.gauge Y := by
  refine N.mul_gauge_le_of_all_mul_kyFan_le hd hY (fun k => ?_)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [kyFanApproximationGauge, kyFanApproximationGauge,
      ContinuousLinearMap.kyFanGauge_zero_index,
      ContinuousLinearMap.kyFanGauge_zero_index, mul_zero]
  · have hM := h (KyFanDominantIdealFamily.kyFan (𝕜 := 𝕜) k hk)
      (KyFanDominantIdealFamily.kyFan_mem k hk Y)
    rw [KyFanDominantIdealFamily.kyFan_gauge,
      KyFanDominantIdealFamily.kyFan_gauge] at hM
    exact hM.2

/-! ## Corollary 4.1 and Proposition 4.3 at the source norm -/

section Complex

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Davis--Kahan 1970, Corollary 4.1, at every source unitarily invariant
norm**: `N((1 − V)P)` is minimized, among unitaries carrying `P H` onto `Q H`, by
the direct rotation.

`Corollary4_1_compact_nonacute_complex` is the same statement at an arbitrary
Fan-dominant ideal gauge; this is it read at the paper's norm object, which is the
quantifier the printed corollary uses. -/
theorem Corollary4_1_compact_nonacute_paperUINorm_complex
    (N : PaperUnitaryInvariantNorm)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    (hWmem : N.Mem ((1 - W) ∘L DavisKahan.projection U)) :
    N.Mem ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L DavisKahan.projection U) ∧
      N.gauge ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L
          DavisKahan.projection U) ≤
        N.gauge ((1 - W) ∘L DavisKahan.projection U) := by
  obtain ⟨hmem, hle⟩ := paperUINorm_of_kyFanDominant N one_pos hWmem
    (fun M hM => by
      obtain ⟨h₁, h₂⟩ :=
        Corollary4_1_compact_nonacute_complex M U V hcompact J W hWunitary hWmap hM
      exact ⟨h₁, by rw [one_mul]; exact h₂⟩)
  exact ⟨hmem, by rw [one_mul] at hle; exact hle⟩

/-- **Davis--Kahan 1970, Proposition 4.3, at every source unitarily invariant
norm**: the squared displacement `N((1 − V⋆)(1 − V))` is minimized by the direct
rotation. -/
theorem Proposition4_3_compact_nonacute_paperUINorm_complex
    (N : PaperUnitaryInvariantNorm)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
        (1 - DavisKahan.nonacuteDirectRotation U V J)) ∧
      N.gauge ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - DavisKahan.nonacuteDirectRotation U V J)) ≤
        N.gauge ((1 - star W) * (1 - W)) := by
  obtain ⟨hmem, hle⟩ := paperUINorm_of_kyFanDominant N one_pos hWmem
    (fun M hM => by
      obtain ⟨h₁, h₂⟩ :=
        Proposition4_3_compact_nonacute_idealGauge M U V hcompact J W hWunitary hWmap hM
      exact ⟨h₁, by rw [one_mul]; exact h₂⟩)
  exact ⟨hmem, by rw [one_mul] at hle; exact hle⟩

end Complex

section Real

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Davis--Kahan 1970, Corollary 4.1 over `ℝ`, at every source unitarily
invariant norm.** -/
theorem Corollary4_1_compact_nonacute_paperUINorm_real
    (N : PaperUnitaryInvariantNorm)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℝ]
      DavisKahan.halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    (hWmem : N.Mem ((1 - W) ∘L DavisKahan.projection U)) :
    N.Mem ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L DavisKahan.projection U) ∧
      N.gauge ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L
          DavisKahan.projection U) ≤
        N.gauge ((1 - W) ∘L DavisKahan.projection U) := by
  obtain ⟨hmem, hle⟩ := paperUINorm_of_kyFanDominant N one_pos hWmem
    (fun M hM => by
      obtain ⟨h₁, h₂⟩ :=
        Corollary4_1_compact_nonacute_real U V M hcompact J W hWunitary hWmap hM
      exact ⟨h₁, by rw [one_mul]; exact h₂⟩)
  exact ⟨hmem, by rw [one_mul] at hle; exact hle⟩

/-- **Davis--Kahan 1970, Proposition 4.3 over `ℝ`, at every source unitarily
invariant norm.** -/
theorem Proposition4_3_compact_nonacute_paperUINorm_real
    (N : PaperUnitaryInvariantNorm)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℝ]
      DavisKahan.halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
        (1 - DavisKahan.nonacuteDirectRotation U V J)) ∧
      N.gauge ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - DavisKahan.nonacuteDirectRotation U V J)) ≤
        N.gauge ((1 - star W) * (1 - W)) := by
  obtain ⟨hmem, hle⟩ := paperUINorm_of_kyFanDominant N one_pos hWmem
    (fun M hM => by
      obtain ⟨h₁, h₂⟩ :=
        Proposition4_3_compact_nonacute_real_idealGauge U V M hcompact J W hWunitary hWmap hM
      exact ⟨h₁, by rw [one_mul]; exact h₂⟩)
  exact ⟨hmem, by rw [one_mul] at hle; exact hle⟩

end Real

/-! ## Theorem 5.2 at the source norm -/

section Sylvester

/-- **Davis--Kahan 1970, Theorem 5.2, at every source unitarily invariant
norm**: for closed self-adjoint `A ≥ c + δ > c ≥ B` and a bounded solution of
`A X = X B + R`, `δ N(X) ≤ N(R)`, and `X` lies in the norm's ideal whenever `R`
does. -/
theorem theorem5_2_paperUINorm_complex
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (N : PaperUnitaryInvariantNorm) {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X R : F →L[ℂ] E} {c δ : ℝ} (hδ : 0 < δ)
    (hAlow : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hsyl : TauCeti.LinearPMap.SylvesterEquation A B X R)
    (hR : N.Mem R) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge R :=
  paperUINorm_of_kyFanDominant N hδ hR
    (fun M hM => Theorem5_2 M hA hB hδ hAlow hBhigh hsyl hM)

/-- **Davis--Kahan 1970, Theorem 5.2 over a real Hilbert space, at every source
unitarily invariant norm.**

The real endpoint takes the whole `FormBoundedSylvesterGap`, which is the weaker
separation hypothesis and therefore the stronger theorem: the printed ordered
configuration `A ≥ c + δ > c ≥ B` is its `leftAboveRightBelow` constructor. -/
theorem theorem5_2_paperUINorm_real
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (N : PaperUnitaryInvariantNorm) {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X R : F →L[ℝ] E} {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hsyl : TauCeti.LinearPMap.SylvesterEquation A B X R)
    (hR : N.Mem R) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge R :=
  paperUINorm_of_kyFanDominant N hδ hR
    (fun M hM => DavisKahan.ExactSinTheta.davisKahan1970_sylvester_real
      M hA hB hδ hgap hsyl hM)

end Sylvester

end

end DavisKahan1970
end TauCeti
