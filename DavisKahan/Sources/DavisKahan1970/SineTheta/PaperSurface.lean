/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.Sources.DavisKahan1970.FullSineTheta

/-!
# Auditable Davis--Kahan 1970 sine-theta surface

This module gives the Section 2 sine-theta theorem one declaration intended to
serve both as the paper-facing statement and as the semantic-audit target.  The
substantive proof remains
`TauCeti.DavisKahan1970.sinTheta_headline_generic`.

The central presentation choice is to name the source object `sinTheta₀` as an
explicit theorem parameter and state its concrete realization by an equality
hypothesis.  Thus the conclusion reads like the printed theorem while the
meaning of `sinTheta₀` remains visible in the same theorem signature; there is
no opaque local definition to chase.

Only the domain-aware trial residual and exact complementary spectral
coordinates are grouped into named predicates.  Their characteristic theorems
below expose every bundled clause to the semantic-alignment review.
-/

namespace DavisKahan1970

open scoped InnerProductSpace

noncomputable section

universe u v

open TauCeti
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahanExt
open TauCeti.DavisKahan1970

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The trial-coordinate part of the Davis--Kahan Section 2 setup.

`E₀` is an isometric coordinate map for the trial subspace and `R` is exactly
the residual `A E₀ - E₀ A₀` on the domain of the possibly unbounded trial
operator `A₀`. -/
structure IsTrialResidual
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (E₀ : F →L[𝕜] E)
    (R : F →L[𝕜] E) : Prop where
  isometry : IsometricEmbedding E₀
  mapsDomain : ∀ x : A₀.domain, E₀ (x : F) ∈ A.domain
  residualEquation : ∀ x : A₀.domain,
    A ⟨E₀ (x : F), mapsDomain x⟩ -
      E₀ (A₀ x) = R (x : F)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Fully expanded mathematical meaning of `IsTrialResidual`. -/
theorem isTrialResidual_iff
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (E₀ : F →L[𝕜] E)
    (R : F →L[𝕜] E) :
    IsTrialResidual A A₀ E₀ R ↔
      IsometricEmbedding E₀ ∧
        ∃ hdom : ∀ x : A₀.domain, E₀ (x : F) ∈ A.domain,
          ∀ x : A₀.domain,
            A ⟨E₀ (x : F), hdom x⟩ -
              E₀ (A₀ x) = R (x : F) := by
  constructor
  · intro h
    exact ⟨h.isometry, h.mapsDomain, h.residualEquation⟩
  · rintro ⟨hE₀, hdom, heq⟩
    exact ⟨hE₀, hdom, heq⟩

/-- The exact spectral-coordinate part of the Section 2 sine theorem.

`F₀` represents the desired exact subspace, while `F₁` represents its
orthogonal complement.  The complementary coordinates intertwine the ambient
operator `A` with the exact complementary block `Λ₁`. -/
structure IsExactSpectralDecomposition
    (A : E →ₗ.[𝕜] E)
    (Λ₁ : G →ₗ.[𝕜] G)
    (F₀ : H →L[𝕜] E)
    (F₁ : G →L[𝕜] E) : Prop where
  desiredIsometry : IsometricEmbedding F₀
  complementIsometry : IsometricEmbedding F₁
  orthogonal : F₀.adjoint ∘L F₁ = 0
  complete :
    F₀ ∘L F₀.adjoint + F₁ ∘L F₁.adjoint =
      ContinuousLinearMap.id 𝕜 E
  mapsDomain : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain
  intertwines : ∀ y : Λ₁.domain,
    A ⟨F₁ (y : G), mapsDomain y⟩ =
      F₁ (Λ₁ y)

/-- Fully expanded mathematical meaning of `IsExactSpectralDecomposition`. -/
theorem isExactSpectralDecomposition_iff
    (A : E →ₗ.[𝕜] E)
    (Λ₁ : G →ₗ.[𝕜] G)
    (F₀ : H →L[𝕜] E)
    (F₁ : G →L[𝕜] E) :
    IsExactSpectralDecomposition A Λ₁ F₀ F₁ ↔
      IsometricEmbedding F₀ ∧
        IsometricEmbedding F₁ ∧
          F₀.adjoint ∘L F₁ = 0 ∧
            F₀ ∘L F₀.adjoint + F₁ ∘L F₁.adjoint =
              ContinuousLinearMap.id 𝕜 E ∧
            ∃ hdom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain,
              ∀ y : Λ₁.domain,
                A ⟨F₁ (y : G), hdom y⟩ =
                  F₁ (Λ₁ y) := by
  constructor
  · intro h
    exact ⟨h.desiredIsometry, h.complementIsometry, h.orthogonal,
      h.complete, h.mapsDomain, h.intertwines⟩
  · rintro ⟨hF₀, hF₁, horth, hcomplete, hdom, hintertwines⟩
    exact ⟨hF₀, hF₁, horth, hcomplete, hdom, hintertwines⟩

/-- **Davis--Kahan 1970, Section 2 sine-theta theorem.**

This is the canonical presentation-facing and audit-facing declaration.  It is
generic over `RCLike 𝕜`, so it retains the real/complex and
infinite-dimensional scope of the proved headline theorem.

The source object `sinTheta₀` is an explicit parameter, and `hSinTheta₀` states
its concrete realization `(I - F₀ F₀*) E₀` in the theorem signature.  The
claim after the colon is therefore the printed factor-one inequality itself.
The stronger supporting theorem `sinTheta_headline_generic` additionally
certifies membership of this operator in the source norm ideal. -/
theorem sinTheta_headline
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    [HasUnboundedSylvesterKyFan.{u, v} 𝕜]
    (N : UnitaryInvariantNorm)
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (Λ₁ : G →ₗ.[𝕜] G)
    (E₀ : F →L[𝕜] E)
    (F₀ : H →L[𝕜] E)
    (F₁ : G →L[𝕜] E)
    (sinTheta₀ : F →L[𝕜] E)
    (R : F →L[𝕜] E)
    (hSinTheta₀ :
      sinTheta₀ =
        (ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀)
    (hA : IsSelfAdjoint A)
    (hA₀ : IsSelfAdjoint A₀)
    (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {β α δ : ℝ}
    (hβα : β ≤ α)
    (hδ : 0 < δ)
    (hspectral :
      (LinearPMap.realSpectrum A₀ ⊆ Set.Icc β α ∧
          LinearPMap.realSpectrum Λ₁ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}) ∨
        (LinearPMap.realSpectrum Λ₁ ⊆ Set.Icc β α ∧
          LinearPMap.realSpectrum A₀ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}))
    (hR : N.Mem R) :
    δ * N.gauge sinTheta₀ ≤ N.gauge R := by
  have hfull := TauCeti.DavisKahan1970.sinTheta_headline_generic
    N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁
    htrial.isometry hexact.desiredIsometry hexact.complementIsometry
    hexact.orthogonal hexact.complete htrial.mapsDomain hexact.mapsDomain
    htrial.residualEquation hexact.intertwines hβα hδ hspectral hR
  rw [← hSinTheta₀] at hfull
  exact hfull.2

end

end DavisKahan1970
