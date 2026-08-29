/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.CommonDomain
import DavisKahan.Sources.DavisKahan1970.SineTheta.Theorem62

/-!
# Literal common-domain source forms of Theorems 6.1 and 6.2

The unbounded appendix phrases the residual identity on the common dense domain
of `A E₀` and `E₀ A₀`.  These wrappers take that equality as public data and
construct the internal full-domain package.  No smaller unspecified core is
substituted.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe u v

open TauCeti.DavisKahanExt

/-- Scalar-generic source bookkeeping before choosing the spectral gap. -/
structure PaperCommonDomainSinThetaData
    (𝕜 : Type u) [RCLike 𝕜]
    (E F G H : Type v)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] where
  A : E →ₗ.[𝕜] E
  A₀ : F →ₗ.[𝕜] F
  Λ₁ : G →ₗ.[𝕜] G
  E₀ : F →L[𝕜] E
  F₀ : H →L[𝕜] E
  F₁ : G →L[𝕜] E
  R : F →L[𝕜] E
  A_selfAdjoint : IsSelfAdjoint A
  A₀_selfAdjoint : IsSelfAdjoint A₀
  Λ₁_selfAdjoint : IsSelfAdjoint Λ₁
  exact_decomposition : OrthogonalExactDecomposition F₀ F₁
  common_domain : HasPaperCommonDomain A A₀ E₀
  F₁_maps_domain : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain
  residual_on_common_domain :
    ∀ x : F, (hx : E₀ x ∈ A.domain) → (hx₀ : x ∈ A₀.domain) →
      A ⟨E₀ x, hx⟩ - E₀ (A₀ ⟨x, hx₀⟩) = R x
  F₁_intertwines : ∀ y : Λ₁.domain,
    A ⟨F₁ (y : G), F₁_maps_domain y⟩ =
      F₁ (Λ₁ y)

namespace PaperCommonDomainSinThetaData

/-- Internal data canonically constructed from the exact source domain. -/
noncomputable def toUnboundedSinThetaData
    {𝕜 : Type u} [RCLike 𝕜]
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (P : PaperCommonDomainSinThetaData 𝕜 E F G H) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G) :=
  unboundedSinThetaDataOfPaperCommonDomain
    P.A P.A₀ P.Λ₁ P.E₀ P.F₁ P.R P.common_domain
    P.F₁_maps_domain P.residual_on_common_domain P.F₁_intertwines

/-- The residual of the derived unbounded sine-theta data is the source's residual. -/
@[simp]
theorem toUnboundedSinThetaData_residual
    {𝕜 : Type u} [RCLike 𝕜]
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (P : PaperCommonDomainSinThetaData 𝕜 E F G H) :
    P.toUnboundedSinThetaData.residual = P.R := rfl

end PaperCommonDomainSinThetaData

section Complex

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Literal common-domain input for Theorem 6.1. -/
structure PaperCommonDomainTheorem61Data where
  source : PaperCommonDomainSinThetaData ℂ E F G H
  gap : ℝ
  epsilon : ℝ
  gap_pos : 0 < gap
  epsilon_pos : 0 < epsilon
  lower_frame : LowerFrameBound source.E₀ epsilon
  spectral_gap :
    FormBoundedSylvesterGap source.A₀ source.Λ₁ gap

namespace PaperCommonDomainTheorem61Data

/-- Package common-domain Theorem 6.1 source data as the general Theorem 6.1 record. -/
noncomputable def toPaperTheorem61Data
    (P : PaperCommonDomainTheorem61Data
      (E := E) (F := F) (G := G) (H := H)) :
    PaperTheorem61Data (E := E) (F := F) (G := G) (H := H) where
  data := P.source.toUnboundedSinThetaData
  exactMap := P.source.F₀
  ambient_selfAdjoint := P.source.A_selfAdjoint
  trial_selfAdjoint := P.source.A₀_selfAdjoint
  complement_selfAdjoint := P.source.Λ₁_selfAdjoint
  exact_decomposition := P.source.exact_decomposition
  gap := P.gap
  frameLowerBound := P.epsilon
  gap_pos := P.gap_pos
  frameLowerBound_pos := P.epsilon_pos
  lowerFrame := P.lower_frame
  spectral_gap := P.spectral_gap

/-- Davis--Kahan Theorem 6.1 with the appendix's exact common-domain
hypothesis and literal universal norm quantifier. -/
theorem result_every_unitarilyInvariantNorm
    (P : PaperCommonDomainTheorem61Data
      (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentative P.toPaperTheorem61Data.canonicalSinTheta)
    (N : PaperUnitaryInvariantNorm) (hR : N.Mem P.source.R) :
    N.Mem S.operator ∧
      P.gap * P.epsilon * N.gauge S.operator ≤ N.gauge P.source.R := by
  simpa [toPaperTheorem61Data,
    PaperCommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toPaperTheorem61Data.result_every_unitarilyInvariantNorm S N hR

/-- Exact common-domain Theorem 6.1 with arbitrary representative
coordinate spaces. -/
theorem result_every_unitarilyInvariantNorm_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    (P : PaperCommonDomainTheorem61Data
      (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.toPaperTheorem61Data.canonicalSinTheta)
    (N : PaperUnitaryInvariantNorm) (hR : N.Mem P.source.R) :
    N.Mem S.operator ∧
      P.gap * P.epsilon * N.gauge S.operator ≤ N.gauge P.source.R := by
  simpa [toPaperTheorem61Data,
    PaperCommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toPaperTheorem61Data.result_every_unitarilyInvariantNorm_across S N hR

end PaperCommonDomainTheorem61Data

/-- Literal common-domain input for Theorem 6.2. -/
structure PaperCommonDomainTheorem62Data where
  source : PaperCommonDomainSinThetaData ℂ E F G H
  gap : ℝ
  epsilon : ℝ
  gap_pos : 0 < gap
  epsilon_pos : 0 < epsilon
  lower_frame : LowerFrameBound source.E₀ epsilon
  spectral_distance : PairwiseSpectrumGap source.A₀ source.Λ₁ gap

namespace PaperCommonDomainTheorem62Data

/-- Package common-domain Theorem 6.2 source data as the general Theorem 6.2 record. -/
noncomputable def toPaperTheorem62Data
    (P : PaperCommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H)) :
    PaperTheorem62Data (E := E) (F := F) (G := G) (H := H) where
  data := P.source.toUnboundedSinThetaData
  exactMap := P.source.F₀
  ambient_selfAdjoint := P.source.A_selfAdjoint
  trial_selfAdjoint := P.source.A₀_selfAdjoint
  complement_selfAdjoint := P.source.Λ₁_selfAdjoint
  exact_decomposition := P.source.exact_decomposition
  gap := P.gap
  frameLowerBound := P.epsilon
  gap_pos := P.gap_pos
  frameLowerBound_pos := P.epsilon_pos
  lowerFrame := P.lower_frame
  spectral_distance := P.spectral_distance

/-- Davis--Kahan Theorem 6.2 with the appendix's exact common domain. -/
theorem result
    (P : PaperCommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentative P.toPaperTheorem62Data.canonicalSinTheta)
    (hR : IsPaperHilbertSchmidt P.source.R) :
    IsPaperHilbertSchmidt S.operator ∧
      P.gap * P.epsilon * paperHilbertSchmidtNorm S.operator ≤
        paperHilbertSchmidtNorm P.source.R := by
  simpa [toPaperTheorem62Data,
    PaperCommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toPaperTheorem62Data.result S hR

/-- The source bound-norm fallback under an explicit finite-rank premise. -/
theorem operatorNorm_result_of_rank_le
    (P : PaperCommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentative P.toPaperTheorem62Data.canonicalSinTheta)
    {r : ℕ} (hRank : P.source.R.rank ≤ (r : Cardinal)) :
    P.gap * P.epsilon * ‖S.operator‖ ≤ ‖P.source.R‖ * Real.sqrt r := by
  simpa [toPaperTheorem62Data,
    PaperCommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toPaperTheorem62Data.operatorNorm_result_of_rank_le S hRank

/-- Exact common-domain Theorem 6.2 with arbitrary representative
coordinate spaces. -/
theorem result_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    (P : PaperCommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.toPaperTheorem62Data.canonicalSinTheta)
    (hR : IsPaperHilbertSchmidt P.source.R) :
    IsPaperHilbertSchmidt S.operator ∧
      P.gap * P.epsilon * paperHilbertSchmidtNorm S.operator ≤
        paperHilbertSchmidtNorm P.source.R := by
  simpa [toPaperTheorem62Data,
    PaperCommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toPaperTheorem62Data.result_across S hR

end PaperCommonDomainTheorem62Data

end Complex

section Real

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Real common-domain input for Theorem 6.1. -/
structure PaperRealCommonDomainTheorem61Data where
  source : PaperCommonDomainSinThetaData ℝ E F G H
  gap : ℝ
  epsilon : ℝ
  gap_pos : 0 < gap
  epsilon_pos : 0 < epsilon
  lower_frame : LowerFrameBound source.E₀ epsilon
  spectral_gap :
    FormBoundedSylvesterGap source.A₀ source.Λ₁ gap

namespace PaperRealCommonDomainTheorem61Data

/-- Real-scalar packaging of common-domain Theorem 6.1 source data. -/
noncomputable def toPaperTheorem61Data
    (P : PaperRealCommonDomainTheorem61Data
      (E := E) (F := F) (G := G) (H := H)) :
    PaperRealTheorem61Data (E := E) (F := F) (G := G) (H := H) where
  data := P.source.toUnboundedSinThetaData
  exactMap := P.source.F₀
  ambient_selfAdjoint := P.source.A_selfAdjoint
  trial_selfAdjoint := P.source.A₀_selfAdjoint
  complement_selfAdjoint := P.source.Λ₁_selfAdjoint
  exact_decomposition := P.source.exact_decomposition
  gap := P.gap
  frameLowerBound := P.epsilon
  gap_pos := P.gap_pos
  frameLowerBound_pos := P.epsilon_pos
  lowerFrame := P.lower_frame
  spectral_gap := P.spectral_gap

/-- Real Davis--Kahan Theorem 6.1 with the exact common domain. -/
theorem result_every_unitarilyInvariantNorm
    (P : PaperRealCommonDomainTheorem61Data
      (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentative P.toPaperTheorem61Data.canonicalSinTheta)
    (N : PaperUnitaryInvariantNorm) (hR : N.Mem P.source.R) :
    N.Mem S.operator ∧
      P.gap * P.epsilon * N.gauge S.operator ≤ N.gauge P.source.R := by
  simpa [toPaperTheorem61Data,
    PaperCommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toPaperTheorem61Data.result_every_unitarilyInvariantNorm S N hR

/-- Real exact common-domain Theorem 6.1 with arbitrary representative
coordinate spaces. -/
theorem result_every_unitarilyInvariantNorm_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℝ F₀] [CompleteSpace F₀]
    (P : PaperRealCommonDomainTheorem61Data
      (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.toPaperTheorem61Data.canonicalSinTheta)
    (N : PaperUnitaryInvariantNorm) (hR : N.Mem P.source.R) :
    N.Mem S.operator ∧
      P.gap * P.epsilon * N.gauge S.operator ≤ N.gauge P.source.R := by
  simpa [toPaperTheorem61Data,
    PaperCommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toPaperTheorem61Data.result_every_unitarilyInvariantNorm_across S N hR

end PaperRealCommonDomainTheorem61Data

/-- Real common-domain input for Theorem 6.2. -/
structure PaperRealCommonDomainTheorem62Data where
  source : PaperCommonDomainSinThetaData ℝ E F G H
  gap : ℝ
  epsilon : ℝ
  gap_pos : 0 < gap
  epsilon_pos : 0 < epsilon
  lower_frame : LowerFrameBound source.E₀ epsilon
  spectral_distance :
    ∀ lam ∈ TauCeti.LinearPMap.realSpectrum source.A₀, ∀ α ∈ TauCeti.LinearPMap.realSpectrum source.Λ₁,
      gap ≤ |lam - α|

namespace PaperRealCommonDomainTheorem62Data

/-- Real-scalar packaging of common-domain Theorem 6.2 source data. -/
noncomputable def toPaperTheorem62Data
    (P : PaperRealCommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H)) :
    PaperRealTheorem62Data (E := E) (F := F) (G := G) (H := H) where
  data := P.source.toUnboundedSinThetaData
  exactMap := P.source.F₀
  ambient_selfAdjoint := P.source.A_selfAdjoint
  trial_selfAdjoint := P.source.A₀_selfAdjoint
  complement_selfAdjoint := P.source.Λ₁_selfAdjoint
  exact_decomposition := P.source.exact_decomposition
  gap := P.gap
  frameLowerBound := P.epsilon
  gap_pos := P.gap_pos
  frameLowerBound_pos := P.epsilon_pos
  lowerFrame := P.lower_frame
  spectral_distance := P.spectral_distance

/-- Real Davis--Kahan Theorem 6.2 with the exact common domain. -/
theorem result
    (P : PaperRealCommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentative P.toPaperTheorem62Data.canonicalSinTheta)
    (hR : IsPaperHilbertSchmidt P.source.R) :
    IsPaperHilbertSchmidt S.operator ∧
      P.gap * P.epsilon * paperHilbertSchmidtNorm S.operator ≤
        paperHilbertSchmidtNorm P.source.R := by
  simpa [toPaperTheorem62Data,
    PaperCommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toPaperTheorem62Data.result S hR

/-- Real source bound-norm fallback. -/
theorem operatorNorm_result_of_rank_le
    (P : PaperRealCommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentative P.toPaperTheorem62Data.canonicalSinTheta)
    {r : ℕ} (hRank : P.source.R.rank ≤ (r : Cardinal)) :
    P.gap * P.epsilon * ‖S.operator‖ ≤ ‖P.source.R‖ * Real.sqrt r := by
  simpa [toPaperTheorem62Data,
    PaperCommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toPaperTheorem62Data.operatorNorm_result_of_rank_le S hRank

/-- Real exact common-domain Theorem 6.2 with arbitrary representative
coordinate spaces. -/
theorem result_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℝ F₀] [CompleteSpace F₀]
    (P : PaperRealCommonDomainTheorem62Data
      (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.toPaperTheorem62Data.canonicalSinTheta)
    (hR : IsPaperHilbertSchmidt P.source.R) :
    IsPaperHilbertSchmidt S.operator ∧
      P.gap * P.epsilon * paperHilbertSchmidtNorm S.operator ≤
        paperHilbertSchmidtNorm P.source.R := by
  simpa [toPaperTheorem62Data,
    PaperCommonDomainSinThetaData.toUnboundedSinThetaData] using
    P.toPaperTheorem62Data.result_across S hR

end PaperRealCommonDomainTheorem62Data

end Real

end

end ExactSinTheta
end DavisKahan
end TauCeti