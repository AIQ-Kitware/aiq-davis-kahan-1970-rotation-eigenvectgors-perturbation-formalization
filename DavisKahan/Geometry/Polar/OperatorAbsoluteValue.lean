/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
import ForTauCeti.Analysis.InnerProductSpace.Polar.PartialIsometry

/-!
# Bounded operator absolute value and polar factor — bridge names

This module exposes the bounded polar decomposition under the `spectra*` bridge
names used across the Davis--Kahan operator-angle and direct-rotation programs.

The names date from a complex-only era; the statements below are over an
arbitrary `RCLike` field, carrying the functional-calculus hypothesis of
`ForTauCeti`'s modulus API, which typeclass inference discharges at `𝕜 = ℂ` and
at `𝕜 = ℝ` alike.

## Provenance — this is no longer Spectra-backed

Originally these were thin aliases for `Spectra.QuantumMechanics.Channels.absOp`
and `.polarIsometry`, and the module imported
`Spectra.QuantumMechanics.Channels.PolarDecomp`.  `ForTauCeti` since grew its own
bounded polar decomposition — `ContinuousLinearMap.modulus` and
`ContinuousLinearMap.polarPartial`, more general than Spectra's (rectangular
rather than square) — and this module already carried the two bridge theorems
proving the constructions *equal*: `spectraOperatorAbsoluteValue = T.modulus`
and `spectraPolarIsometry = T.polarPartial`.

Phase S1 of the completed Spectra removal took the obvious next step:
the definitions now *are* the `ForTauCeti` ones, so those two bridge theorems
collapse to `rfl` and the Spectra import is gone.  Cluster C of the port surface
(`absOp`, `polarIsometry`, `polarRange`) is closed by this file.

Nothing downstream changes: every `spectra*` name keeps its statement, so its
call sites across `Geometry/Polar/**` and `SpectralTheory/**` are untouched.
**The names are misnomers — there is no Spectra behind them.**  Renaming them is
a sweep over 100 declarations and about 1400 call sites, deliberately *not*
folded into the dependency removal; it is recorded as an open finding in
`dev/honesty-census-2026-08-31.md`.

Two theorems were deleted rather than kept, because they mentioned Spectra
constants and nothing outside this file used them: `spectra_absOp_eq_modulus`
and `spectra_polarRange_eq_polarInitial`.  `spectraOperatorAbsoluteValue_eq_modulus`
and `spectraPolarIsometry_eq_polarPartial` survive as `rfl`, since
`Geometry/Polar/Section3Nonacute.lean` rewrites with the latter.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-! The scalar-action and continuous-functional-calculus hypotheses under which
`ContinuousLinearMap.modulus` is defined
(`ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean`).  Typeclass
inference discharges all three at `𝕜 = ℂ` and, since commit `069c246e`, at
`𝕜 = ℝ` as well, so no consumer supplies anything. -/
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
  [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

/-- The bounded operator modulus `|T| = (T⋆T)^{1/2}`, under the bridge name. -/
noncomputable def spectraOperatorAbsoluteValue (T : H →L[𝕜] H) : H →L[𝕜] H :=
  T.modulus

/-- The modulus is positive. -/
theorem spectraOperatorAbsoluteValue_nonneg (T : H →L[𝕜] H) :
    0 ≤ spectraOperatorAbsoluteValue T :=
  T.modulus_nonneg

/-- The modulus is self-adjoint. -/
theorem spectraOperatorAbsoluteValue_isSelfAdjoint (T : H →L[𝕜] H) :
    IsSelfAdjoint (spectraOperatorAbsoluteValue T) :=
  T.modulus_isSelfAdjoint

/-- Squaring the modulus gives `T⋆T`. -/
theorem spectraOperatorAbsoluteValue_mul_self (T : H →L[𝕜] H) :
    spectraOperatorAbsoluteValue T * spectraOperatorAbsoluteValue T =
      star T * T :=
  T.modulus_mul_self_eq_star_mul_self

/-- The modulus and the original operator have equal pointwise norms. -/
theorem norm_spectraOperatorAbsoluteValue_apply (T : H →L[𝕜] H) (x : H) :
    ‖spectraOperatorAbsoluteValue T x‖ = ‖T x‖ :=
  T.norm_modulus_apply x

/-- The modulus has the same operator norm as the original operator. -/
theorem norm_spectraOperatorAbsoluteValue (T : H →L[𝕜] H) :
    ‖spectraOperatorAbsoluteValue T‖ = ‖T‖ :=
  T.norm_modulus

/-- Anything commuting with the Gram operator `T⋆T` commutes with the modulus
`|T|`.  Since `|T| = CFC.sqrt (T⋆T)` is a continuous function of `T⋆T`, this is
the non-unital `nnreal` continuous-functional-calculus commutation lemma. -/
theorem commute_spectraOperatorAbsoluteValue_of_commute_star_mul_self
    (T b : H →L[𝕜] H) (h : Commute (star T * T) b) :
    Commute (spectraOperatorAbsoluteValue T) b := by
  have : spectraOperatorAbsoluteValue T = CFC.sqrt (star T * T) :=
    T.modulus_eq_sqrt_star_mul_self
  rw [this, CFC.sqrt]
  exact Commute.cfcₙ_nnreal h NNReal.sqrt

/-- The partial isometry in the bounded polar decomposition, under the bridge
name. -/
noncomputable def spectraPolarIsometry (T : H →L[𝕜] H) : H →L[𝕜] H :=
  T.polarPartial

/-- The bounded polar decomposition `T = U |T|`. -/
theorem spectraPolar_decomposition (T : H →L[𝕜] H) :
    spectraPolarIsometry T ∘L spectraOperatorAbsoluteValue T = T :=
  T.polarPartial_comp_modulus

/-! ## Identification with the canonical `ForTauCeti` names

These were bridge *theorems* while the definitions above were Spectra's; they are
now definitional.  They are kept because downstream proofs rewrite with them. -/

/-- The donor development's operator absolute value is the canonical
`ContinuousLinearMap.modulus`.

Definitional after the repointing, so the proof is `rfl`; the theorem is kept as
a `simp` lemma because downstream proofs still rewrite along the old name. -/
@[simp]
theorem spectraOperatorAbsoluteValue_eq_modulus (T : H →L[𝕜] H) :
    spectraOperatorAbsoluteValue T = T.modulus :=
  rfl

/-- The polar isometry of the donor development agrees with `polarPartial`.  This is the
reconciliation that lets the donor-derived results be read as statements about the canonical
partial isometry. -/
@[simp]
theorem spectraPolarIsometry_eq_polarPartial (T : H →L[𝕜] H) :
    spectraPolarIsometry T = T.polarPartial :=
  rfl

/-- **The adjoint of the polar isometry is the polar isometry of the adjoint.** -/
theorem adjoint_spectraPolarIsometry (T : H →L[𝕜] H) :
    (spectraPolarIsometry T).adjoint = spectraPolarIsometry T.adjoint :=
  -- `polarPartial_adjoint` is oriented `W(M⋆) = W(M)⋆`; the bridge name is stated
  -- the other way round.
  T.polarPartial_adjoint.symm

/-- The final projection identity. -/
theorem spectraPolarIsometry_comp_adjoint (T : H →L[𝕜] H) :
    spectraPolarIsometry T ∘L (spectraPolarIsometry T).adjoint =
      T.polarFinal.starProjection :=
  T.polarPartial_comp_adjoint

/-- The initial projection identity. -/
theorem adjoint_spectraPolarIsometry_comp (T : H →L[𝕜] H) :
    (spectraPolarIsometry T).adjoint ∘L spectraPolarIsometry T
      = T.polarInitial.starProjection :=
  T.adjoint_comp_polarPartial

end DavisKahan
end TauCeti
