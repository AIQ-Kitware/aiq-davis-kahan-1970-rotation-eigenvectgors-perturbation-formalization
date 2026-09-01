/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.MultiplicityModel

/-!
# Spectral multiplicity data as a complete unitary invariant

`TauCeti.MultiplicityDatum 𝕜` presents an operator as multiplication by the spectral coordinate
on `L²` of a finite base measure on `ℂ` together with an antitone family of measurable level
sets.  This module turns that presentation into a **relation between operators** and proves that,
over `ℂ`, the relation is exactly unitary equivalence.

* `TauCeti.SameSpectralMultiplicity` says that two operators admit multiplicity data whose base
  measures lie in the same measure class and whose level sets agree up to null sets.  It is
  stated over an arbitrary `RCLike` scalar field: the spectral parameter and the base measure
  stay complex, and only the `L²` fibres and the model operator use `𝕜`.
* `TauCeti.sameSpectralMultiplicity_iff_operatorUnitaryEquiv_complex` is the complex classification:
  two bounded self-adjoint operators on complex Hilbert spaces, the first separable, have the
  same multiplicity data if and only if they are unitarily equivalent.

## What the relation is, and is not

It is an existential over **presentations**, and that is what makes the classification provable
without a uniqueness theorem for the multiplicity decomposition.  It is **not** a canonical
invariant: nothing here says the datum of an operator is unique.

The cardinal-valued multiplicity function is encoded by its super-level sets: `level k` is
`{z | k < m z}`, so a point of `level k \ level (k + 1)` has multiplicity exactly `k + 1` and a
point of every `level k` has multiplicity `ℵ₀`.  The encoding is not a proxy --
`TauCeti.MultiplicityDatum.multiplicity` is the honest `ℂ → ℕ∞` multiplicity function,
`TauCeti.MultiplicityDatum.mem_level_iff` proves `level k = {z | k < multiplicity z}`, and
`TauCeti.MultiplicityDatum.measurable_multiplicity` proves it measurable.  Level sets are carried
in the structure only because that makes every hypothesis a plain `MeasurableSet`.

## Scope of the classification

Both classification theorems below stay at `𝕜 = ℂ`, for different reasons.

* The direction from multiplicity data to unitary equivalence rests on
  `TauCeti.operatorUnitaryEquiv_of_measureEquiv_complex`, whose Radon--Nikodym unitary is complex.
* The converse rests on `TauCeti.BorelCalculus.exists_hasMultiplicityModel`, complex
  Hahn--Hellinger, and that is where separability of the first space is spent: a model is built
  from a *countable* cyclic decomposition, and countability of the index is what lets the
  level-set normalisation run, since ranks count earlier indices.  A non-separable statement
  would need the uniform-multiplicity form indexed by cardinals, whose measures are not
  σ-finite.

The real analogues of both directions exist and are proved downstream, against
`TauCeti.operatorUnitaryEquiv_of_measureEquiv_real` and the real Hahn--Hellinger existence
theorem; only the *definition* above is shared, and it is already field-generic.

## Main results

* `TauCeti.SameSpectralMultiplicity`: the relation.
* `TauCeti.operatorUnitaryEquiv_of_sameSpectralMultiplicity_complex`: same data implies unitary
  equivalence, with no separability hypothesis on either space.
* `TauCeti.sameSpectralMultiplicity_of_operatorUnitaryEquiv_complex`: unitary equivalence implies
the
  same data, for a self-adjoint operator on a separable space.
* `TauCeti.sameSpectralMultiplicity_iff_operatorUnitaryEquiv_complex`: the classification.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

namespace TauCeti

universe u v

section SpectralMultiplicityData

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

/-- **Equality of spectral multiplicity data over an arbitrary `RCLike` scalar field.**

Two operators have the same spectral multiplicity when each is unitarily equivalent to the
multiplication model of a `TauCeti.MultiplicityDatum 𝕜` -- a finite measure on `ℂ` together with
an **antitone** sequence of measurable level sets -- and the two data agree: the base measures
are in the same **measure class**, and the level sets agree up to null sets.  The spectral
parameter and base measure remain complex; only the `L²` fibres and model operator use `𝕜`.

The measure class is `TauCeti.MeasureEquiv`, a named relation proved to be an `Equivalence` at
the point of definition so that the quotient can be formed later.

This is an existential over *presentations*, and it is what
makes
`TauCeti.sameSpectralMultiplicity_iff_operatorUnitaryEquiv_complex` provable.  It is **not** a
canonical
invariant: nothing here says the datum of an operator is unique. -/
def SameSpectralMultiplicity (A : H₁ →L[𝕜] H₁) (B : H₂ →L[𝕜] H₂) : Prop :=
  ∃ D E : MultiplicityDatum 𝕜,
    OperatorUnitaryEquiv A D.operator ∧
    OperatorUnitaryEquiv B E.operator ∧
    MeasureEquiv D.base E.base ∧
    ∀ k, D.base (symmDiff (D.level k) (E.level k)) = 0

/-- The introduction rule for `TauCeti.SameSpectralMultiplicity`: two models, in the same measure
class, with level sets agreeing up to null sets. -/
theorem sameSpectralMultiplicity_of_models {A : H₁ →L[𝕜] H₁} {B : H₂ →L[𝕜] H₂}
    (D E : MultiplicityDatum 𝕜) (hAD : OperatorUnitaryEquiv A D.operator)
    (hBE : OperatorUnitaryEquiv B E.operator) (hbase : MeasureEquiv D.base E.base)
    (hlevel : ∀ k, D.base (symmDiff (D.level k) (E.level k)) = 0) :
    SameSpectralMultiplicity A B :=
  ⟨D, E, hAD, hBE, hbase, hlevel⟩

/-- The elimination rule, dual to `TauCeti.sameSpectralMultiplicity_of_models`.  It exists so
that consumers can destructure the relation without relying on the definition unfolding. -/
theorem SameSpectralMultiplicity.exists_models {A : H₁ →L[𝕜] H₁} {B : H₂ →L[𝕜] H₂}
    (h : SameSpectralMultiplicity A B) :
    ∃ D E : MultiplicityDatum 𝕜,
      OperatorUnitaryEquiv A D.operator ∧
      OperatorUnitaryEquiv B E.operator ∧
      MeasureEquiv D.base E.base ∧
      ∀ k, D.base (symmDiff (D.level k) (E.level k)) = 0 :=
  h

end SpectralMultiplicityData

section ComplexClassification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

/-- **Same multiplicity data implies unitary equivalence**, with no separability hypothesis on
either space.

Chain the two models: `A ≃ D.operator ≃ E.operator ≃ B`.  The statement remains at the complex
specialization because the middle step `TauCeti.operatorUnitaryEquiv_of_measureEquiv_complex` uses
the
complex `rnDerivL2Equiv` API; the real analogue is proved separately from
`TauCeti.operatorUnitaryEquiv_of_measureEquiv_real`. -/
theorem operatorUnitaryEquiv_of_sameSpectralMultiplicity_complex (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂)
    (h : SameSpectralMultiplicity A B) : OperatorUnitaryEquiv A B := by
  obtain ⟨D, E, hAD, hBE, hbase, hlevel⟩ := h.exists_models
  exact hAD.trans ((operatorUnitaryEquiv_of_measureEquiv_complex hbase hlevel).trans hBE.symm)

/-- **Unitary equivalence implies the same multiplicity data.**

This is the direction that needs the existence half of Hahn--Hellinger, and therefore the
separability of `H₁`: a model for `A` is built from a *countable* cyclic decomposition, and
countability of the index is what lets the level-set normalisation run, since ranks count
earlier indices.  `H₂` needs nothing -- `B` inherits `A`'s model along the given unitary, so the
same datum serves for both. -/
theorem sameSpectralMultiplicity_of_operatorUnitaryEquiv_complex [CompleteSpace H₁]
    [TopologicalSpace.SeparableSpace H₁] (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂)
    (hA : IsSelfAdjoint A) (h : OperatorUnitaryEquiv A B) : SameSpectralMultiplicity A B := by
  obtain ⟨D, hAD⟩ := BorelCalculus.exists_hasMultiplicityModel hA.isStarNormal
  refine sameSpectralMultiplicity_of_models D D hAD ?_ (MeasureEquiv.refl _) fun k => ?_
  · exact (OperatorUnitaryEquiv.symm h).trans hAD
  · simp

/-- **Spectral multiplicity data classify bounded self-adjoint operators on a separable complex
Hilbert space up to unitary equivalence.**

Separability is carried on `H₁` only, and is needed for `→` alone; see
`TauCeti.operatorUnitaryEquiv_of_sameSpectralMultiplicity_complex` for the separability-free
converse.
Self-adjointness of `B` is not needed: it follows from that of `A` along the unitary, and in the
`←` direction it is not used at all. -/
theorem sameSpectralMultiplicity_iff_operatorUnitaryEquiv_complex [CompleteSpace H₁]
    [TopologicalSpace.SeparableSpace H₁] (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂)
    (hA : IsSelfAdjoint A) :
    SameSpectralMultiplicity A B ↔ OperatorUnitaryEquiv A B :=
  ⟨operatorUnitaryEquiv_of_sameSpectralMultiplicity_complex A B,
    sameSpectralMultiplicity_of_operatorUnitaryEquiv_complex A B hA⟩

end ComplexClassification

end TauCeti
