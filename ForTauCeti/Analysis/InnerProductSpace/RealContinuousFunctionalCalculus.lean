/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Complexification.Spectrum
public import ForTauCeti.Analysis.InnerProductSpace.Polar.PartialIsometry

/-!
# Continuous functional calculus over `ℝ` for a real Hilbert space

`ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint` registers

```text
ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint
```

for **every** real Hilbert space `E`, at unrestricted dimension.

## Why this is not in Mathlib

Mathlib's only unital real calculus for operators,
`IsSelfAdjoint.instContinuousFunctionalCalculus`, descends by spectrum restriction from a
calculus over `ℂ` for star-normal elements, and `CStarAlgebra (E →L[𝕜] E)` is registered only
at `𝕜 = ℂ`.  `Matrix n n 𝕜` escapes this through a separate spectral-theorem construction in
`Analysis/Matrix/HermitianFunctionalCalculus.lean`, so a real matrix calculus exists while the
operator one does not.  Mathlib records the gap in prose: `Analysis/InnerProductSpace/`
`StarOrder.lean` proves `ContinuousLinearMap.instStarOrderedRingRCLike` for a general `RCLike`
field and declines to register it, because it takes exactly this calculus as an argument and
"for the moment we only have this for `𝕜 := ℂ`".  Registering the instance below therefore also
supplies `StarOrderedRing (E →L[ℝ] E)`, and turns the whole `RCLike`-generic operator modulus
and polar factorization API of this library from stated into usable over `ℝ`.

**This result is not on the current Tau Ceti roadmap and is proposed for it.**

## The construction

Complexification, as a proof technique rather than as architecture: the missing ingredient is
genuinely complex-only, so the smallest necessary portion is transported and the actual
mathematical object -- `cfcHom` itself -- is descended, not an existential witness.

For `a : E →L[ℝ] E` self-adjoint:

1. `complexify a` is a self-adjoint operator on the complexification, and the complexified
   algebra already carries a real calculus (`realContinuousFunctionalCalculus`);
2. `spectrum_complexify` identifies the two spectra, so the symbol algebras agree
   (`spectrumComplexifyMap`) and `complexifiedCfcHom` is a real `⋆`-algebra map
   `C(spectrum ℝ a, ℝ) →⋆ₐ[ℝ] (Eℂ →L[ℂ] Eℂ)`;
3. its whole image is fixed by the canonical conjugation
   (`conjugateOperator_complexifiedCfcHom`, from `conjugateOperator_cfcHom`), and a
   conjugation-fixed operator **is** a complexification (`complexify_realPartOperator`), so the
   map descends to `realCfcHom : C(spectrum ℝ a, ℝ) →⋆ₐ[ℝ] (E →L[ℝ] E)`;
4. every field of the calculus is then read off through `complexify`, which is an injective
   isometric unital `⋆`-algebra map (`complexifyStarAlgHom`, `isometry_complexify`).

## Main results

* `TauCeti.RealComplexification.realCfcHom`: the descended calculus;
* `ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint`: the instance;
* the `example`s at the end of the file: `modulus` and `polarPartial` at `ℝ`.

## A duplication this file does not resolve

`complexify_mul`, `complexify_one` and `complexify_star` are each declared in two or three
`DavisKahan` modules, in different namespaces, and several consumers use the bare names under an
`open` of `TauCeti.RealComplexification`.  Adding canonical copies here would make those uses
ambiguous, so this file routes through `complexifyStarAlgHom` and `map_mul` / `map_one` /
`map_star` instead.  Consolidating the three copies into `Complexification/Basic.lean` is a
separate, mechanical piece of work.
-/

public section

open scoped InnerProductSpace

namespace TauCeti
namespace RealComplexification

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## Transporting the symbol algebra -/

/-- The identity, read as a map from the spectrum of `complexify a` to the spectrum of `a`.
It is a bijection, by `spectrum_complexify`. -/
@[expose]
def spectrumComplexifyMap (a : E →L[ℝ] E) :
    C(spectrum ℝ (complexify a), spectrum ℝ a) :=
  ⟨Set.inclusion (spectrum_complexify a).subset, continuous_inclusion _⟩

omit [CompleteSpace E] in
/-- `spectrumComplexifyMap` does not move points: it is the identity on underlying reals. -/
@[simp]
theorem spectrumComplexifyMap_coe (a : E →L[ℝ] E) (x : spectrum ℝ (complexify a)) :
    ((spectrumComplexifyMap a x : spectrum ℝ a) : ℝ) = (x : ℝ) := rfl

omit [CompleteSpace E] in
/-- `spectrumComplexifyMap` is surjective, the two spectra being equal.  This is what makes
precomposition with it injective on symbols, and what turns `Set.range (f ∘ _)` into
`Set.range f`. -/
theorem spectrumComplexifyMap_surjective (a : E →L[ℝ] E) :
    Function.Surjective (spectrumComplexifyMap a) := fun y =>
  ⟨⟨(y : ℝ), by rw [spectrum_complexify]; exact y.2⟩, Subtype.ext rfl⟩

/-! ## The calculus of `a`, computed in the complexification -/

/-- The real continuous functional calculus of `a`, taken in the complexified operator
algebra: a symbol on `spectrum ℝ a` is read as a symbol on `spectrum ℝ (complexify a)` and fed
to the calculus that `Complexification/FunctionalCalculus.lean` already registers there. -/
@[expose]
def complexifiedCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    C(spectrum ℝ a, ℝ) →⋆ₐ[ℝ] (RealComplexification E →L[ℂ] RealComplexification E) :=
  (cfcHom ((complexify_isSelfAdjoint_iff a).2 ha)).comp
    (ContinuousMap.compStarAlgHom' ℝ ℝ (spectrumComplexifyMap a))

/-- `complexifiedCfcHom` unfolded: reindex the symbol, then apply the complex-algebra
calculus. -/
theorem complexifiedCfcHom_apply {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) :
    complexifiedCfcHom ha f =
      cfcHom ((complexify_isSelfAdjoint_iff a).2 ha) (f.comp (spectrumComplexifyMap a)) := rfl

/-- `complexifiedCfcHom` is continuous: `cfcHom` is, and reindexing symbols is. -/
theorem continuous_complexifiedCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    Continuous (complexifiedCfcHom ha) :=
  ((cfcHom_continuous ((complexify_isSelfAdjoint_iff a).2 ha)).comp
    (ContinuousMap.continuous_precomp (spectrumComplexifyMap a))).congr fun f =>
      (complexifiedCfcHom_apply ha f).symm

/-- `complexifiedCfcHom` is injective: `cfcHom` is, and reindexing along a surjection is. -/
theorem complexifiedCfcHom_injective {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    Function.Injective (complexifiedCfcHom ha) := by
  intro f g hfg
  rw [complexifiedCfcHom_apply, complexifiedCfcHom_apply] at hfg
  have h := cfcHom_injective ((complexify_isSelfAdjoint_iff a).2 ha) hfg
  refine ContinuousMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := spectrumComplexifyMap_surjective a x
  exact congrFun (congrArg DFunLike.coe h) y

/-- `complexifiedCfcHom` sends the restricted identity symbol to `complexify a`. -/
theorem complexifiedCfcHom_id {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    complexifiedCfcHom ha ((ContinuousMap.id ℝ).restrict (spectrum ℝ a)) = complexify a := by
  have h : ((ContinuousMap.id ℝ).restrict (spectrum ℝ a)).comp (spectrumComplexifyMap a) =
      (ContinuousMap.id ℝ).restrict (spectrum ℝ (complexify a)) := by
    exact ContinuousMap.ext fun x => rfl
  rw [complexifiedCfcHom_apply, h, cfcHom_id]

/-- The spectral mapping theorem for `complexifiedCfcHom`. -/
theorem complexifiedCfcHom_map_spectrum {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) :
    spectrum ℝ (complexifiedCfcHom ha f) = Set.range f := by
  rw [complexifiedCfcHom_apply, cfcHom_map_spectrum]
  exact (spectrumComplexifyMap_surjective a).range_comp f

/-- `complexifiedCfcHom` produces self-adjoint operators, real symbols being self-adjoint. -/
theorem isSelfAdjoint_complexifiedCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) : IsSelfAdjoint (complexifiedCfcHom ha f) := by
  rw [complexifiedCfcHom_apply]
  exact cfcHom_predicate ((complexify_isSelfAdjoint_iff a).2 ha) _

/-- **The calculus of `complexify a` stays in the fixed-point subalgebra of the canonical
conjugation.**  This is the descent step: by `complexify_realPartOperator` a conjugation-fixed
operator *is* the complexification of a bounded real operator. -/
theorem conjugateOperator_complexifiedCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) :
    conjugateOperator (complexifiedCfcHom ha f) = complexifiedCfcHom ha f := by
  rw [complexifiedCfcHom_apply]
  exact conjugateOperator_cfcHom _ ((complexify_isSelfAdjoint_iff a).2 ha)
    (conjugateOperator_complexify a) _

/-! ## The descended calculus -/

/-- The real continuous functional calculus of a self-adjoint `a : E →L[ℝ] E`, as a function on
symbols: `complexifiedCfcHom` followed by the descent of a conjugation-fixed operator to the
real copy.  `complexifyStarAlgHom_realCfcFun` says the descent is exact. -/
@[expose]
def realCfcFun {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) (f : C(spectrum ℝ a, ℝ)) : E →L[ℝ] E :=
  realPartOperator (complexifiedCfcHom ha f)

/-- **The defining property of the descended calculus.**  Every algebraic law below is this
identity plus injectivity of `complexify`. -/
theorem complexifyStarAlgHom_realCfcFun {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) :
    complexifyStarAlgHom (realCfcFun ha f) = complexifiedCfcHom ha f := by
  rw [complexifyStarAlgHom_apply]
  exact complexify_realPartOperator (conjugateOperator_complexifiedCfcHom ha f)

/-- `complexifyStarAlgHom` is injective; this is `complexify_injective` under the bundling. -/
theorem complexifyStarAlgHom_injective :
    Function.Injective (complexifyStarAlgHom (E := E)) := complexify_injective

/-- **The real continuous functional calculus of a self-adjoint bounded operator on a real
Hilbert space**, bundled as a `⋆`-algebra homomorphism over `ℝ`. -/
@[expose]
def realCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    C(spectrum ℝ a, ℝ) →⋆ₐ[ℝ] (E →L[ℝ] E) where
  toFun := realCfcFun ha
  map_one' := complexifyStarAlgHom_injective <| by
    rw [complexifyStarAlgHom_realCfcFun, map_one, map_one]
  map_mul' f g := complexifyStarAlgHom_injective <| by
    rw [complexifyStarAlgHom_realCfcFun, map_mul complexifyStarAlgHom,
      complexifyStarAlgHom_realCfcFun, complexifyStarAlgHom_realCfcFun, map_mul]
  map_zero' := complexifyStarAlgHom_injective <| by
    rw [complexifyStarAlgHom_realCfcFun, map_zero, map_zero]
  map_add' f g := complexifyStarAlgHom_injective <| by
    rw [complexifyStarAlgHom_realCfcFun, map_add complexifyStarAlgHom,
      complexifyStarAlgHom_realCfcFun, complexifyStarAlgHom_realCfcFun, map_add]
  commutes' r := complexifyStarAlgHom_injective <| by
    rw [complexifyStarAlgHom_realCfcFun, AlgHomClass.commutes, AlgHomClass.commutes]
  map_star' f := complexifyStarAlgHom_injective <| by
    rw [complexifyStarAlgHom_realCfcFun, map_star complexifyStarAlgHom,
      complexifyStarAlgHom_realCfcFun, map_star]

/-- `realCfcHom` acts by `realCfcFun`. -/
@[simp]
theorem realCfcHom_apply {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) (f : C(spectrum ℝ a, ℝ)) :
    realCfcHom ha f = realCfcFun ha f := rfl

/-- **The descent identity for the bundled calculus**: complexifying `realCfcHom` recovers the
calculus computed in the complexification.  Every property of `realCfcHom` below is transported
through this equation. -/
theorem complexify_realCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) :
    complexify (realCfcHom ha f) = complexifiedCfcHom ha f :=
  complexifyStarAlgHom_realCfcFun ha f

/-- `realCfcHom` is continuous.  Continuity transports *backwards* along `complexify` because
it is an isometric embedding, not merely norm-preserving; this is what `isometry_complexify`
is for. -/
theorem continuous_realCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    Continuous (realCfcHom ha) := by
  refine (isometry_complexify (E := E) (F := E)).isEmbedding.isInducing.continuous_iff.2 ?_
  simpa only [Function.comp_def, complexify_realCfcHom] using continuous_complexifiedCfcHom ha

/-- `realCfcHom` is injective. -/
theorem realCfcHom_injective {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    Function.Injective (realCfcHom ha) := fun f g hfg =>
  complexifiedCfcHom_injective ha <| by
    rw [← complexify_realCfcHom, ← complexify_realCfcHom, hfg]

/-- `realCfcHom` sends the restricted identity symbol to `a`; with continuity and
multiplicativity this is what pins the calculus down uniquely. -/
theorem realCfcHom_id {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    realCfcHom ha ((ContinuousMap.id ℝ).restrict (spectrum ℝ a)) = a :=
  complexify_injective <| by
    rw [complexify_realCfcHom, complexifiedCfcHom_id]

/-- **The spectral mapping theorem over `ℝ`**: the spectrum of `f` applied to `a` is the range
of `f` on the spectrum of `a`. -/
theorem realCfcHom_map_spectrum {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) : spectrum ℝ (realCfcHom ha f) = Set.range f := by
  rw [← spectrum_complexify, complexify_realCfcHom, complexifiedCfcHom_map_spectrum]

/-- `realCfcHom` produces self-adjoint operators, so the calculus is closed on its own
predicate. -/
theorem isSelfAdjoint_realCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) : IsSelfAdjoint (realCfcHom ha f) :=
  (complexify_isSelfAdjoint_iff _).1 <| by
    rw [complexify_realCfcHom]
    exact isSelfAdjoint_complexifiedCfcHom ha f

/-! ## Nontriviality -/

omit [CompleteSpace E] in
/-- A nontrivial bounded operator algebra forces a nontrivial space. -/
theorem nontrivial_of_nontrivial_operator (h : Nontrivial (E →L[ℝ] E)) : Nontrivial E := by
  by_contra hE
  rw [not_nontrivial_iff_subsingleton] at hE
  exact (not_subsingleton (E →L[ℝ] E))
    ⟨fun S T => ContinuousLinearMap.ext fun x => Subsingleton.elim _ _⟩

end

end RealComplexification
end TauCeti

/-! ## The instance -/

namespace ContinuousLinearMap

open TauCeti.RealComplexification
open scoped TauCeti.RealComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The continuous functional calculus over `ℝ` for self-adjoint bounded operators on a real
Hilbert space, in unrestricted dimension.** -/
instance instContinuousFunctionalCalculusRealIsSelfAdjoint :
    ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint where
  predicate_zero := IsSelfAdjoint.zero _
  compactSpace_spectrum a := isCompact_iff_compactSpace.mp (spectrum.isCompact a)
  spectrum_nonempty a ha := by
    have hE : Nontrivial E := nontrivial_of_nontrivial_operator inferInstance
    have hc : Nontrivial (TauCeti.RealComplexification E) :=
      (ofReal (E := E)).injective.nontrivial
    have : Nontrivial
        (TauCeti.RealComplexification E →L[ℂ] TauCeti.RealComplexification E) :=
      ⟨1, 0, one_ne_zero⟩
    rw [← spectrum_complexify a]
    exact ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) (complexify a)
      ((complexify_isSelfAdjoint_iff a).2 ha)
  exists_cfc_of_predicate a ha :=
    ⟨realCfcHom ha, continuous_realCfcHom ha, realCfcHom_injective ha, realCfcHom_id ha,
      realCfcHom_map_spectrum ha, isSelfAdjoint_realCfcHom ha⟩

/-! ## The downstream API, instantiated at `ℝ`

The instance above is worth having only because it discharges the hypothesis block

```text
[Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
[ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]
```

that `OperatorModulus.lean`, `ModulusConjugation.lean` and `Polar/PartialIsometry.lean` carry.
"The instance compiles" and "the downstream API is usable" are different claims; these
statements check the second one, at unrestricted dimension, between two different real spaces.
They are `example`s deliberately -- they add no names, and they fail loudly if the instance ever
stops being found. -/

section Downstream

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

example : StarOrderedRing (E →L[ℝ] E) := inferInstance

example (T : E →L[ℝ] F) : 0 ≤ T.modulus := T.modulus_nonneg

example (T : E →L[ℝ] F) : T.modulus * T.modulus = T.adjoint ∘L T := T.modulus_mul_self

example (T : E →L[ℝ] F) (x : E) : ‖T.modulus x‖ = ‖T x‖ := T.norm_modulus_apply x

example (T : E →L[ℝ] F) : ‖T.modulus‖ = ‖T‖ := T.norm_modulus

example (T : E →L[ℝ] F) : T.polarPartial ∘L T.modulus = T := T.polarPartial_comp_modulus

example (T : E →L[ℝ] F) : T.polarPartial.IsPartialIsometry := T.polarPartial_isPartialIsometry

end Downstream

end ContinuousLinearMap
