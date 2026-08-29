/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
import DavisKahan.Geometry.Halmos.GenericReconstruction
import ForTauCeti.Analysis.InnerProductSpace.RealContinuousFunctionalCalculus
import DavisKahan.SpectralTheory.Real.SpectralMultiplicityClassification

/-!
# Davis--Kahan 1970, Theorem 3.1 in the paper's multiplicity phrasing

Theorem 3.1 classifies ordered pairs of subspaces up to a unitary of the ambient space.  Its
invariant has two halves: the dimensions of the four elementary Halmos summands, and the *spectral
multiplicity function* of the angle operator on the generic part.  The two source-facing
statements below record exactly that, over `ℂ` and over `ℝ`.

Each is a wrapper over two independently proved theorems and adds no mathematics of its own:

* the operator-level Halmos classification `twoProjection_operator_classification` below, which
  carries the classification *content* with no compactness, no finite dimension and no
  separability; and
* the spectral-multiplicity translation of its generic invariant --
  `TauCeti.sameSpectralMultiplicity_iff_operatorUnitaryEquiv` over `ℂ`, and
  `TauCeti.DavisKahan.RealSpectralRestriction.sameSpectralMultiplicity_iff_operatorUnitaryEquiv_real`
  over `ℝ` -- which is Hahn--Hellinger, and which Mathlib has for no scalar field.

## The angle operator is `genericCosineBlock`

The statement compares the `U`-side cosine block on the generic part, not the symmetrized block
`genericHalmosCosineSq`.  On the generic part the symmetrized operator is `A ⊕ A` -- doubled
multiplicity -- and recovering `A` from `A ⊕ A` is multiplicity-halving, which this development
does not have and does not need.  Davis and Kahan state Theorem 3.1 for the angle operator on the
`U`-side, so the block used here is the paper-faithful reading; the docstring at
`SameHalmosCosineBlockInvariant` in `Geometry/Halmos/GenericReconstruction.lean` records the
2026-08-04 decision.

## On separability

Separability is carried on `H₁` only.  It is one of the paper's **standing assumptions**, taken
from the Introduction and Sections 1--2 and so governing Section 3; see
`prose/distilled_literature/DavisKahan1970_part_III.tex`, *Standing assumptions from the
transcription*.  It is needed for `→` alone -- producing a multiplicity model requires the
existence half of Hahn--Hellinger -- and the `←` direction is separability-free.  Nothing already
proved is weakened by it: `twoProjection_operator_classification`, grounded on
`pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`, remains stated and proved
with no separability at all.

## Note on the relation carrier

The Halmos classification layer still states its generic component with
`TauCeti.DavisKahan.BoundedOperatorsUnitaryEquivalent`, while the promoted
multiplicity theorems are stated with the canonical `TauCeti.OperatorUnitaryEquiv`.  The two are
literally the same existential; `operatorUnitaryEquiv_iff_boundedOperatorsUnitaryEquivalent`
below is the one-line bridge, and it is private because the intended long-term outcome is that
the Halmos layer moves to the canonical relation and the bridge disappears.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open DavisKahan
open DavisKahan.RealSpectralRestriction

universe u v

section Bridge

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

private theorem operatorUnitaryEquiv_iff_boundedOperatorsUnitaryEquivalent
    (A : H₁ →L[𝕜] H₁) (B : H₂ →L[𝕜] H₂) :
    OperatorUnitaryEquiv A B ↔ BoundedOperatorsUnitaryEquivalent A B :=
  Iff.rfl

end Bridge

section OperatorClassification

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule 𝕜 H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule 𝕜 H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-! The converse direction reconstructs the pair from the cosine block through the
polar decomposition of the Halmos cross block, so it carries the functional-calculus
hypotheses of `Geometry/Halmos/GenericReconstruction.lean`.  They are found by typeclass
inference at `𝕜 = ℂ` and at `𝕜 = ℝ` alike. -/

variable [Algebra ℝ (genericLeftHalf U₁ V₁ →L[𝕜] genericLeftHalf U₁ V₁)]
  [IsScalarTower ℝ 𝕜 (genericLeftHalf U₁ V₁ →L[𝕜] genericLeftHalf U₁ V₁)]
  [ContinuousFunctionalCalculus ℝ
    (genericLeftHalf U₁ V₁ →L[𝕜] genericLeftHalf U₁ V₁) IsSelfAdjoint]
variable [Algebra ℝ (genericLeftHalf U₂ V₂ →L[𝕜] genericLeftHalf U₂ V₂)]
  [IsScalarTower ℝ 𝕜 (genericLeftHalf U₂ V₂ →L[𝕜] genericLeftHalf U₂ V₂)]
  [ContinuousFunctionalCalculus ℝ
    (genericLeftHalf U₂ V₂ →L[𝕜] genericLeftHalf U₂ V₂) IsSelfAdjoint]

/-- **Davis--Kahan 1970, Theorem 3.1: the operator-level classification, both
directions.**

Two ordered pairs of subspaces are unitarily equivalent *as pairs* exactly when
their four elementary Halmos summands are isometric and their angle operators
`cos²Θ` -- read on the `U`-side, as the paper reads them -- are unitarily
equivalent.  This is the constructive spine of the theorem and needs no
direct-integral presentation, no compactness, no finite dimension and no
separability.

Grounded by `:=` on
`pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`, so there
is a single source of truth; the two forms differ only in splitting the stable
five-field invariant into the paper's two printed halves.  The forward direction
restricts a pair-equivalence to the `U`-half of the generic part; the converse is
bricks (1) and (2) -- brick (1) reconstructs the generic-part unitary from the
cosine block alone (`Geometry/Halmos/GenericReconstruction`), brick (2) glues it
to the four elementary summand isometries (`Geometry/Halmos/Assembly`). -/
theorem twoProjection_operator_classification :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
        BoundedOperatorsUnitaryEquivalent
          (genericCosineBlock U₁ V₁) (genericCosineBlock U₂ V₂) := by
  rw [pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant
    U₁ V₁ U₂ V₂]
  constructor
  · rintro ⟨hc, hs, ht, he, hg⟩
    exact ⟨⟨hc, hs, ht, he⟩, hg⟩
  · rintro ⟨⟨hc, hs, ht, he⟩, hg⟩
    exact ⟨hc, hs, ht, he, hg⟩

end OperatorClassification

section RealOperatorClassification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℝ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℝ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

set_option maxSynthPendingDepth 3

/-- **Davis--Kahan 1970, Theorem 3.1, the operator-level classification, over a
real Hilbert space.**

The `𝕜 = ℝ` instance of `twoProjection_operator_classification`.  No
compactness, no finite dimension, no separability. -/
theorem twoProjection_operator_classification_real :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
        BoundedOperatorsUnitaryEquivalent
          (genericCosineBlock U₁ V₁) (genericCosineBlock U₂ V₂) :=
  twoProjection_operator_classification U₁ V₁ U₂ V₂

end RealOperatorClassification

section ComplexClassification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℂ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℂ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-! Instantiating the field-generic Halmos classification at `𝕜 = ℂ` asks typeclass
inference for `ContinuousFunctionalCalculus ℝ (M →L[ℂ] M) IsSelfAdjoint` with `M` the
`U`-half of the generic part.  Mathlib supplies it through the C⋆-algebra structure on
bounded operators, but reaching it from a subspace coercion needs one more level of
pending synthesis than the default allows; the instance is found at depth `3`. -/
set_option maxSynthPendingDepth 3

/-- **Davis--Kahan 1970, Theorem 3.1**, in the paper's own phrasing: the spectral multiplicity
data of the two angle operators, together with the elementary multiplicities, form a complete
invariant for ordered pairs of subspaces of a complex Hilbert space.

See the module docstring for the choice of angle operator and for the status of the separability
hypothesis. -/
theorem theorem3_1_spectralMultiplicity_classification
    [TopologicalSpace.SeparableSpace H₁] :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      SameSpectralMultiplicity
        (genericCosineBlock U₁ V₁)
        (genericCosineBlock U₂ V₂) := by
  rw [twoProjection_operator_classification]
  constructor
  · rintro ⟨htriv, hgen⟩
    refine ⟨htriv, sameSpectralMultiplicity_of_operatorUnitaryEquiv _ _ ?_ ?_⟩
    · exact isSelfAdjoint_genericCosineBlock U₁ V₁
    · exact (operatorUnitaryEquiv_iff_boundedOperatorsUnitaryEquivalent _ _).2 hgen
  · rintro ⟨htriv, hmult⟩
    exact ⟨htriv, (operatorUnitaryEquiv_iff_boundedOperatorsUnitaryEquivalent _ _).1
      (operatorUnitaryEquiv_of_sameSpectralMultiplicity _ _ hmult)⟩

end ComplexClassification

section RealClassification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℝ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℝ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

set_option maxSynthPendingDepth 3

/-- **Davis--Kahan 1970, Theorem 3.1, in the paper's own phrasing, over a real Hilbert space.**

The spectral multiplicity data of the two angle operators, together with the elementary
multiplicities, form a complete invariant for ordered pairs of subspaces of a real Hilbert space.

The classification *content* was already real (`twoProjection_operator_classification_real`, with
no compactness, no finite dimension and no separability); what is added here is the translation of
its invariant into multiplicity language, which is Hahn--Hellinger over `ℝ`.  Separability of
`H₁` is carried for the `→` direction alone, exactly as in the complex statement; the `←`
direction is separability-free. -/
theorem theorem3_1_spectralMultiplicity_classification_real
    [TopologicalSpace.SeparableSpace H₁] :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      SameSpectralMultiplicity
        (genericCosineBlock U₁ V₁)
        (genericCosineBlock U₂ V₂) := by
  rw [twoProjection_operator_classification]
  constructor
  · rintro ⟨htriv, hgen⟩
    refine ⟨htriv, sameSpectralMultiplicity_of_operatorUnitaryEquiv_real _ _ ?_ ?_⟩
    · exact isSelfAdjoint_genericCosineBlock U₁ V₁
    · exact (operatorUnitaryEquiv_iff_boundedOperatorsUnitaryEquivalent _ _).2 hgen
  · rintro ⟨htriv, hmult⟩
    exact ⟨htriv, (operatorUnitaryEquiv_iff_boundedOperatorsUnitaryEquivalent _ _).1
      (operatorUnitaryEquiv_of_sameSpectralMultiplicity_real _ _ hmult)⟩

end RealClassification

end DavisKahan1970
end TauCeti
