/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.SectionTwo

/-!
# Using the four Section 2 theorems

A worked reading of `DavisKahan.Sources.DavisKahan1970.SectionTwo` for someone who
knows operator theory and not this repository.  Nothing here is new mathematics:
each declaration below takes the data an operator theorist would already have and
hands it to one of the four canonical theorems, so the compiler checks that the
advertised entry points really are reachable from ordinary hypotheses.

What the four ask for, in the vocabulary of the subject:

* **the ambient operator** is a `LinearPMap` `A : H →ₗ.[𝕜] H` with
  `IsSelfAdjoint A` -- unbounded, with an explicit domain;
* **the trial or spectral subspace** is a `Submodule 𝕜 H` carrying
  `[HasOrthogonalProjection]`, or is selected from `A` by a measurable set of
  reals through `TauCeti.LinearPMap.specRange` / `realSpecRange`;
* **the gap** is either a `FormBoundedSylvesterGap` between two self-adjoint
  restrictions, or the printed ordered/interval separation written out;
* **the residual or perturbation** is a bounded operator: `R` in the `sin Θ`
  theorem, `H` in `tan Θ`, `E` in `sin 2Θ`, `B` in `tan 2Θ`;
* **the norm** is a `PaperUnitaryInvariantNorm`, the paper's symmetric gauge, and
  ideal membership of the perturbation (`N.Mem`) is a hypothesis while ideal
  membership of the angle is part of the conclusion -- in infinite dimension that
  is a statement, not a side condition;
* **the angle** in the conclusion is a paper object:
  `(I - F₀F₀⋆) E₀` for `sin Θ`, `paperTanAngleOperatorC` for `tan Θ`,
  `sinTwoAngleOperatorC` for `sin 2Θ`, `paperAbsTanTwoAngleOperatorC` for
  `tan 2Θ`.

Structural facts are carried by objects with constructors, so they never become
proof obligations for the caller:

```
DavisKahan.UnboundedRitzPair.ofTrialBlock        -- from a bounded compression bundle
DavisKahan.ReducingComplement.ofReducesSubspace  -- from `V` reduces `A`
DavisKahan.ReflectionIntertwines.ofReducesSubspace -- from `V` reduces `A + B`
```

The last two start from `TauCeti.LinearPMap.ReducesSubspace`, the generic
reducing-subspace vocabulary, which is what a spectral subspace already gives you.

No Sylvester witness, reflection block, secant, or capability instance appears
below, and none is needed.
-/

namespace TauCeti
namespace DavisKahan1970

universe u₁ v₁
namespace SectionTwoUsage

open scoped InnerProductSpace

open TauCeti.DavisKahan.ExactSinTheta TauCeti.DavisKahanExt

noncomputable section

universe v

/-! ## `sin Θ` from the printed interval/exterior separation -/

section SinTheta

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Reading `sin Θ` with the separation in its printed shape: the trial spectrum
inside `[β, α]`, the complementary spectrum outside `(β - δ, α + δ)`.

`FormBoundedSylvesterGap.intervalExterior` turns that into the gap the theorem
takes, and `_root_.DavisKahan1970.sinTheta_unbounded_intervalExterior_paperUINorm_complex` packages
the same step; this spells it out so the seam is visible. -/
theorem sinTheta_from_printed_separation
    (N : PaperUnitaryInvariantNorm)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : _root_.DavisKahan1970.IsTrialResidual A A₀ E₀ R)
    (hexact : _root_.DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (htrialSpec : TauCeti.LinearPMap.realSpectrum A₀ ⊆ Set.Icc β α)
    (hcomplSpec : TauCeti.LinearPMap.realSpectrum Λ₁ ⊆
      {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x})
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R :=
  SectionTwo.sinTheta_complex N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hδ
    (FormBoundedSylvesterGap.intervalExterior hβα (Or.inl ⟨htrialSpec, hcomplSpec⟩))
    hR

/-- The same call over an arbitrary `RCLike` field, through the newly bound
`SectionTwo.sinTheta`.

This is the reachability check for the scalar-generic endpoint: ordinary
operator-theory hypotheses in, printed conclusion out, with no problem record
assembled by hand.  The two class hypotheses are the field capabilities, which
`ℝ` and `ℂ` both satisfy by instance. -/
theorem sinTheta_from_printed_separation_rclike
    {𝕜 : Type u₁} [RCLike 𝕜]
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u₁, v₁} 𝕜]
    [TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan.{u₁, v₁} 𝕜]
    {E F G H : Type v₁}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (N : PaperUnitaryInvariantNorm)
    (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F) (Λ₁ : G →ₗ.[𝕜] G)
    (E₀ : F →L[𝕜] E) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : _root_.DavisKahan1970.IsTrialResidual A A₀ E₀ R)
    (hexact : _root_.DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (htrialSpec : TauCeti.LinearPMap.realSpectrum A₀ ⊆ Set.Icc β α)
    (hcomplSpec : TauCeti.LinearPMap.realSpectrum Λ₁ ⊆
      {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x})
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R :=
  SectionTwo.sinTheta N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hδ
    (FormBoundedSylvesterGap.intervalExterior hβα (Or.inl ⟨htrialSpec, hcomplSpec⟩))
    hR

end SinTheta

/-! ## `tan Θ` from a Ritz pair and a reducing subspace -/

section TanTheta

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Reading `tan Θ` when what you have is a reducing subspace rather than the
theorem's projection-commutation clauses.

`DavisKahan.ReducingComplement.ofReducesSubspace` is the only step; everything
else is the mathematics the theorem is about. -/
theorem tanTheta_from_reducingSubspace
    (N : PaperUnitaryInvariantNorm)
    {A : E →ₗ.[ℂ] E}
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace U]
    (D : DavisKahan.UnboundedRitzPair A U)
    (hVred : TauCeti.LinearPMap.ReducesSubspace A V)
    (Hop : E →L[ℂ] E) (hH : IsSelfAdjoint Hop)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual : D.trial.residual = Uᗮ.starProjection ∘L Hop ∘L U.subtypeL)
    (hMem : N.Mem Hop) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge Hop :=
  SectionTwo.tanTheta_complex N D (DavisKahan.ReducingComplement.ofReducesSubspace hVred)
    Hop hH hdelta hupper hUnwanted h35 hResidual hMem

/-- The same reading with a bounded Ritz compression, which is the common case.

`DavisKahan.UnboundedRitzPair.ofTrialBlock` builds the Ritz pair from the
`UnboundedTrialBlock` bundle, so neither of the two structural objects has to be
assembled by hand. -/
theorem tanTheta_from_trialBlock
    (N : PaperUnitaryInvariantNorm)
    {A : E →ₗ.[ℂ] E}
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace U]
    (D : DavisKahan.TanTheta.UnboundedTrialBlock A U)
    (hVred : TauCeti.LinearPMap.ReducesSubspace A V)
    (Hop : E →L[ℂ] E) (hH : IsSelfAdjoint Hop)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove
      (DavisKahan.UnboundedRitzPair.ofTrialBlock D).trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual : D.residual = Uᗮ.starProjection ∘L Hop ∘L U.subtypeL)
    (hMem : N.Mem Hop) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge Hop :=
  SectionTwo.tanTheta_complex N (DavisKahan.UnboundedRitzPair.ofTrialBlock D)
    (DavisKahan.ReducingComplement.ofReducesSubspace hVred) Hop hH hdelta hupper
    hUnwanted h35 hResidual hMem

end TanTheta

/-! ## `sin 2Θ` from a measurable spectral selection

This section was missing until 2026-08-31, and its absence hid a certification
defect: writing the call is what makes visible that the complex endpoint cannot
be reached at the source's half-infinite gap scope. -/

section SinTwoTheta

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- `sin 2Θ` over `ℂ`, from a measurable spectral selection and the printed
separation, through `SectionTwo.sinTwoTheta_complex`.

The separation is `FormBoundedSylvesterGap` between the two spectral
restrictions, which is the printed scope: it carries the bounded interval and
both half-infinite configurations.  `sinTwoTheta_from_halfInfinite_separation`
below exercises one of the latter, which is the case the endpoint could not be
written at until the complex full-gap route landed. -/
theorem sinTwoTheta_from_printed_separation
    (N : PaperUnitaryInvariantNorm)
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (Eop : E →L[ℂ] E) (hEop : DavisKahan.IsSelfAdjointOperator Eop)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : DavisKahan.ExactSinTheta.FormBoundedSylvesterGap
      (DavisKahan.selfAdjointSpectralRestriction A hA B hB)
      (DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahanExt.sinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahanExt.sinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop :=
  SectionTwo.sinTwoTheta_complex N A hA Eop hEop B S hB hS hδ hgap hEmem

/-- `sin 2Θ` over `ℂ` at a **half-infinite** separating interval.

The selected restriction is bounded below by `c + δ` in form and the
complementary restriction is bounded above by `c`; neither is bounded on the
other side.  Davis and Kahan state the four theorems with intervals that "may be
half-infinite", and this is that configuration: `[c + δ, ∞)` against `(-∞, c]`.

The caller supplies the two form bounds and nothing else — no finite `β ≤ α`, no
spectrum-avoidance certificate. -/
theorem sinTwoTheta_from_halfInfinite_separation
    (N : PaperUnitaryInvariantNorm)
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (Eop : E →L[ℂ] E) (hEop : DavisKahan.IsSelfAdjointOperator Eop)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {c δ : ℝ} (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (DavisKahan.selfAdjointSpectralRestriction A hA B hB) (c + δ))
    (hBcomplHigh : TauCeti.LinearPMap.SemiboundedAbove
      (DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ hB.compl) c)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahanExt.sinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahanExt.sinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop :=
  SectionTwo.sinTwoTheta_complex N A hA Eop hEop B S hB hS hδ
    (DavisKahan.ExactSinTheta.FormBoundedSylvesterGap.leftAboveRightBelow
      c hBlow hBcomplHigh)
    hEmem

end SinTwoTheta

/-! ## `tan 2Θ` from a subspace reducing the perturbed operator -/

section TanTwoTheta

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Reading `tan 2Θ` when what you have is a subspace reducing `A + B`.

`DavisKahan.ReflectionIntertwines.ofReducesSubspace` supplies the reflection and
its commutation; the caller never builds a spectral reflection, never proves it
self-adjoint or involutive, and never certifies that `cos 2θ` avoids zero -- the
ordered gap already forces that. -/
theorem tanTwoTheta_from_reducingSubspace
    (N : PaperUnitaryInvariantNorm)
    {A : E →ₗ.[ℂ] E} {B : E →L[ℂ] E} {a b c : ℝ}
    (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A)
    (hBsa : IsSelfAdjoint B)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
    (hVred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain,
      (x : E) ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : E) ∈
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    (hab : a < b) (hBmem : N.Mem B) :
    N.Mem (paperAbsTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V) ∧
      (b - a) * N.gauge (paperAbsTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V) ≤
        2 * N.gauge B :=
  SectionTwo.tanTwoTheta_complex N V hA hBsa hB
    (DavisKahan.ReflectionIntertwines.ofReducesSubspace hVred) hUa hUb hab hBmem

end TanTwoTheta

end

end SectionTwoUsage
end DavisKahan1970
end TauCeti
