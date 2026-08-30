/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.Sources.DavisKahan1970.FullSineTheta
import DavisKahan.SinTheta.Canonical
import DavisKahan.SinTheta.Real.Canonical

/-!
# The Davis--Kahan 1970 sine-theta source surface

**The canonical source-facing theorems are `sinTheta_complex` and
`sinTheta_real`**, at the end of this module, and they are re-exported as
`TauCeti.DavisKahan1970.SectionTwo.sinTheta` / `…sinTheta_real` alongside the other
three Section 2 results.  They state the Section 2 result at
its full proved scope: unbounded self-adjoint `LinearPMap` operators, arbitrary
Hilbert dimension, the whole `FormBoundedSylvesterGap` rather than one of its
branches, a `PaperUnitaryInvariantNorm`, and both conclusions -- ideal membership
and the inequality.  They carry no capability class.  Cite one of those two.

`sinTheta_headline` below is kept for **presentation and compatibility**.  It is
scalar-generic, which reads well, but it pays for that twice: it carries the
capability classes `ContinuousLinearMap.HasMinMaxLowerBoundEverywhere` and
`HasUnboundedSylvesterKyFan` in its signature, and it inlines the finite
interval/exterior branch of the separation, so it states a strictly smaller
theorem than the one that is proved.  It also drops the ideal-membership half of
the conclusion.  It remains correct and remains the declaration the semantic
review reads for its explicit `sinTheta₀` parameter; it is no longer the theorem
to cite.

The substantive proof remains
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

/-- **Davis--Kahan 1970, Section 2 sine-theta theorem, presentation form.**

**Not the theorem to cite.**  `sinTheta_complex` and `sinTheta_real` below are the
canonical source-facing statements; this one is kept because its explicit
`sinTheta₀` parameter makes the printed inequality legible in the signature, and
because callers already depend on it.

It is generic over `RCLike 𝕜`, so it retains the real/complex and
infinite-dimensional scope of the proved headline theorem -- but that genericity
is why it must carry the two capability classes, and its separation hypothesis is
only the interval/exterior branch of `FormBoundedSylvesterGap`.

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

/-! ## The canonical fixed-field statements

`sinTheta_headline` above is the presentation declaration, and it pays for being
scalar-generic twice over: it carries the two capability classes
`ContinuousLinearMap.HasMinMaxLowerBoundEverywhere` and
`HasUnboundedSylvesterKyFan`, and its separation hypothesis is only the finite
interval/exterior branch.

Neither cost is Davis--Kahan mathematics.

The capability classes package the unbounded Sylvester Ky Fan estimate and a
min-max lower bound, both of which this repository *proves* for the two scalar
fields the paper uses.  They appear in a scalar-generic signature only because
`RCLike` is an open abstraction: separate proofs for `ℝ` and `ℂ` do not give a
proof for an arbitrary instance.  A reader of the source theorem should not have
to meet them, and a caller working over `ℂ` or `ℝ` should not have to supply
them.

The separation hypothesis is the second cost.  `FormBoundedSylvesterGap` is the
general form-bounded gap, and the interval/exterior configuration is one of its
constructors (`FormBoundedSylvesterGap.intervalExterior`); the ordered half-line
configurations the Appendix needs are others.  Stating the headline with the
interval branch inlined therefore fixes a strictly smaller theorem than the one
that is proved.

The two declarations below are the canonical source-facing statements: direct
argument lists, the full gap, both conclusions, and no capability class.  The
scalar-generic `sinTheta_headline_generic` remains the engine underneath. -/

section FixedField

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Davis--Kahan 1970, the sine-theta theorem, over `ℂ`.**

For an unbounded self-adjoint ambient operator `A`, a trial pair `(A₀, E₀)` with
domain-aware residual `R`, an exact complementary spectral decomposition
`(Λ₁, F₀, F₁)`, and a form-bounded Sylvester gap `δ` between the trial and
complementary spectra, the sine of the angle between the trial and desired
subspaces is controlled by the residual in every source unitarily invariant
norm:

`δ · N(sin Θ₀) ≤ N(R)`, where `sin Θ₀ = (1 − F₀F₀*) E₀`.

The theorem also concludes that `sin Θ₀` lies in the norm's ideal, which in
infinite dimension is part of the statement rather than a side condition.

This is the full gap scope: `FormBoundedSylvesterGap` covers the interval and
exterior configuration of Section 2 and the ordered half-line configurations of
the Appendix alike. -/
theorem sinTheta_complex
    (N : PaperUnitaryInvariantNorm)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R := by
  refine N.mul_gauge_le_of_all_mul_kyFan_le hδ hR ?_
  intro k
  by_cases hk : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hmain :=
      FormBoundedIsometricSinThetaProblem.result_complex
        (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hkpos)
        { data :=
            { A := A, A₀ := A₀, Λ₁ := Λ₁, X := E₀, F₁ := F₁, residual := R
              X_maps_domain := htrial.mapsDomain
              F₁_maps_domain := hexact.mapsDomain
              residual_eq := htrial.residualEquation
              intertwines := hexact.intertwines }
          exactMap := F₀
          ambient_selfAdjoint := hA
          trial_selfAdjoint := hA₀
          complement_selfAdjoint := hΛ₁
          trial_isometry := htrial.isometry
          exact_decomposition :=
            { isometry₀ := hexact.desiredIsometry
              isometry₁ := hexact.complementIsometry
              orthogonal := hexact.orthogonal
              projection_sum := hexact.complete }
          gap := δ
          gap_pos := hδ
          spectral_gap := hgap
          residual_mem := KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℂ) k hkpos R }
    simpa only [KyFanDominantIdealFamily.kyFan_gauge] using hmain.2

/-- **The familiar Section 2 interval form, over `ℂ`.**

`sinTheta_complex` with the gap spelled out as the printed separation: the
trial spectrum inside `[β, α]` and the complementary spectrum outside
`(β − δ, α + δ)`, or the same with the two roles exchanged.  This is one
constructor of `FormBoundedSylvesterGap`; the Appendix's ordered half-line
configurations are others, and they reach the theorem above directly. -/
theorem sinTheta_complex_of_intervalExterior
    (N : PaperUnitaryInvariantNorm)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hspectral :
      (TauCeti.LinearPMap.realSpectrum A₀ ⊆ Set.Icc β α ∧
          TauCeti.LinearPMap.realSpectrum Λ₁ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}) ∨
        (TauCeti.LinearPMap.realSpectrum Λ₁ ⊆ Set.Icc β α ∧
          TauCeti.LinearPMap.realSpectrum A₀ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}))
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R :=
  sinTheta_complex N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hδ
    (FormBoundedSylvesterGap.intervalExterior hβα hspectral) hR

end FixedField

section FixedFieldReal

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Davis--Kahan 1970, the sine-theta theorem, over `ℝ`.**

The real-scalar sibling of `sinTheta_complex`, with the same argument list and
the same full gap scope.  The real proof descends from the complex one by
complexification inside `result_real`; the descent is not visible here. -/
theorem sinTheta_real
    (N : PaperUnitaryInvariantNorm)
    (A : E →ₗ.[ℝ] E) (A₀ : F →ₗ.[ℝ] F) (Λ₁ : G →ₗ.[ℝ] G)
    (E₀ : F →L[ℝ] E) (F₀ : H →L[ℝ] E) (F₁ : G →L[ℝ] E) (R : F →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R := by
  refine N.mul_gauge_le_of_all_mul_kyFan_le hδ hR ?_
  intro k
  by_cases hk : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hmain :=
      FormBoundedIsometricSinThetaProblem.result_real
        (KyFanDominantIdealFamily.kyFan (𝕜 := ℝ) k hkpos)
        { data :=
            { A := A, A₀ := A₀, Λ₁ := Λ₁, X := E₀, F₁ := F₁, residual := R
              X_maps_domain := htrial.mapsDomain
              F₁_maps_domain := hexact.mapsDomain
              residual_eq := htrial.residualEquation
              intertwines := hexact.intertwines }
          exactMap := F₀
          ambient_selfAdjoint := hA
          trial_selfAdjoint := hA₀
          complement_selfAdjoint := hΛ₁
          trial_isometry := htrial.isometry
          exact_decomposition :=
            { isometry₀ := hexact.desiredIsometry
              isometry₁ := hexact.complementIsometry
              orthogonal := hexact.orthogonal
              projection_sum := hexact.complete }
          gap := δ
          gap_pos := hδ
          spectral_gap := hgap
          residual_mem := KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℝ) k hkpos R }
    simpa only [KyFanDominantIdealFamily.kyFan_gauge] using hmain.2

/-- **The familiar Section 2 interval form, over `ℝ`.**

`sinTheta_real` with the gap spelled out as the printed separation: the
trial spectrum inside `[β, α]` and the complementary spectrum outside
`(β − δ, α + δ)`, or the same with the two roles exchanged.  This is one
constructor of `FormBoundedSylvesterGap`; the Appendix's ordered half-line
configurations are others, and they reach the theorem above directly. -/
theorem sinTheta_real_of_intervalExterior
    (N : PaperUnitaryInvariantNorm)
    (A : E →ₗ.[ℝ] E) (A₀ : F →ₗ.[ℝ] F) (Λ₁ : G →ₗ.[ℝ] G)
    (E₀ : F →L[ℝ] E) (F₀ : H →L[ℝ] E) (F₁ : G →L[ℝ] E) (R : F →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hspectral :
      (TauCeti.LinearPMap.realSpectrum A₀ ⊆ Set.Icc β α ∧
          TauCeti.LinearPMap.realSpectrum Λ₁ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}) ∨
        (TauCeti.LinearPMap.realSpectrum Λ₁ ⊆ Set.Icc β α ∧
          TauCeti.LinearPMap.realSpectrum A₀ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}))
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R :=
  sinTheta_real N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hδ
    (FormBoundedSylvesterGap.intervalExterior hβα hspectral) hR

end FixedFieldReal

end

end DavisKahan1970
