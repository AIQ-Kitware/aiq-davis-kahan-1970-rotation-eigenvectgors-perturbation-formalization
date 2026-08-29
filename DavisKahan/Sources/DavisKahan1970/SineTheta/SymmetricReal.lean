/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Anthropic Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.FullAngleReal
import DavisKahan.Sources.DavisKahan1970.SineTheta.Lemma61
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.HeterogeneousRepresentative
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport
import DavisKahan.SpectralTheory.ReducingSubspace.RestrictionExtras
import DavisKahan.Sylvester.RealUnbounded

/-!
# Davis--Kahan Proposition 6.1 over a real Hilbert space

This is the real-scalar sibling of
`DavisKahan.Sources.DavisKahan1970.SineTheta.Symmetric`.  Standing assumption 1
of the transcription allows the ambient space to be real or complex, and
assumption 4 allows infinite dimension; the complex file covers only half of
that scope because its *conclusion* is phrased through
`paperSinAngleOperatorC`, which is `cfc Real.sin` of the complex operator angle.

The mathematics is not reopened here.  The proof is the paper's, step for step,
and it is the same proof the complex file runs:

1. Apply the one-sided sine theorem to the selected block of `A` and the
   complementary block of `B`.
2. Apply it again with `A` and `B` interchanged.
3. Use Lemma 6.1 to combine the two orthogonal cross blocks sharply.
4. Use Lemma 6.2 to contract the two corresponding perturbation blocks by the
   norm of `H = B - A`.

The one substitution is in step 1--2:
`davisKahan1970_sylvester_complex` becomes `real_unbounded_sylvester_kyFan`.
Everything else -- `paperLemma61_all_kyFan`, `paperDiagonalPair_all_kyFan_le`,
the ambient/subspace singular-value transport, and `PaperUnitaryInvariantNorm`
-- is already `RCLike`-generic and is reused verbatim.

## Why the conclusion is stated on `paperCrossSineSum`

Step 5 of the complex file identifies the cross-block sum with the literal
functional-calculus `sin Theta`.  There is no real continuous functional
calculus in this repository, and building one would be the wrong response: a
unitarily invariant norm sees an operator *only* through its complete
singular-value sequence, so the source statement does not need an operator that
is pointwise the sine of an angle.  It needs an operator carrying the paper's
whole-space sine singular-value sequence.

`paperCrossSineSum U V` is such an operator, and that is compiled rather than
asserted: `paperCrossSineSum_same_projectionDiff` gives it exactly the complete
approximation-singular-value sequence of `P_V - P_U`, which is the paper's
whole-space `sin Theta` sequence.  `crossSineSum_paperMem_iff_and_gauge_eq`
below records the resulting norm identity, and
`result_every_unitarilyInvariantNorm_representative_real` states the theorem for
an arbitrary operator with that sequence, which is the precise sense in which
only the source singular sequence matters.

No complexification, no finite-dimensionality, and no caller-supplied
inequality occurs anywhere below.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A subspace admitting an orthogonal projection inside a complete ambient
space is itself complete.  `local instance` does not propagate through imports,
so it is reinstalled here.

As in the complex file, Proposition 6.1 works throughout in the coordinate
spaces of `U`, `V` and their complements, so every adjoint and every reducing
restriction below needs it. -/
local instance instCompleteSpaceCoeOfHasOrthogonalProjectionSymmetricReal
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (U : Submodule ℝ G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-- The same reinstallation over `ℂ`.  The complexified coordinates that
`paperSourceFullSinR` is defined on are complex subspaces, so the dictionary
lemma below needs this as well as the real version above. -/
local instance instCompleteSpaceCoeOfHasOrthogonalProjectionSymmetricRealC
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-! ### The source dictionary for the real whole-space sine

`paperCrossSineSum U V` is the operator the real theorem below bounds.  The two
lemmas here are what make that a statement about the paper's `sin Theta` rather
than about an ad hoc projection expression.  Neither is used in the proof of
Proposition 6.1; they exist so the identification is checked by the compiler. -/

/-- The real cross-block sum carries exactly the complete singular-value
sequence of the repository's **literal** real full sine angle
`paperSourceFullSinR`, the direct sum of the two source-directed angles.

This is the compiled answer to the source-acceptance question: every source
unitarily invariant norm evaluates the operator appearing in
`result_every_unitarilyInvariantNorm_real` exactly as it evaluates the paper's
whole-space `sin Theta` list.  The equality is proved through the projector
difference and exact complexification invariance of the approximation numbers;
no real continuous functional calculus is constructed, and the real theorem's
own statement does not mention a complexification.

It is stated as a raw equality of approximation numbers rather than as a
`SameApproximationSingularSequence`, because that relation fixes a single scalar
field for both operands and `paperSourceFullSinR` is by construction an operator
over `ℂ` on complexified coordinates.  Approximation numbers are real, so the
comparison itself is unproblematic; only the relation's binders are too narrow.
Lifting this to a `PaperUnitaryInvariantNorm` equality would need a cross-field
counterpart of `SameApproximationSingularSequence.paperExtendedGauge_eq`, which
is deliberately not added here -- the norm-level dictionary the theorem below
actually uses is `crossSineSum_paperMem_iff_and_gauge_eq`, entirely over `ℝ`. -/
theorem approximationNumber_paperSourceFullSinR_eq_paperCrossSineSum
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ∀ n : ℕ,
      (paperSourceFullSinR V U).approximationNumber n =
        (paperCrossSineSum U V).approximationNumber n := by
  -- `paperCrossSineSum U V` has the singular values of `P_V - P_U`.
  have hreal : SameApproximationSingularSequence
      (paperCrossSineSum U V) (V.starProjection - U.starProjection) :=
    paperCrossSineSum_same_projectionDiff U V
  -- The literal full sine of the complexified pair has the singular values of
  -- the complexified projector difference.
  have hcomplex : SameApproximationSingularSequence
      (paperSourceFullSinR V U)
      ((TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule
          V).starProjection -
        (TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule
          U).starProjection) :=
    paperSourceFullSin_same_projectionDifference _ _
  have hcx :
      (TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule
          V).starProjection -
        (TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule
          U).starProjection =
        TauCeti.RealComplexification.complexify
          (V.starProjection - U.starProjection) := by
    rw [TauCeti.DavisKahan.Foundation.RealComplexification.starProjection_complexifySubmodule,
      TauCeti.DavisKahan.Foundation.RealComplexification.starProjection_complexifySubmodule,
      RealComplexification.complexify_sub]
  rw [hcx] at hcomplex
  intro n
  rw [hcomplex n, ComplexificationApproximation.approximationNumber_complexify,
    (hreal n).symm]

/-- Exact bounded inputs of Proposition 6.1 over a real Hilbert space.  This is
`PaperSymmetricSinThetaProblem` with `ℂ` replaced by `ℝ`: the same printed data
and nothing derived.  The two gap hypotheses are the paper's two applications of
the original sine theorem. -/
structure PaperRealSymmetricSinThetaProblem where
  A : E →L[ℝ] E
  B : E →L[ℝ] E
  selfAdjoint_A : A.IsSymmetric
  selfAdjoint_B : B.IsSymmetric
  U : Submodule ℝ E
  V : Submodule ℝ E
  proj_U : U.HasOrthogonalProjection
  proj_V : V.HasOrthogonalProjection
  reduces_A_U : A.Reduces U
  reduces_B_V : B.Reduces V
  gap : ℝ
  gap_pos : 0 < gap
  gap_U_to_Vperp : FormBoundedSylvesterGap
    (TauCeti.LinearPMap.reducingRestriction ((A.toLinearMap.toPMap ⊤)) U
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace A U reduces_A_U))
    (TauCeti.LinearPMap.reducingRestriction ((B.toLinearMap.toPMap ⊤)) Vᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace B V reduces_B_V).orthogonal)
    gap
  gap_V_to_Uperp : FormBoundedSylvesterGap
    (TauCeti.LinearPMap.reducingRestriction ((B.toLinearMap.toPMap ⊤)) V
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace B V reduces_B_V))
    (TauCeti.LinearPMap.reducingRestriction ((A.toLinearMap.toPMap ⊤)) Uᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace A U reduces_A_U).orthogonal)
    gap

attribute [instance] PaperRealSymmetricSinThetaProblem.proj_U
attribute [instance] PaperRealSymmetricSinThetaProblem.proj_V

namespace PaperRealSymmetricSinThetaProblem

/-- The perturbation `H` of the paper. -/
def perturbation (P : PaperRealSymmetricSinThetaProblem (E := E)) : E →L[ℝ] E :=
  P.B - P.A

/-- Internal data for the first directed application. -/
noncomputable def forwardData
    (P : PaperRealSymmetricSinThetaProblem (E := E)) :
    UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := P.U) (G := P.Vᗮ) where
  A := (P.B.toLinearMap.toPMap ⊤)
  A₀ := TauCeti.LinearPMap.reducingRestriction ((P.A.toLinearMap.toPMap ⊤)) P.U
    (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U)
  Λ₁ := TauCeti.LinearPMap.reducingRestriction ((P.B.toLinearMap.toPMap ⊤)) P.Vᗮ
    (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V).orthogonal
  X := P.U.subtypeL
  F₁ := P.Vᗮ.subtypeL
  residual := P.perturbation ∘L P.U.subtypeL
  X_maps_domain := by intro x; simp
  F₁_maps_domain := by intro x; simp
  residual_eq := by
    intro x
    rfl
  intertwines :=
    PartialMap.reducingRestriction_inclusion_intertwines
      ((P.B.toLinearMap.toPMap ⊤)) P.Vᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V).orthogonal

/-- Internal data for the reversed application. -/
noncomputable def reverseData
    (P : PaperRealSymmetricSinThetaProblem (E := E)) :
    UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := P.V) (G := P.Uᗮ) where
  A := (P.A.toLinearMap.toPMap ⊤)
  A₀ := TauCeti.LinearPMap.reducingRestriction ((P.B.toLinearMap.toPMap ⊤)) P.V
    (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V)
  Λ₁ := TauCeti.LinearPMap.reducingRestriction ((P.A.toLinearMap.toPMap ⊤)) P.Uᗮ
    (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U).orthogonal
  X := P.V.subtypeL
  F₁ := P.Uᗮ.subtypeL
  residual := (-P.perturbation) ∘L P.V.subtypeL
  X_maps_domain := by intro x; simp
  F₁_maps_domain := by intro x; simp
  residual_eq := by
    intro x
    simp [perturbation]
    rfl
  intertwines :=
    PartialMap.reducingRestriction_inclusion_intertwines
      ((P.A.toLinearMap.toPMap ⊤)) P.Uᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U).orthogonal

/-- The first exact cross-projection block. -/
def forwardSineBlock (P : PaperRealSymmetricSinThetaProblem (E := E)) :
    E →L[ℝ] E :=
  P.Vᗮ.starProjection ∘L P.U.starProjection

/-- The reversed exact cross-projection block. -/
def reverseSineBlock (P : PaperRealSymmetricSinThetaProblem (E := E)) :
    E →L[ℝ] E :=
  P.Uᗮ.starProjection ∘L P.V.starProjection

/-- The first projected perturbation block from the proof of Proposition 6.1. -/
def forwardResidualBlock (P : PaperRealSymmetricSinThetaProblem (E := E)) :
    E →L[ℝ] E :=
  P.Vᗮ.starProjection ∘L P.perturbation ∘L P.U.starProjection

/-- The second projected perturbation block. -/
def reverseResidualBlock (P : PaperRealSymmetricSinThetaProblem (E := E)) :
    E →L[ℝ] E :=
  P.V.starProjection ∘L P.perturbation ∘L P.Uᗮ.starProjection

/-- First one-sided estimate simultaneously for every finite Ky Fan gauge. -/
theorem forward_all_kyFan
    (P : PaperRealSymmetricSinThetaProblem (E := E)) :
    ∀ k,
      P.gap * kyFanApproximationGauge k P.forwardSineBlock ≤
        kyFanApproximationGauge k P.forwardResidualBlock := by
  intro k
  set D := P.forwardData with hD
  have hA0 : _root_.IsSelfAdjoint D.A₀ :=
    PartialMap.reducingRestriction_isSelfAdjoint
      ((P.A.toLinearMap.toPMap ⊤)) P.U
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U)
      (TauCeti.DavisKahanExt.ofBounded_isSelfAdjoint P.A P.selfAdjoint_A)
  have hL : _root_.IsSelfAdjoint D.Λ₁ :=
    PartialMap.reducingRestriction_isSelfAdjoint
      ((P.B.toLinearMap.toPMap ⊤)) P.Vᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V).orthogonal
      (TauCeti.DavisKahanExt.ofBounded_isSelfAdjoint P.B P.selfAdjoint_B)
  have hEq := unbounded_adjoint_residual_block_identity D
    (TauCeti.DavisKahanExt.ofBounded_isSelfAdjoint P.B P.selfAdjoint_B) hA0 hL
  -- The only mathematical substitution against the complex file.
  have hraw := real_unbounded_sylvester_kyFan hA0 hL P.gap_pos
    P.gap_U_to_Vperp hEq k
  -- The ambient transport lemma produces the *adjoint* orientation of each
  -- block, so both comparisons are heterogeneous and both pick up one adjoint
  -- step.  Ky Fan gauges are adjoint-invariant, so nothing is lost.
  have hsine : SameApproximationSingularSequence
      (P.U.starProjection ∘L P.Vᗮ.starProjection)
      (D.X.adjoint ∘L D.F₁) := by
    simpa [hD, forwardData, Submodule.adjoint_subtypeL,
      Submodule.starProjection, ContinuousLinearMap.comp_assoc] using
      sameApproximationSingularValues_ambientSubspaceBlock
        P.Vᗮ P.U (D.X.adjoint ∘L D.F₁)
  have hsineAdj : P.forwardSineBlock =
      (P.U.starProjection ∘L P.Vᗮ.starProjection).adjoint := by
    rw [ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection P.U).adjoint_eq,
      (isSelfAdjoint_starProjection P.Vᗮ).adjoint_eq]
    rfl
  have hres : SameApproximationSingularSequence
      (-P.forwardResidualBlock.adjoint)
      (-(D.residual.adjoint ∘L D.F₁)) := by
    simpa [hD, forwardData, forwardResidualBlock, perturbation,
      Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
      Submodule.starProjection,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      map_sub, map_neg] using
      sameApproximationSingularValues_ambientSubspaceBlock
        P.Vᗮ P.U (-(D.residual.adjoint ∘L D.F₁))
  have hgaugeSine : kyFanApproximationGauge k P.forwardSineBlock =
      kyFanApproximationGauge k (D.X.adjoint ∘L D.F₁) := by
    rw [hsineAdj, kyFanApproximationGauge_adjoint,
      hsine.kyFanApproximationGauge_eq k]
  have hgaugeRes : kyFanApproximationGauge k P.forwardResidualBlock =
      kyFanApproximationGauge k (-(D.residual.adjoint ∘L D.F₁)) := by
    rw [← kyFanApproximationGauge_adjoint k P.forwardResidualBlock,
      ← kyFanApproximationGauge_neg k P.forwardResidualBlock.adjoint,
      hres.kyFanApproximationGauge_eq k]
  rw [hgaugeSine, hgaugeRes]
  exact hraw

/-- Reversed one-sided estimate simultaneously for every finite Ky Fan gauge. -/
theorem reverse_all_kyFan
    (P : PaperRealSymmetricSinThetaProblem (E := E)) :
    ∀ k,
      P.gap * kyFanApproximationGauge k P.reverseSineBlock ≤
        kyFanApproximationGauge k P.reverseResidualBlock := by
  intro k
  set D := P.reverseData with hD
  have hA0 : _root_.IsSelfAdjoint D.A₀ :=
    PartialMap.reducingRestriction_isSelfAdjoint
      ((P.B.toLinearMap.toPMap ⊤)) P.V
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V)
      (TauCeti.DavisKahanExt.ofBounded_isSelfAdjoint P.B P.selfAdjoint_B)
  have hL : _root_.IsSelfAdjoint D.Λ₁ :=
    PartialMap.reducingRestriction_isSelfAdjoint
      ((P.A.toLinearMap.toPMap ⊤)) P.Uᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U).orthogonal
      (TauCeti.DavisKahanExt.ofBounded_isSelfAdjoint P.A P.selfAdjoint_A)
  have hEq := unbounded_adjoint_residual_block_identity D
    (TauCeti.DavisKahanExt.ofBounded_isSelfAdjoint P.A P.selfAdjoint_A) hA0 hL
  have hraw := real_unbounded_sylvester_kyFan hA0 hL P.gap_pos
    P.gap_V_to_Uperp hEq k
  -- Mirror of the forward case: the ambient transport lemma again produces the
  -- adjoint orientation, and Ky Fan gauges are adjoint-invariant.
  have hsine : SameApproximationSingularSequence
      (P.V.starProjection ∘L P.Uᗮ.starProjection)
      (D.X.adjoint ∘L D.F₁) := by
    simpa [hD, reverseData, Submodule.adjoint_subtypeL,
      Submodule.starProjection, ContinuousLinearMap.comp_assoc] using
      sameApproximationSingularValues_ambientSubspaceBlock
        P.Uᗮ P.V (D.X.adjoint ∘L D.F₁)
  have hsineAdj : P.reverseSineBlock =
      (P.V.starProjection ∘L P.Uᗮ.starProjection).adjoint := by
    rw [ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection P.V).adjoint_eq,
      (isSelfAdjoint_starProjection P.Uᗮ).adjoint_eq]
    rfl
  -- Here `A` and `B` are symmetric, so the ambient block comes out in the
  -- original orientation rather than the adjoint one.
  have hadjA : P.A.adjoint = P.A := P.selfAdjoint_A.isSelfAdjoint.adjoint_eq
  have hadjB : P.B.adjoint = P.B := P.selfAdjoint_B.isSelfAdjoint.adjoint_eq
  have hres : SameApproximationSingularSequence
      P.reverseResidualBlock
      (-(D.residual.adjoint ∘L D.F₁)) := by
    simpa [hD, reverseData, reverseResidualBlock, perturbation, hadjA, hadjB,
      Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
      Submodule.starProjection,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      map_sub, map_neg] using
      sameApproximationSingularValues_ambientSubspaceBlock
        P.Uᗮ P.V (-(D.residual.adjoint ∘L D.F₁))
  have hgaugeSine : kyFanApproximationGauge k P.reverseSineBlock =
      kyFanApproximationGauge k (D.X.adjoint ∘L D.F₁) := by
    rw [hsineAdj, kyFanApproximationGauge_adjoint,
      hsine.kyFanApproximationGauge_eq k]
  have hgaugeRes : kyFanApproximationGauge k P.reverseResidualBlock =
      kyFanApproximationGauge k (-(D.residual.adjoint ∘L D.F₁)) :=
    hres.kyFanApproximationGauge_eq k
  rw [hgaugeSine, hgaugeRes]
  exact hraw

/-- Ky Fan form of the real symmetric sine theorem, before universal Fan
dominance.  The left-hand operator is the paper's whole-space sine
representative; see `crossSineSum_paperMem_iff_and_gauge_eq`. -/
theorem symmetric_all_kyFan_real
    (P : PaperRealSymmetricSinThetaProblem (E := E)) :
    ∀ k,
      P.gap * kyFanApproximationGauge k (paperCrossSineSum P.U P.V) ≤
        kyFanApproximationGauge k P.perturbation := by
  intro k
  have hadjA : P.A.adjoint = P.A := P.selfAdjoint_A.isSelfAdjoint.adjoint_eq
  have hadjB : P.B.adjoint = P.B := P.selfAdjoint_B.isSelfAdjoint.adjoint_eq
  have hadjH : P.perturbation.adjoint = P.perturbation := by
    simp [perturbation, map_sub, hadjA, hadjB]
  have hUperp : P.Uᗮᗮ = P.U := Submodule.orthogonal_orthogonal P.U
  have hgapNorm : ‖P.gap‖ = P.gap := abs_of_pos P.gap_pos
  -- Lemma 6.1 is applied to the *scaled identity*, not to a scaled
  -- perturbation: the two one-sided estimates bound `gap` times a pure
  -- projection product, and `paperProjectionBlock Ω Γ (gap • id)` is exactly
  -- `gap` times that product.  Feeding it `gap • H` would instead demand
  -- `gap * gauge (block H) ≤ gauge (block H)`, which is false for `gap > 1`.
  have hcombine := paperLemma61_all_kyFan P.Uᗮ P.V
    (P.gap • ContinuousLinearMap.id ℝ E) (P.gap • ContinuousLinearMap.id ℝ E)
    P.perturbation P.perturbation
    (fun j => by
      have hrev := P.reverse_all_kyFan j
      have hblockSine :
          paperProjectionBlock P.Uᗮ P.V (P.gap • ContinuousLinearMap.id ℝ E) =
            P.gap • P.reverseSineBlock := by
        ext x; simp [paperProjectionBlock, reverseSineBlock]
      have hblockRes :
          paperProjectionBlock P.Uᗮ P.V P.perturbation =
            P.reverseResidualBlock.adjoint := by
        simp [paperProjectionBlock, reverseResidualBlock,
          ContinuousLinearMap.adjoint_comp, hadjH,
          (isSelfAdjoint_starProjection P.V).adjoint_eq,
          (isSelfAdjoint_starProjection P.Uᗮ).adjoint_eq,
          ContinuousLinearMap.comp_assoc]
      rw [hblockSine, hblockRes, kyFanApproximationGauge_smul,
        hgapNorm, kyFanApproximationGauge_adjoint]
      exact hrev)
    (fun j => by
      have hfwd := P.forward_all_kyFan j
      have hblockSine :
          paperProjectionBlock P.Uᗮᗮ P.Vᗮ (P.gap • ContinuousLinearMap.id ℝ E) =
            P.gap • P.forwardSineBlock.adjoint := by
        simp only [hUperp]
        ext x
        simp [paperProjectionBlock, forwardSineBlock,
          ContinuousLinearMap.adjoint_comp,
          (isSelfAdjoint_starProjection P.U).adjoint_eq,
          (isSelfAdjoint_starProjection P.Vᗮ).adjoint_eq]
      have hblockRes :
          paperProjectionBlock P.Uᗮᗮ P.Vᗮ P.perturbation =
            P.forwardResidualBlock.adjoint := by
        simp only [hUperp]
        simp [paperProjectionBlock, forwardResidualBlock,
          ContinuousLinearMap.adjoint_comp, hadjH,
          (isSelfAdjoint_starProjection P.U).adjoint_eq,
          (isSelfAdjoint_starProjection P.Vᗮ).adjoint_eq,
          ContinuousLinearMap.comp_assoc]
      rw [hblockSine, hblockRes, kyFanApproximationGauge_smul,
        hgapNorm, kyFanApproximationGauge_adjoint,
        kyFanApproximationGauge_adjoint]
      exact hfwd) k
  have hres := paperDiagonalPair_all_kyFan_le P.Uᗮ P.V P.perturbation k
  have hcross :
      paperProjectionBlock P.Uᗮ P.V (P.gap • ContinuousLinearMap.id ℝ E) +
          paperProjectionBlock P.Uᗮᗮ P.Vᗮ (P.gap • ContinuousLinearMap.id ℝ E) =
        P.gap • paperCrossSineSum P.U P.V := by
    simp only [hUperp]
    ext x
    simp [paperProjectionBlock, paperCrossSineSum, smul_add]
  rw [hcross] at hcombine
  calc
    P.gap * kyFanApproximationGauge k (paperCrossSineSum P.U P.V) =
        kyFanApproximationGauge k (P.gap • paperCrossSineSum P.U P.V) := by
      rw [kyFanApproximationGauge_smul, hgapNorm]
    _ ≤ kyFanApproximationGauge k
        (paperDiagonalPair P.Uᗮ P.V P.perturbation) := hcombine
    _ ≤ kyFanApproximationGauge k P.perturbation := hres

/-- **Davis--Kahan 1970, Proposition 6.1 over a real Hilbert space**, for every
normalized unitarily invariant norm in the source sense. -/
theorem result_every_unitarilyInvariantNorm_real
    (P : PaperRealSymmetricSinThetaProblem (E := E))
    (N : PaperUnitaryInvariantNorm) (hH : N.Mem P.perturbation) :
    N.Mem (paperCrossSineSum P.U P.V) ∧
      P.gap * N.gauge (paperCrossSineSum P.U P.V) ≤ N.gauge P.perturbation :=
  N.mul_gauge_le_of_all_mul_kyFan_le P.gap_pos hH P.symmetric_all_kyFan_real

/-- The compiled source dictionary.  Every source norm evaluates the operator
appearing in `result_every_unitarilyInvariantNorm_real` exactly as it evaluates
the paper's whole-space sine singular-value list, which is the complete
approximation-singular-value sequence of the projector difference
`P_V - P_U`. -/
theorem crossSineSum_paperMem_iff_and_gauge_eq
    (P : PaperRealSymmetricSinThetaProblem (E := E))
    (N : PaperUnitaryInvariantNorm) :
    (N.Mem (paperCrossSineSum P.U P.V) ↔
        N.Mem (P.V.starProjection - P.U.starProjection)) ∧
      N.gauge (paperCrossSineSum P.U P.V) =
        N.gauge (P.V.starProjection - P.U.starProjection) :=
  SameApproximationSingularSequence.paperMem_iff_and_gauge_eq N
    (paperCrossSineSum_same_projectionDiff P.U P.V)

/-- Proposition 6.1 for an arbitrary source realization of `sin Theta`: any
operator carrying the paper's whole-space sine singular-value sequence obeys
the same estimate.  This is the exact sense in which the theorem depends only
on the source singular sequence and not on a chosen functional calculus. -/
theorem result_every_unitarilyInvariantNorm_representative_real
    (P : PaperRealSymmetricSinThetaProblem (E := E))
    (S : PaperSinThetaRepresentative (paperCrossSineSum P.U P.V))
    (N : PaperUnitaryInvariantNorm) (hH : N.Mem P.perturbation) :
    N.Mem S.operator ∧
      P.gap * N.gauge S.operator ≤ N.gauge P.perturbation := by
  obtain ⟨hmem, hbound⟩ := P.result_every_unitarilyInvariantNorm_real N hH
  obtain ⟨hiff, hgauge⟩ :=
    SameApproximationSingularSequence.paperMem_iff_and_gauge_eq N
      S.same_singular_values
  exact ⟨hiff.mpr hmem, by rw [hgauge]; exact hbound⟩

end PaperRealSymmetricSinThetaProblem

end

end ExactSinTheta
end DavisKahan
end TauCeti
