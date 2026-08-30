/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.Sources.DavisKahan1970.TanThetaWholeSpace
import DavisKahan.TanTheta.Theorem63UnboundedInfiniteTrial
import DavisKahan.TanTheta.Theorem63UnboundedCompression
import DavisKahan.TanTheta.RitzPair

/-!
# Unbounded ambient single-angle tangent assembly

This file isolates the missing ambient half of the Section 2 `tan Theta`
theorem from the already-proved unbounded directed Theorem 6.3 estimate.

The ambient step is bounded operator geometry once a sharp lower-corner
Ky Fan estimate is available.  Two data paths supply that estimate:
`Theorem63TrialData` covers an unbounded ambient operator with bounded Ritz
compression, while `UnboundedCompressionTrialData` supplies the full Appendix
scope in which the Ritz compression itself may be unbounded.  In the latter
case the Appendix spectral truncation/release argument is consumed through
`UnboundedCompressionTrialData.all_kyFan_core`.  The upper tangent corner is the
adjoint of the lower one, and Davis--Kahan Lemmas 6.1 and 6.2 assemble the two
corners without loss.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace BigOperators
open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.ExactTanTheta
open TauCeti.DavisKahan.TanTheta
open TauCeti.ApproximationNumber

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

local instance instCompleteSpaceCoeOfHasOrthogonalProjectionTanThetaUnboundedAmbient
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

omit [CompleteSpace E] in
private theorem comp_eq_mul_unboundedTanThetaAmbient
    (f g : E →L[ℂ] E) : f ∘L g = f * g := rfl

omit [CompleteSpace E] in
private theorem projectionBlock_lower_unboundedTanThetaAmbient
    {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    (K : E →L[ℂ] E) :
    paperProjectionBlock Uᗮ U K =
      (1 - U.starProjection) * K * U.starProjection := by
  rw [paperProjectionBlock, Submodule.starProjection_orthogonal',
    comp_eq_mul_unboundedTanThetaAmbient,
    comp_eq_mul_unboundedTanThetaAmbient, mul_assoc]

omit [CompleteSpace E] in
private theorem projectionBlock_upper_unboundedTanThetaAmbient
    {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    (K : E →L[ℂ] E) :
    paperProjectionBlock Uᗮᗮ Uᗮ K =
      U.starProjection * K * (1 - U.starProjection) := by
  have hUperp : Uᗮᗮ = U := Submodule.orthogonal_orthogonal U
  rw [paperProjectionBlock]
  simp only [hUperp, Submodule.starProjection_orthogonal',
    comp_eq_mul_unboundedTanThetaAmbient]
  rw [mul_assoc]

omit [CompleteSpace E] in
private theorem projectionBlock_smul_unboundedTanThetaAmbient
    (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (c : ℂ) (K : E →L[ℂ] E) :
    paperProjectionBlock Ω Γ (c • K) = c • paperProjectionBlock Ω Γ K := by
  ext x
  simp [paperProjectionBlock]

private theorem subtypeL_comp_adjoint_subtypeL_unboundedTanThetaAmbient
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    U.subtypeL ∘L U.subtypeL.adjoint = U.starProjection := by
  rw [Submodule.adjoint_subtypeL]
  rfl

/-- Pure bounded-operator assembly for the ambient tangent theorem.

The hypothesis `hlower` is the only place the unbounded Theorem 6.3 argument
enters: it supplies the sharp lower-corner estimate.  Everything after that is
the same two-corner Lemma-6.1/Lemma-6.2 argument as the bounded source theorem. -/
theorem tanTheta_ambient_all_kyFan_of_lowerCorner
    {H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hH : IsSelfAdjoint H)
    {delta : ℝ} (hdelta : 0 < delta)
    (htr : ‖sinAngleOperatorC U V‖ < 1)
    (hlower : ∀ k : ℕ,
      delta * kyFanApproximationGauge k
          (paperProjectionBlock Uᗮ U
            (paperProjectorDifference U V * paperSecantSquared U V)) ≤
        kyFanApproximationGauge k (paperProjectionBlock Uᗮ U H)) :
    ∀ k : ℕ,
      delta * kyFanApproximationGauge k (paperTanAngleOperatorC U V) ≤
        kyFanApproximationGauge k H := by
  intro k
  have hdeltac : ‖((delta : ℝ) : ℂ)‖ = delta := by
    simp [abs_of_pos hdelta]
  set K := paperProjectorDifference U V * paperSecantSquared U V
  have h₀ : ∀ j : ℕ,
      kyFanApproximationGauge j
          (paperProjectionBlock Uᗮ U (((delta : ℝ) : ℂ) • K)) ≤
        kyFanApproximationGauge j (paperProjectionBlock Uᗮ U H) := by
    intro j
    rw [projectionBlock_smul_unboundedTanThetaAmbient,
      kyFanApproximationGauge_smul, hdeltac]
    exact hlower j
  have h₁ : ∀ j : ℕ,
      kyFanApproximationGauge j
          (paperProjectionBlock Uᗮᗮ Uᗮ (((delta : ℝ) : ℂ) • K)) ≤
        kyFanApproximationGauge j (paperProjectionBlock Uᗮᗮ Uᗮ H) := by
    intro j
    have hleft :
        paperProjectionBlock Uᗮᗮ Uᗮ (((delta : ℝ) : ℂ) • K) =
          (((delta : ℝ) : ℂ) • paperProjectionBlock Uᗮ U K).adjoint := by
      rw [projectionBlock_smul_unboundedTanThetaAmbient,
        upperCorner_eq_adjoint_lowerCorner htr]
      show ((delta : ℝ) : ℂ) • star (paperProjectionBlock Uᗮ U K) =
        star (((delta : ℝ) : ℂ) • paperProjectionBlock Uᗮ U K)
      rw [star_smul, RCLike.star_def, Complex.conj_ofReal]
    have hright :
        paperProjectionBlock Uᗮᗮ Uᗮ H =
          (paperProjectionBlock Uᗮ U H).adjoint := by
      have hp := isSelfAdjoint_starProjection U
      rw [projectionBlock_upper_unboundedTanThetaAmbient,
        projectionBlock_lower_unboundedTanThetaAmbient]
      show _ = star _
      simp only [star_mul, star_sub, star_one, hp.star_eq, hH.star_eq]
      noncomm_ring
    rw [hleft, hright, kyFanApproximationGauge_adjoint,
      kyFanApproximationGauge_adjoint, kyFanApproximationGauge_smul, hdeltac]
    exact hlower j
  have hcombine := paperLemma61_all_kyFan Uᗮ U
    (((delta : ℝ) : ℂ) • K) (((delta : ℝ) : ℂ) • K) H H h₀ h₁ k
  have hsum :
      paperProjectionBlock Uᗮ U (((delta : ℝ) : ℂ) • K) +
          paperProjectionBlock Uᗮᗮ Uᗮ (((delta : ℝ) : ℂ) • K) =
        ((delta : ℝ) : ℂ) • paperTanBlockRepresentative U V := by
    rw [paperTanBlockRepresentative, paperDiagonalPair,
      projectionBlock_smul_unboundedTanThetaAmbient,
      projectionBlock_smul_unboundedTanThetaAmbient, ← smul_add]
    rfl
  have hsumH :
      paperProjectionBlock Uᗮ U H + paperProjectionBlock Uᗮᗮ Uᗮ H =
        paperDiagonalPair Uᗮ U H := rfl
  rw [hsum, hsumH, kyFanApproximationGauge_smul, hdeltac] at hcombine
  have hpinch := paperDiagonalPair_all_kyFan_le Uᗮ U H k
  have hmodulus :
      kyFanApproximationGauge k (paperTanAngleOperatorC U V) =
        kyFanApproximationGauge k (paperTanBlockRepresentative U V) := by
    rw [paperTanAngleOperatorC_eq_modulus_blockRepresentative htr]
    exact (ContinuousLinearMap.modulus_hasSameApproximationNumbers
      (paperTanBlockRepresentative U V)).kyFanGauge_eq k
  rw [hmodulus]
  exact hcombine.trans hpinch

/-- Paper-norm form of `tanTheta_ambient_all_kyFan_of_lowerCorner`. -/
theorem tanTheta_ambient_paperUINorm_of_lowerCorner
    (N : PaperUnitaryInvariantNorm)
    {H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hH : IsSelfAdjoint H)
    {delta : ℝ} (hdelta : 0 < delta)
    (htr : ‖sinAngleOperatorC U V‖ < 1)
    (hlower : ∀ k : ℕ,
      delta * kyFanApproximationGauge k
          (paperProjectionBlock Uᗮ U
            (paperProjectorDifference U V * paperSecantSquared U V)) ≤
        kyFanApproximationGauge k (paperProjectionBlock Uᗮ U H))
    (hMem : N.Mem H) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge H :=
  N.mul_gauge_le_of_all_mul_kyFan_le hdelta hMem
    (tanTheta_ambient_all_kyFan_of_lowerCorner hH hdelta htr hlower)

/-- **Unbounded-data ambient `tan Theta` theorem with transversality supplied.**

This is the assembly half of `tanTheta_unbounded_ambient_paperUINorm_of_data`:
everything except the derivation of `‖sin Theta‖ < 1` from the printed standing
assumption (3.5).  Separating the two lets the real-scalar counterpart consume
this half after establishing transversality natively on the real side, so the
crossed-defect condition never has to be transported across complexification.

`data` is the bounded trial-block data extracted from an unbounded self-adjoint
problem.  Its residual is assumed to be exactly the lower `U -> U-perp` block of
the bounded perturbation `H`; this is the operator form of the printed
Rayleigh--Ritz condition `H_0 = 0`. -/
theorem tanTheta_unbounded_ambient_paperUINorm_of_data_of_transversality
    (N : PaperUnitaryInvariantNorm)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (data : Theorem63TrialData U V)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompression : ∀ z : U,
      RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : U,
      (alpha + delta) * ‖Vᗮ.starProjection ((z : U) : E)‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection ((z : U) : E),
          Vᗮ.starProjection (data.action z)⟫_ℂ)
    (htr : ‖sinAngleOperatorC U V‖ < 1)
    (hResidual :
      data.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge H := by
  have hblock :
      paperProjectionBlock Uᗮ U H =
        data.residual ∘L U.subtypeL.adjoint := by
    rw [hResidual, paperProjectionBlock]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply]
    have hproj :
        U.subtypeL ∘L U.subtypeL.adjoint = U.starProjection :=
      subtypeL_comp_adjoint_subtypeL_unboundedTanThetaAmbient U
    have happ := congrArg (fun L : E →L[ℂ] E => L x) hproj
    simpa only [ContinuousLinearMap.comp_apply] using
      (congrArg (fun y : E => Uᗮ.starProjection (H y)) happ).symm
  have hlower : ∀ k : ℕ,
      delta * kyFanApproximationGauge k
          (paperProjectionBlock Uᗮ U
            (paperProjectorDifference U V * paperSecantSquared U V)) ≤
        kyFanApproximationGauge k (paperProjectionBlock Uᗮ U H) := by
    intro k
    have hcorner := kyFan_lowerCorner_le (U := U) (V := V) htr k
    have hcore := data.all_kyFan_core_of_formBounds_infinite
      hdelta hCompression hcross k
    have hresKy :
        kyFanApproximationGauge k data.residual =
          kyFanApproximationGauge k (paperProjectionBlock Uᗮ U H) := by
      rw [hblock]
      have hs := sameApproximationSingularValues_extendDomainByZero U data.residual
      exact (hs.kyFanApproximationGauge_eq k).symm
    calc
      delta * kyFanApproximationGauge k
          (paperProjectionBlock Uᗮ U
            (paperProjectorDifference U V * paperSecantSquared U V))
          ≤ delta * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
              (approximationSingularValue n (theorem63DirectedSineBlock U V))) :=
        mul_le_mul_of_nonneg_left hcorner hdelta.le
      _ ≤ kyFanApproximationGauge k data.residual := hcore
      _ = kyFanApproximationGauge k (paperProjectionBlock Uᗮ U H) := hresKy
  exact tanTheta_ambient_paperUINorm_of_lowerCorner N hH hdelta htr hlower hMem

/-- **Unbounded-data ambient `tan Theta` theorem, complex form.**

`data` is the bounded trial-block data extracted from an unbounded self-adjoint
problem.  Its residual is assumed to be exactly the lower `U -> U-perp` block of
the bounded perturbation `H`; this is the operator form of the printed
Rayleigh--Ritz condition `H_0 = 0`.  The form bounds are precisely the two
inputs already consumed by the unbounded arbitrary-trial Theorem 6.3 chain.

Uniform transversality is not assumed: the directed sine values are already
strictly below one under those form bounds, and the printed standing assumption
(3.5) identifies the symmetric gap with the directed one.

The conclusion is the missing sharp ambient inequality
`delta * N(tan Theta) <= N(H)` for every paper unitary-invariant norm. -/
theorem tanTheta_unbounded_ambient_paperUINorm_of_data
    (N : PaperUnitaryInvariantNorm)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (data : Theorem63TrialData U V)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompression : ∀ z : U,
      RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : U,
      (alpha + delta) * ‖Vᗮ.starProjection ((z : U) : E)‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection ((z : U) : E),
          Vᗮ.starProjection (data.action z)⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual :
      data.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge H := by
  have hdirected :
      approximationSingularValue 0 (theorem63DirectedSineBlock U V) < 1 :=
    data.approximationSingularValue_sineBlock_lt_one_infiniteData
      hdelta hCompression hcross 0
  have hambient : ‖paperDirectedSineAmbient U V‖ < 1 := by
    have h := approximationNumber_paperDirectedSineAmbient_le (U := U) (V := V) 0
    rw [(paperDirectedSineAmbient U V).approximationNumber_index_zero] at h
    exact lt_of_le_of_lt h hdirected
  have htr : ‖sinAngleOperatorC U V‖ < 1 := by
    rw [norm_sinAngleOperatorC U V,
      DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent
        U V h35]
    exact hambient
  exact tanTheta_unbounded_ambient_paperUINorm_of_data_of_transversality N data H hH
    hdelta hCompression hcross htr hResidual hMem

/-! ## Appendix scope: the Ritz compression itself may be unbounded -/

/-- **Ambient `tan Theta` assembly with a genuinely unbounded Ritz compression,
with transversality supplied.**

This is the Appendix counterpart of
`tanTheta_unbounded_ambient_paperUINorm_of_data_of_transversality`.  The crucial
difference is that `D.compression` is a densely defined self-adjoint closed
operator on the trial space, not a bounded continuous endomorphism.  Only the
residual is bounded.  The lower-corner estimate therefore comes from
`UnboundedCompressionTrialData.all_kyFan_core`, which performs the Appendix
spectral truncation and release argument.  Once that estimate is available, the
whole-space assembly is again purely bounded operator geometry. -/
theorem tanTheta_unboundedCompression_ambient_paperUINorm_of_data_of_transversality
    (N : PaperUnitaryInvariantNorm)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : UnboundedCompressionTrialData U)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hcross : ∀ z : D.compression.domain,
      (alpha + delta) * ‖Vᗮ.starProjection (((z : U) : E))‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection (((z : U) : E)),
          Vᗮ.starProjection (D.action z)⟫_ℂ)
    (htr : ‖sinAngleOperatorC U V‖ < 1)
    (hResidual :
      D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge H := by
  have hblock :
      paperProjectionBlock Uᗮ U H =
        D.residual ∘L U.subtypeL.adjoint := by
    rw [hResidual, paperProjectionBlock]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply]
    have hproj :
        U.subtypeL ∘L U.subtypeL.adjoint = U.starProjection :=
      subtypeL_comp_adjoint_subtypeL_unboundedTanThetaAmbient U
    have happ := congrArg (fun L : E →L[ℂ] E => L x) hproj
    simpa only [ContinuousLinearMap.comp_apply] using
      (congrArg (fun y : E => Uᗮ.starProjection (H y)) happ).symm
  have hlower : ∀ k : ℕ,
      delta * kyFanApproximationGauge k
          (paperProjectionBlock Uᗮ U
            (paperProjectorDifference U V * paperSecantSquared U V)) ≤
        kyFanApproximationGauge k (paperProjectionBlock Uᗮ U H) := by
    intro k
    have hcorner := kyFan_lowerCorner_le (U := U) (V := V) htr k
    have hcore := D.all_kyFan_core V hdelta hupper hcross k
    have hresKy :
        kyFanApproximationGauge k D.residual =
          kyFanApproximationGauge k (paperProjectionBlock Uᗮ U H) := by
      rw [hblock]
      have hs := sameApproximationSingularValues_extendDomainByZero U D.residual
      exact (hs.kyFanApproximationGauge_eq k).symm
    calc
      delta * kyFanApproximationGauge k
          (paperProjectionBlock Uᗮ U
            (paperProjectorDifference U V * paperSecantSquared U V))
          ≤ delta * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
              (approximationSingularValue n (theorem63DirectedSineBlock U V))) :=
        mul_le_mul_of_nonneg_left hcorner hdelta.le
      _ ≤ kyFanApproximationGauge k D.residual := hcore
      _ = kyFanApproximationGauge k (paperProjectionBlock Uᗮ U H) := hresKy
  exact tanTheta_ambient_paperUINorm_of_lowerCorner N hH hdelta htr hlower hMem

/-- **Davis--Kahan's ambient `tan Theta` estimate with an unbounded Ritz
compression, complex form.**

The Appendix explicitly allows `A₀ ≤ alpha` and `Lambda₁ ≥ alpha + delta` to
*both* be unbounded.  Here `D.compression` is that unbounded self-adjoint Ritz
operator and `D.residual` is the bounded residual.  Uniform transversality is
derived from the Appendix no-pole theorem plus the paper's standing condition
(3.5), not assumed by the caller. -/
theorem tanTheta_unboundedCompression_ambient_paperUINorm_of_data
    (N : PaperUnitaryInvariantNorm)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : UnboundedCompressionTrialData U)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hcross : ∀ z : D.compression.domain,
      (alpha + delta) * ‖Vᗮ.starProjection (((z : U) : E))‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection (((z : U) : E)),
          Vᗮ.starProjection (D.action z)⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual :
      D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge H := by
  have hdirected :
      approximationSingularValue 0 (theorem63DirectedSineBlock U V) < 1 :=
    D.approximationSingularValue_sineBlock_lt_one V hdelta hupper hcross 0
  have hambient : ‖paperDirectedSineAmbient U V‖ < 1 := by
    have h := approximationNumber_paperDirectedSineAmbient_le (U := U) (V := V) 0
    rw [(paperDirectedSineAmbient U V).approximationNumber_index_zero] at h
    exact lt_of_le_of_lt h hdirected
  have htr : ‖sinAngleOperatorC U V‖ < 1 := by
    rw [norm_sinAngleOperatorC U V,
      DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent
        U V h35]
    exact hambient
  exact tanTheta_unboundedCompression_ambient_paperUINorm_of_data_of_transversality
    N D H hH hdelta hupper hcross htr hResidual hMem

/-- **Davis--Kahan 1970, Appendix-complete ambient `tan Theta` theorem.**

This is the source-shaped wrapper for the genuinely unbounded Ritz-compression
case.  The ambient self-adjoint operator and the Ritz compression may both be
unbounded; the residual and perturbation `H` are bounded.  The hypotheses
`hZA`/`haction` identify the abstract Ritz data with the ambient operator on the
Ritz domain, `hVdom`/`hVcomm` say the unwanted subspace reduces the ambient
operator, `hupper` and `hUnwanted` are the two printed form bounds, and `h35` is
the standing condition (3.5). -/
theorem tanTheta_unboundedCompression_ambient_paperUINorm_exact
    (N : PaperUnitaryInvariantNorm)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : UnboundedCompressionTrialData U)
    (A : E →ₗ.[ℂ] E)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hZA : ∀ z : D.compression.domain, ((z : U) : E) ∈ A.domain)
    (haction : ∀ z : D.compression.domain,
      D.action z = A ⟨((z : U) : E), hZA z⟩)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : E)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : E)), hVdom x⟩)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤
        RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual : D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge H := by
  refine tanTheta_unboundedCompression_ambient_paperUINorm_of_data
    N D H hH hdelta hupper ?_ h35 hResidual hMem
  intro z
  exact D.crossed_lower_of_reducing V A hZA haction hVdom hVcomm hUnwanted z

/-- The same theorem specialized to an actual unbounded trial block and an
arbitrary chosen reducing subspace.  All domain-sensitive crossed-form work is
reused from the already-proved unbounded Theorem 6.3 implementation. -/
theorem tanTheta_unbounded_ambient_paperUINorm_exact
    (N : PaperUnitaryInvariantNorm)
    (A : E →ₗ.[ℂ] E)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : UnboundedTrialBlock A U)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : E)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : E)), hVdom x⟩)
    (hCompression : ∀ z : U,
      RCLike.re ⟪D.operator z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤
        RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual : D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge H := by
  let data := Theorem63TrialData.ofUnbounded D V
  refine tanTheta_unbounded_ambient_paperUINorm_of_data N data H hH hdelta
    hCompression ?_ h35 ?_ hMem
  · intro z
    exact crossed_lower_of_reducing A D V hVdom hVcomm hUnwanted z
  · exact hResidual

/-! ### The constructor-first interface

`tanTheta_unboundedCompression_ambient_paperUINorm_exact` above is the most
general form, and it asks the caller for four separate facts that are not
Davis--Kahan mathematics: two saying the compression data is `A`'s Ritz pair on
`U`, and two saying `Vᗮ` reduces `A`.  `DavisKahan.UnboundedRitzPair` and
`DavisKahan.ReducingComplement` hold those, and
`UnboundedRitzPair.ofTrialBlock` builds the first from the bounded-compression
bundle a caller usually has.

What stays a hypothesis is what the theorem is about: the semiboundedness of the
compression, the coercivity on the unwanted subspace, and the crossed-defect
standing condition (3.5). -/

/-- **Davis--Kahan 1970, `tan Θ`, unbounded ambient form, taking the Ritz pair and
the reducing complement as objects.**

`tanTheta_unboundedCompression_ambient_paperUINorm_exact` with its four
structural arguments replaced by `DavisKahan.UnboundedRitzPair A U` and
`DavisKahan.ReducingComplement A V`.  The mathematics -- semiboundedness,
coercivity on the unwanted subspace, and the crossed-defect condition (3.5) --
is unchanged and still supplied by the caller. -/
theorem tanTheta_unbounded_ambient_ritz_paperUINorm
    (N : PaperUnitaryInvariantNorm)
    {A : E →ₗ.[ℂ] E}
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace U]
    (D : DavisKahan.UnboundedRitzPair A U)
    (hV : DavisKahan.ReducingComplement A V)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤
        RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual : D.trial.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge H :=
  tanTheta_unboundedCompression_ambient_paperUINorm_exact N D.trial A H hH hdelta
    D.mem_domain D.action_eq hV.mapsDomain hV.commutes hupper hUnwanted h35
    hResidual hMem

end

end DavisKahan1970
end TauCeti
