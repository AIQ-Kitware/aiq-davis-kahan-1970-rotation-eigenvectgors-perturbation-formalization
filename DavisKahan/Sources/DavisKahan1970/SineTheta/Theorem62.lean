/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.Sylvester.HilbertSchmidtPairwise
import DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtFiniteRank
import DavisKahan.SinTheta.FrameFactorization
import DavisKahan.SinTheta.Real.FrameFactorization
import DavisKahan.Sources.DavisKahan1970.SineTheta.OperatorAngleBridge

/-!
# Davis--Kahan Theorem 6.2: the second generalized sine theorem

This file states the theorem with exactly the weaker pairwise spectral-distance
hypothesis of the paper and the square-norm conclusion.  The constant is one.
The general arbitrary-norm `pi / 2` theorem for disconnected spectra is not
used and is not an acceptable substitute.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

open TauCeti.DavisKahanExt

section Complex

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact inputs of Davis--Kahan Theorem 6.2. -/
structure PaperTheorem62Data where
  data : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G)
  exactMap : H →L[ℂ] E
  ambient_selfAdjoint : _root_.IsSelfAdjoint data.A
  trial_selfAdjoint : _root_.IsSelfAdjoint data.A₀
  complement_selfAdjoint : _root_.IsSelfAdjoint data.Λ₁
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  gap : ℝ
  frameLowerBound : ℝ
  gap_pos : 0 < gap
  frameLowerBound_pos : 0 < frameLowerBound
  lowerFrame : LowerFrameBound data.X frameLowerBound
  spectral_distance : PairwiseSpectrumGap data.A₀ data.Λ₁ gap

namespace PaperTheorem62Data

/-- The normalized complementary block whose singular values are the paper's
`sin Theta_0`. -/
noncomputable def canonicalSinTheta
    (P : PaperTheorem62Data (E := E) (F := F) (G := G) (H := H)) :
    G →L[ℂ] F :=
  sinThetaBlockOfPolarData
    (lowerFramePolarData P.data.X P.lowerFrame P.frameLowerBound_pos)
    P.data.F₁

/-- The raw Sylvester unknown `E_0^* F_1`. -/
def rawOverlap
    (P : PaperTheorem62Data (E := E) (F := F) (G := G) (H := H)) :
    G →L[ℂ] F :=
  P.data.X.adjoint ∘L P.data.F₁

/-- The projected residual in the adjoint Sylvester equation. -/
def projectedResidual
    (P : PaperTheorem62Data (E := E) (F := F) (G := G) (H := H)) :
    G →L[ℂ] F :=
  -(P.data.residual.adjoint ∘L P.data.F₁)

/-- The projected residual is Hilbert--Schmidt whenever the full residual is. -/
theorem projectedResidual_isPaperHilbertSchmidt
    (P : PaperTheorem62Data (E := E) (F := F) (G := G) (H := H))
    (hR : IsPaperHilbertSchmidt P.data.residual) :
    IsPaperHilbertSchmidt P.projectedResidual := by
  have hRadj : IsPaperHilbertSchmidt P.data.residual.adjoint :=
    (isPaperHilbertSchmidt_adjoint_iff P.data.residual).2 hR
  have hcomp : IsPaperHilbertSchmidt
      (ContinuousLinearMap.id ℂ F ∘L P.data.residual.adjoint ∘L P.data.F₁) :=
    hRadj.comp (ContinuousLinearMap.id ℂ F) P.data.F₁
  simpa [projectedResidual, ContinuousLinearMap.id_comp] using
    (isPaperHilbertSchmidt_neg_iff
      (P.data.residual.adjoint ∘L P.data.F₁)).2 (by simpa using hcomp)

/-- Projection onto the complementary exact block cannot enlarge the square
norm of the residual. -/
theorem projectedResidual_norm_le
    (P : PaperTheorem62Data (E := E) (F := F) (G := G) (H := H))
    (hR : IsPaperHilbertSchmidt P.data.residual) :
    paperHilbertSchmidtNorm P.projectedResidual ≤
      paperHilbertSchmidtNorm P.data.residual := by
  have hRadj : IsPaperHilbertSchmidt P.data.residual.adjoint :=
    (isPaperHilbertSchmidt_adjoint_iff P.data.residual).2 hR
  have hF₁ : ‖P.data.F₁‖ ≤ 1 :=
    opNorm_le_one_of_isometry P.exact_decomposition.isometry₁
  calc
    paperHilbertSchmidtNorm P.projectedResidual =
        paperHilbertSchmidtNorm
          (P.data.residual.adjoint ∘L P.data.F₁) := by
      simp [projectedResidual]
    _ = paperHilbertSchmidtNorm
          (ContinuousLinearMap.id ℂ F ∘L P.data.residual.adjoint ∘L
            P.data.F₁) := by simp
    _ ≤ paperHilbertSchmidtNorm P.data.residual.adjoint :=
      paperHilbertSchmidtNorm_comp_isometries_le
        (ContinuousLinearMap.id ℂ F) hRadj P.data.F₁
        ContinuousLinearMap.norm_id_le hF₁
    _ = paperHilbertSchmidtNorm P.data.residual :=
      paperHilbertSchmidtNorm_adjoint P.data.residual

/-- The weaker spectral hypothesis gives the raw square-norm estimate. -/
theorem rawOverlap_bound
    (P : PaperTheorem62Data (E := E) (F := F) (G := G) (H := H))
    (hR : IsPaperHilbertSchmidt P.data.residual) :
    IsPaperHilbertSchmidt P.rawOverlap ∧
      P.gap * paperHilbertSchmidtNorm P.rawOverlap ≤
        paperHilbertSchmidtNorm P.projectedResidual := by
  have hEq := unbounded_adjoint_residual_block_identity P.data
    P.ambient_selfAdjoint P.trial_selfAdjoint P.complement_selfAdjoint
  exact paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
    P.trial_selfAdjoint P.complement_selfAdjoint P.gap_pos
    P.spectral_distance hEq (P.projectedResidual_isPaperHilbertSchmidt hR)

/-- Whitening introduces exactly the source factor `epsilon^(-1)`. -/
theorem canonicalSinTheta_frame_bound
    (P : PaperTheorem62Data (E := E) (F := F) (G := G) (H := H))
    (hraw : IsPaperHilbertSchmidt P.rawOverlap) :
    IsPaperHilbertSchmidt P.canonicalSinTheta ∧
      P.frameLowerBound * paperHilbertSchmidtNorm P.canonicalSinTheta ≤
        paperHilbertSchmidtNorm P.rawOverlap := by
  let Q := lowerFramePolarData P.data.X P.lowerFrame P.frameLowerBound_pos
  have hblock :
      P.canonicalSinTheta = Q.invSqrt.adjoint ∘L P.rawOverlap := by
    simp [canonicalSinTheta, rawOverlap, sinThetaBlockOfPolarData,
      frameIsometryOfPolarData, Q, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.comp_assoc]
  have hmem : IsPaperHilbertSchmidt P.canonicalSinTheta := by
    rw [hblock]
    have := hraw.comp Q.invSqrt.adjoint (ContinuousLinearMap.id ℂ G)
    simpa using this
  have hnorm : ‖Q.invSqrt.adjoint‖ ≤ P.frameLowerBound⁻¹ := by
    simpa using Q.invSqrt_norm_le
  have hcomp : paperHilbertSchmidtNorm P.canonicalSinTheta ≤
      ‖Q.invSqrt.adjoint‖ * paperHilbertSchmidtNorm P.rawOverlap := by
    have h := paperHilbertSchmidtNorm_comp_le
      Q.invSqrt.adjoint hraw (ContinuousLinearMap.id ℂ G)
    rw [ContinuousLinearMap.comp_id] at h
    rw [hblock]
    exact h.trans (mul_le_of_le_one_right
      (mul_nonneg (norm_nonneg _) (paperHilbertSchmidtNorm_nonneg _))
      ContinuousLinearMap.norm_id_le)
  refine ⟨hmem, ?_⟩
  calc
    P.frameLowerBound * paperHilbertSchmidtNorm P.canonicalSinTheta
        ≤ P.frameLowerBound *
            (‖Q.invSqrt.adjoint‖ * paperHilbertSchmidtNorm P.rawOverlap) :=
      mul_le_mul_of_nonneg_left hcomp P.frameLowerBound_pos.le
    _ ≤ P.frameLowerBound *
          (P.frameLowerBound⁻¹ *
            paperHilbertSchmidtNorm P.rawOverlap) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hnorm
          (paperHilbertSchmidtNorm_nonneg P.rawOverlap))
        P.frameLowerBound_pos.le
    _ = paperHilbertSchmidtNorm P.rawOverlap := by
      rw [← mul_assoc, mul_inv_cancel₀ P.frameLowerBound_pos.ne', one_mul]

/-- **Davis--Kahan 1970, Theorem 6.2, complex square-norm form.** -/
theorem result
    (P : PaperTheorem62Data (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentative P.canonicalSinTheta)
    (hR : IsPaperHilbertSchmidt P.data.residual) :
    IsPaperHilbertSchmidt S.operator ∧
      P.gap * P.frameLowerBound * paperHilbertSchmidtNorm S.operator ≤
        paperHilbertSchmidtNorm P.data.residual := by
  have hraw := P.rawOverlap_bound hR
  have hframe := P.canonicalSinTheta_frame_bound hraw.1
  have hS : IsPaperHilbertSchmidt S.operator :=
    (S.same_singular_values.isPaperHilbertSchmidt_iff).2 hframe.1
  have hSnorm := S.same_singular_values.paperHilbertSchmidtNorm_eq
  refine ⟨hS, ?_⟩
  rw [hSnorm]
  calc
    P.gap * P.frameLowerBound * paperHilbertSchmidtNorm P.canonicalSinTheta
        = P.gap *
            (P.frameLowerBound * paperHilbertSchmidtNorm P.canonicalSinTheta) := by ring
    _ ≤ P.gap * paperHilbertSchmidtNorm P.rawOverlap :=
      mul_le_mul_of_nonneg_left hframe.2 P.gap_pos.le
    _ ≤ paperHilbertSchmidtNorm P.projectedResidual := hraw.2
    _ ≤ paperHilbertSchmidtNorm P.data.residual :=
      P.projectedResidual_norm_le hR

/-- The finite-rank bound-norm fallback printed after Theorem 6.2.

The subscript-one norm in the source is the operator norm. -/
theorem operatorNorm_result_of_rank_le
    (P : PaperTheorem62Data (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentative P.canonicalSinTheta)
    {r : ℕ} (hRank : P.data.residual.rank ≤ (r : Cardinal)) :
    P.gap * P.frameLowerBound * ‖S.operator‖ ≤
      ‖P.data.residual‖ * Real.sqrt r := by
  have hR : IsPaperHilbertSchmidt P.data.residual :=
    isPaperHilbertSchmidt_of_rank_le hRank
  have hmain := P.result S hR
  calc
    P.gap * P.frameLowerBound * ‖S.operator‖
        ≤ P.gap * P.frameLowerBound *
            paperHilbertSchmidtNorm S.operator :=
      mul_le_mul_of_nonneg_left
        (opNorm_le_paperHilbertSchmidtNorm hmain.1)
        (mul_nonneg P.gap_pos.le P.frameLowerBound_pos.le)
    _ ≤ paperHilbertSchmidtNorm P.data.residual := hmain.2
    _ ≤ Real.sqrt r * ‖P.data.residual‖ :=
      paperHilbertSchmidtNorm_le_sqrt_rank_mul_opNorm hRank
    _ = ‖P.data.residual‖ * Real.sqrt r := mul_comm _ _

/-- Theorem 6.2 with the source representative allowed to use arbitrary
Hilbert coordinate spaces. -/
theorem result_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    (P : PaperTheorem62Data (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.canonicalSinTheta)
    (hR : IsPaperHilbertSchmidt P.data.residual) :
    IsPaperHilbertSchmidt S.operator ∧
      P.gap * P.frameLowerBound * paperHilbertSchmidtNorm S.operator ≤
        paperHilbertSchmidtNorm P.data.residual := by
  have hcanonical := P.result
    (PaperSinThetaRepresentative.canonical P.canonicalSinTheta) hR
  have hmem := S.same_singular_sequence.isPaperHilbertSchmidt_iff
  have hnorm := S.same_singular_sequence.paperHilbertSchmidtNorm_eq
  refine ⟨hmem.mpr hcanonical.1, ?_⟩
  rw [hnorm]
  exact hcanonical.2

/-- The finite-rank bound-norm fallback for an arbitrary source
representative. -/
theorem operatorNorm_result_across_of_rank_le
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    (P : PaperTheorem62Data (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.canonicalSinTheta)
    {r : ℕ} (hRank : P.data.residual.rank ≤ (r : Cardinal)) :
    P.gap * P.frameLowerBound * ‖S.operator‖ ≤
      ‖P.data.residual‖ * Real.sqrt r := by
  have hcanonical := P.operatorNorm_result_of_rank_le
    (PaperSinThetaRepresentative.canonical P.canonicalSinTheta) hRank
  rw [S.same_singular_sequence.opNorm_eq]
  exact hcanonical

end PaperTheorem62Data

end Complex

section Real

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Real exact inputs of Theorem 6.2. -/
structure PaperRealTheorem62Data where
  data : UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := F) (G := G)
  exactMap : H →L[ℝ] E
  ambient_selfAdjoint : _root_.IsSelfAdjoint data.A
  trial_selfAdjoint : _root_.IsSelfAdjoint data.A₀
  complement_selfAdjoint : _root_.IsSelfAdjoint data.Λ₁
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  gap : ℝ
  frameLowerBound : ℝ
  gap_pos : 0 < gap
  frameLowerBound_pos : 0 < frameLowerBound
  lowerFrame : LowerFrameBound data.X frameLowerBound
  spectral_distance :
    ∀ lam ∈ TauCeti.LinearPMap.realSpectrum data.A₀, ∀ α ∈ TauCeti.LinearPMap.realSpectrum data.Λ₁,
      gap ≤ |lam - α|

namespace PaperRealTheorem62Data

/-- The canonical sine-theta operator of a Theorem 6.2 configuration. -/
noncomputable def canonicalSinTheta
    (P : PaperRealTheorem62Data (E := E) (F := F) (G := G) (H := H)) :
    G →L[ℝ] F :=
  sinThetaBlockOfPolarData
    (lowerFramePolarDataReal P.data.X P.lowerFrame P.frameLowerBound_pos)
    P.data.F₁

/-- The raw overlap block `X⋆ F₁`, before any frame normalization. -/
def rawOverlap
    (P : PaperRealTheorem62Data (E := E) (F := F) (G := G) (H := H)) :
    G →L[ℝ] F := P.data.X.adjoint ∘L P.data.F₁

/-- The residual projected onto the complementary block. -/
def projectedResidual
    (P : PaperRealTheorem62Data (E := E) (F := F) (G := G) (H := H)) :
    G →L[ℝ] F := -(P.data.residual.adjoint ∘L P.data.F₁)

/-- Whitening introduces exactly the source factor `epsilon^(-1)`.

The real mirror of `PaperTheorem62Data.canonicalSinTheta_frame_bound`.  The complex section
factors this out and its `result` cites it; the real section had inlined the same
derivation into `result`, which is the only reason the two sections looked different. -/
theorem canonicalSinTheta_frame_bound
    (P : PaperRealTheorem62Data (E := E) (F := F) (G := G) (H := H))
    (hraw : IsPaperHilbertSchmidt P.rawOverlap) :
    IsPaperHilbertSchmidt P.canonicalSinTheta ∧
      P.frameLowerBound * paperHilbertSchmidtNorm P.canonicalSinTheta ≤
        paperHilbertSchmidtNorm P.rawOverlap := by
  let Q := lowerFramePolarDataReal P.data.X P.lowerFrame P.frameLowerBound_pos
  have hcanonical : P.canonicalSinTheta = Q.invSqrt.adjoint ∘L P.rawOverlap := by
    simp [canonicalSinTheta, rawOverlap, sinThetaBlockOfPolarData,
      frameIsometryOfPolarData, Q, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.comp_assoc]
  have hmem : IsPaperHilbertSchmidt P.canonicalSinTheta := by
    rw [hcanonical]
    have h := hraw.comp Q.invSqrt.adjoint (ContinuousLinearMap.id ℝ G)
    rwa [ContinuousLinearMap.comp_id] at h
  have hnorm : ‖Q.invSqrt.adjoint‖ ≤ P.frameLowerBound⁻¹ := by
    simpa using Q.invSqrt_norm_le
  have hcomp : paperHilbertSchmidtNorm P.canonicalSinTheta ≤
      ‖Q.invSqrt.adjoint‖ * paperHilbertSchmidtNorm P.rawOverlap := by
    have h := paperHilbertSchmidtNorm_comp_le
      Q.invSqrt.adjoint hraw (ContinuousLinearMap.id ℝ G)
    rw [ContinuousLinearMap.comp_id] at h
    rw [hcanonical]
    exact h.trans (mul_le_of_le_one_right
      (mul_nonneg (norm_nonneg _) (paperHilbertSchmidtNorm_nonneg _))
      ContinuousLinearMap.norm_id_le)
  refine ⟨hmem, ?_⟩
  calc
    P.frameLowerBound * paperHilbertSchmidtNorm P.canonicalSinTheta
        ≤ P.frameLowerBound *
            (‖Q.invSqrt.adjoint‖ * paperHilbertSchmidtNorm P.rawOverlap) :=
      mul_le_mul_of_nonneg_left hcomp P.frameLowerBound_pos.le
    _ ≤ P.frameLowerBound *
          (P.frameLowerBound⁻¹ * paperHilbertSchmidtNorm P.rawOverlap) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hnorm
          (paperHilbertSchmidtNorm_nonneg P.rawOverlap))
        P.frameLowerBound_pos.le
    _ = paperHilbertSchmidtNorm P.rawOverlap := by
      rw [← mul_assoc, mul_inv_cancel₀ P.frameLowerBound_pos.ne', one_mul]

/-- Real Theorem 6.2, proved by exact complexification of the square-norm
Sylvester step and the scalar-generic lower-frame algebra. -/
theorem result
    (P : PaperRealTheorem62Data (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentative P.canonicalSinTheta)
    (hR : IsPaperHilbertSchmidt P.data.residual) :
    IsPaperHilbertSchmidt S.operator ∧
      P.gap * P.frameLowerBound * paperHilbertSchmidtNorm S.operator ≤
        paperHilbertSchmidtNorm P.data.residual := by
  have hRadj : IsPaperHilbertSchmidt P.data.residual.adjoint :=
    (isPaperHilbertSchmidt_adjoint_iff P.data.residual).2 hR
  have hProjected : IsPaperHilbertSchmidt P.projectedResidual := by
    have hcomp := hRadj.comp (ContinuousLinearMap.id ℝ F) P.data.F₁
    simpa [projectedResidual] using
      (isPaperHilbertSchmidt_neg_iff
        (P.data.residual.adjoint ∘L P.data.F₁)).2 (by simpa using hcomp)
  have hEq := unbounded_adjoint_residual_block_identity P.data
    P.ambient_selfAdjoint P.trial_selfAdjoint P.complement_selfAdjoint
  have hraw := paperHilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap_direct
    P.trial_selfAdjoint P.complement_selfAdjoint P.gap_pos
    P.spectral_distance hEq hProjected
  have hrawHS : IsPaperHilbertSchmidt P.rawOverlap := hraw.1
  obtain ⟨hcanonmem, hframe⟩ := P.canonicalSinTheta_frame_bound hrawHS
  have hprojNorm : paperHilbertSchmidtNorm P.projectedResidual ≤
      paperHilbertSchmidtNorm P.data.residual := by
    have hF₁ : ‖P.data.F₁‖ ≤ 1 :=
      opNorm_le_one_of_isometry P.exact_decomposition.isometry₁
    calc
      paperHilbertSchmidtNorm P.projectedResidual =
          paperHilbertSchmidtNorm (P.data.residual.adjoint ∘L P.data.F₁) := by
        simp [projectedResidual]
      _ = paperHilbertSchmidtNorm
            (ContinuousLinearMap.id ℝ F ∘L P.data.residual.adjoint ∘L
              P.data.F₁) := by simp
      _ ≤ paperHilbertSchmidtNorm P.data.residual.adjoint :=
        paperHilbertSchmidtNorm_comp_isometries_le
          (ContinuousLinearMap.id ℝ F) hRadj P.data.F₁
          ContinuousLinearMap.norm_id_le hF₁
      _ = paperHilbertSchmidtNorm P.data.residual :=
        paperHilbertSchmidtNorm_adjoint P.data.residual
  have hS : IsPaperHilbertSchmidt S.operator :=
    (S.same_singular_values.isPaperHilbertSchmidt_iff).2 hcanonmem
  refine ⟨hS, ?_⟩
  rw [S.same_singular_values.paperHilbertSchmidtNorm_eq]
  calc
    P.gap * P.frameLowerBound * paperHilbertSchmidtNorm P.canonicalSinTheta
        = P.gap *
            (P.frameLowerBound * paperHilbertSchmidtNorm P.canonicalSinTheta) := by ring
    _ ≤ P.gap * paperHilbertSchmidtNorm P.rawOverlap :=
      mul_le_mul_of_nonneg_left hframe P.gap_pos.le
    _ ≤ paperHilbertSchmidtNorm P.projectedResidual := hraw.2
    _ ≤ paperHilbertSchmidtNorm P.data.residual := hprojNorm

/-- Real finite-rank bound-norm fallback printed after Theorem 6.2. -/
theorem operatorNorm_result_of_rank_le
    (P : PaperRealTheorem62Data (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentative P.canonicalSinTheta)
    {r : ℕ} (hRank : P.data.residual.rank ≤ (r : Cardinal)) :
    P.gap * P.frameLowerBound * ‖S.operator‖ ≤
      ‖P.data.residual‖ * Real.sqrt r := by
  have hR : IsPaperHilbertSchmidt P.data.residual :=
    isPaperHilbertSchmidt_of_rank_le hRank
  have hmain := P.result S hR
  calc
    P.gap * P.frameLowerBound * ‖S.operator‖
        ≤ P.gap * P.frameLowerBound *
            paperHilbertSchmidtNorm S.operator :=
      mul_le_mul_of_nonneg_left
        (opNorm_le_paperHilbertSchmidtNorm hmain.1)
        (mul_nonneg P.gap_pos.le P.frameLowerBound_pos.le)
    _ ≤ paperHilbertSchmidtNorm P.data.residual := hmain.2
    _ ≤ Real.sqrt r * ‖P.data.residual‖ :=
      paperHilbertSchmidtNorm_le_sqrt_rank_mul_opNorm hRank
    _ = ‖P.data.residual‖ * Real.sqrt r := mul_comm _ _

/-- Real Theorem 6.2 with arbitrary representative coordinate spaces. -/
theorem result_across
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℝ F₀] [CompleteSpace F₀]
    (P : PaperRealTheorem62Data (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.canonicalSinTheta)
    (hR : IsPaperHilbertSchmidt P.data.residual) :
    IsPaperHilbertSchmidt S.operator ∧
      P.gap * P.frameLowerBound * paperHilbertSchmidtNorm S.operator ≤
        paperHilbertSchmidtNorm P.data.residual := by
  have hcanonical := P.result
    (PaperSinThetaRepresentative.canonical P.canonicalSinTheta) hR
  have hmem := S.same_singular_sequence.isPaperHilbertSchmidt_iff
  have hnorm := S.same_singular_sequence.paperHilbertSchmidtNorm_eq
  refine ⟨hmem.mpr hcanonical.1, ?_⟩
  rw [hnorm]
  exact hcanonical.2

/-- Real finite-rank bound-norm fallback for an arbitrary source
representative. -/
theorem operatorNorm_result_across_of_rank_le
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℝ F₀] [CompleteSpace F₀]
    (P : PaperRealTheorem62Data (E := E) (F := F) (G := G) (H := H))
    (S : PaperSinThetaRepresentativeAcross
      (E₀ := E₀) (F₀ := F₀) P.canonicalSinTheta)
    {r : ℕ} (hRank : P.data.residual.rank ≤ (r : Cardinal)) :
    P.gap * P.frameLowerBound * ‖S.operator‖ ≤
      ‖P.data.residual‖ * Real.sqrt r := by
  have hcanonical := P.operatorNorm_result_of_rank_le
    (PaperSinThetaRepresentative.canonical P.canonicalSinTheta) hRank
  rw [S.same_singular_sequence.opNorm_eq]
  exact hcanonical

end PaperRealTheorem62Data

end Real

end

end ExactSinTheta
end DavisKahan
end TauCeti