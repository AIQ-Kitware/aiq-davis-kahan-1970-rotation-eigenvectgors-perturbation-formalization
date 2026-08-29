/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedExact
import DavisKahan.Sources.DavisKahan1970.SineTheta.ProjectionBlocks

/-!
# Exact source-facing unbounded ambient `tan 2Theta`

`TanTwoThetaUnboundedExact.lean` closes the difficult directed residual half of
Davis--Kahan's unbounded extension.  The ambient half needs no second spectral
argument.  It is the same block assembly as the bounded Section 7 proof:

* the reflection tangent is purely off diagonal and skew-adjoint;
* the self-adjoint perturbation is purely off diagonal by `H₀ = H₁ = 0`;
* the directed estimate therefore holds on both complementary corners; and
* Davis--Kahan Lemmas 6.1 and 6.2 assemble the two corners without changing the
  sharp factor `2`.

All spectral cutoffs and pole exclusion remain internal.  No quarter-angle
branch, finite-rank hypothesis, compactness hypothesis, or externally supplied
cutoff family occurs in the source-facing theorem below.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace
open Filter
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.ApproximationNumber

noncomputable section

universe u

variable {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace G]

local instance instCompleteSpaceCoeOfHasOrthogonalProjectionUnboundedAmbientExact
    (W : Submodule ℂ G) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

/-! ## Block bookkeeping -/

omit [CompleteSpace G] in
private theorem comp_eq_mul_unboundedAmbientExact (f g : G →L[ℂ] G) :
    f ∘L g = f * g := rfl

omit [CompleteSpace G] in
private theorem projectionBlock_lower_unboundedAmbientExact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection]
    (K : G →L[ℂ] G) :
    paperProjectionBlock Uᗮ U K =
      (1 - U.starProjection) * K * U.starProjection := by
  rw [paperProjectionBlock, Submodule.starProjection_orthogonal',
    comp_eq_mul_unboundedAmbientExact, comp_eq_mul_unboundedAmbientExact, mul_assoc]

omit [CompleteSpace G] in
private theorem projectionBlock_upper_unboundedAmbientExact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection]
    (K : G →L[ℂ] G) :
    paperProjectionBlock Uᗮᗮ Uᗮ K =
      U.starProjection * K * (1 - U.starProjection) := by
  have hUperp : Uᗮᗮ = U := Submodule.orthogonal_orthogonal U
  rw [paperProjectionBlock]
  simp only [hUperp, Submodule.starProjection_orthogonal',
    comp_eq_mul_unboundedAmbientExact]
  rw [mul_assoc]

omit [CompleteSpace G] in
private theorem projectionBlock_smul_unboundedAmbientExact
    (Ω Γ : Submodule ℂ G)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (c : ℂ) (K : G →L[ℂ] G) :
    paperProjectionBlock Ω Γ (c • K) = c • paperProjectionBlock Ω Γ K := by
  ext x
  simp [paperProjectionBlock]

private theorem kyFan_upper_eq_lower_of_selfAdjoint_unboundedAmbientExact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection]
    (K : G →L[ℂ] G) (hK : IsSelfAdjoint K) (k : ℕ) :
    kyFanApproximationGauge k (paperProjectionBlock Uᗮᗮ Uᗮ K) =
      kyFanApproximationGauge k (paperProjectionBlock Uᗮ U K) := by
  have hadj : paperProjectionBlock Uᗮᗮ Uᗮ K =
      (paperProjectionBlock Uᗮ U K).adjoint := by
    rw [projectionBlock_upper_unboundedAmbientExact,
      projectionBlock_lower_unboundedAmbientExact]
    show _ = star _
    simp only [star_mul, star_sub, star_one,
      (isSelfAdjoint_starProjection U).star_eq, hK.star_eq]
    noncomm_ring
  rw [hadj, kyFanApproximationGauge_adjoint]

private theorem kyFan_upper_eq_lower_of_skewAdjoint_unboundedAmbientExact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection]
    (K : G →L[ℂ] G) (hK : K.adjoint = -K) (k : ℕ) :
    kyFanApproximationGauge k (paperProjectionBlock Uᗮᗮ Uᗮ K) =
      kyFanApproximationGauge k (paperProjectionBlock Uᗮ U K) := by
  have hadj : paperProjectionBlock Uᗮᗮ Uᗮ K =
      -(paperProjectionBlock Uᗮ U K).adjoint := by
    rw [projectionBlock_upper_unboundedAmbientExact,
      projectionBlock_lower_unboundedAmbientExact]
    show _ = -star _
    have hKstar : star K = -K := by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact hK
    simp only [star_mul, star_sub, star_one,
      (isSelfAdjoint_starProjection U).star_eq, hKstar]
    noncomm_ring
  rw [hadj, kyFanApproximationGauge_neg, kyFanApproximationGauge_adjoint]

omit [CompleteSpace G] in
private theorem diagonalPart_eq_zero_of_isOddFor_unboundedAmbientExact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection] {K : G →L[ℂ] G}
    (hK : TauCeti.IsOddFor U K) : U.diagonalPart K = 0 := by
  ext x
  rw [Submodule.diagonalPart_apply]
  have hlow : K (U.starProjection x) ∈ Uᗮ :=
    hK.1 _ (U.starProjection_apply_mem x)
  have hupp : K (Uᗮ.starProjection x) ∈ U :=
    hK.2 _ (Uᗮ.starProjection_apply_mem x)
  have hupp' : K (Uᗮ.starProjection x) ∈ Uᗮᗮ :=
    U.le_orthogonal_orthogonal hupp
  rw [(U.starProjection_apply_eq_zero_iff).mpr hlow,
    (Uᗮ.starProjection_apply_eq_zero_iff).mpr hupp', zero_add]
  rfl

omit [CompleteSpace G] in
private theorem paperDiagonalPair_orthogonal_eq_offDiagonalPart_unboundedAmbientExact
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] (K : G →L[ℂ] G) :
    paperDiagonalPair Uᗮ U K = U.offDiagonalPart K := by
  rw [paperDiagonalPair, Submodule.offDiagonalPart_eq, Submodule.diagonalPart_eq]
  simp only [Submodule.orthogonal_orthogonal, Submodule.starProjection_orthogonal',
    comp_eq_mul_unboundedAmbientExact]
  have hp : U.starProjection * U.starProjection = U.starProjection :=
    U.isIdempotentElem_starProjection
  noncomm_ring [hp]

omit [CompleteSpace G] in
private theorem paperDiagonalPair_orthogonal_eq_self_of_isOddFor_unboundedAmbientExact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection] {K : G →L[ℂ] G}
    (hK : TauCeti.IsOddFor U K) : paperDiagonalPair Uᗮ U K = K := by
  rw [paperDiagonalPair_orthogonal_eq_offDiagonalPart_unboundedAmbientExact]
  rw [Submodule.offDiagonalPart_eq,
    diagonalPart_eq_zero_of_isOddFor_unboundedAmbientExact hK, sub_zero]

/-! ## The reflection tangent is an odd skew-adjoint block -/

omit [CompleteSpace G] in
private theorem ringInverse_diagonalPart_sq_mem_orthogonal_of_mem_orthogonal_unboundedAmbientExact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection] {Z : G →L[ℂ] G}
    (hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z))
    {y : G} (hy : y ∈ Uᗮ) :
    Ring.inverse (U.diagonalPart Z * U.diagonalPart Z) y ∈ Uᗮ := by
  have hcomm : Commute U.starProjection
      (Ring.inverse (U.diagonalPart Z * U.diagonalPart Z)) :=
    commute_ringInverse hCC
      ((commute_starProjection_diagonalPart U Z).mul_right
        (commute_starProjection_diagonalPart U Z))
  have h := congrArg (fun S : G →L[ℂ] G => S y) hcomm.eq
  simp only [_root_.mul_apply_eq_comp] at h
  have hy0 : U.starProjection y = 0 :=
    (U.starProjection_apply_eq_zero_iff).mpr hy
  rw [hy0, map_zero] at h
  exact (U.starProjection_apply_eq_zero_iff).mp h

omit [CompleteSpace G] in
/-- The whole reflection tangent exchanges the two source summands. -/
theorem isOddFor_unboundedReflectionTangent_exact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection] {Z : G →L[ℂ] G}
    (hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z)) :
    TauCeti.IsOddFor U (unboundedReflectionTangent U Z) := by
  refine ⟨?_, ?_⟩
  · intro y hy
    exact unboundedReflectionTangent_mem_orthogonal_of_mem U Z hCC hy
  · intro y hy
    rw [unboundedReflectionTangent_eq]
    simp only [_root_.mul_apply_eq_comp]
    exact TauCeti.offDiagonalPart_mem_of_mem_orthogonal U Z
      (ringInverse_diagonalPart_sq_mem_orthogonal_of_mem_orthogonal_unboundedAmbientExact
        hCC (TauCeti.diagonalPart_mem_orthogonal_of_mem_orthogonal U Z hy))

/-- The whole reflection tangent is skew-adjoint.  This is the operator form of
having two complementary directed tangent blocks that are adjoints up to sign. -/
theorem adjoint_unboundedReflectionTangent_eq_neg_exact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection] {Z : G →L[ℂ] G}
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z)) :
    (unboundedReflectionTangent U Z).adjoint = -unboundedReflectionTangent U Z := by
  set C := U.diagonalPart Z
  set S := U.offDiagonalPart Z
  set T := unboundedReflectionTangent U Z
  set D := Ring.inverse (C * C)
  have hCsa : IsSelfAdjoint C := TauCeti.isSelfAdjoint_diagonalPart (U := U) hZsa
  have hSsa : IsSelfAdjoint S := TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa
  have hDCC : D * (C * C) = 1 := by
    dsimp only [D, C]
    exact Ring.inverse_mul_cancel _ hCC
  have hTformula : T = S * D * C := by
    rfl
  have hTC : T * C = S := by
    rw [hTformula]
    calc
      S * D * C * C = S * (D * (C * C)) := by noncomm_ring
      _ = S := by rw [hDCC, mul_one]
  have hCTstar : C * T.adjoint = S := by
    have h := congrArg ContinuousLinearMap.adjoint hTC
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.mul_def, hCsa.adjoint_eq, hSsa.adjoint_eq] at h
    exact h
  have hanti : C * S + S * C = 0 := by
    simpa only [C, S] using
      TauCeti.diagonalPart_mul_offDiagonalPart_add_offDiagonalPart_mul_diagonalPart
        (U := U) hZ2
  have hCS : C * S = -(S * C) := add_eq_zero_iff_eq_neg.mp hanti
  have hCD : Commute C D := by
    dsimp only [D]
    exact commute_ringInverse hCC ((Commute.refl C).mul_right (Commute.refl C))
  have hCT : C * T = -S := by
    rw [hTformula]
    calc
      C * (S * D * C) = (C * S) * D * C := by noncomm_ring
      _ = -(S * C) * D * C := by rw [hCS]
      _ = -(S * (C * D) * C) := by noncomm_ring
      _ = -(S * (D * C) * C) := by rw [hCD.eq]
      _ = -(S * D * (C * C)) := by noncomm_ring
      _ = -(S * (D * (C * C))) := by rw [mul_assoc]
      _ = -S := by rw [hDCC, mul_one]
  have hCunit : IsUnit C := ((Commute.refl C).isUnit_mul_iff.mp hCC).1
  have hsum : C * (T.adjoint + T) = 0 := by
    rw [mul_add, hCTstar, hCT]
    abel
  have hleft : Ring.inverse C * C = 1 := Ring.inverse_mul_cancel C hCunit
  have hzero : T.adjoint + T = 0 := by
    calc
      T.adjoint + T = 1 * (T.adjoint + T) := by rw [one_mul]
      _ = (Ring.inverse C * C) * (T.adjoint + T) := by rw [hleft]
      _ = Ring.inverse C * (C * (T.adjoint + T)) := by noncomm_ring
      _ = 0 := by rw [hsum, mul_zero]
  exact eq_neg_of_add_eq_zero_left hzero

/-! ## Exact ambient endpoint -/

/-- **Paper-exact unbounded ambient `tan 2Theta` theorem, complex form.**

This is the ambient conclusion of the Section 2 headline theorem at the
unbounded self-adjoint scope advertised by Davis--Kahan.  The caller supplies
only source data: the unbounded self-adjoint `A`, its low-energy spectral
subspace, a bounded self-adjoint fully off-diagonal perturbation `B`, the
reducing reflection `Z` of `A+B`, and the separated form bounds.  Membership of
`B` in the selected source ideal is the only norm-domain premise.

The canonical spectral cutoffs, pole exclusion, directed residual estimate,
and both-corner Lemma-6.1 assembly are all internal. -/
theorem tanTwoTheta_unbounded_ambient_paperUINorm_exact
    (N : PaperUnitaryInvariantNorm)
    {A : G →ₗ.[ℂ] G} {B Z : G →L[ℂ] G} {a b c : ℝ}
    (hA : IsSelfAdjoint A)
    (hBsa : IsSelfAdjoint B)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : G), hZdom x⟩ + B (Z (x : G)) = Z (A x) + Z (B (x : G)))
    (hUa : ∀ x : A.domain,
      (x : G) ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic →
      RCLike.re ⟪A x, (x : G)⟫_ℂ ≤ a * ‖(x : G)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : G) ∈
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : G)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : G)⟫_ℂ)
    (hab : a < b) (hBmem : N.Mem B) :
    IsUnit
        ((TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z *
          (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z) ∧
      N.Mem (unboundedReflectionTangent
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) Z) ∧
      (b - a) * N.gauge (unboundedReflectionTangent
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) Z) ≤
        2 * N.gauge B := by
  let U : Submodule ℂ G :=
    TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic
  have hred : TauCeti.LinearPMap.ReducesSubspace A U :=
    TauCeti.LinearPMap.reducesSubspace_specRange hA (Set.Iic c) measurableSet_Iic
  have hgU : ∀ y ∈ U,
      ‖U.offDiagonalPart Z y‖ ≤ TauCeti.crossBlockBound (b - a) ‖B‖ * ‖y‖ := by
    intro y hy
    exact TauCeti.norm_offDiagonalPart_apply_le_specRange hA hB hZsa hZ2 hZdom
      hZcomm hUa hUb hab hy
  have hg0 : 0 ≤ TauCeti.crossBlockBound (b - a) ‖B‖ :=
    TauCeti.crossBlockBound_nonneg (norm_nonneg B)
  have hg1 : TauCeti.crossBlockBound (b - a) ‖B‖ < 1 :=
    crossBlockBound_lt_one (sub_pos.mpr hab) (norm_nonneg B)
  have hSle : ‖U.offDiagonalPart Z‖ ≤ TauCeti.crossBlockBound (b - a) ‖B‖ :=
    norm_offDiagonalPart_le hZsa hg0 hgU
  have hS1 : ‖U.offDiagonalPart Z‖ < 1 := lt_of_le_of_lt hSle hg1
  have hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z) :=
    isUnit_diagonalPart_sq_of_forall_mem hZsa hZ2 hg0 hg1 hgU
  have hstrong : StronglyTendsto
      (fun n : ℕ => cutoffCorner (TauCeti.spectralCutoffSeq hA c n)) atTop
      (ContinuousLinearMap.id ℂ U) := by
    simpa [U] using stronglyTendsto_cutoffCorner_spectralCutoffSeq hA c
  have hcorner : ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k (reflectionTangentCorner U Z) ≤
        2 * kyFanApproximationGauge k (reflectionResidualCorner U B) := by
    intro k
    exact gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan hred hB hZsa hZ2
      hZdom hZcomm hUa hUb hab hS1
      (σ := fun n : ℕ => |c| + n) (fun n : ℕ => by positivity)
      (fun n : ℕ => TauCeti.spectralCutoffSeq hA c n) hstrong k
  let T : G →L[ℂ] G := unboundedReflectionTangent U Z
  have hTodd : TauCeti.IsOddFor U T := by
    simpa only [T] using isOddFor_unboundedReflectionTangent_exact
      (U := U) (Z := Z) hCC
  have hTskew : T.adjoint = -T := by
    simpa only [T] using adjoint_unboundedReflectionTangent_eq_neg_exact
      (U := U) (Z := Z) hZsa hZ2 hCC
  have hhalf : 0 < (b - a) / 2 := by linarith
  have hcnorm : ‖((((b - a) / 2 : ℝ)) : ℂ)‖ = (b - a) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhalf]
  have h₀ : ∀ k : ℕ,
      kyFanApproximationGauge k (paperProjectionBlock Uᗮ U
          (((((b - a) / 2 : ℝ)) : ℂ) • T)) ≤
        kyFanApproximationGauge k (paperProjectionBlock Uᗮ U B) := by
    intro k
    rw [projectionBlock_smul_unboundedAmbientExact,
      kyFanApproximationGauge_smul, hcnorm]
    rw [(paperProjectionBlock_same_compression Uᗮ U T).kyFanApproximationGauge_eq k,
      (paperProjectionBlock_same_compression Uᗮ U B).kyFanApproximationGauge_eq k]
    change ((b - a) / 2) * kyFanApproximationGauge k (reflectionTangentCorner U Z) ≤
      kyFanApproximationGauge k (reflectionResidualCorner U B)
    linarith [hcorner k]
  have h₁ : ∀ k : ℕ,
      kyFanApproximationGauge k (paperProjectionBlock Uᗮᗮ Uᗮ
          (((((b - a) / 2 : ℝ)) : ℂ) • T)) ≤
        kyFanApproximationGauge k (paperProjectionBlock Uᗮᗮ Uᗮ B) := by
    intro k
    rw [projectionBlock_smul_unboundedAmbientExact,
      kyFanApproximationGauge_smul, hcnorm,
      kyFan_upper_eq_lower_of_skewAdjoint_unboundedAmbientExact T hTskew k,
      kyFan_upper_eq_lower_of_selfAdjoint_unboundedAmbientExact B hBsa k]
    have hk := h₀ k
    rw [projectionBlock_smul_unboundedAmbientExact,
      kyFanApproximationGauge_smul, hcnorm] at hk
    exact hk
  have hcombine := paperLemma61_all_kyFan Uᗮ U
    (((((b - a) / 2 : ℝ)) : ℂ) • T)
    (((((b - a) / 2 : ℝ)) : ℂ) • T) B B h₀ h₁
  have hpairT : paperDiagonalPair Uᗮ U T = T :=
    paperDiagonalPair_orthogonal_eq_self_of_isOddFor_unboundedAmbientExact hTodd
  have hpairB : paperDiagonalPair Uᗮ U B = B :=
    paperDiagonalPair_orthogonal_eq_self_of_isOddFor_unboundedAmbientExact hB
  have hwhole : ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k T ≤ 2 * kyFanApproximationGauge k B := by
    intro k
    have h := hcombine k
    have hsumT :
        paperProjectionBlock Uᗮ U (((((b - a) / 2 : ℝ)) : ℂ) • T) +
          paperProjectionBlock Uᗮᗮ Uᗮ (((((b - a) / 2 : ℝ)) : ℂ) • T) =
        ((((b - a) / 2 : ℝ)) : ℂ) • T := by
      rw [projectionBlock_smul_unboundedAmbientExact,
        projectionBlock_smul_unboundedAmbientExact, ← smul_add]
      change (((((b - a) / 2 : ℝ)) : ℂ) • paperDiagonalPair Uᗮ U T) = _
      rw [hpairT]
    have hsumB :
        paperProjectionBlock Uᗮ U B + paperProjectionBlock Uᗮᗮ Uᗮ B = B := by
      change paperDiagonalPair Uᗮ U B = B
      exact hpairB
    rw [hsumT, hsumB, kyFanApproximationGauge_smul, hcnorm] at h
    linarith
  have hscaled : ∀ k : ℕ,
      ((b - a) / 2) * kyFanApproximationGauge k T ≤ kyFanApproximationGauge k B := by
    intro k
    linarith [hwhole k]
  have hUI := N.mul_gauge_le_of_all_mul_kyFan_le hhalf hBmem hscaled
  change IsUnit (U.diagonalPart Z * U.diagonalPart Z) ∧
      N.Mem T ∧ (b - a) * N.gauge T ≤ 2 * N.gauge B
  refine ⟨hCC, hUI.1, ?_⟩
  nlinarith [hUI.2]

end

end DavisKahan1970
end TauCeti
