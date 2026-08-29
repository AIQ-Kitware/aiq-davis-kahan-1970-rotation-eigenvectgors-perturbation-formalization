/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaWholeSpace
import DavisKahan.Sources.DavisKahan1970.SineTheta.TrialReflection

/-!
# The unbounded directed half of the `sin 2Θ` theorem, at the printed residual

> **Theorem (the `sin 2θ` theorem).**  Assume there is an interval `[β,α]` and a
> `δ > 0` such that the spectrum of `Λ₀` lies entirely in `[β,α]` while that of
> `Λ₁` lies entirely outside of `]β-δ, α+δ[`.  Then for every unitary-invariant
> norm, `δ‖sin 2Θ₀‖ ≤ 2‖R‖` and `δ‖sin 2Θ‖ ≤ 2‖H‖`.

`R` is the trial residual of equation (1.8),

`R = (A + H) E₀ - E₀ A₀`,

with `E₀` the isometry onto the trial subspace and `A₀` the trial (Ritz)
operator.  Section 2 states the theorem for unbounded self-adjoint operators as
well, "although we must assume `H` or `R` bounded to draw useful inferences",
and allows the gap interval to be half-infinite.

The directed conclusion at that unbounded scope is what this module proves.  The
repository already had

* the bounded directed trial-residual theorem
  `sinTwoTheta_directedResidual_paperUINorm`, and
* an unbounded directed theorem whose right-hand side is a **reflection**
  residual — a bounded self-adjoint `R` with `(A + R) J_V = J_V A` — which is a
  different operator from the printed `R` and therefore does not certify the
  printed statement.

## The route

The paper reflects through the trial subspace.  Here the ambient operator is a
possibly unbounded self-adjoint closed operator, so the reflected system is
built from the trial data rather than from an ambient bounded operator:

* `A P_V` is bounded, because `R` and `A₀` are and `V ⊆ dom A`; call it `T`;
* `X = P_{Vᗮ} T P_V` is the single off-diagonal block, and `X = P_{Vᗮ} R E₀*`,
  so every Ky Fan gauge of `X` is at most that of `R`;
* `S = X + X*` is the purely off-diagonal part, and its reflection defect
  `J_V S J_V - S = -2S` is exactly the bounded operator that intertwines the
  reflected system, `(A + D) J_V = J_V A` on `dom A`.

The reflection bridge is therefore internal: the caller never sees `D`.  The
sharp factor two comes from
`kyFan_reflectedDefectBlock_le_two_mul_offDiagonalBlock`, the same doubling
identity the bounded theorem uses, and not from a triangle inequality.
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A subspace admitting an orthogonal projection inside a complete ambient
space is itself complete.  `local instance` does not propagate through imports,
so it is reinstalled here. -/
local instance instCompleteSpaceCoeOfHasOrthogonalProjectionDirectedResidual
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe


section MainEstimate

variable {V : Submodule ℂ H} [V.HasOrthogonalProjection]
  {M : V →L[ℂ] V} {R : V →L[ℂ] H}
  {A : H →ₗ.[ℂ] H}

/-- **Davis--Kahan 1970, the directed half of the `sin 2Θ` theorem for an
unbounded self-adjoint operator, Ky Fan form.**

`A` is the (possibly unbounded) self-adjoint operator whose reducing subspace is
the exact one, `V` is the trial subspace, `M` is the trial operator `A₀`, and `R`
is the printed residual `R = A E₀ - E₀ A₀`.  The gap hypotheses are the printed
ones: the exact block is between `β` and `α`, and the complementary block has no
spectrum in `]β-δ, α+δ[`.  The conclusion is

`δ · kyFan_k (sin 2Θ₀) ≤ 2 · kyFan_k R`

with the printed factor two. -/
theorem sinTwoTheta_unbounded_directedResidual_all_kyFan
    (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hVdom : ∀ v : V, (v : H) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : H), hVdom v⟩ = R v + ((M v : V) : H))
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl)) :
    ∀ k : ℕ,
      δ * kyFanApproximationGauge k
          (sinTwoThetaIdealBlock (selfAdjointSpectralSubspace A hA B hB) V) ≤
        2 * kyFanApproximationGauge k R := by
  intro k
  by_cases hk0 : k = 0
  · subst hk0
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  have hSsa : IsSelfAdjoint (trialOffDiagonalPart V M R) :=
    isSelfAdjoint_trialOffDiagonalPart
  have hDsa : IsSelfAdjointOperator ((-2 : ℂ) • trialOffDiagonalPart V M R) := by
    refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp ?_
    rw [IsSelfAdjoint, star_smul, hSsa.star_eq]
    norm_num
  have hraw := sinTwoTheta_reflectionResidual_block_gauge_of_spectrum_gap
    (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hk).toSymmetricOperatorIdealFamily
    A hA ((-2 : ℂ) • trialOffDiagonalPart V M R) hDsa B hB V hβα hδ
    hBlow hBhigh hBcomplSpec (reflectionOperator_mem_domain hVdom)
    (trialReflection_intertwines hA hVdom hres)
    (KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℂ) k hk _)
  rw [KyFanDominantIdealFamily.toSymmetric_gaugeReal,
    KyFanDominantIdealFamily.toSymmetric_gaugeReal,
    KyFanDominantIdealFamily.kyFan_gauge,
    KyFanDominantIdealFamily.kyFan_gauge] at hraw
  -- flip the block to the orientation of the doubling identity
  have hDsa' : IsSelfAdjoint ((-2 : ℂ) • trialOffDiagonalPart V M R) := by
    rw [IsSelfAdjoint, star_smul, hSsa.star_eq]
    norm_num
  have hflip : kyFanApproximationGauge k
        ((selfAdjointSpectralSubspace A hA B hB).starProjection ∘L
          ((-2 : ℂ) • trialOffDiagonalPart V M R) ∘L
          ((selfAdjointSpectralSubspace A hA B hB)ᗮ.map
            (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) =
      kyFanApproximationGauge k
        (((selfAdjointSpectralSubspace A hA B hB)ᗮ.map
            (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection ∘L
          ((-2 : ℂ) • trialOffDiagonalPart V M R) ∘L
          (selfAdjointSpectralSubspace A hA B hB).starProjection) := by
    rw [← kyFanApproximationGauge_adjoint]
    congr 1
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection _).adjoint_eq,
      (isSelfAdjoint_starProjection _).adjoint_eq,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp hDsa']
    rfl
  have hdefectEq : conjByIsometryEquiv V.reflection (trialOffDiagonalPart V M R) -
      trialOffDiagonalPart V M R = (-2 : ℂ) • trialOffDiagonalPart V M R := by
    rw [conjByReflection_sub_eq_reflectionDefect,
      reflectionDefect_trialOffDiagonalPart]
  have hdouble := kyFan_reflectedDefectBlock_le_two_mul_offDiagonalBlock hSsa
    (selfAdjointSpectralSubspace A hA B hB) V k
  rw [hdefectEq, trialOffDiagonalPart_upper] at hdouble
  have hblockR : kyFanApproximationGauge k (trialOffDiagonalBlock V M R) ≤
      kyFanApproximationGauge k R := by
    rw [trialOffDiagonalBlock_eq]
    refine (kyFanApproximationGauge_comp_le k Vᗮ.starProjection R
      V.subtypeL.adjoint).trans ?_
    have hQ : ‖(Vᗮ.starProjection : H →L[ℂ] H)‖ ≤ 1 := Submodule.starProjection_norm_le _
    have hI : ‖(V.subtypeL.adjoint : H →L[ℂ] V)‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact opNorm_le_one_of_isometry (fun _ => rfl)
    have hnn : 0 ≤ kyFanApproximationGauge k R := kyFanApproximationGauge_nonneg k R
    calc ‖(Vᗮ.starProjection : H →L[ℂ] H)‖ * kyFanApproximationGauge k R *
          ‖(V.subtypeL.adjoint : H →L[ℂ] V)‖
        ≤ 1 * kyFanApproximationGauge k R * 1 := by gcongr
      _ = kyFanApproximationGauge k R := by ring
  calc δ * kyFanApproximationGauge k
        (sinTwoThetaIdealBlock (selfAdjointSpectralSubspace A hA B hB) V)
      ≤ kyFanApproximationGauge k
          ((selfAdjointSpectralSubspace A hA B hB).starProjection ∘L
            ((-2 : ℂ) • trialOffDiagonalPart V M R) ∘L
            ((selfAdjointSpectralSubspace A hA B hB)ᗮ.map
              (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) := hraw.2
    _ = kyFanApproximationGauge k
          (((selfAdjointSpectralSubspace A hA B hB)ᗮ.map
              (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection ∘L
            ((-2 : ℂ) • trialOffDiagonalPart V M R) ∘L
            (selfAdjointSpectralSubspace A hA B hB).starProjection) := hflip
    _ ≤ 2 * kyFanApproximationGauge k (trialOffDiagonalBlock V M R) := hdouble
    _ ≤ 2 * kyFanApproximationGauge k R := by gcongr

/-- **Davis--Kahan 1970, the directed half of the `sin 2Θ` theorem for an
unbounded self-adjoint operator, at every source unitarily invariant norm.**

This is the printed Section 2 directed conclusion at the unbounded scope the
source claims for it:

`δ N(sin 2Θ₀) ≤ 2 N(R)`,  `R = A E₀ - E₀ A₀`,

for every `PaperUnitaryInvariantNorm`, with the printed spectral separation, the
printed residual, the printed factor two, and no hypothesis beyond the printed
ones: `A` self-adjoint and possibly unbounded, the trial subspace inside its
domain, and the residual bounded — which is exactly the source's own
requirement for a useful unbounded conclusion.

The reflected system is built internally from the trial data; no reflection
residual appears in the statement. -/
theorem sinTwoTheta_unbounded_directedResidual_paperUINorm
    (N : PaperUnitaryInvariantNorm)
    (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hVdom : ∀ v : V, (v : H) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : H), hVdom v⟩ = R v + ((M v : V) : H))
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock (selfAdjointSpectralSubspace A hA B hB) V) ∧
      δ * N.gauge
          (sinTwoThetaIdealBlock (selfAdjointSpectralSubspace A hA B hB) V) ≤
        2 * N.gauge R := by
  let R0 : H →L[ℂ] H := R ∘L V.subtypeL.adjoint
  have hsameR : SameApproximationSingularSequence R0 R :=
    sameApproximationSingularValues_extendDomainByZero V R
  have htransport := hsameR.paperMem_iff_and_gauge_eq N
  have hMem0 : N.Mem R0 := htransport.1.mpr hRmem
  have hgauge : N.gauge R0 = N.gauge R := htransport.2
  have htwo : ‖((2 : ℝ) : ℂ)‖ = 2 := by norm_num
  have hscaled : ∀ k : ℕ,
      δ * kyFanApproximationGauge k
          (sinTwoThetaIdealBlock (selfAdjointSpectralSubspace A hA B hB) V) ≤
        kyFanApproximationGauge k (((2 : ℝ) : ℂ) • R0) := by
    intro k
    rw [kyFanApproximationGauge_smul, htwo, hsameR.kyFanApproximationGauge_eq k]
    exact sinTwoTheta_unbounded_directedResidual_all_kyFan hA B hB hVdom hres
      hβα hδ hBlow hBhigh hBcomplSpec k
  have hMem2 : N.Mem (((2 : ℝ) : ℂ) • R0) := by
    intro htop
    rw [N.extendedGauge_smul, htwo] at htop
    rcases ENNReal.mul_eq_top.mp htop with ⟨_, h⟩ | ⟨h, _⟩
    · exact hMem0 h
    · exact absurd h (by simp)
  obtain ⟨hmem, hle⟩ := N.mul_gauge_le_of_all_mul_kyFan_le hδ hMem2 hscaled
  refine ⟨hmem, ?_⟩
  rw [N.gauge_smul _ hMem0, htwo, hgauge] at hle
  exact hle

end MainEstimate

end

end DavisKahan1970
end TauCeti
