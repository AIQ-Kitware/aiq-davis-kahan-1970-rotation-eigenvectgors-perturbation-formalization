/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.InfiniteDimensional.SinTheta.RestrictionCompat
import DavisKahan.InfiniteDimensional.SinTheta.SpectralBridge
import DavisKahan.SpectralTheory.Complexification.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import ForTauCeti.Analysis.InnerProductSpace.Polar.GramContraction
import DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Infinite-dimensional `sin Θ` theorems

Literature writeup: local TeX, Sections 12--13.  Both residual and perturbation
forms are represented, including general separated spectra and ideal-norm
versions.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace
open DavisKahan

set_option maxHeartbeats 1000000

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- A submodule with an orthogonal projection is closed in the complete
ambient space, hence complete: it is the equalizer of the projection and the
identity. -/
private theorem completeSpace_of_hasOrthogonalProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : CompleteSpace U := by
  have hclosed : IsClosed (U : Set E) := by
    have heq : (U : Set E) = {x : E | U.starProjection x = x} := by
      ext x
      exact ⟨fun hx => Submodule.starProjection_eq_self_iff.mpr hx,
        fun hx => Submodule.starProjection_eq_self_iff.mp hx⟩
    rw [heq]
    exact isClosed_eq U.starProjection.continuous continuous_id
  exact hclosed.completeSpace_coe

/-- The real spectrum of a bounded operator is bounded by its norm.

Used below in place of compactness of the spectrum: the cut construction needs
only `BddAbove` / `BddBelow`, and those follow from `‖λ‖ ≤ ‖T‖` for `λ` in the
spectrum without any of the topology. -/
private theorem abs_le_norm_of_mem_realSpectrum {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [CompleteSpace G] {T : G →L[𝕜] G} {r : ℝ}
    (hr : r ∈ TauCeti.DavisKahan.Foundation.realSpectrum T) :
    |r| ≤ ‖T‖ * ‖(1 : G →L[𝕜] G)‖ := by
  -- `norm_le_norm_of_mem` would give the cleaner `‖T‖`, but it wants
  -- `NormOneClass (G →L[𝕜] G)`, which fails when `G` is trivial.
  have h : ‖((r : 𝕜))‖ ≤ ‖T‖ * ‖(1 : G →L[𝕜] G)‖ := spectrum.norm_le_norm_mul_of_mem hr
  rwa [RCLike.norm_ofReal] at h

/-- **A common cut between two ordered spectra**, over a general `RCLike` field.

This is `exists_common_cut_of_orderedSeparation` (`Sylvester/OrderedSemigroup`)
with `ℂ` relaxed to `𝕜`.  Nothing in the argument was complex: the cut is
`sSup (realSpectrum B)` when that spectrum is nonempty and
`sInf (realSpectrum A) - d` when it is not, and the boundedness it needs is the
norm bound above rather than compactness of the spectrum. -/
private theorem exists_common_cut_of_orderedSeparation_rclike
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {d : ℝ}
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d) :
    ∃ c : ℝ,
      TauCeti.DavisKahan.Foundation.realSpectrum B ⊆ Set.Iic c ∧
      TauCeti.DavisKahan.Foundation.realSpectrum A ⊆ Set.Ici (c + d) := by
  obtain ⟨hInvB, hInvA, hord⟩ := hsep
  have hkey : ∀ b ∈ TauCeti.DavisKahan.Foundation.realSpectrum B,
      ∀ a ∈ TauCeti.DavisKahan.Foundation.realSpectrum A, b + d ≤ a := by
    intro b hb a ha
    refine hord b ?_ a ?_
    · rw [restrictedSpectrum_top_eq_realSpectrum_general]; exact hb
    · rw [restrictedSpectrum_top_eq_realSpectrum_general]; exact ha
  rcases (TauCeti.DavisKahan.Foundation.realSpectrum B).eq_empty_or_nonempty
    with hB0 | hBne
  · rcases (TauCeti.DavisKahan.Foundation.realSpectrum A).eq_empty_or_nonempty
      with hA0 | hAne
    · exact ⟨0, by simp [hB0], by simp [hA0]⟩
    · refine ⟨sInf (TauCeti.DavisKahan.Foundation.realSpectrum A) - d,
        by simp [hB0], fun a ha => ?_⟩
      have hbdd : BddBelow (TauCeti.DavisKahan.Foundation.realSpectrum A) :=
        ⟨-(‖A‖ * ‖(1 : F →L[𝕜] F)‖), fun r hr =>
          neg_le_of_abs_le (abs_le_norm_of_mem_realSpectrum hr)⟩
      have := csInf_le hbdd ha
      simp only [Set.mem_Ici]
      linarith
  · refine ⟨sSup (TauCeti.DavisKahan.Foundation.realSpectrum B),
      fun b hb => ?_, fun a ha => ?_⟩
    · exact le_csSup ⟨‖B‖ * ‖(1 : E →L[𝕜] E)‖, fun r hr =>
        le_of_abs_le (abs_le_norm_of_mem_realSpectrum hr)⟩ hb
    · have hsup : sSup (TauCeti.DavisKahan.Foundation.realSpectrum B) ≤ a - d :=
        csSup_le hBne fun b hb => by linarith [hkey b hb a ha]
      simp only [Set.mem_Ici]
      linarith

/-- **The constant-one ordered Sylvester estimate over a general `RCLike`
field.**

This was a leaf obligation until 2026-07-30, on the stated grounds that the `ℂ`
case is `norm_sylvester_le_of_orderedSeparation` and "the general case is its
complexification transport".  **No transport is needed and none is done here.**
`ExactSinTheta.sylvester_mem_and_gauge_le_of_intervalExteriorGap` is already
proved over general `RCLike`, for every rectangular ideal family, with constant
one; `sinTheta_perturbation` below instantiates it at `operatorNormFamily` in
exactly the same way.

The only real step is the shape change.  Ordered separation says one spectrum
sits below the other, which gives a *cut*; the bridge wants an
*interval/exterior* pair.  Putting `B` in `Icc β c` for the cut `c` and any
`β` below both `-‖B‖` and `c` leaves `A` in the exterior `{x | c + d ≤ x}`, which
is what ordered separation already gives. -/
theorem norm_sylvester_le_of_orderedSeparation_rclike
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (hEq : sylvesterOperator A B X = C) :
    d * ‖X‖ ≤ ‖C‖ := by
  obtain ⟨c, hBc, hAc⟩ := exists_common_cut_of_orderedSeparation_rclike hsep
  set β : ℝ := min (-(‖B‖ * ‖(1 : E →L[𝕜] E)‖) - 1) (c - 1) with hβ
  have hβc : β ≤ c := (min_le_right _ _).trans (by linarith)
  have hgap : ExactSinTheta.IntervalExteriorGap A B β c d := by
    refine Or.inr ⟨fun r hr => ?_, fun r hr => ?_⟩
    · rw [boundedRealSpectrum_eq_realSpectrum] at hr
      have hup : r ≤ c := hBc hr
      have hlow : -(‖B‖ * ‖(1 : E →L[𝕜] E)‖) ≤ r :=
        neg_le_of_abs_le (abs_le_norm_of_mem_realSpectrum hr)
      exact ⟨le_trans (min_le_left _ _) (by linarith), hup⟩
    · rw [boundedRealSpectrum_eq_realSpectrum] at hr
      exact Or.inr (hAc hr)
  have hsolve := ExactSinTheta.sylvester_mem_and_gauge_le_of_intervalExteriorGap
    (TauCeti.operatorNormFamily.{u, v} 𝕜) hA hB hβc hd hgap hEq
    (TauCeti.SymmetricOperatorIdealFamily.mem_operatorNormFamily _)
  exact hsolve.2

open TauCeti.RealComplexification in
open scoped TauCeti.DavisKahan.Foundation.RealScalarRestriction in
/-- **The universal `π/2` Sylvester estimate over a general `RCLike` field.**

Proved by restricting scalars to `ℝ` and complexifying, which is the route the
leaf obligation this replaced described as "its complexification transport". -/
theorem norm_sylvester_le_of_generalSeparation_rclike
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : sylvesterOperator A B X = C) :
    d * ‖X‖ ≤ (Real.pi / 2) * ‖C‖ := by
  have hEqr : (A.restrictScalars ℝ) ∘L (X.restrictScalars ℝ)
      - (X.restrictScalars ℝ) ∘L (B.restrictScalars ℝ) = C.restrictScalars ℝ := by
    ext x
    have := congrArg (fun T : E →L[𝕜] F => T x) hEq
    simpa [sylvesterOperator] using this
  have hEqc : sylvesterOperator (complexify (A.restrictScalars ℝ))
      (complexify (B.restrictScalars ℝ)) (complexify (X.restrictScalars ℝ)) =
      complexify (C.restrictScalars ℝ) := by
    show complexify (A.restrictScalars ℝ) ∘L complexify (X.restrictScalars ℝ)
      - complexify (X.restrictScalars ℝ) ∘L complexify (B.restrictScalars ℝ) = _
    rw [← complexify_comp, ← complexify_comp, ← complexify_sub, hEqr]
  -- self-adjointness survives both steps: restricting scalars takes the real part
  -- of the form, and `complexify_adjoint` moves the adjoint through the second.
  have hsymr : ∀ (G : Type v) (_ : NormedAddCommGroup G) (_ : InnerProductSpace 𝕜 G),
      True := fun _ _ _ => trivial
  have hAr : (A.restrictScalars ℝ).IsSymmetric := fun x y => by
    simpa [real_inner_eq_re_inner (𝕜 := 𝕜)] using congrArg RCLike.re (hA x y)
  have hBr : (B.restrictScalars ℝ).IsSymmetric := fun x y => by
    simpa [real_inner_eq_re_inner (𝕜 := 𝕜)] using congrArg RCLike.re (hB x y)
  have hAc : IsSelfAdjointOperator (complexify (A.restrictScalars ℝ)) := by
    have hsa : IsSelfAdjoint (complexify (A.restrictScalars ℝ)) := by
      show ContinuousLinearMap.adjoint _ = _
      rw [← TauCeti.RealComplexification.complexify_adjoint]
      exact congrArg complexify
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 hAr)
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa
  have hBc : IsSelfAdjointOperator (complexify (B.restrictScalars ℝ)) := by
    have hsa : IsSelfAdjoint (complexify (B.restrictScalars ℝ)) := by
      show ContinuousLinearMap.adjoint _ = _
      rw [← TauCeti.RealComplexification.complexify_adjoint]
      exact congrArg complexify
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 hBr)
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa
  -- the separation survives both steps: `realSpectrum` is what a `⊤`-separation
  -- hypothesis is about, it is the `ℝ`-spectrum after restricting scalars, and it
  -- is unchanged by complexification.
  have hreal : ∀ (G : Type v) [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
      [CompleteSpace G] (T : G →L[𝕜] G),
      Foundation.realSpectrum (complexify (T.restrictScalars ℝ)) =
        Foundation.realSpectrum T := by
    intro G _ _ _ T
    rw [TauCeti.DavisKahan.Foundation.RealComplexification.realSpectrum_complexify (T.restrictScalars ℝ),
      Foundation.realSpectrum_eq_spectrum_restrictScalars T]
    rfl
  have hsepc : SpectraSeparated (complexify (A.restrictScalars ℝ)) ⊤
      (complexify (B.restrictScalars ℝ)) ⊤ d := by
    show Foundation.SpectraSeparated _ ⊤ _ ⊤ d
    rw [Foundation.spectraSeparated_top_iff]
    intro a ha b hb
    rw [hreal F A] at ha
    rw [hreal E B] at hb
    exact (Foundation.spectraSeparated_top_iff A B d).1 hsep a ha b hb
  have hmain := norm_sylvester_le_of_generalSeparation hAc hBc hd hsepc hEqc
  rwa [TauCeti.RealComplexification.norm_complexify,
    TauCeti.RealComplexification.norm_complexify,
    ContinuousLinearMap.norm_restrictScalars,
    ContinuousLinearMap.norm_restrictScalars] at hmain

/-- Residual `sin Θ` theorem for an isometric trial map.

Lean proof route for a weaker agent:

1. Set `Y=(I-P_U)X` and derive `A|_{Uᗮ} Y - Y M = (I-P_U) residual A X M`.
2. Apply the ordered constant-one Sylvester theorem using `hsep`.
3. Bound the projected residual by the full residual norm.
4. Identify `Y` with `sinThetaEmbedding U X`.


Ext-agent signature audit (GPT 5.6 High): Correct as a directed residual theorem. The
isometric embedding is needed for the subspace interpretation, although the raw
Sylvester norm estimate itself uses only boundedness.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_residual
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U)
    {X : F →L[𝕜] E} (_hX : IsometricEmbedding X)
    {M : F →L[𝕜] F} (hM : IsSelfAdjointOperator M)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated M ⊤ A Uᗮ d) :
    d * ‖sinThetaEmbedding U X‖ ≤ ‖residual A X M‖ := by
  let Y : F →L[𝕜] Uᗮ :=
    codRestrictTo (complementaryProjection U ∘L X) Uᗮ
      (fun x => Uᗮ.starProjection_apply_mem _)
  let C : F →L[𝕜] Uᗮ :=
    codRestrictTo (complementaryProjection U ∘L residual A X M) Uᗮ
      (fun x => Uᗮ.starProjection_apply_mem _)
  have hEq : sylvesterOperator (restrictToOrthogonal A U hU) M Y = C :=
    directedResidual_sylvesterEquation hA hU
  have hsep' : OrderedSpectraSeparated M ⊤
      (restrictToOrthogonal A U hU) ⊤ d := by
    obtain ⟨hM, hAperp, hord⟩ := hsep
    refine ⟨hM, fun x _ => Submodule.mem_top, ?_⟩
    intro a ha b hb
    refine hord a ha b ?_
    have hb' : b ∈ TauCeti.DavisKahan.Foundation.realSpectrum
        (restrictToOrthogonal A U hU) :=
      (restrictedSpectrum_top_eq_realSpectrum_general
        (restrictToOrthogonal A U hU)) ▸ hb
    have h2 : TauCeti.DavisKahan.Foundation.restrictedSpectrum
          A Uᗮ =
        TauCeti.DavisKahan.Foundation.realSpectrum
          (restrictToOrthogonal A U hU) :=
      restrictedSpectrum_orthogonal_eq A U hU
    rw [h2]
    exact hb'
  have hbound := norm_sylvester_le_of_orderedSeparation_rclike
    (hA.restrictToOrthogonal U hU) hM hd hsep' hEq
  have hY : ‖Y‖ = ‖sinThetaEmbedding U X‖ :=
    norm_codRestrictTo_eq _ _ _
  have hC : ‖C‖ ≤ ‖residual A X M‖ := by
    calc
      ‖C‖ = ‖complementaryProjection U ∘L residual A X M‖ :=
        norm_codRestrictTo_eq _ _ _
      _ ≤ ‖residual A X M‖ :=
        projection_comp_opNorm_le Uᗮ _
  simpa [hY] using hbound.trans hC

/-- One-sided perturbation theorem for spectral subspaces. 

Lean proof route for a weaker agent:

1. Derive the off-diagonal Sylvester equation for `X=(I-P_V)P_U`.
2. Use the interval/exterior decomposition to apply the constant-one ordered Sylvester estimate to the lower and upper pieces.
3. Bound the right-hand residual by `‖B-A‖`.
4. Rewrite `‖X‖` as the directed gap.


Ext-agent signature audit (GPT 5.6 High): Correct as a one-sided directed-angle theorem.
One mixed interval/exterior gap is intentionally insufficient for a full
projector-difference conclusion.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_perturbation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right d : ℝ} (hlr : left ≤ right) (hd : 0 < d)
    (hgap : IntervalExteriorSeparated A U B Vᗮ left right d) :
    d * directedGap U V ≤ ‖B - A‖ := by
  let X : U →L[𝕜] Vᗮ :=
    codRestrictTo (complementaryProjection V ∘L U.subtypeL) Vᗮ
      (fun x => Vᗮ.starProjection_apply_mem _)
  let C : U →L[𝕜] Vᗮ :=
    codRestrictTo
      (complementaryProjection V ∘L (B - A) ∘L U.subtypeL) Vᗮ
      (fun x => Vᗮ.starProjection_apply_mem _)
  have hEq := directedPerturbation_sylvesterEquation hA hB hU hV
  have hgap' : ExactSinTheta.IntervalExteriorGap
      (restrictToOrthogonal B V hV) (restrictToReducingSubspace A U hU)
      left right d := by
    exact intervalExteriorSeparated_restrictions hA hB hU hV hgap
  have : CompleteSpace U := completeSpace_of_hasOrthogonalProjection U
  have : CompleteSpace Vᗮ := completeSpace_of_hasOrthogonalProjection Vᗮ
  have hsolve := ExactSinTheta.sylvester_mem_and_gauge_le_of_intervalExteriorGap
    (TauCeti.operatorNormFamily.{u, v} 𝕜)
    (hB.restrictToOrthogonal V hV) (hA.restrictToReducingSubspace U hU)
    hlr hd hgap' hEq
    (TauCeti.SymmetricOperatorIdealFamily.mem_operatorNormFamily _)
  have hC : ‖C‖ ≤ ‖B - A‖ :=
    restricted_projection_sandwich_norm_le _ _ _
  have h2 : d * ‖codRestrictTo
      (Vᗮ.starProjection ∘L U.subtypeL) Vᗮ
      (fun x => Vᗮ.starProjection_apply_mem _)‖ ≤ ‖B - A‖ :=
    hsolve.2.trans hC
  rw [directedGap_eq_restrictedBlock_norm U V] at h2
  exact h2

/-- **The dimension-free operator-norm Davis--Kahan `sin Θ` theorem, coercivity
form.**  For self-adjoint `A, B` on an arbitrary Hilbert space, `U` reducing `A`
with quadratic form `≥ (c+g)‖·‖²` on `U`, and `V` reducing `B` with quadratic
form `≤ c‖·‖²` on `V`,

`‖P_V P_U‖ ≤ ‖B − A‖ / g`.

This is the genuine infinite-dimensional `sin Θ` bound: the analytic core is the
integral-free Sylvester estimate `norm_sylvester_le_of_coercive` (no spectral
measure, no dimension or completeness hypothesis on the *bound* itself), and the
block construction `A ∘L P + (c+g)(1−P)`, `B ∘L Q + c(1−Q)` uses only the
dimension-free projection commutation `projection_apply_comm_of_isInvariant`.  The
spectrum-predicate forms (`sinTheta_perturbation`, `IntervalExteriorSeparated`)
follow from this once a bounded spectral theorem converts spectral separation to
these coercivity bounds. -/
theorem sinTheta_directed_coercive
    {A B : E →L[𝕜] E} (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {c g : ℝ} (hg : 0 < g)
    (hUc : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hVc : ∀ x ∈ V, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    ‖(projection V ∘L projection U : E →L[𝕜] E)‖ ≤ ‖B - A‖ / g := by
  set P := projection U with hP
  set Q := projection V with hQ
  set A' : E →L[𝕜] E := A ∘L P + ((c + g : ℝ) : 𝕜) • (1 - P) with hA'
  set B' : E →L[𝕜] E := B ∘L Q + ((c : ℝ) : 𝕜) • (1 - Q) with hB'
  set X : E →L[𝕜] E := P ∘L Q with hX
  set Y : E →L[𝕜] E := P ∘L (A - B) ∘L Q with hY
  have hPsa : IsSelfAdjoint P := isSelfAdjoint_starProjection U
  have hQsa : IsSelfAdjoint Q := isSelfAdjoint_starProjection V
  have hAsa : IsSelfAdjoint A := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hA
  have hBsa : IsSelfAdjoint B := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  have hcgsa : IsSelfAdjoint ((c + g : ℝ) : 𝕜) := isSelfAdjoint_iff.mpr (RCLike.conj_ofReal _)
  have hcsa : IsSelfAdjoint ((c : ℝ) : 𝕜) := isSelfAdjoint_iff.mpr (RCLike.conj_ofReal _)
  have hone : IsSelfAdjoint (1 : E →L[𝕜] E) := IsSelfAdjoint.one _
  -- commutations
  have hcommA : A ∘L P = P ∘L A := by
    ext x; simp only [ContinuousLinearMap.comp_apply]
    exact (projection_apply_comm_of_isInvariant A U hU x).symm
  have hcommB : B ∘L Q = Q ∘L B := by
    ext x; simp only [ContinuousLinearMap.comp_apply]
    exact (projection_apply_comm_of_isInvariant B V hV x).symm
  -- self-adjointness of A', B'
  have hA'sa : IsSelfAdjoint A' := by
    have h1 : IsSelfAdjoint (A ∘L P) := (IsSelfAdjoint.commute_iff hAsa hPsa).mp hcommA
    have h2 : IsSelfAdjoint (((c + g : ℝ) : 𝕜) • ((1 : E →L[𝕜] E) - P)) := by
      rw [isSelfAdjoint_iff, star_smul, hcgsa.star_eq, (hone.sub hPsa).star_eq]
    exact hA' ▸ h1.add h2
  have hB'sa : IsSelfAdjoint B' := by
    have h1 : IsSelfAdjoint (B ∘L Q) := (IsSelfAdjoint.commute_iff hBsa hQsa).mp hcommB
    have h2 : IsSelfAdjoint (((c : ℝ) : 𝕜) • ((1 : E →L[𝕜] E) - Q)) := by
      rw [isSelfAdjoint_iff, star_smul, hcsa.star_eq, (hone.sub hQsa).star_eq]
    exact hB' ▸ h1.add h2
  have hA'sym : IsSelfAdjointOperator A' := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hA'sa
  have hB'sym : IsSelfAdjointOperator B' := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hB'sa
  -- coercivity of A'
  have hA'c : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A' x, x⟫_𝕜 := by
    intro x
    have hpx : P x ∈ U := U.starProjection_apply_mem x
    have hrest : x - P x ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
    have hAxeq : A' x = A (P x) + ((c + g : ℝ) : 𝕜) • (x - P x) := by
      simp only [hA', add_apply, ContinuousLinearMap.comp_apply,
        smul_apply, sub_apply, one_apply_eq_self]
    have hre : RCLike.re ⟪A' x, x⟫_𝕜
        = RCLike.re ⟪A (P x), x⟫_𝕜 + (c + g) * RCLike.re ⟪x - P x, x⟫_𝕜 := by
      rw [hAxeq, inner_add_left, inner_smul_left, RCLike.conj_ofReal, map_add, RCLike.re_ofReal_mul]
    have h1 : RCLike.re ⟪A (P x), x⟫_𝕜 = RCLike.re ⟪A (P x), P x⟫_𝕜 := by
      have hz : ⟪A (P x), x - P x⟫_𝕜 = 0 :=
        Submodule.inner_right_of_mem_orthogonal (hU.1 _ hpx) hrest
      have : ⟪A (P x), x⟫_𝕜 = ⟪A (P x), P x⟫_𝕜 + ⟪A (P x), x - P x⟫_𝕜 := by
        rw [← inner_add_right]; congr 1; abel
      rw [this, hz, add_zero]
    have h2 : RCLike.re ⟪x - P x, x⟫_𝕜 = ‖x - P x‖ ^ 2 := by
      have hz : ⟪x - P x, P x⟫_𝕜 = 0 := Submodule.inner_left_of_mem_orthogonal hpx hrest
      have : ⟪x - P x, x⟫_𝕜 = ⟪x - P x, x - P x⟫_𝕜 := by
        have h' : ⟪x - P x, x⟫_𝕜 = ⟪x - P x, P x⟫_𝕜 + ⟪x - P x, x - P x⟫_𝕜 := by
          rw [← inner_add_right]; congr 1; abel
        rw [h', hz, zero_add]
      rw [this, inner_self_eq_norm_sq]
    have hpyth : ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 := by
      have h0 : RCLike.re ⟪P x, x - P x⟫_𝕜 = 0 := by
        rw [Submodule.inner_right_of_mem_orthogonal hpx hrest]; simp
      have hns := norm_add_sq (𝕜 := 𝕜) (P x) (x - P x)
      rw [show P x + (x - P x) = x by abel, h0] at hns
      linarith
    rw [hre, h1, h2, hpyth]
    nlinarith [hUc (P x) hpx]
  -- upper bound for B'
  have hB'c : ∀ x, RCLike.re ⟪B' x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
    intro x
    have hqx : Q x ∈ V := V.starProjection_apply_mem x
    have hrest : x - Q x ∈ Vᗮ := V.sub_starProjection_mem_orthogonal x
    have hBxeq : B' x = B (Q x) + ((c : ℝ) : 𝕜) • (x - Q x) := by
      simp only [hB', add_apply, ContinuousLinearMap.comp_apply,
        smul_apply, sub_apply, one_apply_eq_self]
    have hre : RCLike.re ⟪B' x, x⟫_𝕜
        = RCLike.re ⟪B (Q x), x⟫_𝕜 + c * RCLike.re ⟪x - Q x, x⟫_𝕜 := by
      rw [hBxeq, inner_add_left, inner_smul_left, RCLike.conj_ofReal, map_add, RCLike.re_ofReal_mul]
    have h1 : RCLike.re ⟪B (Q x), x⟫_𝕜 = RCLike.re ⟪B (Q x), Q x⟫_𝕜 := by
      have hz : ⟪B (Q x), x - Q x⟫_𝕜 = 0 :=
        Submodule.inner_right_of_mem_orthogonal (hV.1 _ hqx) hrest
      have : ⟪B (Q x), x⟫_𝕜 = ⟪B (Q x), Q x⟫_𝕜 + ⟪B (Q x), x - Q x⟫_𝕜 := by
        rw [← inner_add_right]; congr 1; abel
      rw [this, hz, add_zero]
    have h2 : RCLike.re ⟪x - Q x, x⟫_𝕜 = ‖x - Q x‖ ^ 2 := by
      have hz : ⟪x - Q x, Q x⟫_𝕜 = 0 := Submodule.inner_left_of_mem_orthogonal hqx hrest
      have : ⟪x - Q x, x⟫_𝕜 = ⟪x - Q x, x - Q x⟫_𝕜 := by
        have h' : ⟪x - Q x, x⟫_𝕜 = ⟪x - Q x, Q x⟫_𝕜 + ⟪x - Q x, x - Q x⟫_𝕜 := by
          rw [← inner_add_right]; congr 1; abel
        rw [h', hz, zero_add]
      rw [this, inner_self_eq_norm_sq]
    have hpyth : ‖x‖ ^ 2 = ‖Q x‖ ^ 2 + ‖x - Q x‖ ^ 2 := by
      have h0 : RCLike.re ⟪Q x, x - Q x⟫_𝕜 = 0 := by
        rw [Submodule.inner_right_of_mem_orthogonal hqx hrest]; simp
      have hns := norm_add_sq (𝕜 := 𝕜) (Q x) (x - Q x)
      rw [show Q x + (x - Q x) = x by abel, h0] at hns
      linarith
    rw [hre, h1, h2, hpyth]
    nlinarith [hVc (Q x) hqx]
  -- Sylvester relation A' X - X B' = Y
  have hsylv : sylvesterOperator A' B' X = Y := by
    show A' ∘L X - X ∘L B' = Y
    ext x
    have hQxV : Q x ∈ V := V.starProjection_apply_mem x
    have hPP : P (P (Q x)) = P (Q x) :=
      U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem (Q x))
    have hQrest : Q (x - Q x) = 0 := by
      have hQQ : Q (Q x) = Q x := V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
      rw [map_sub, hQQ, sub_self]
    have hQBQ : Q (B (Q x)) = B (Q x) := V.starProjection_eq_self_iff.mpr (hV.1 _ hQxV)
    have hAP : A (P (Q x)) = P (A (Q x)) :=
      (projection_apply_comm_of_isInvariant A U hU (Q x)).symm
    have hAX : (A' ∘L X) x = A (P (Q x)) := by
      simp only [ContinuousLinearMap.comp_apply, hX, hA', add_apply,
        smul_apply, sub_apply,
        one_apply_eq_self, hPP, sub_self, smul_zero, add_zero]
    have hXB : (X ∘L B') x = P (B (Q x)) := by
      simp only [ContinuousLinearMap.comp_apply, hX, hB', add_apply,
        smul_apply, sub_apply,
        one_apply_eq_self, map_add, map_smul, hQBQ, hQrest, map_zero, smul_zero, add_zero]
    have hYx : Y x = P (A (Q x)) - P (B (Q x)) := by
      simp only [hY, ContinuousLinearMap.comp_apply, sub_apply, map_sub]
    rw [sub_apply, hAX, hXB, hYx, hAP]
  -- norm bound
  have hYnorm : ‖Y‖ ≤ ‖B - A‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have hc : ‖P ((A - B) (Q x))‖ ≤ ‖(A - B) (Q x)‖ := by
      rw [hP]; exact U.norm_starProjection_apply_le _
    calc ‖Y x‖ = ‖P ((A - B) (Q x))‖ := by simp only [hY, ContinuousLinearMap.comp_apply]
      _ ≤ ‖(A - B) (Q x)‖ := hc
      _ = ‖(B - A) (Q x)‖ := by rw [show A - B = -(B - A) by abel, neg_apply, norm_neg]
      _ ≤ ‖B - A‖ * ‖Q x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖B - A‖ * ‖x‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [hQ]; exact V.norm_starProjection_apply_le x
  have hXbound : ‖X‖ ≤ ‖B - A‖ / g :=
    (norm_sylvester_le_of_coercive hA'sym hB'sym hg hA'c hB'c hsylv).trans (by gcongr)
  have hstar : star (Q ∘L P : E →L[𝕜] E) = P ∘L Q := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      hPsa.star_eq, hQsa.star_eq]
  have : ‖(Q ∘L P : E →L[𝕜] E)‖ = ‖X‖ := by rw [hX, ← hstar]; exact (norm_star _).symm
  calc ‖(projection V ∘L projection U : E →L[𝕜] E)‖ = ‖(Q ∘L P : E →L[𝕜] E)‖ := by rw [hP, hQ]
    _ = ‖X‖ := this
    _ ≤ ‖B - A‖ / g := hXbound

/-- Symmetric projector-difference form requiring both mixed gaps. 

Lean proof route for a weaker agent:

1. Apply `sinTheta_perturbation` to `(U,V)` and again to `(V,U)` using the reverse gap.
2. Use the two-projection norm identity that the full gap is the maximum of the two directed gaps.
3. Combine the two inequalities with `max_le` and simplify the perturbation sign.


Ext-agent signature audit (GPT 5.6 High): Correct with both mixed gaps. The full
projection gap is the maximum of the two directed gaps in operator norm.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_symmetric
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right left' right' d : ℝ}
    (hlr : left ≤ right) (hlr' : left' ≤ right') (hd : 0 < d)
    (hUV : IntervalExteriorSeparated A U B Vᗮ left right d)
    (hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d) :
    d * subspaceGap U V ≤ ‖B - A‖ := by
  have h1 : d * directedGap U V ≤ ‖B - A‖ :=
    sinTheta_perturbation hA hB hU hV hlr hd hUV
  have h2 : d * directedGap V U ≤ ‖A - B‖ :=
    sinTheta_perturbation hB hA hV hU hlr' hd hVU
  rw [show A - B = -(B - A) by abel, norm_neg] at h2
  have hmax : subspaceGap U V = max (directedGap U V) (directedGap V U) := by
    show ‖U.starProjection - V.starProjection‖ =
      max ‖Vᗮ.starProjection ∘L U.starProjection‖
        ‖Uᗮ.starProjection ∘L V.starProjection‖
    rw [Submodule.norm_starProjection_sub_eq_max,
      Submodule.starProjection_orthogonal' V,
      Submodule.starProjection_orthogonal' U]
  rw [hmax, mul_max_of_nonneg _ _ hd.le]
  exact max_le h1 h2

/-- General separated-spectrum form with the optimal universal `π / 2`
Sylvester constant. 

Lean proof route for a weaker agent:

1. Derive the Sylvester equation for `(I-P_V)P_U` from the two reducing relations.
2. Apply `norm_sylvester_le_of_generalSeparation` with the hybrid spectral gap.
3. Bound the residual block by `‖B-A‖` using projection contractions.
4. Rewrite the block norm as `directedGap U V`.


Ext-agent signature audit (GPT 5.6 High): Correct as a directed theorem with the `π/2`
constant. The hybrid gap matches the cross block `P_{Vᗮ}P_U`.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_generalSeparation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d) (hgap : HybridGap A B U V d) :
    d * directedGap U V ≤ (Real.pi / 2) * ‖B - A‖ := by
  let X : U →L[𝕜] Vᗮ :=
    codRestrictTo (complementaryProjection V ∘L U.subtypeL) Vᗮ
      (fun x => Vᗮ.starProjection_apply_mem _)
  let C : U →L[𝕜] Vᗮ :=
    codRestrictTo
      (complementaryProjection V ∘L (B - A) ∘L U.subtypeL) Vᗮ
      (fun x => Vᗮ.starProjection_apply_mem _)
  have hEq := directedPerturbation_sylvesterEquation hA hB hU hV
  have hsep : SpectraSeparated (restrictToOrthogonal B V hV) ⊤
      (restrictToReducingSubspace A U hU) ⊤ d :=
    hybridGap_restrictions hA hB hU hV hgap
  have : CompleteSpace U := completeSpace_of_hasOrthogonalProjection U
  have : CompleteSpace Vᗮ := completeSpace_of_hasOrthogonalProjection Vᗮ
  have hsol := norm_sylvester_le_of_generalSeparation_rclike
    (hB.restrictToOrthogonal V hV) (hA.restrictToReducingSubspace U hU) hd hsep hEq
  have hC : ‖C‖ ≤ ‖B - A‖ :=
    restricted_projection_sandwich_norm_le _ _ _
  have h2 : d * ‖codRestrictTo
      (Vᗮ.starProjection ∘L U.subtypeL) Vᗮ
      (fun x => Vᗮ.starProjection_apply_mem _)‖ ≤
      (Real.pi / 2) * ‖B - A‖ :=
    hsol.trans (mul_le_mul_of_nonneg_left hC (by positivity))
  rw [directedGap_eq_restrictedBlock_norm U V] at h2
  exact h2

/-! ## Bounded measurable spectral subspaces

Actually constructing the measurable spectral subspace of a bounded
self-adjoint operator over a general `RCLike` field requires the bounded Borel
functional calculus.  Over `ℂ` that calculus exists in this development and is
*not* experimental: it is `TauCeti.BorelCalculus.boundedPVM`, with the spectral
subspace itself at
`DavisKahan/SpectralTheory/BoundedSelfAdjointSpectralProjection.lean` as
`boundedSelfAdjointSpectralSubspace`.  The general case is its complexification
transport, which does not exist yet.

That `ℂ` construction cannot simply be reused here, because
`TauCeti.ProjValMeasure` fixes the scalar field **in its own binder** — it is
declared over `[InnerProductSpace ℂ H]` — while this section is over a general
`𝕜 : RCLike`.  Reusing it would mean either restricting this section to `ℂ` or
generalising `ProjValMeasure`, and neither is necessary.

So the `ℂ`-only ingredient is carried as a *hypothesis*, exactly as the operator
absolute value is in the `OperatorAbsoluteValue` section below, and for the
reason given there: an unproved `def` is an opaque term with no body, so no
theorem about it can be proved at all, whereas the definitions below unfold.
Relative to `BoundedBorelProjection` the three former leaf obligations are
ordinary theorems, and the `sin Θ` consequences are fully proved.
-/

section SpectralSubspace

/-- **Hypothesis class: the bounded Borel functional calculus of a self-adjoint
operator**, presented as the projection assignment it induces.

Only the two laws actually needed downstream are demanded — idempotence, which
makes the range a closed subspace with an orthogonal projection, and commutation
with the operator, which makes that subspace reducing.  Nothing here asserts
countable additivity or multiplicativity in `s`; a genuine projection-valued
measure supplies this and much more, so the hypothesis is weaker than the object
that discharges it.

At `𝕜 = ℂ` it is discharged by `TauCeti.BorelCalculus.boundedPVM`: `proj_idem`
is its `proj_idem` field, and `proj_comm` is the commutation of a spectral
projection with its own operator.  The instance is deliberately *not* declared
in this file, which would drag the whole Borel-calculus import chain into this
generic `RCLike` module; it lives in `BoundedBorelProjectionComplex.lean`. -/
class BoundedBorelProjection (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] where
  /-- The spectral projection of `A` over a Borel set `s`. -/
  proj : ∀ (A : E →L[𝕜] E), IsSelfAdjointOperator A →
    ∀ s : Set ℝ, MeasurableSet s → E →L[𝕜] E
  /-- Spectral projections are idempotent. -/
  proj_idem : ∀ (A : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s), IsIdempotentElem (proj A hA s hs)
  /-- Spectral projections commute with their operator. -/
  proj_comm : ∀ (A : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s),
    A ∘L proj A hA s hs = proj A hA s hs ∘L A

variable [BoundedBorelProjection 𝕜 E]

/-- The measurable spectral subspace of a bounded operator: the range of the
spectral projection of `s`.

Relative to the `BoundedBorelProjection` hypothesis this is a real definition
rather than a leaf obligation, so the results below unfold it. -/
noncomputable def spectralSubspace (A : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    Submodule 𝕜 E :=
  (BoundedBorelProjection.proj A hA s hs).range

omit [CompleteSpace E] in
/-- Unfolding lemma: the spectral subspace *is* the range of the spectral
projection.  Stated so that downstream rewrites do not have to unfold a `def`. -/
theorem spectralSubspace_eq_range (A : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    spectralSubspace A hA s hs = (BoundedBorelProjection.proj A hA s hs).range :=
  rfl

/-- The spectral subspace is closed, hence admits an orthogonal projection in
the complete ambient space.

This needs only idempotence: the range of a bounded idempotent is closed. -/
noncomputable instance spectralSubspace_hasOrthogonalProjection
    (A : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (spectralSubspace A hA s hs).HasOrthogonalProjection :=
  ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
    (BoundedBorelProjection.proj_idem A hA s hs)

/-- The measurable spectral projection: the orthogonal projection onto the
spectral subspace. -/
noncomputable def spectralProjection (A : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    E →L[𝕜] E :=
  (spectralSubspace A hA s hs).starProjection

omit [CompleteSpace E] in
/-- Spectral subspaces of a self-adjoint operator reduce it.

Only invariance has to be checked: `IsSymmetric.reduces_of_invariant` supplies
invariance of the orthogonal complement from symmetry of `A`.  Invariance is
immediate from commutation, since `A (P y) = P (A y)` is again in the range. -/
theorem isInvariant_spectralSubspace (A : E →L[𝕜] E)
    (hA : IsSelfAdjointOperator A) (s : Set ℝ) (hs : MeasurableSet s) :
    Reduces A (spectralSubspace A hA s hs) := by
  refine ContinuousLinearMap.IsSymmetric.reduces_of_invariant hA ?_
  rintro x ⟨y, rfl⟩
  refine ⟨A y, ?_⟩
  exact congrFun (congrArg DFunLike.coe
    (BoundedBorelProjection.proj_comm A hA s hs).symm) y

/-- The subspace projection of the spectral subspace is the spectral
projection. -/
theorem projection_spectralSubspace_eq (A : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    projection (spectralSubspace A hA s hs) = spectralProjection A hA s hs :=
  rfl

/-- Canonical spectral-projection form.

Lean proof route for a weaker agent:

1. Convert the four spectral-containment hypotheses into the two `IntervalExteriorSeparated` predicates.
2. Apply `sinTheta_symmetric` to the canonical spectral subspaces, using `isInvariant_spectralSubspace`.
3. Rewrite the subspace gap as the norm of the two spectral projections.


Ext-agent signature audit (GPT 5.6 High): Correct after the measurable-set hypotheses
were added. The four containments encode exactly the two mixed interval/exterior gaps.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem spectralProjection_sinTheta
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    {left right left' right' d : ℝ}
    (hlr : left ≤ right) (hlr' : left' ≤ right') (hd : 0 < d)
    (hAs : SpectrumIn A (spectralSubspace A hA s hs) (Set.Icc left right))
    (hBt : SpectrumIn B (spectralSubspace B hB t ht)ᗮ
      {x | x ≤ left - d ∨ right + d ≤ x})
    (hBs : SpectrumIn B (spectralSubspace B hB t ht) (Set.Icc left' right'))
    (hAt : SpectrumIn A (spectralSubspace A hA s hs)ᗮ
      {x | x ≤ left' - d ∨ right' + d ≤ x}) :
    d * ‖spectralProjection A hA s hs - spectralProjection B hB t ht‖ ≤
      ‖B - A‖ := by
  let U := spectralSubspace A hA s hs
  let V := spectralSubspace B hB t ht
  have hredA := isInvariant_spectralSubspace A hA s hs
  have hredB := isInvariant_spectralSubspace B hB t ht
  have hUV : IntervalExteriorSeparated A U B Vᗮ left right d :=
    ⟨hAs, hBt⟩
  have hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d :=
    ⟨hBs, hAt⟩
  have h := sinTheta_symmetric hA hB hredA hredB hlr hlr' hd hUV hVU
  have hgapeq : subspaceGap U V =
      ‖spectralProjection A hA s hs - spectralProjection B hB t ht‖ := rfl
  calc d * ‖spectralProjection A hA s hs - spectralProjection B hB t ht‖
      = d * subspaceGap U V := by rw [hgapeq]
    _ ≤ ‖B - A‖ := h

end SpectralSubspace

/-! ## Ideal-valued form

The ideal-valued projector-difference estimate below is a genuinely missing
analytic ingredient (the gauge identity `‖|T|‖_I = ‖T‖_I` needs the polar
partial isometry) and stays a leaf obligation.

The operator absolute value is **not** missing, and the reason is worth
recording, because it was previously an escape and was sized as research.
Over `ℂ` it is `CFC.sqrt (star T * T)`; over a general `RCLike` field every
ingredient is already available except one typeclass:

* `CStarRing (E →L[𝕜] E)` is an unconditional instance
  (`Mathlib/Analysis/InnerProductSpace/Adjoint.lean`);
* `NonnegSpectrumClass ℝ (E →L[𝕜] E)` is an unconditional instance
  (`Mathlib/Analysis/InnerProductSpace/StarOrder.lean`);
* `StarOrderedRing (E →L[𝕜] E)` is *proved* for general `𝕜` there as
  `instStarOrderedRingRCLike`, taking `ContinuousFunctionalCalculus ℝ _
  IsSelfAdjoint` as its single argument;
* the operator itself is `CFC.abs`, already upstream in
  `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Abs.lean`.

Mathlib states the remaining gap explicitly: that continuous functional
calculus instance is known only for `𝕜 = ℂ`, which is exactly why
`instStarOrderedRingRCLike` is a lemma there rather than an instance.  So the
absolute value is carried here as a *hypothesis*, not as an escape.  This is
the difference between unproved and unprovable: an unproved `def` is an opaque
term with no body, so no theorem about it can be proved at all, whereas the
definition below unfolds and discharges automatically at `𝕜 = ℂ`.
-/

section OperatorAbsoluteValue

/-! The first two are the scalar-action assumptions Mathlib itself makes when
relating the Loewner order on `E →L[𝕜] E` to the continuous functional
calculus.  The third is the one genuinely `ℂ`-only ingredient: Mathlib has that
instance for `𝕜 = ℂ`, and carrying it as a hypothesis keeps the development
general without pretending the general case is already available. -/
variable [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

/-- The operator absolute value `|T| = (T⋆T)^{1/2}`, as the continuous
functional calculus `CFC.abs`.

Relative to the `ContinuousFunctionalCalculus` hypothesis above this is a real
definition rather than a leaf obligation, so the results below unfold it. -/
noncomputable def operatorAbsoluteValue (T : E →L[𝕜] E) : E →L[𝕜] E :=
  CFC.abs T

/-- Unfolding lemma: the absolute value *is* `CFC.abs`.  Stated so that
downstream rewrites do not have to unfold a `def`. -/
theorem operatorAbsoluteValue_eq (T : E →L[𝕜] E) :
    operatorAbsoluteValue T = CFC.abs T := rfl

/-- The absolute value is nonnegative in the Loewner order.

This is the first consequence that was previously out of reach: with an opaque
term there is nothing to unfold, so even this could not be stated usefully. -/
@[simp]
theorem operatorAbsoluteValue_nonneg (T : E →L[𝕜] E) :
    0 ≤ operatorAbsoluteValue T :=
  CFC.abs_nonneg T

/-- The absolute value is insensitive to sign. -/
@[simp]
theorem operatorAbsoluteValue_neg (T : E →L[𝕜] E) :
    operatorAbsoluteValue (-T) = operatorAbsoluteValue T :=
  CFC.abs_neg T

/-- The absolute value of `0` is `0`. -/
@[simp]
theorem operatorAbsoluteValue_zero :
    operatorAbsoluteValue (0 : E →L[𝕜] E) = 0 :=
  CFC.abs_zero

/-- **The absolute value is norm-preserving.**  `‖|T|‖ = ‖T‖`, by the C⋆
identity applied twice: `|T|` is self-adjoint and `|T| * |T| = T⋆ T`, so
`‖|T|‖² = ‖|T|⋆ |T|‖ = ‖T⋆ T‖ = ‖T‖²`.

This is the gauge-free half of what a symmetric norm ideal wants from the
absolute value, and unlike the gauge half it needs no polar decomposition — so
it is available over a general `RCLike` field, where
`operatorAbsoluteValue_mem_and_gauge_eq` is still a leaf. -/
theorem norm_operatorAbsoluteValue (T : E →L[𝕜] E) :
    ‖operatorAbsoluteValue T‖ = ‖T‖ := by
  have hsa : star (operatorAbsoluteValue T) = operatorAbsoluteValue T :=
    (CFC.abs_nonneg T).isSelfAdjoint
  have hsq : ‖operatorAbsoluteValue T‖ * ‖operatorAbsoluteValue T‖ = ‖T‖ * ‖T‖ := by
    calc ‖operatorAbsoluteValue T‖ * ‖operatorAbsoluteValue T‖
        = ‖star (operatorAbsoluteValue T) * operatorAbsoluteValue T‖ :=
          (CStarRing.norm_star_mul_self).symm
      _ = ‖star T * T‖ := by
          rw [hsa, operatorAbsoluteValue_eq, CFC.abs_mul_abs]
      _ = ‖T‖ * ‖T‖ := CStarRing.norm_star_mul_self
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The full ambient sine-angle operator of two subspaces: the absolute value
of the projector difference. -/
noncomputable def sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  operatorAbsoluteValue (projection U - projection V)

/-- **Symmetric norm ideals contain absolute values with equal gauge, given a
polar partial isometry.**

This is the mathematical content of the leaf obligation below, with the one
genuinely missing ingredient — the polar partial isometry — taken as an explicit
hypothesis rather than assumed into existence.

Two things are worth recording about the proof.  First, **unitary invariance is
not needed**, although the leaf's own description reaches for it: `ideal_bound`
alone closes both directions, because each of `|T|` and `T` is a two-sided
multiple of the other.  Second, only the *norm bounds* on `W` are used, not that
it is a partial isometry, so the hypotheses here are weaker than polar
decomposition actually delivers. -/
theorem SymmetricNormIdeal.operatorAbsoluteValue_mem_and_gauge_eq_of_polar
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E)) {T W : E →L[𝕜] E}
    (hT : I.mem T)
    (hWT : W ∘L operatorAbsoluteValue T = T)
    (hWadj : (ContinuousLinearMap.adjoint W) ∘L T = operatorAbsoluteValue T)
    (hWnorm : ‖W‖ ≤ 1) (hWadjnorm : ‖ContinuousLinearMap.adjoint W‖ ≤ 1) :
    I.mem (operatorAbsoluteValue T) ∧
      I.gauge (operatorAbsoluteValue T) = I.gauge T := by
  have hid : ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  -- `|T| = W⋆ ∘ T ∘ 1`, so membership and one gauge bound come from the ideal axioms.
  have habs : ContinuousLinearMap.adjoint W ∘L T ∘L ContinuousLinearMap.id 𝕜 E =
      operatorAbsoluteValue T := by
    rw [ContinuousLinearMap.comp_id]; exact hWadj
  have hmem : I.mem (operatorAbsoluteValue T) := by
    have := I.ideal_mem (ContinuousLinearMap.adjoint W) (ContinuousLinearMap.id 𝕜 E) hT
    rwa [habs] at this
  refine ⟨hmem, le_antisymm ?_ ?_⟩
  · have hb := I.ideal_bound (ContinuousLinearMap.adjoint W) (ContinuousLinearMap.id 𝕜 E) hT
    rw [habs] at hb
    refine hb.trans ?_
    have h0 : 0 ≤ I.gauge T := I.nonneg hT
    calc ‖ContinuousLinearMap.adjoint W‖ * I.gauge T * ‖ContinuousLinearMap.id 𝕜 E‖
        ≤ 1 * I.gauge T * 1 := by
          gcongr
      _ = I.gauge T := by ring
  · -- and symmetrically `T = W ∘ |T| ∘ 1`.
    have hT' : W ∘L operatorAbsoluteValue T ∘L ContinuousLinearMap.id 𝕜 E = T := by
      rw [ContinuousLinearMap.comp_id]; exact hWT
    have hb := I.ideal_bound W (ContinuousLinearMap.id 𝕜 E) hmem
    rw [hT'] at hb
    refine hb.trans ?_
    have h0 : 0 ≤ I.gauge (operatorAbsoluteValue T) := I.nonneg hmem
    calc ‖W‖ * I.gauge (operatorAbsoluteValue T) * ‖ContinuousLinearMap.id 𝕜 E‖
        ≤ 1 * I.gauge (operatorAbsoluteValue T) * 1 := by
          gcongr
      _ = I.gauge (operatorAbsoluteValue T) := by ring

/-- **Symmetric norm ideals contain absolute values with equal gauge.**

**Closed 2026-08-04.**  This was a leaf obligation, with the mathematics already
proved directly above in `operatorAbsoluteValue_mem_and_gauge_eq_of_polar` and
only the polar partial isometry missing, "over a general `RCLike` field in
infinite dimensions" — `ContinuousLinearMap.polarPartial` being `ℂ`-only and the
`RCLike` `polarFactor` being for plain linear maps.

The field restriction turned out to be an artefact of how that isometry was
*keyed*, not of the mathematics.  Both existing constructions build it from
`|T|`, so both inherit `|T|`'s dependence on a continuous functional calculus,
which Mathlib supplies only for `ℂ`.  But the construction never uses the
calculus: it uses `‖|T| x‖ = ‖T x‖`, which is a consequence of the *Gram*
identity `|T|² = T⋆T` and self-adjointness alone.  Keying on the Gram identity
instead — `ForTauCeti/Analysis/InnerProductSpace/Polar/GramContraction.lean` —
removes the restriction, and the calculus enters here only where it already did,
in producing `|T|` itself. -/
theorem SymmetricNormIdeal.operatorAbsoluteValue_mem_and_gauge_eq
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E)) {T : E →L[𝕜] E}
    (hT : I.mem T) :
    I.mem (operatorAbsoluteValue T) ∧
      I.gauge (operatorAbsoluteValue T) = I.gauge T := by
  have hgram : operatorAbsoluteValue T ∘L operatorAbsoluteValue T =
      ContinuousLinearMap.adjoint T ∘L T := by
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def,
      ← ContinuousLinearMap.star_eq_adjoint, operatorAbsoluteValue_eq]
    exact CFC.abs_mul_abs T
  obtain ⟨W, hWnorm, hWadjnorm, hWT, hWadj⟩ :=
    ContinuousLinearMap.exists_contraction_of_gram_eq
      (operatorAbsoluteValue_nonneg T).isSelfAdjoint hgram
  exact I.operatorAbsoluteValue_mem_and_gauge_eq_of_polar hT hWT hWadj hWnorm hWadjnorm

/-! ### Reduction of the ideal-valued projector-difference estimate

The leaf below is stated with the sharp constant **one**, and its own earlier
description — "requiring the ideal-valued Sylvester engine on both off-diagonal
blocks" — understates it, because that engine already exists and is proved
(`sylvester_mem_and_gauge_le_of_intervalExteriorGap`, general `RCLike`, constant
one).  The two lemmas below carry out the reduction, so that what is left is one
precisely identified gap rather than a vague campaign.

Write `S = P_U − P_V` and `R = B − A`.  Then:

* `S` satisfies a **Sylvester equation** on the nose,
  `A S − S B = R P_V − P_U R` (`projectionDifference_sylvester`, proved below,
  and needing only that `A` reduces `U` and `B` reduces `V`);
* its right-hand side is a **reflection pinch** of `R`, hence gauge-contractive:
  `R P_V − P_U R = (R J_V − J_U R)/2` with `J = 2P − 1` the reflections, so
  `gauge (R P_V − P_U R) ≤ gauge R`
  (`gauge_projectionCross_le`, proved below).

**What is still missing, precisely.**  `S` is purely off-diagonal for the block
structure `(U ⊕ Uᗮ, V ⊕ Vᗮ)`: its `(U,V)` and `(Uᗮ,Vᗮ)` blocks vanish.  The
hypotheses separate exactly the two *surviving* corners — `spec(A|U)` from
`spec(B|Vᗮ)`, and `spec(A|Uᗮ)` from `spec(B|V)` — and say nothing about the other
two, which is correct because `S` is zero there.  But the Sylvester engine is a
statement about the *global* spectra of `A` and `B`, and those are not separated.
Shifting by `κ P_Uᗮ` and `κ P_V` leaves the equation invariant (precisely because
`S`'s `(U,V)` block vanishes) and can align the two interval centres, but it
cannot make all four corner pairs separated at once.

Applying the engine to each corner separately and adding gives constant **2**,
which is what `Sylvester/Spectrum.lean`'s `sinTheta_spectrum_gauge_symmetric`
already proves.  Constant one needs the Schur-multiplier form of the estimate on
the *union of two* interval/exterior rectangles — i.e. a kernel representation of
`(a − b)⁻¹` of total mass `1/d` valid on that union — and that is the missing
piece.  The statement itself is believed true and sharp: equality holds at
`B − A = d (P_U − P_V)`.
-/

omit [CompleteSpace E] [Algebra ℝ (E →L[𝕜] E)]
  [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)] in
/-- **The projector difference solves a Sylvester equation.**

With `A` reducing `U` and `B` reducing `V`,
`A (P_U − P_V) − (P_U − P_V) B = (B − A) P_V − P_U (B − A)`.

Pure algebra: the two reducing hypotheses let `A` and `P_U` swap, and `B` and
`P_V` swap, after which everything cancels. -/
theorem projectionDifference_sylvester
    {A B : E →L[𝕜] E} {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V) :
    A ∘L (projection U - projection V) - (projection U - projection V) ∘L B =
      (B - A) ∘L projection V - projection U ∘L (B - A) := by
  have hAU : A ∘L projection U = projection U ∘L A :=
    (ContinuousLinearMap.starProjection_comp_comm_of_reduces A U hU).symm
  have hBV : projection V ∘L B = B ∘L projection V :=
    ContinuousLinearMap.starProjection_comp_comm_of_reduces B V hV
  simp only [← ContinuousLinearMap.mul_def] at hAU hBV ⊢
  rw [mul_sub, sub_mul, sub_mul, mul_sub, hAU, hBV]
  abel

omit [CompleteSpace E] [Algebra ℝ (E →L[𝕜] E)]
  [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)] in
/-- **The cross term is a reflection pinch**: `R P_V − P_U R = (R J_V − J_U R)/2`.

Immediate from `J = 2P − 1`, but worth naming: it is what makes the right-hand
side of `projectionDifference_sylvester` gauge-contractive in `R`. -/
theorem projectionCross_eq_reflectionPinch
    (R : E →L[𝕜] E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    R ∘L projection V - projection U ∘L R =
      ((2 : 𝕜)⁻¹) • (R ∘L V.reflectionOperator - U.reflectionOperator ∘L R) := by
  have hU : (U.reflectionOperator : E →L[𝕜] E) =
      (2 : 𝕜) • projection U - ContinuousLinearMap.id 𝕜 E :=
    Submodule.reflectionOperator_eq_two_smul_sub_id U
  have hV : (V.reflectionOperator : E →L[𝕜] E) =
      (2 : 𝕜) • projection V - ContinuousLinearMap.id 𝕜 E :=
    Submodule.reflectionOperator_eq_two_smul_sub_id V
  rw [hU, hV]
  ext x
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    sub_apply, smul_apply,
    ContinuousLinearMap.coe_id', id_eq, map_sub, map_smul]
  match_scalars <;> (try field_simp) ; ring

omit [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint] [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)] in
/-- **The cross term is gauge-contractive**: `gauge (R P_V − P_U R) ≤ gauge R`.

The two-subspace analogue of `gauge_offDiagonalPart_le`, which pinches against a
single reflection.  Both one-sided factors are reflections, so each has operator
norm at most one and the ideal bound applies on either side; the triangle
inequality and the factor `1/2` then give constant one. -/
theorem SymmetricNormIdeal.gauge_projectionCross_le
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {R : E →L[𝕜] E} (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hR : I.mem R) :
    I.mem (R ∘L projection V - projection U ∘L R) ∧
      I.gauge (R ∘L projection V - projection U ∘L R) ≤ I.gauge R := by
  have hJU : ‖(U.reflectionOperator : E →L[𝕜] E)‖ ≤ 1 :=
    Submodule.norm_reflectionOperator_le_one U
  have hJV : ‖(V.reflectionOperator : E →L[𝕜] E)‖ ≤ 1 :=
    Submodule.norm_reflectionOperator_le_one V
  -- `R J_V` and `J_U R` are ideal members with gauge at most `gauge R`.
  have hrightMem : I.mem (R ∘L V.reflectionOperator) := by
    have := I.ideal_mem (ContinuousLinearMap.id 𝕜 E) V.reflectionOperator hR
    simpa using this
  have hleftMem : I.mem (U.reflectionOperator ∘L R) := by
    have := I.ideal_mem U.reflectionOperator (ContinuousLinearMap.id 𝕜 E) hR
    simpa using this
  have hrightGauge : I.gauge (R ∘L V.reflectionOperator) ≤ I.gauge R := by
    have hb := I.ideal_bound (ContinuousLinearMap.id 𝕜 E) V.reflectionOperator hR
    simp only [ContinuousLinearMap.id_comp] at hb
    refine hb.trans ?_
    have h0 : 0 ≤ I.gauge R := I.nonneg hR
    have hid : ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    calc ‖ContinuousLinearMap.id 𝕜 E‖ * I.gauge R *
          ‖(V.reflectionOperator : E →L[𝕜] E)‖
        ≤ 1 * I.gauge R * 1 := by gcongr
      _ = I.gauge R := by ring
  have hleftGauge : I.gauge (U.reflectionOperator ∘L R) ≤ I.gauge R := by
    have hb := I.ideal_bound U.reflectionOperator (ContinuousLinearMap.id 𝕜 E) hR
    simp only [ContinuousLinearMap.comp_id] at hb
    refine hb.trans ?_
    have h0 : 0 ≤ I.gauge R := I.nonneg hR
    have hid : ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    calc ‖(U.reflectionOperator : E →L[𝕜] E)‖ * I.gauge R *
          ‖ContinuousLinearMap.id 𝕜 E‖
        ≤ 1 * I.gauge R * 1 := by gcongr
      _ = I.gauge R := by ring
  have hnegMem : I.mem (-(U.reflectionOperator ∘L R)) := by
    simpa using I.smul_mem (-1 : 𝕜) hleftMem
  have hnegGauge : I.gauge (-(U.reflectionOperator ∘L R)) =
      I.gauge (U.reflectionOperator ∘L R) := by
    have h := I.gauge_smul (-1 : 𝕜) hleftMem
    simpa using h
  have hdiffMem : I.mem (R ∘L V.reflectionOperator - U.reflectionOperator ∘L R) := by
    have := I.add_mem hrightMem hnegMem
    simpa [sub_eq_add_neg] using this
  have hdiffGauge :
      I.gauge (R ∘L V.reflectionOperator - U.reflectionOperator ∘L R) ≤
        I.gauge R + I.gauge R := by
    have ht := I.triangle hrightMem hnegMem
    rw [hnegGauge] at ht
    have hrw : R ∘L V.reflectionOperator + -(U.reflectionOperator ∘L R) =
        R ∘L V.reflectionOperator - U.reflectionOperator ∘L R := by
      rw [sub_eq_add_neg]
    rw [hrw] at ht
    linarith
  rw [projectionCross_eq_reflectionPinch R U V]
  refine ⟨I.smul_mem _ hdiffMem, ?_⟩
  rw [I.gauge_smul _ hdiffMem]
  have hnorm : ‖((2 : 𝕜)⁻¹)‖ = 1 / 2 := by
    rw [norm_inv, RCLike.norm_ofNat]
    norm_num
  rw [hnorm]
  linarith

end OperatorAbsoluteValue

end DavisKahanExt
end TauCeti