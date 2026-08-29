/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.DoubleAngle.UnboundedIdeal
import DavisKahan.OperatorIdeal.CanonicalRealView
import DavisKahan.TanTwoTheta.UnboundedIdeal
import DavisKahan.TanTheta.Spectrum
import DavisKahan.TanTheta.UnboundedGraphAngle
import DavisKahan.FiniteDimensional.TanTheta.RitzResidual
import DavisKahan.TanTheta.Theorem63FiniteSource
import DavisKahan.TanTheta.Theorem63InfiniteTrial
import DavisKahan.TanTheta.Theorem63Unbounded
import DavisKahan.Sources.DavisKahan1970.Section2TanThetaPerturbation
import ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
import ForTauCeti.Analysis.Normed.Operator.PartialSylvesterBoundedInverse

/-!
# Remaining source-level endpoint signatures

This module records the principal paper-facing statements that still lack an
exact source wrapper or a proof at the full Hilbert-space norm-ideal scope.
They are kept outside the supported source facade until their hypotheses and
conclusions are compiler-certified and audited against the paper.
-/

open scoped InnerProductSpace
open Set

namespace TauCeti
namespace DavisKahan1970
namespace RemainingSourceSurface

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open DavisKahanExt
open TauCeti.DavisKahan

universe u v

section BanachSylvester

variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- A norm on cross-space bounded operators compatible with contractions on
both sides, as required in Davis--Kahan Theorem 5.1. -/
structure CompatibleCrossOperatorNorm where
  toFun : (X →L[ℂ] Y) → ℝ
  nonneg : ∀ T, 0 ≤ toFun T
  eq_zero : ∀ T, toFun T = 0 → T = 0
  smul : ∀ c : ℂ, ∀ T, toFun (c • T) = ‖c‖ * toFun T
  triangle : ∀ S T, toFun (S + T) ≤ toFun S + toFun T
  compatible : ∀ (L : Y →L[ℂ] Y) (T : X →L[ℂ] Y)
    (R : X →L[ℂ] X), ‖L‖ ≤ 1 → ‖R‖ ≤ 1 →
      toFun (L ∘L T ∘L R) ≤ toFun T

/-- The residual surface subspace is orthogonally complemented. -/
instance : CoeFun (CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (fun _ => (X →L[ℂ] Y) → ℝ) :=
  ⟨CompatibleCrossOperatorNorm.toFun⟩

/-- An explicit bounded left inverse of `A` with a reciprocal norm bound.  On a
general Banach space a lower bound on `A` does not furnish a bounded projection
onto the (possibly non-complemented) range, so the reusable datum is the left
inverse itself; on a Hilbert space the spectral-separation lower bound supplies
it through the closed-range orthogonal projection. -/
structure BoundedLeftInverseData (A : Y →L[ℂ] Y) (c : ℝ) where
  leftInverse : Y →L[ℂ] Y
  comp_eq_id : leftInverse ∘L A = ContinuousLinearMap.id ℂ Y
  norm_le : ‖leftInverse‖ ≤ c

/-- An explicit bounded right inverse with a reciprocal norm bound, used by the
source's symmetric form of Theorem 5.1. -/
structure BoundedRightInverseData (B : X →L[ℂ] X) (c : ℝ) where
  rightInverse : X →L[ℂ] X
  comp_eq_id : B ∘L rightInverse = ContinuousLinearMap.id ℂ X
  norm_le : ‖rightInverse‖ ≤ c

namespace CompatibleCrossOperatorNorm

/-- The compatible norm vanishes at the zero operator. -/
theorem map_zero (N : CompatibleCrossOperatorNorm (X := X) (Y := Y)) :
    N (0 : X →L[ℂ] Y) = 0 := by
  have h := N.smul 0 (0 : X →L[ℂ] Y)
  simpa using h

/-- Full two-sided ideal estimate obtained by normalizing the multipliers. -/
theorem comp_le_mul (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (L : Y →L[ℂ] Y) (T : X →L[ℂ] Y) (R : X →L[ℂ] X) :
    N (L ∘L T ∘L R) ≤ ‖L‖ * N T * ‖R‖ := by
  by_cases hL : L = 0
  · subst L; simp [map_zero N]
  by_cases hR : R = 0
  · subst R; simp [map_zero N]
  let Ln : Y →L[ℂ] Y := (‖L‖ : ℂ)⁻¹ • L
  let Rn : X →L[ℂ] X := (‖R‖ : ℂ)⁻¹ • R
  have hLnorm : ‖L‖ ≠ 0 := norm_ne_zero_iff.mpr hL
  have hRnorm : ‖R‖ ≠ 0 := norm_ne_zero_iff.mpr hR
  have hLcomplex : (‖L‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLnorm
  have hRcomplex : (‖R‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hRnorm
  have hLn : ‖Ln‖ ≤ 1 := by
    change ‖(‖L‖ : ℂ)⁻¹ • L‖ ≤ 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg L), inv_mul_cancel₀ hLnorm]
  have hRn : ‖Rn‖ ≤ 1 := by
    change ‖(‖R‖ : ℂ)⁻¹ • R‖ ≤ 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg R), inv_mul_cancel₀ hRnorm]
  have hcompat := N.compatible Ln T Rn hLn hRn
  have hfactor :
      L ∘L T ∘L R = ((‖L‖ * ‖R‖ : ℝ) : ℂ) • (Ln ∘L T ∘L Rn) := by
    ext x
    simp [Ln, Rn, hLcomplex, hRcomplex, smul_smul,
      mul_left_comm, mul_comm]
  rw [hfactor, N.smul]
  calc
    ‖((‖L‖ * ‖R‖ : ℝ) : ℂ)‖ * N (Ln ∘L T ∘L Rn)
        ≤ (‖L‖ * ‖R‖) * N T := by
          simpa using mul_le_mul_of_nonneg_left hcompat
            (mul_nonneg (norm_nonneg L) (norm_nonneg R))
    _ = ‖L‖ * N T * ‖R‖ := by ring

/-- One-sided left estimate. -/
theorem comp_left_le_mul (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (L : Y →L[ℂ] Y) (T : X →L[ℂ] Y) :
    N (L ∘L T) ≤ ‖L‖ * N T := by
  have h := comp_le_mul N L T (ContinuousLinearMap.id ℂ X)
  rw [ContinuousLinearMap.comp_id] at h
  calc
    N (L ∘L T) ≤ ‖L‖ * N T * ‖ContinuousLinearMap.id ℂ X‖ := h
    _ ≤ ‖L‖ * N T * 1 :=
      mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
        (mul_nonneg (norm_nonneg L) (N.nonneg T))
    _ = ‖L‖ * N T := by ring

/-- A compatible cross-operator norm is invariant under negation. -/
theorem map_neg (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (T : X →L[ℂ] Y) : N (-T) = N T := by
  have h := N.smul (-1) T
  simpa using h

/-- One-sided right ideal estimate. -/
theorem comp_right_le_mul (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (T : X →L[ℂ] Y) (R : X →L[ℂ] X) :
    N (T ∘L R) ≤ N T * ‖R‖ := by
  have h := comp_le_mul N (ContinuousLinearMap.id ℂ Y) T R
  have hid : ‖ContinuousLinearMap.id ℂ Y‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  calc
    N (T ∘L R) = N ((ContinuousLinearMap.id ℂ Y) ∘L T ∘L R) := by
      rw [ContinuousLinearMap.id_comp]
    _ ≤ ‖ContinuousLinearMap.id ℂ Y‖ * N T * ‖R‖ := h
    _ ≤ 1 * N T * ‖R‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hid (N.nonneg T)) (norm_nonneg R)
    _ = N T * ‖R‖ := by ring

end CompatibleCrossOperatorNorm

/-- Reusable Banach-space Sylvester lower bound from a bounded left inverse.

Davis--Kahan Theorem 5.1 assumes a genuine bounded inverse `A⁻¹` with
`‖A⁻¹‖ ≤ (gamma + delta)⁻¹`.  The proof uses only the left-inverse half of that
datum, so this reusable theorem is intentionally stronger than the printed
statement.  The source-facing theorem `theorem5_1_banach_sylvester_exact` below
restores the literal two-sided inverse hypothesis for statement-level auditing. -/
theorem theorem5_1_banach_sylvester
    (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (A : Y →L[ℂ] Y) (B : X →L[ℂ] X)
    (T C : X →L[ℂ] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hB : ‖B‖ ≤ gamma)
    (hleft : BoundedLeftInverseData A (gamma + delta)⁻¹)
    (hEq : A ∘L T - T ∘L B = C) :
    delta * N T ≤ N C := by
  let L := hleft.leftInverse
  have hgd : 0 < gamma + delta := add_pos_of_nonneg_of_pos hgamma hdelta
  have hLT : T = L ∘L C + L ∘L T ∘L B := by
    have hcancel : L ∘L A = ContinuousLinearMap.id ℂ Y := hleft.comp_eq_id
    apply ContinuousLinearMap.ext
    intro x
    have heqpoint := congrArg (fun S : X →L[ℂ] Y => S x) hEq
    simp only [sub_apply, ContinuousLinearMap.comp_apply] at heqpoint
    change T x = L (C x) + L (T (B x))
    have hLA : L (A (T x)) = T x := by
      have hp := congrArg (fun S : Y →L[ℂ] Y => S (T x)) hcancel
      simpa using hp
    rw [← heqpoint, map_sub, hLA]
    abel
  have htri : N T ≤ N (L ∘L C) + N (L ∘L T ∘L B) := by
    calc
      N T = N (L ∘L C + L ∘L T ∘L B) := congrArg N.toFun hLT
      _ ≤ N (L ∘L C) + N (L ∘L T ∘L B) := N.triangle _ _
  have hLC : N (L ∘L C) ≤ (gamma + delta)⁻¹ * N C :=
    (CompatibleCrossOperatorNorm.comp_left_le_mul N L C).trans
      (mul_le_mul_of_nonneg_right hleft.norm_le (N.nonneg C))
  have hLTB : N (L ∘L T ∘L B) ≤ (gamma + delta)⁻¹ * N T * gamma :=
    (CompatibleCrossOperatorNorm.comp_le_mul N L T B).trans
      (mul_le_mul
        (mul_le_mul_of_nonneg_right hleft.norm_le (N.nonneg T))
        hB (norm_nonneg B)
        (mul_nonneg (inv_nonneg.mpr hgd.le) (N.nonneg T)))
  have hsum : N T ≤ (gamma + delta)⁻¹ * N C +
      (gamma + delta)⁻¹ * N T * gamma :=
    htri.trans (add_le_add hLC hLTB)
  have hscaled := mul_le_mul_of_nonneg_left hsum hgd.le
  have hnormalize :
      (gamma + delta) *
          ((gamma + delta)⁻¹ * N C + (gamma + delta)⁻¹ * N T * gamma) =
        N C + N T * gamma := by
    calc
      (gamma + delta) *
          ((gamma + delta)⁻¹ * N C + (gamma + delta)⁻¹ * N T * gamma) =
          ((gamma + delta) * (gamma + delta)⁻¹) * N C +
            ((gamma + delta) * (gamma + delta)⁻¹) * N T * gamma := by ring
      _ = N C + N T * gamma := by
        rw [mul_inv_cancel₀ hgd.ne']; ring
  rw [hnormalize] at hscaled
  nlinarith


/-- **Davis--Kahan 1970, Theorem 5.1 with the printed inverse hypothesis.**

The paper states `‖A⁻¹‖ ≤ (gamma + delta)⁻¹`.  This source-facing wrapper
carries that literally as a bounded operator `Ainv` which is both a left and a
right inverse of `A`.  The proof below only needs the left-inverse equation,
which is why the reusable theorem `theorem5_1_banach_sylvester` is formulated
with the weaker `BoundedLeftInverseData` hypothesis. -/
theorem theorem5_1_banach_sylvester_exact
    (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (A Ainv : Y →L[ℂ] Y) (B : X →L[ℂ] X)
    (T C : X →L[ℂ] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hB : ‖B‖ ≤ gamma)
    (hAinv_left : Ainv ∘L A = ContinuousLinearMap.id ℂ Y)
    (_hAinv_right : A ∘L Ainv = ContinuousLinearMap.id ℂ Y)
    (hAinv_norm : ‖Ainv‖ ≤ (gamma + delta)⁻¹)
    (hEq : A ∘L T - T ∘L B = C) :
    delta * N T ≤ N C := by
  exact theorem5_1_banach_sylvester N A B T C hgamma hdelta hB
    ⟨Ainv, hAinv_left, hAinv_norm⟩ hEq


/-- **Davis--Kahan 1970, Theorem 5.1 with the roles of `A` and `B`
interchanged.**

This is the printed symmetry remark following Theorem 5.1.  The left block is
bounded by `gamma`, the right block has a bounded right inverse of norm at most
`(gamma + delta)⁻¹`, and the same compatible-norm conclusion follows. -/
theorem theorem5_1_banach_sylvester_interchanged
    (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (A : Y →L[ℂ] Y) (B : X →L[ℂ] X)
    (T C : X →L[ℂ] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hA : ‖A‖ ≤ gamma)
    (hright : BoundedRightInverseData B (gamma + delta)⁻¹)
    (hEq : A ∘L T - T ∘L B = C) :
    delta * N T ≤ N C :=
  TauCeti.ContinuousLinearMap.opNorm_le_of_sylvester_of_rightInverse
    N.triangle N.map_neg
    (fun L S => N.comp_left_le_mul L S)
    (fun S R => N.comp_right_le_mul S R)
    N.nonneg hright.comp_eq_id hgamma hdelta hright.norm_le hA hEq


/-- **The printed `A`/`B` interchange remark with a literal inverse of `B`.**

This is the symmetric source wrapper: `A` is bounded by `gamma`, while `Binv`
is a genuine bounded two-sided inverse of `B` with norm at most
`(gamma + delta)⁻¹`. -/
theorem theorem5_1_banach_sylvester_interchanged_exact
    (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (A : Y →L[ℂ] Y) (B Binv : X →L[ℂ] X)
    (T C : X →L[ℂ] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hA : ‖A‖ ≤ gamma)
    (_hBinv_left : Binv ∘L B = ContinuousLinearMap.id ℂ X)
    (hBinv_right : B ∘L Binv = ContinuousLinearMap.id ℂ X)
    (hBinv_norm : ‖Binv‖ ≤ (gamma + delta)⁻¹)
    (hEq : A ∘L T - T ∘L B = C) :
    delta * N T ≤ N C := by
  exact theorem5_1_banach_sylvester_interchanged N A B T C hgamma hdelta hA
    ⟨Binv, hBinv_right, hBinv_norm⟩ hEq

/-- **Davis--Kahan 1970, Theorem 5.1 with an unbounded left block.**

The partial operator `A` is closed and densely defined as stated in the paper,
and has an everywhere-defined bounded left inverse.  The bounded maps `T` and
`C` satisfy the Sylvester equation on that domain.  No right inverse or
surjectivity hypothesis is imposed: the proof uses only cancellation after
applying `A` to `T x`.  The conclusion is the same compatible-norm bound as in
the bounded theorem. -/
theorem theorem5_1_banach_sylvester_unboundedA
    (N : CompatibleCrossOperatorNorm (X := X) (Y := Y))
    (A : Y →ₗ.[ℂ] Y) (_hAdense : Dense (A.domain : Set Y))
    (_hAclosed : A.IsClosed)
    (hAinv : TauCeti.LinearPMap.BoundedEverywhereLeftInverseData A)
    (B : X →L[ℂ] X) (T C : X →L[ℂ] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hAinvNorm : ‖hAinv.inv‖ ≤ (gamma + delta)⁻¹)
    (hB : ‖B‖ ≤ gamma)
    (hEq : TauCeti.LinearPMap.BoundedRightSylvesterEquation A B T C) :
    delta * N T ≤ N C :=
  TauCeti.LinearPMap.opNorm_le_of_boundedRight_sylvester_of_everywhereLeftInverse
    N.triangle
    (fun L S => N.comp_left_le_mul L S)
    (fun S R => N.comp_right_le_mul S R)
    N.nonneg hAinv hgamma hdelta hAinvNorm hB hEq

end BanachSylvester

section GeneralizedTangentResidual

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Residual operator of a trial subspace for a bounded self-adjoint operator. -/
noncomputable def trialResidual
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] : Z →L[ℂ] H :=
  Zᗮ.starProjection ∘L T ∘L Z.subtypeL

end GeneralizedTangentResidual

section GeneralizedTangent

/-!
## Source-audit correction for Theorem 6.3

The previous frontier draft mistranscribed the paper.  Davis--Kahan Theorem 6.3
assumes a strict dimension inequality between the coordinate spaces and defines
`tan Θ₀` from the singular values of the directed cross block `E₀⋆ F₁`.  It does
not infer the symmetric relation `IsAcute Z V` from an abstract isometric
embedding of the smaller space into the larger one.

The bounded strict-dimension theorem is now proved at the paper's effective
scope: finite trial coordinates and an arbitrary complete ambient Hilbert
space.  This follows from the paper's global separability convention together
with its strict Hilbert-dimension inequality.  The equal-dimension tangent
theorem and the Appendix's full unbounded arbitrary-ideal extension remain
separate open endpoints.
-/

/-- Compiled finite-dimensional strict-lower-rank specialization of
Davis--Kahan 1970, Theorem 6.3.  This is intentionally not named as the full
source endpoint. -/
alias theorem6_3_finite_generalizedTanTheta_ideal :=
  DavisKahanTheory.davisKahan1970_generalizedTanTheta0_ritzResidual_le

/-- Compiled finite-dimensional equal-rank specialization of the Section 2
single-angle tangent theorem. -/
alias theorem6_3_equalRank_finite_tanTheta_ideal :=
  DavisKahanTheory.davisKahan1970_tanTheta0_ritzResidual_le

/-- Compiled unbounded graph-angle companion at operator norm.  This is useful
partial source coverage but does not discharge the paper's arbitrary
unitarily-invariant-norm statement. -/
alias theorem6_3_unbounded_graphAngle_opNorm_partial :=
  DavisKahan.TanTheta.tanTheta_unbounded_graphAngle_trialBlock

/-- Unique frontier marker for the arbitrary-ideal unbounded scope.

**Closed 2026-08-06.**  It used to alias the operator-norm graph-angle companion, and
the manifest carried it as an open obligation, because the paper claims *arbitrary
unitarily invariant norm* and only the operator norm was grounded.  It now aliases the
ideal-gauge theorem.

The ambient operator is closed, unbounded and self-adjoint; `V` is its spectral subspace
for `Set.Iic α`; the spectral gap `Set.Ioo α (α + δ)` carries no spectrum; the Ritz
compression is bounded above by `α`.  The tangent representative is constructed, not
assumed. -/
alias unbounded_angle_theorems_source_scope_partial_marker :=
  ExactTanTheta.theorem6_3_unbounded_ideal_directedTangent

/-- The unbounded tangent theorem with an arbitrary tangent representative supplied. -/
alias theorem6_3_unbounded_tanTheta_ideal :=
  ExactTanTheta.theorem6_3_unbounded_ideal

/-- Retained: the operator-norm graph-angle companion.  Useful partial coverage, and
**not** the arbitrary-unitarily-invariant-norm scope claim -- that is the alias above. -/
alias theorem6_3_unbounded_graphAngle_opNorm_companion :=
  DavisKahan.TanTheta.tanTheta_unbounded_graphAngle_trialBlock

/-- Completed finite-trial/arbitrary-ambient Ky Fan root of Theorem 6.3. -/
alias theorem6_3_all_kyFan_core :=
  ExactTanTheta.theorem6_3_all_kyFan_core

/-- Completed bounded source-faithful Davis--Kahan Theorem 6.3. -/
alias theorem6_3_generalizedTanTheta_source_ideal :=
  ExactTanTheta.theorem6_3_generalizedTanTheta_source_ideal

/-! ### Theorem 6.3 without a tangent-representative hypothesis

The two aliases above quantify over a `tanTheta0` satisfying
`HasTheorem63DirectedTangentApproximationNumbers`, and until 2026-08-05 nothing
in the repository constructed one — so the compiled Theorem 6.3 was a
conditional whose antecedent had no witness, which is weaker than what Davis and
Kahan assert.

`theorem63DirectedTangent` is the witness: diagonal in the right singular basis
of the sine block, with entries `tan (arcsin sᵢ)`.  Its finiteness needs
`sᵢ < 1`, and that is not a new hypothesis — `theorem63_singularValues_sine_lt_one`
derives it from the source gap the theorem already assumes.  The two aliases
below therefore carry exactly the printed hypotheses and nothing else. -/

/-- The directed tangent representative of Theorem 6.3, and the proof that it
has the approximation numbers the theorem asks for. -/
alias theorem6_3_directedTangent :=
  ExactTanTheta.theorem63DirectedTangent

alias theorem6_3_directedTangent_approximationNumbers :=
  ExactTanTheta.hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent

/-- Theorem 6.3's Ky Fan root with the representative supplied, not assumed. -/
alias theorem6_3_all_kyFan_core_unconditional :=
  ExactTanTheta.theorem6_3_all_kyFan_core_directedTangent

/-- Theorem 6.3 at ideal-gauge scope with the representative supplied, not
assumed. -/
alias theorem6_3_generalizedTanTheta_source_ideal_unconditional :=
  ExactTanTheta.theorem6_3_generalizedTanTheta_source_ideal_directedTangent

/-! ### The equal-rank tangent theorem

Section 2's tangent theorem is about a pair of subspaces of **equal** rank, so
it cannot be obtained by specialising a statement that assumes
`rank Z < rank V`.  It does not have to be: the printed `dim X(E₀) < dim X(F₀)`
does one job — under the paper's separability convention it forces the trial
coordinate space to be finite-dimensional — and here that is an explicit
instance hypothesis.  Lean had already recorded the redundancy, binding the
comparison as `_hStrictDimension` and never using it.

`theorem6_3_equalRank_tanTheta_ideal` is the residual half of the Section 2
tangent theorem at arbitrary unitarily invariant ideal-gauge scope, in an
arbitrary complete complex Hilbert space, with a finite-dimensional trial
space and no dimension comparison. -/

/-- The equal-rank tangent bound from form bounds. -/
alias theorem6_3_equalRank_tanTheta_formBounds :=
  ExactTanTheta.theorem6_3_generalizedTanTheta_of_formBounds_equalRank

/-- The equal-rank tangent bound in the source's spectral-separation form. -/
alias theorem6_3_equalRank_tanTheta_ideal :=
  ExactTanTheta.theorem6_3_generalizedTanTheta_equalRank_spectral

/-! ### The equal-dimensional infinite/noncompact tangent theorem

The two aliases above still assume a finite-dimensional trial space.  The paper's
Section 2 claims the theorem for arbitrary equal-dimensional pairs in an infinite
Hilbert space, and its Appendix supplies the missing case by the finite-projector
cutoff/Ky-Fan limiting argument.  That passage is formalized in
`DavisKahan/TanTheta/Theorem63InfiniteTrial.lean`: the trial subspace carries **no**
dimension hypothesis, the tangent representative is exhibited with the paper's
approximation numbers (`tan (arcsin sᵢ)` over the directed sine block's approximation
numbers), and the bound holds in every Fan-dominant unitarily invariant ideal gauge.

The residual half is stated in the source's spectral-separation form and in form-bound
form; the perturbation companion assumes invariance of the trial space under the
perturbed operator, exactly as in the finite case. -/

/-- Section 2 tangent theorem, residual half, at arbitrary trial dimension and
ideal-gauge scope, spectral-separation form. -/
alias theorem6_3_equalDimension_tanTheta_ideal_spectral :=
  ExactTanTheta.theorem6_3_infiniteTrial_spectral_exists

/-- Section 2 tangent theorem, residual half, at arbitrary trial dimension and
ideal-gauge scope, form-bound form. -/
alias theorem6_3_equalDimension_tanTheta_ideal_formBounds :=
  ExactTanTheta.theorem6_3_infiniteTrial_of_formBounds_exists

/-- Section 2 tangent theorem, perturbation half, at arbitrary trial dimension and
ideal-gauge scope. -/
alias theorem6_3_equalDimension_tanTheta_perturbation :=
  TauCeti.DavisKahan.Section2.theorem6_3_perturbation_infiniteTrial

end GeneralizedTangent

section DoubleAngleSourceWrappers

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Source-numbered residual and perturbation form of the sine-double-angle
theorem at arbitrary rectangular ideal-gauge scope. -/
theorem section7_sinTwoTheta_source_ideal
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, u} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : IsSelfAdjointOperator E)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {beta alpha delta : ℝ} (hba : beta ≤ alpha) (hdelta : 0 < delta)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) beta)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) alpha)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (beta - delta) (alpha + delta),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hEmem : N.Mem E) :
    N.Mem (sinTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) ∧
    delta * N.gaugeReal (sinTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) ≤
      2 * N.gaugeReal E := by
  exact sinTwoTheta_addBounded_gauge_of_spectrum_gap
    N A hA E hE B S hB hS hba hdelta hBlow hBhigh hBcomplSpec hEmem

/-- Source-numbered tangent-double-angle theorem after Section 8 selects the
strict quarter-acute branch.

The bound carries the positive double-cosine denominator
`1 - 2 * directedGap ^ 2` (positive under the quarter-acute hypothesis).  This
factor is intrinsic to `tanTwoThetaIdealBlock = sinTwoThetaIdealBlock ∘L cos⁻¹`;
a bare `2 * N.gaugeReal E` on the right is strictly stronger than the tangent
construction supports, so the denominator is a required part of the statement,
not an artifact. -/
theorem section7_tanTwoTheta_source_ideal
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, u} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : IsSelfAdjointOperator E)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {beta alpha delta : ℝ} (hba : beta ≤ alpha) (hdelta : 0 < delta)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) beta)
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) alpha)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (beta - delta) (alpha + delta),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl))
    (hEmem : N.Mem E)
    (hquarter : IsQuarterAcute
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
        (addBounded_isSelfAdjoint A hA E hE) S hS)) :
    N.Mem (tanTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
        (addBounded_isSelfAdjoint A hA E hE) S hS) hquarter) ∧
    delta * N.gaugeReal (tanTwoThetaIdealBlock
      (selfAdjointSpectralSubspace A hA B hB)
      (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
        (addBounded_isSelfAdjoint A hA E hE) S hS) hquarter) ≤
      (2 * N.gaugeReal E) /
        (1 - 2 * directedGap
          (selfAdjointSpectralSubspace A hA B hB)
          (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
            (addBounded_isSelfAdjoint A hA E hE) S hS) ^ 2) := by
  exact tanTwoTheta_addBounded_gauge_of_spectrum_gap
    N A hA E hE B S hB hS hba hdelta hBlow hBhigh hBcomplSpec hEmem hquarter

end DoubleAngleSourceWrappers

end RemainingSourceSurface
end DavisKahan1970
end TauCeti
