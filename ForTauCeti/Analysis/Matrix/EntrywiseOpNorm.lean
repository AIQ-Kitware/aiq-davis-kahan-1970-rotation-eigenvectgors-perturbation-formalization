/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Staged for Tau Ceti, roadmap topic T19.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/PiL2.lean`
(the `ℓ¹ ≤ √card · ℓ²` bound) and `Mathlib/Analysis/Matrix/Normed.lean` (the
entrywise → `ℓ²`-operator-norm bound).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Chebyshev


/-! # `ℓ¹`–`ℓ²` and entrywise–operator norm comparisons

Two elementary norm comparisons that are absent from Mathlib (which has the
`ℓ²`-operator-norm API in `Mathlib/Analysis/CStarAlgebra/Matrix.lean` but no
bound of it by the entrywise norm):

* on `EuclideanSpace 𝕜 ι`, `∑ i, ‖x i‖ ≤ √(card ι) · ‖x‖` (Cauchy–Schwarz /
  Chebyshev);
* for a real `n × n` matrix with entries bounded by `ε`, the induced Euclidean
  operator `Matrix.toEuclideanLin A` has `‖A x‖ ≤ n ε ‖x‖`.

## Main results

* `TauCeti.sum_norm_le_sqrt_card_mul_norm`
* `TauCeti.norm_toEuclideanLin_le_of_entry_le`

The matrix bound's constant `n` is loose (the Frobenius bound gives `√(card)`);
it is the form produced by an entrywise sup bound and consumed by operator-norm
spectral-perturbation arguments.

**The matrix bound is stated over `ℝ`, and the `RCLike` form is open — but it is
not the routine transport an earlier version of this docstring promised.**
`Matrix.toEuclideanLin` over a general `𝕜` carries the conjugate-linear
convention on one side, so the entrywise hypothesis composes through `‖·‖` rather
than through the real absolute value and **the factor `n` has to be re-derived**
rather than transported.  Restating the real proof with `[RCLike 𝕜]` written over
it is the move the operator-ideal roadmap's generality bar forbids, and it is the
first thing a reader who trusts the word *routine* will try.  The `ℓ¹`-versus-`ℓ²`
companion, `sum_norm_le_sqrt_card_mul_norm`, is already `RCLike` and is not
affected.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.Matrix.EntrywiseOpNorm`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `7366186`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped BigOperators
open Matrix

/--
**`ℓ¹ ≤ √card · ℓ²` on Euclidean space.** For `x : EuclideanSpace 𝕜 ι`,
`∑ i, ‖x i‖ ≤ √(card ι) · ‖x‖`.
-/
theorem sum_norm_le_sqrt_card_mul_norm {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]
    (x : EuclideanSpace 𝕜 ι) :
    ∑ i, ‖x i‖ ≤ Real.sqrt (Fintype.card ι) * ‖x‖ := by
  have hcs : (∑ i, ‖x i‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
    simpa [Finset.card_univ] using
      sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => ‖x i‖)
  have hnorm : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := EuclideanSpace.norm_sq_eq x
  have hsum_nonneg : 0 ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hrhs_nonneg : 0 ≤ Real.sqrt (Fintype.card ι) * ‖x‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsq : (∑ i, ‖x i‖) ^ 2 ≤ (Real.sqrt (Fintype.card ι) * ‖x‖) ^ 2 := by
    have hrw : (Real.sqrt (Fintype.card ι) * ‖x‖) ^ 2 = (Fintype.card ι : ℝ) * ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (Fintype.card ι : ℝ))]
    rw [hrw, hnorm]; exact hcs
  exact (abs_le_of_sq_le_sq' hsq hrhs_nonneg).2

/--
**Entrywise → Euclidean operator-norm bound.** If every entry of a real
`n × n` matrix `A` has `|A i j| ≤ ε`, then the operator `Matrix.toEuclideanLin A`
satisfies `‖A x‖ ≤ n ε ‖x‖` for all `x`.
-/
theorem norm_toEuclideanLin_le_of_entry_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {ε : ℝ} (hentry : ∀ i j, |A i j| ≤ ε) (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin A x‖ ≤ (n : ℝ) * ε * ‖x‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hzero : Matrix.toEuclideanLin A x = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]; simp
  · have hε : 0 ≤ ε := (abs_nonneg _).trans (hentry ⟨0, hn⟩ ⟨0, hn⟩)
    -- Row-wise: `|(A x) i| ≤ ε ∑ |x j| ≤ ε √n ‖x‖`.
    have hrow : ∀ i : Fin n,
        |(Matrix.toEuclideanLin A x) i| ≤ ε * (Real.sqrt n * ‖x‖) := by
      intro i
      have happ : (Matrix.toEuclideanLin A x) i = ∑ j : Fin n, A i j * x j := by
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        change (A.mulVec (WithLp.ofLp x)) i = _
        simp [Matrix.mulVec, dotProduct]
      calc
        |(Matrix.toEuclideanLin A x) i|
            = |∑ j : Fin n, A i j * x j| := by rw [happ]
          _ ≤ ∑ j : Fin n, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j : Fin n, |A i j| * |x j| := by simp [abs_mul]
          _ ≤ ∑ j : Fin n, ε * |x j| :=
                Finset.sum_le_sum fun j _ =>
                  mul_le_mul_of_nonneg_right (hentry i j) (abs_nonneg _)
          _ = ε * ∑ j : Fin n, |x j| := by rw [Finset.mul_sum]
          _ ≤ ε * (Real.sqrt n * ‖x‖) := by
                refine mul_le_mul_of_nonneg_left ?_ hε
                simpa using sum_norm_le_sqrt_card_mul_norm x
    -- Sum the squared rows.
    have hnorm_sq : ‖Matrix.toEuclideanLin A x‖ ^ 2
        ≤ (n : ℝ) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
      have hexp : ‖Matrix.toEuclideanLin A x‖ ^ 2
          = ∑ i : Fin n, |(Matrix.toEuclideanLin A x) i| ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs]
      have hpt : ∀ i : Fin n,
          |(Matrix.toEuclideanLin A x) i| ^ 2 ≤ (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
        intro i
        rw [sq, sq]
        exact mul_self_le_mul_self (abs_nonneg _) (hrow i)
      rw [hexp]
      calc
        ∑ i : Fin n, |(Matrix.toEuclideanLin A x) i| ^ 2
            ≤ ∑ _i : Fin n, (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
              apply Finset.sum_le_sum
              intro i _
              exact hpt i
          _ = (n : ℝ) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    -- Take square roots.
    have hrhs_nonneg : 0 ≤ (n : ℝ) * ε * ‖x‖ := by positivity
    have hsq_eq : ((n : ℝ) * ε * ‖x‖) ^ 2 = (n : ℝ) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
      have hs : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      calc ((n : ℝ) * ε * ‖x‖) ^ 2
          = (n : ℝ) * ((n : ℝ) * (ε ^ 2 * ‖x‖ ^ 2)) := by ring
        _ = (n : ℝ) * ((Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) * (ε ^ 2 * ‖x‖ ^ 2)) := by
              rw [hs]
        _ = (n : ℝ) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by ring
    have hle : ‖Matrix.toEuclideanLin A x‖ ^ 2 ≤ ((n : ℝ) * ε * ‖x‖) ^ 2 := by
      rw [hsq_eq]; exact hnorm_sq
    exact (abs_le_of_sq_le_sq' hle hrhs_nonneg).2

end TauCeti
