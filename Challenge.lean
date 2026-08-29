/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
import Mathlib

/-!
# The Davis–Kahan operator-norm sin-Θ theorem

## What this says

Let `T` and `S` be symmetric operators on a finite-dimensional inner product space
over `ℝ` or `ℂ`. Let `U` be a subspace invariant under `T` on which the quadratic
form of `T` sits at or above `c + g`, and let `V` be a subspace invariant under `S`
on which the quadratic form of `S` sits at or below `c`. So the two subspaces are
associated with parts of the two spectra separated by a gap of width `g > 0`. If
`S` differs from `T` by at most `ε` in operator norm, then

  `‖P_V ∘ P_U‖ ≤ ε / g`

where `P_U` and `P_V` are the orthogonal projections. The left-hand side is
`‖sin Θ‖`, the largest sine of a principal angle between `U` and `V`: it vanishes
exactly when `U ⊆ V ᗮ`… more usefully, it measures how far `U` is from being
orthogonal to `V`, and the bound says a small perturbation cannot rotate a
spectrally separated subspace far.

## Why this is the interesting statement

This is the sin-Θ theorem, the central estimate of Davis and Kahan's paper and one
of the standard tools of numerical linear algebra, operator theory, and — through
its statistical descendants — high-dimensional statistics. It is the reason one can
say that computed invariant subspaces are accurate: it converts a bound on the
*residual* of an operator into a bound on the *angle* of a subspace, which is what
an eigenvalue computation actually needs.

Three features of this form are worth naming. The bound is **dimension-free**: `ε`
and `g` are the only quantities on the right, with no dependence on the dimension
of `E` or of the subspaces. The separation hypothesis is **one-sided and given by
quadratic forms**, which is how the theorem is used in practice — one does not
need the spectra themselves, only that the form of `T` on `U` dominates the form
of `S` on `V` by `g`. And the subspaces are **not assumed to be spectral
subspaces** of any particular eigenvalue set: invariance plus the form separation
is enough.

## Source

Chandler Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
III*, SIAM Journal on Numerical Analysis 7(1), 1970, 1–46,
<https://doi.org/10.1137/0707001>. See also R. Bhatia, *Matrix Analysis*, Chapter
VII.

The accompanying development formalizes the paper considerably more broadly than
this entry — including the unbounded self-adjoint statement for arbitrary
unitarily invariant norms, which is the scope the paper actually claims. This
entry compares the operator-norm form, whose statement can be written in ordinary
Mathlib vocabulary; the general one cannot, because it needs a unitarily invariant
norm class and a spectral-subspace API that are not in Mathlib.

## Comparator note

The proof below is a deliberate statement-side placeholder. The proof lives in the
solution module, which supplies it from the ordinary library development: it
extends `T` and `S` to globally coercive and globally bounded operators using the
invariance of `U` and `V`, derives a Sylvester relation for `P_U ∘ P_V`, and
applies a Sylvester norm bound.
-/

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E] {T S : E →ₗ[𝕜] E}

/-- **The Davis–Kahan operator-norm sin-Θ theorem.**

`T` and `S` are symmetric; `U` is `T`-invariant with the quadratic form of `T`
bounded below by `c + g` on it; `V` is `S`-invariant with the quadratic form of `S`
bounded above by `c` on it; and `S - T` has norm at most `ε`. Then the sine of the
largest principal angle between `U` and `V`, namely `‖P_V ∘ P_U‖`, is at most
`ε / g`.

The bound does not depend on the dimension of `E` or of either subspace. -/
theorem norm_starProjection_comp_starProjection_le (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {c g ε : ℝ} (hg : 0 < g)
    (hU : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hV : ∀ x ∈ V, RCLike.re ⟪S x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ‖V.starProjection ∘L U.starProjection‖ ≤ ε / g := by
  sorry

end TauCeti
