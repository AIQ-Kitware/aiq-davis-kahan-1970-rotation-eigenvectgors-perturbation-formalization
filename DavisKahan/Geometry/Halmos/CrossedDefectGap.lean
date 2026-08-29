/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.BoundedOperator.Compat
import DavisKahan.Geometry.Halmos.GenericRotationPredicates
import ForTauCeti.Analysis.InnerProductSpace.AngleGeometry

/-!
# Davis--Kahan 1970, standing assumption (3.5): the symmetric gap is directed

Section 3 of the paper runs under a standing assumption, printed as (3.5), that
the two crossed intersections `U ⊓ Vᗮ` and `Uᗮ ⊓ V` carry the same data.  This
module records what that assumption buys at the level of gaps:

`subspaceGap U V = directedGap U V`.

The hypothesis is `CrossedDefectsEquivalent`, the repository's *constructive*
form of (3.5) — a linear isometric identification of the two crossed defects,
not an equality of cardinals.  Nothing stronger is used, and in fact only its
qualitative shadow is consumed: one crossed defect is trivial exactly when the
other is.

## What carries the mathematics

Everything except the transfer of triviality across the identification is
generic two-subspace geometry and lives in `ForTauCeti`:

* `Submodule.directedProjectionGap_le_of_inf_orthogonal_eq_bot` — a single
  vanishing crossed intersection already reverses the directed estimate;
* `Submodule.directedProjectionGap_eq_one_of_inf_orthogonal_ne_bot` — a nonzero
  crossed intersection pins its directed gap at `1`;
* `Submodule.projectionGap_eq_directedProjectionGap_of_inf_orthogonal_eq_bot_iff`
  — the combination, through `projectionGap_eq_max_directedProjectionGap`.

## Why (3.5) is not implied by (1.5)

`Geometry/Halmos/BilateralShiftExample.lean` builds the separating pair: on
`ℓ²(ℤ)` the shift-related half-spaces satisfy (1.5) while their source crossed
defect is a line and their target crossed defect is zero.  The two directed gaps
of that pair are `1` and `0`, so `directedGap_comm_of_crossedDefectsEquivalent`
fails on it outright; that is recorded there, next to the pair, as
`directedGap_asymmetric_coordinateHalfSpace`.  The paper's own Remark, which
reads that pair as the separation of (1.5) from (3.5), is
`DavisKahan1970.remark3_2_bilateralShift_separates_dimensionHypotheses`.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- A submodule linearly isometric to a trivial submodule is itself trivial.

Only surjectivity and linearity are used, so the isometry hypothesis is more
than needed; it is kept because `CrossedDefectsEquivalent` supplies exactly
this datum. -/
theorem eq_bot_of_linearIsometryEquiv {K L : Submodule 𝕜 H} (e : K ≃ₗᵢ[𝕜] L)
    (hK : K = ⊥) : L = ⊥ := by
  refine (Submodule.eq_bot_iff L).mpr fun x hx => ?_
  have hzero : e.symm ⟨x, hx⟩ = 0 := by
    have hmem : ((e.symm ⟨x, hx⟩ : K) : H) ∈ K := (e.symm ⟨x, hx⟩).2
    exact Subtype.ext ((Submodule.eq_bot_iff K).mp hK _ hmem)
  have hnorm : ‖(⟨x, hx⟩ : L)‖ = 0 := by
    rw [← e.symm.norm_map ⟨x, hx⟩, hzero, norm_zero]
  simpa using congrArg Subtype.val (norm_eq_zero.mp hnorm)

omit [CompleteSpace H] in
/-- **The qualitative content of (3.5).**

Under the crossed-defect equivalence the source crossed intersection `U ⊓ Vᗮ`
is trivial exactly when the target crossed intersection `Uᗮ ⊓ V` is.  This is
the only consequence of (3.5) that the gap identity consumes. -/
theorem halmosSourceDefect_eq_bot_iff_halmosTargetDefect_eq_bot
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : CrossedDefectsEquivalent U V) :
    halmosSourceDefect U V = ⊥ ↔ halmosTargetDefect U V = ⊥ := by
  obtain ⟨e⟩ := h
  exact ⟨eq_bot_of_linearIsometryEquiv e, eq_bot_of_linearIsometryEquiv e.symm⟩

/-- **Under (3.5) the two directed gaps agree.**

Either both crossed defects vanish, and each directed gap bounds the other by
`Submodule.directedProjectionGap_le_of_inf_orthogonal_eq_bot`, or neither does
and both directed gaps equal `1`.

This is the statement that fails on the bilateral-shift pair of the Remark
after Proposition 3.2, where the two sides are `1` and `0`. -/
theorem directedGap_comm_of_crossedDefectsEquivalent
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : CrossedDefectsEquivalent U V) :
    directedGap U V = directedGap V U :=
  U.directedProjectionGap_comm_of_inf_orthogonal_eq_bot_iff V
    (halmosSourceDefect_eq_bot_iff_halmosTargetDefect_eq_bot U V h)

/-- **Davis--Kahan 1970, the effect of standing assumption (3.5) on the gap.**

The symmetric projection gap `‖P_U - P_V‖` is the maximum of the two directed
gaps, so under (3.5) it is either one of them.  This is the identification the
paper performs silently whenever it reads a directed `sin Θ` estimate as a
statement about the maximal angle, and it replaces the equal-`finrank`
conversion that finite-dimensional consumers currently use. -/
theorem subspaceGap_eq_directedGap_of_crossedDefectsEquivalent
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : CrossedDefectsEquivalent U V) :
    subspaceGap U V = directedGap U V :=
  U.projectionGap_eq_directedProjectionGap_of_inf_orthogonal_eq_bot_iff V
    (halmosSourceDefect_eq_bot_iff_halmosTargetDefect_eq_bot U V h)

omit [CompleteSpace H] in
/-- **In the nonacute case the crossed defect spaces are nonzero.**

Acuteness of a pair is the vanishing of both crossed intersections `U ⊓ Vᗮ` and
`Uᗮ ⊓ V`, so failing to be acute makes at least one of them nonzero; the
identification supplied by (3.5) then transports that to the source defect. -/
theorem halmosSourceDefect_ne_bot_of_not_isAcute
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hdefect : CrossedDefectsEquivalent U V) (hnonacute : ¬ TauCeti.IsAcute U V) :
    halmosSourceDefect U V ≠ ⊥ := by
  intro hbot
  exact hnonacute (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mpr
    ⟨hbot, (halmosSourceDefect_eq_bot_iff_halmosTargetDefect_eq_bot U V hdefect).mp hbot⟩)

end DavisKahan
end TauCeti
