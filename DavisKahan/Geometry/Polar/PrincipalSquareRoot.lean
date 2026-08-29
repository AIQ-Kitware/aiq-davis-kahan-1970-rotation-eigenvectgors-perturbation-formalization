/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Geometry.Halmos.TwoProjections
-- supplies the two crossed intersections `halmosSourceDefect`/`halmosTargetDefect`, the
-- projection calculus they are described by, and `complementaryProjection_mul_projection`.
import DavisKahan.Geometry.Halmos.GenericRotationPredicates
-- supplies `IsPaperDirectRotation`, the five-field predicate whose characterisation this
-- module proves.  It lives in `TauCeti.DavisKahan`.
import DavisKahan.Geometry.Polar.DirectRotation
-- supplies `spectraReflectionProduct`, `spectraCanonicalIntertwiner`, the operator absolute
-- value `spectraOperatorAbsoluteValue` and the polar identities relating them.  That module
-- and everything beneath it are `Geometry`/`BoundedOperator` leaves and never import
-- the source layer, so this module is acyclic.

/-!
# Principal unitary square roots of the reflection product

Davis--Kahan 1970, Proposition 3.3, characterises the direct rotation between two subspaces
`U` and `V` as the *principal* unitary square root of the reflection product
`J_V J_U = spectraReflectionProduct U V`: the square root whose spectrum avoids the open left
half-plane, singled out among the square roots by the requirement that it carry the source
crossed intersection `U ⊓ Vᗮ` onto the target crossed intersection `Uᗮ ⊓ V`.

This module owns that characterisation and the block calculus it runs on.  It was extracted
from the Section 3 frontier module; the mathematics is unchanged.  The extraction is what
lets `DavisKahan/Sources/DavisKahan1970/Section3PrincipalSquareRoot.lean` -- the source-facing
home of Proposition 3.3 -- stop importing the former `DavisKahan.Section3`.

## Scope

Everything here is at the paper's arbitrary-pair scope: complex scalars, a complete space, and
**no acuteness hypothesis**.  Acuteness enters only downstream, where the principal branch is
identified with the canonical direct rotation.

## Main results

* `IsPrincipalUnitarySquareRoot`: unitary, squares to the given operator, spectrum in the
  closed right half-plane.
* `proposition3_3_principalSquareRoot_forward`: every direct rotation is such a square root,
  and carries one crossed intersection onto the other.
* `proposition3_3_principalSquareRoot_converse`: every such square root with the crossed
  mapping property is a direct rotation.
* `proposition3_3_principalSquareRoot_iff`: the two halves as a characterisation.
* `crossedDefect_image_of_unitary_sq`: the crossed mapping condition is free for any unitary
  square root that intertwines the projections.

The `BlockCalculus` section is the `U`-block bookkeeping shared with Proposition 3.1, which
stays in the frontier module and consumes it from here.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan


universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

section BlockCalculus

/-! ### The `U`-block calculus of a unitary intertwiner

These four identities are what both Proposition 3.1 and Proposition 3.3 run on, and they need
no acuteness.  They were originally inlined in Proposition 3.1's proof; Proposition 3.3's
forward direction needs the same seventy-five lines, so they live here once. -/

variable (T : H →L[ℂ] H)

omit [CompleteSpace H] in
/-- **Block decomposition of an operator relative to `U ⊕ Uᗮ`.** -/
theorem eq_sum_blocks (A : H →L[ℂ] H) :
    A = projection U * A * projection U + projection U * A * complementaryProjection U
      + complementaryProjection U * A * projection U
      + complementaryProjection U * A * complementaryProjection U := by
  have hone : projection U + complementaryProjection U = 1 := by
    rw [show complementaryProjection U = 1 - projection U from
      Submodule.starProjection_orthogonal' U]
    abel
  calc A = (projection U + complementaryProjection U) * A
        * (projection U + complementaryProjection U) := by rw [hone, one_mul, mul_one]
    _ = _ := by noncomm_ring

/-- **The `U`-blocks of `star T`**, for an operator whose diagonal compressions are self-adjoint
and whose crossed blocks are skew: the diagonal blocks are fixed and the off-diagonal ones are
sign-flipped. -/
theorem star_blocks_eq
    (hsource_sa : IsSelfAdjoint (projection U * T * projection U))
    (hcomplement_sa :
      IsSelfAdjoint (complementaryProjection U * T * complementaryProjection U))
    (hcrossed : complementaryProjection U * T * projection U =
      -star (projection U * T * complementaryProjection U)) :
    projection U * star T * projection U = projection U * T * projection U ∧
      complementaryProjection U * star T * complementaryProjection U
        = complementaryProjection U * T * complementaryProjection U ∧
      projection U * star T * complementaryProjection U
        = -(projection U * T * complementaryProjection U) ∧
      complementaryProjection U * star T * projection U
        = -(complementaryProjection U * T * projection U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hsource_sa.star_eq
    rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq, ← mul_assoc] at h
    exact h
  · have h := hcomplement_sa.star_eq
    rw [star_mul, star_mul, (isSelfAdjoint_starProjection Uᗮ).star_eq, ← mul_assoc] at h
    exact h
  · have h := congrArg star hcrossed
    rw [star_neg, star_star, star_mul, star_mul,
      (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection Uᗮ).star_eq, ← mul_assoc] at h
    exact h
  · have h := hcrossed
    rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection Uᗮ).star_eq, ← mul_assoc] at h
    rw [h, neg_neg]

/-- **A direct rotation squares to the reflection product**, with no acuteness hypothesis.

The reflection through `U` conjugates `star T` back to `T` -- the diagonal blocks survive and the
off-diagonal ones are negated twice -- and the intertwining turns that into `T * T = J_V J_U`. -/
theorem sq_eq_spectraReflectionProduct
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hintertwines : T * projection U = projection V * T)
    (hsource_sa : IsSelfAdjoint (projection U * T * projection U))
    (hcomplement_sa :
      IsSelfAdjoint (complementaryProjection U * T * complementaryProjection U))
    (hcrossed : complementaryProjection U * T * projection U =
      -star (projection U * T * complementaryProjection U)) :
    T * T = spectraReflectionProduct U V := by
  obtain ⟨e11, e22, e12, e21⟩ := star_blocks_eq U T hsource_sa hcomplement_sa hcrossed
  have hRsub : reflectionOperator U = projection U - complementaryProjection U := by
    rw [reflectionOperator_eq_projection_add_projection_sub_one U,
      show complementaryProjection U = 1 - projection U from
        Submodule.starProjection_orthogonal' U]
    abel
  have hkey : reflectionOperator U * star T * reflectionOperator U = T := by
    rw [hRsub]
    have expand : (projection U - complementaryProjection U) * star T
        * (projection U - complementaryProjection U)
        = projection U * star T * projection U
          - projection U * star T * complementaryProjection U
          - complementaryProjection U * star T * projection U
          + complementaryProjection U * star T * complementaryProjection U := by
      noncomm_ring
    rw [expand, e11, e12, e21, e22]
    conv_rhs => rw [eq_sum_blocks U T]
    abel
  have hTR : T * reflectionOperator U = reflectionOperator V * T := by
    rw [reflectionOperator_eq_projection_add_projection_sub_one U,
      reflectionOperator_eq_projection_add_projection_sub_one V,
      mul_sub, mul_add, mul_one, sub_mul, add_mul, one_mul, hintertwines]
  have hRV : reflectionOperator V = T * reflectionOperator U * star T := by
    have hTsT : T * star T = 1 := Unitary.mul_star_self_of_mem hunitary
    calc reflectionOperator V
        = reflectionOperator V * (T * star T) := by rw [hTsT, mul_one]
      _ = reflectionOperator V * T * star T := by rw [mul_assoc]
      _ = T * reflectionOperator U * star T := by rw [← hTR]
  have hexp : spectraReflectionProduct U V
      = T * (reflectionOperator U * star T * reflectionOperator U) := by
    change reflectionOperator V * reflectionOperator U = _
    rw [hRV]; noncomm_ring
  rw [hexp, hkey]

/-- **The Hermitian part of a direct rotation is twice its diagonal.**

The crossed blocks of `T` and of `star T` are negatives of one another, so they cancel in the
sum and only the diagonal survives, doubled. -/
theorem add_star_eq_two_diagonal
    (hsource_sa : IsSelfAdjoint (projection U * T * projection U))
    (hcomplement_sa :
      IsSelfAdjoint (complementaryProjection U * T * complementaryProjection U))
    (hcrossed : complementaryProjection U * T * projection U =
      -star (projection U * T * complementaryProjection U)) :
    T + star T =
      projection U * T * projection U + projection U * T * projection U
        + (complementaryProjection U * T * complementaryProjection U
          + complementaryProjection U * T * complementaryProjection U) := by
  obtain ⟨e11, e22, e12, e21⟩ := star_blocks_eq U T hsource_sa hcomplement_sa hcrossed
  calc T + star T
      = (projection U * T * projection U + projection U * T * complementaryProjection U
            + complementaryProjection U * T * projection U
            + complementaryProjection U * T * complementaryProjection U)
          + (projection U * star T * projection U
            + projection U * star T * complementaryProjection U
            + complementaryProjection U * star T * projection U
            + complementaryProjection U * star T * complementaryProjection U) := by
        rw [← eq_sum_blocks U T, ← eq_sum_blocks U (star T)]
    _ = _ := by rw [e11, e12, e21, e22]; abel

end BlockCalculus

/-- A unitary principal square root of the reflection product. -/
structure IsPrincipalUnitarySquareRoot
    (A T : H →L[ℂ] H) : Prop where
  unitary_mem : T ∈ unitary (H →L[ℂ] H)
  square_eq : T * T = A
  spectrum_right_half_plane :
    ∀ z ∈ spectrum ℂ T, 0 ≤ z.re

open scoped ComplexOrder in
/-- Davis--Kahan 1970, Proposition 3.3, converse direction.  The crossed
intersection mapping condition selects the correct square root on the
minus-one spectral subspace. -/
theorem proposition3_3_principalSquareRoot_converse
    (T : H →L[ℂ] H)
    (hroot : IsPrincipalUnitarySquareRoot
      (spectraReflectionProduct U V) T)
    (hcross : T '' (halmosSourceDefect U V : Set H) =
      (halmosTargetDefect U V : Set H)) :
    IsPaperDirectRotation U V T := by
  set A := spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) with hAdef
  have hunit := hroot.unitary_mem
  have hTsT : T * star T = 1 := Unitary.mul_star_self_of_mem hunit
  have hsTT : star T * T = 1 := Unitary.star_mul_self_of_mem hunit
  have hTnorm : IsStarNormal T := isStarNormal_of_mem_unitary hunit
  -- (1) accretive: 0 ≤ T + star T
  have hTpos : (0 : H →L[ℂ] H) ≤ T + star T := by
    have e2 : cfc (fun z : ℂ => star z) T = star T := by
      rw [cfc_star (R := ℂ) (fun z : ℂ => z) T, cfc_id' ℂ T]
    have e3 : T + star T = cfc (fun z : ℂ => z + star z) T := by
      rw [cfc_add (R := ℂ) T (fun z : ℂ => z) (fun z : ℂ => star z)
        continuous_id.continuousOn continuous_star.continuousOn, cfc_id' ℂ T, e2]
    rw [e3]
    apply cfc_nonneg
    intro z hz
    have hre : 0 ≤ z.re := hroot.spectrum_right_half_plane z hz
    rw [Complex.le_def]
    refine ⟨?_, ?_⟩
    · simp only [Complex.zero_re, Complex.add_re, Complex.star_def, Complex.conj_re]
      linarith
    · simp only [Complex.zero_im, Complex.add_im, Complex.star_def, Complex.conj_im]
      ring
  -- accretive quadratic form
  have haccr : ∀ y : H, 0 ≤ RCLike.re ⟪T y, y⟫_ℂ := by
    intro y
    have hp := (ContinuousLinearMap.nonneg_iff_isPositive (T + star T)).mp hTpos
    have hy := hp.re_inner_nonneg_left y
    rw [add_apply, inner_add_left, map_add] at hy
    have hstar : RCLike.re ⟪star T y, y⟫_ℂ = RCLike.re ⟪T y, y⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
      exact inner_re_symm (𝕜 := ℂ) y (T y)
    rw [hstar] at hy
    linarith
  -- (2) T + star T = A + A
  have hkey : T + star T = A + A := by
    have hsqeq : (T + star T) * (T + star T) = (A + A) * (A + A) := by
      have expand : (T + star T) * (T + star T)
          = T * T + T * star T + star T * T + star T * star T := by noncomm_ring
      have hstarTT : star T * star T = star (spectraReflectionProduct U V) := by
        rw [← star_mul, hroot.square_eq]
      have expandR : (A + A) * (A + A) = A * A + A * A + A * A + A * A := by noncomm_ring
      have hAA : A * A = star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V :=
        spectraOperatorAbsoluteValue_mul_self _
      rw [expand, hroot.square_eq, hTsT, hsTT, hstarTT, expandR, hAA]
      have hG : spectraReflectionProduct U V + 1 =
          spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V := by
        rw [add_comm]
        exact (spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct U V).symm
      have hstarG : star (spectraReflectionProduct U V) + 1 =
          star (spectraCanonicalIntertwiner U V) + star (spectraCanonicalIntertwiner U V) := by
        have h := congrArg star hG
        rwa [star_add, star_add, star_one] at h
      have hSS : spectraCanonicalIntertwiner U V + star (spectraCanonicalIntertwiner U V)
          = star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
            + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V :=
        spectraCanonicalIntertwiner_add_star U V
      calc spectraReflectionProduct U V + 1 + 1 + star (spectraReflectionProduct U V)
          = (spectraReflectionProduct U V + 1) + (star (spectraReflectionProduct U V) + 1) := by
            abel
        _ = (spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V)
              + (star (spectraCanonicalIntertwiner U V) + star (spectraCanonicalIntertwiner U V)) := by
            rw [hG, hstarG]
        _ = (spectraCanonicalIntertwiner U V + star (spectraCanonicalIntertwiner U V))
              + (spectraCanonicalIntertwiner U V + star (spectraCanonicalIntertwiner U V)) := by
            abel
        _ = (star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
              + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V)
            + (star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
              + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V) := by
            rw [hSS]
        _ = star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
              + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
              + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
              + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V := by
            abel
    have h2A_nonneg : (0 : H →L[ℂ] H) ≤ A + A :=
      add_nonneg (spectraOperatorAbsoluteValue_nonneg _) (spectraOperatorAbsoluteValue_nonneg _)
    calc T + star T
        = CFC.sqrt ((T + star T) * (T + star T)) := (CFC.sqrt_unique rfl hTpos).symm
      _ = CFC.sqrt ((A + A) * (A + A)) := by rw [hsqeq]
      _ = A + A := CFC.sqrt_unique rfl h2A_nonneg
  -- (3) T * A = S
  have hTA : T * A = spectraCanonicalIntertwiner U V := by
    have h1 : T * (T + star T) = spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V := by
      rw [mul_add, hroot.square_eq, hTsT,
        spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct U V]
      abel
    rw [hkey, mul_add] at h1
    -- h1 : T * A + T * A = S + S
    have hh : (2 : ℂ) • (T * A) = (2 : ℂ) • spectraCanonicalIntertwiner U V := by
      rw [two_smul, two_smul]; exact h1
    exact smul_right_injective (H →L[ℂ] H) (two_ne_zero) hh
  -- crossed_blocks and compressions and intertwines
  have hAP : A * projection U = projection U * A :=
    (spectraCanonicalAbsoluteValue_commute_projection U V).eq
  -- hXA
  have hXA : (T * projection U - projection V * T) * A = 0 := by
    have step : T * projection U * A = projection V * T * A := by
      calc T * projection U * A
          = T * (projection U * A) := by rw [mul_assoc]
        _ = T * (A * projection U) := by rw [← hAP]
        _ = (T * A) * projection U := by rw [mul_assoc]
        _ = spectraCanonicalIntertwiner U V * projection U := by rw [hTA]
        _ = projection V * spectraCanonicalIntertwiner U V :=
            spectraCanonicalIntertwiner_mul_projection U V
        _ = projection V * (T * A) := by rw [hTA]
        _ = projection V * T * A := by rw [mul_assoc]
    rw [sub_mul, step, sub_self]
  -- G = -1 on source defect
  have hGneg : ∀ z, z ∈ halmosSourceDefect U V → spectraReflectionProduct U V z = -z := by
    intro z hz
    obtain ⟨hPz, hQz⟩ := projections_apply_of_mem_halmosSourceDefect hz
    have hRU : reflectionOperator U z = z := by
      rw [Submodule.reflectionOperator_apply, hPz]; module
    rw [mul_apply_eq_comp, hRU, Submodule.reflectionOperator_apply, hQz]
    module
  -- X vanishes on ker A
  have hXker : ∀ x : H, A x = 0 → (T * projection U - projection V * T) x = 0 := by
    intro x hx
    have hSx : spectraCanonicalIntertwiner U V x = 0 := by
      have hn : ‖spectraCanonicalIntertwiner U V x‖ = 0 := by
        rw [← norm_spectraOperatorAbsoluteValue_apply (spectraCanonicalIntertwiner U V) x, ← hAdef,
          hx, norm_zero]
      exact norm_eq_zero.mp hn
    have hSexpand : spectraCanonicalIntertwiner U V x =
        projection V (projection U x) + complementaryProjection V (complementaryProjection U x) := by
      show (projection V * projection U + complementaryProjection V * complementaryProjection U) x = _
      simp only [add_apply, mul_apply_eq_comp]
    rw [hSexpand] at hSx
    have hmemV : projection V (projection U x) ∈ V := V.starProjection_apply_mem _
    have hmemVc : complementaryProjection V (complementaryProjection U x) ∈ Vᗮ :=
      Vᗮ.starProjection_apply_mem _
    have hab_inner : ⟪projection V (projection U x),
        complementaryProjection V (complementaryProjection U x)⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal hmemV hmemVc
    have hQPx : projection V (projection U x) = 0 := by
      have hself : ⟪projection V (projection U x), projection V (projection U x)⟫_ℂ = 0 := by
        calc ⟪projection V (projection U x), projection V (projection U x)⟫_ℂ
            = ⟪projection V (projection U x),
                projection V (projection U x)
                  + complementaryProjection V (complementaryProjection U x)⟫_ℂ
              - ⟪projection V (projection U x),
                complementaryProjection V (complementaryProjection U x)⟫_ℂ := by
              rw [inner_add_right]; ring
          _ = 0 := by rw [hSx, hab_inner, inner_zero_right]; ring
      exact inner_self_eq_zero.mp hself
    have hPxsource : projection U x ∈ halmosSourceDefect U V := by
      refine Submodule.mem_inf.mpr ⟨U.starProjection_apply_mem x, ?_⟩
      exact (Submodule.starProjection_apply_eq_zero_iff V).mp hQPx
    have hQcPcx : complementaryProjection V (complementaryProjection U x) = 0 := by
      have := hSx
      rw [hQPx, zero_add] at this
      exact this
    have hPcxtarget : complementaryProjection U x ∈ halmosTargetDefect U V := by
      refine Submodule.mem_inf.mpr ⟨Uᗮ.starProjection_apply_mem x, ?_⟩
      have := (Submodule.starProjection_apply_eq_zero_iff Vᗮ).mp hQcPcx
      simpa using this
    -- x = Px + Pᗮx
    have hxsplit : projection U x + complementaryProjection U x = x :=
      U.starProjection_add_starProjection_orthogonal x
    -- T (Px) ∈ target defect ⊆ V
    have hTPx_mem : T (projection U x) ∈ halmosTargetDefect U V := by
      have : T (projection U x) ∈ (halmosTargetDefect U V : Set H) := by
        rw [← hcross]
        exact Set.mem_image_of_mem T hPxsource
      exact this
    have hQTPx : projection V (T (projection U x)) = T (projection U x) :=
      V.starProjection_eq_self_iff.mpr (mem_halmosTargetDefect.mp hTPx_mem).2
    -- T (Pᗮx) ∈ source defect ⊆ Vᗮ
    have hTPcx_mem : T (complementaryProjection U x) ∈ halmosSourceDefect U V := by
      have hmem : complementaryProjection U x ∈ (halmosTargetDefect U V : Set H) := hPcxtarget
      rw [← hcross] at hmem
      obtain ⟨z, hzsource, hzeq⟩ := hmem
      have hTz : T (T z) = spectraReflectionProduct U V z := by
        have := congrArg (fun f : H →L[ℂ] H => f z) hroot.square_eq
        simpa [mul_apply_eq_comp] using this
      have : T (complementaryProjection U x) = -z := by
        rw [← hzeq, hTz, hGneg z hzsource]
      rw [this]
      exact Submodule.neg_mem _ hzsource
    have hQTPcx : projection V (T (complementaryProjection U x)) = 0 := by
      apply (Submodule.starProjection_apply_eq_zero_iff V).mpr
      exact (mem_halmosSourceDefect.mp hTPcx_mem).2
    -- assemble
    have hTx : T x = T (projection U x) + T (complementaryProjection U x) := by
      rw [← map_add, hxsplit]
    show (T * projection U - projection V * T) x = 0
    rw [sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
      hTx, map_add, hQTPx, hQTPcx, add_zero, sub_self]
  -- final intertwining: X = 0
  have hXeq : T * projection U = projection V * T := by
    have : CompleteSpace A.ker := A.isClosed_ker.completeSpace_coe
    have : A.ker.HasOrthogonalProjection := inferInstance
    have hrangeLe : A.range ≤ (T * projection U - projection V * T).ker := by
      rintro y ⟨z, rfl⟩
      rw [LinearMap.mem_ker]
      have := congrArg (fun f : H →L[ℂ] H => f z) hXA
      simpa [mul_apply_eq_comp] using this
    have hself : ContinuousLinearMap.adjoint A = A := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      exact (spectraOperatorAbsoluteValue_isSelfAdjoint _).star_eq
    have horthEq : A.kerᗮ = A.range.topologicalClosure := by
      have h1 : A.rangeᗮ = A.ker := by rw [A.orthogonal_range, hself]
      calc A.kerᗮ = A.rangeᗮᗮ := by rw [h1]
        _ = A.range.topologicalClosure := Submodule.orthogonal_orthogonal_eq_closure _
    have hOrthLe : A.kerᗮ ≤ (T * projection U - projection V * T).ker := by
      rw [horthEq]
      exact Submodule.topologicalClosure_minimal _ hrangeLe
        (T * projection U - projection V * T).isClosed_ker
    have hsub : ∀ x : H, (T * projection U - projection V * T) x = 0 := by
      intro x
      have hsplit := A.ker.starProjection_add_starProjection_orthogonal x
      rw [← hsplit, map_add]
      have h1 : (T * projection U - projection V * T) (A.ker.starProjection x) = 0 := by
        apply hXker
        exact LinearMap.mem_ker.mp (A.ker.starProjection_apply_mem x)
      have h2 : (T * projection U - projection V * T) (A.kerᗮ.starProjection x) = 0 :=
        LinearMap.mem_ker.mp (hOrthLe (A.kerᗮ.starProjection_apply_mem x))
      rw [h1, h2, add_zero]
    have hzero : T * projection U - projection V * T = 0 := ContinuousLinearMap.ext hsub
    exact sub_eq_zero.mp hzero
  -- crossed_blocks
  refine
    { unitary_mem := hunit
      intertwines := hXeq
      source_compression_nonnegative := ?_
      complement_compression_nonnegative := ?_
      crossed_blocks := ?_ }
  · intro x
    have h := haccr (projection U x)
    have hPTP : (projection U * T * projection U) x = projection U (T (projection U x)) := by
      simp only [mul_apply_eq_comp]
    have hsymm : ⟪projection U x, T (projection U x)⟫_ℂ
        = ⟪x, projection U (T (projection U x))⟫_ℂ :=
      U.starProjection_isSymmetric x (T (projection U x))
    have heq : RCLike.re ⟪x, (projection U * T * projection U) x⟫_ℂ
        = RCLike.re ⟪T (projection U x), projection U x⟫_ℂ := by
      rw [hPTP, ← hsymm]
      exact inner_re_symm (𝕜 := ℂ) _ _
    rw [heq]; exact h
  · intro x
    have h := haccr (complementaryProjection U x)
    have hPTP : (complementaryProjection U * T * complementaryProjection U) x
        = complementaryProjection U (T (complementaryProjection U x)) := by
      simp only [mul_apply_eq_comp]
    have hsymm : ⟪complementaryProjection U x, T (complementaryProjection U x)⟫_ℂ
        = ⟪x, complementaryProjection U (T (complementaryProjection U x))⟫_ℂ :=
      Uᗮ.starProjection_isSymmetric x (T (complementaryProjection U x))
    have heq : RCLike.re ⟪x, (complementaryProjection U * T * complementaryProjection U) x⟫_ℂ
        = RCLike.re ⟪T (complementaryProjection U x), complementaryProjection U x⟫_ℂ := by
      rw [hPTP, ← hsymm]
      exact inner_re_symm (𝕜 := ℂ) _ _
    rw [heq]; exact h
  · have hcomm : Commute (T + star T) (projection U) := by
      rw [hkey]
      exact (spectraCanonicalAbsoluteValue_commute_projection U V).add_left
        (spectraCanonicalAbsoluteValue_commute_projection U V)
    have hblock : complementaryProjection U * (T + star T) * projection U = 0 := by
      calc complementaryProjection U * (T + star T) * projection U
          = complementaryProjection U * ((T + star T) * projection U) := by rw [mul_assoc]
        _ = complementaryProjection U * (projection U * (T + star T)) := by rw [hcomm.eq]
        _ = (complementaryProjection U * projection U) * (T + star T) := by rw [mul_assoc]
        _ = 0 := by rw [complementaryProjection_mul_projection U, zero_mul]
    have hstar : star (projection U * T * complementaryProjection U)
        = complementaryProjection U * star T * projection U := by
      rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq,
        (isSelfAdjoint_starProjection Uᗮ).star_eq, ← mul_assoc]
    rw [hstar]
    have hsum : complementaryProjection U * T * projection U
        + complementaryProjection U * star T * projection U = 0 := by
      have h := hblock
      rw [mul_add, add_mul] at h
      exact h
    exact eq_neg_of_add_eq_zero_left hsum

/-! ### Proposition 3.3, forward direction

The converse above holds for an arbitrary pair, acute or not.  What was missing was the forward
half in the same generality: the printed proposition says *every* direct rotation is a principal
square root of the reflection product, and the compiled forward statements
(`complex_directRotation_sq`, `complex_directRotation_hermitianPart`) speak only about the
canonical acute one.

The block calculus below supplies it.  Three things have to be produced, and only the first two
cost anything:

* `T * T = J_V J_U`.  This is the argument already inside
  `proposition3_1_positivity_characterization`, extracted so that it is available without
  acuteness.
* spectrum in the closed right half-plane.  The Hermitian part of a direct rotation is *twice its
  diagonal*, the crossed blocks cancelling by `crossed_blocks`, so it is positive; for a normal
  operator that transfers to the spectrum through `cfc_nonneg_iff`.
* the crossed-intersection mapping condition.  This one is **free**: the converse takes it as a
  hypothesis, but in the forward direction it is a consequence.  Both crossed intersections sit
  inside the `-1` eigenspace of the reflection product, `T` and `star T` commute with that
  operator because `T * T` *is* it, and the intertwining moves `U` to `V` -- which pins the image
  down to the other crossed intersection.

The self-adjointness hypotheses on the diagonal compressions are the same two that
Proposition 3.1 needs, and for the same reason: `IsPaperDirectRotation` records the compressions
only through their numerical range, which does not by itself force `star T`'s diagonal blocks to
agree with `T`'s. -/

section PrincipalSquareRoot

variable (T : H →L[ℂ] H)

/-- **The Hermitian part of a direct rotation is a positive operator.** -/
theorem nonneg_add_star_of_isPaperDirectRotation (hT : IsPaperDirectRotation U V T)
    (hsource_sa : IsSelfAdjoint (projection U * T * projection U))
    (hcomplement_sa :
      IsSelfAdjoint (complementaryProjection U * T * complementaryProjection U)) :
    (0 : H →L[ℂ] H) ≤ T + star T := by
  have hP : (0 : H →L[ℂ] H) ≤ projection U * T * projection U := by
    refine (ContinuousLinearMap.nonneg_iff_isPositive _).mpr ?_
    refine ContinuousLinearMap.isPositive_def'.mpr ⟨hsource_sa, fun x => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm (𝕜 := ℂ)]
    exact hT.source_compression_nonnegative x
  have hPc : (0 : H →L[ℂ] H)
      ≤ complementaryProjection U * T * complementaryProjection U := by
    refine (ContinuousLinearMap.nonneg_iff_isPositive _).mpr ?_
    refine ContinuousLinearMap.isPositive_def'.mpr ⟨hcomplement_sa, fun x => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm (𝕜 := ℂ)]
    exact hT.complement_compression_nonnegative x
  rw [add_star_eq_two_diagonal U T hsource_sa hcomplement_sa hT.crossed_blocks]
  exact add_nonneg (add_nonneg hP hP) (add_nonneg hPc hPc)

omit [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
open scoped ComplexOrder in
/-- **A unitary whose Hermitian part is positive has spectrum in the closed right half-plane.**

This is what the word "principal" means for a square root of a unitary: among the square roots,
the one whose spectral arc avoids the open left half-plane.  For a normal element the transfer
from operator positivity to the spectrum is `cfc_nonneg_iff`. -/
theorem spectrum_re_nonneg_of_nonneg_add_star
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hpos : (0 : H →L[ℂ] H) ≤ T + star T) :
    ∀ z ∈ spectrum ℂ T, 0 ≤ z.re := by
  have hTnorm : IsStarNormal T := isStarNormal_of_mem_unitary hunitary
  have e2 : cfc (fun z : ℂ => star z) T = star T := by
    rw [cfc_star (R := ℂ) (fun z : ℂ => z) T, cfc_id' ℂ T]
  have e3 : T + star T = cfc (fun z : ℂ => z + star z) T := by
    rw [cfc_add (R := ℂ) T (fun z : ℂ => z) (fun z : ℂ => star z)
      continuous_id.continuousOn continuous_star.continuousOn, cfc_id' ℂ T, e2]
  rw [e3] at hpos
  have hz := (cfc_nonneg_iff (R := ℂ) (fun z : ℂ => z + star z) T
    (by fun_prop) hTnorm).mp hpos
  intro z hzmem
  have h := hz z hzmem
  rw [Complex.le_def] at h
  have hre : (0 : ℝ) ≤ (z + star z).re := h.1
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re] at hre
  linarith

/-! The two crossed intersections are exactly the part of the `-1` eigenspace of the reflection
product that lies in `U`, respectively in `V`.  That is the whole content of the crossed-mapping
condition in the forward direction. -/

omit [CompleteSpace H] in
/-- The reflection product acts as `-1` on the source crossed intersection. -/
theorem reflectionProduct_apply_eq_neg_of_mem_source {z : H}
    (hz : z ∈ halmosSourceDefect U V) : spectraReflectionProduct U V z = -z := by
  obtain ⟨hPz, hQz⟩ := projections_apply_of_mem_halmosSourceDefect hz
  have hRU : reflectionOperator U z = z := by
    rw [Submodule.reflectionOperator_apply, hPz]; module
  rw [mul_apply_eq_comp, hRU, Submodule.reflectionOperator_apply, hQz]
  module

omit [CompleteSpace H] in
/-- The reflection product acts as `-1` on the target crossed intersection. -/
theorem reflectionProduct_apply_eq_neg_of_mem_target {z : H}
    (hz : z ∈ halmosTargetDefect U V) : spectraReflectionProduct U V z = -z := by
  obtain ⟨hPz, hQz⟩ := projections_apply_of_mem_halmosTargetDefect hz
  have hRU : reflectionOperator U z = -z := by
    rw [Submodule.reflectionOperator_apply, hPz]; module
  rw [mul_apply_eq_comp, hRU, map_neg, Submodule.reflectionOperator_apply, hQz]
  module

omit [CompleteSpace H] in
/-- Inside `U`, the `-1` eigenspace of the reflection product is the source crossed
intersection. -/
theorem mem_halmosSourceDefect_of_reflectionProduct_apply_eq_neg {z : H} (hzU : z ∈ U)
    (hz : spectraReflectionProduct U V z = -z) : z ∈ halmosSourceDefect U V := by
  have hPz : projection U z = z := U.starProjection_eq_self_iff.mpr hzU
  have hRU : reflectionOperator U z = z := by
    rw [Submodule.reflectionOperator_apply, hPz]; module
  rw [mul_apply_eq_comp, hRU, Submodule.reflectionOperator_apply] at hz
  have h0 : (2 : ℂ) • projection V z = 0 := by
    have h := congrArg (fun w : H => w + z) hz
    simpa using h
  have hQz : projection V z = 0 := (smul_eq_zero.mp h0).resolve_left two_ne_zero
  exact Submodule.mem_inf.mpr ⟨hzU, (Submodule.starProjection_apply_eq_zero_iff V).mp hQz⟩

omit [CompleteSpace H] in
/-- Inside `V`, the `-1` eigenspace of the reflection product is the target crossed
intersection. -/
theorem mem_halmosTargetDefect_of_reflectionProduct_apply_eq_neg {z : H} (hzV : z ∈ V)
    (hz : spectraReflectionProduct U V z = -z) : z ∈ halmosTargetDefect U V := by
  have hQz : projection V z = z := V.starProjection_eq_self_iff.mpr hzV
  have hJV : reflectionOperator V z = z := by
    rw [Submodule.reflectionOperator_apply, hQz]; module
  have hinv := Submodule.reflectionOperator_involutive (𝕜 := ℂ) V
  have h1 : reflectionOperator V (reflectionOperator U z) = -z := by
    rw [← mul_apply_eq_comp]; exact hz
  have h2 : reflectionOperator V (reflectionOperator V (reflectionOperator U z))
      = reflectionOperator U z := by
    have h := congrArg (fun f : H →L[ℂ] H => f (reflectionOperator U z)) hinv
    simpa using h
  have hJU : reflectionOperator U z = -z := by
    rw [h1, map_neg, hJV] at h2
    exact h2.symm
  rw [Submodule.reflectionOperator_apply] at hJU
  have h0 : (2 : ℂ) • projection U z = 0 := by
    have h := congrArg (fun w : H => w + z) hJU
    simpa using h
  have hPz : projection U z = 0 := (smul_eq_zero.mp h0).resolve_left two_ne_zero
  exact Submodule.mem_inf.mpr ⟨(Submodule.starProjection_apply_eq_zero_iff U).mp hPz, hzV⟩

/-- **The crossed-intersection mapping condition is free.**

For *any* unitary that squares to the reflection product and intertwines the two
projections, the source crossed intersection is carried onto the target one.  Neither
positivity of the diagonal blocks nor acuteness enters: both crossed intersections sit
inside the `-1` eigenspace of the reflection product, `T` and `star T` commute with that
operator because `T * T` *is* it, and the intertwining moves `U` to `V`, which pins the
image down to the other crossed intersection.

Proposition 3.3's forward direction and printed Proposition 3.4 both consume this. -/
theorem crossedDefect_image_of_unitary_sq
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hsq : T * T = spectraReflectionProduct U V)
    (hintertwines : T * projection U = projection V * T) :
    T '' (halmosSourceDefect U V : Set H) = (halmosTargetDefect U V : Set H) := by
  have hTsT : T * star T = 1 := Unitary.mul_star_self_of_mem hunitary
  have hsTT : star T * T = 1 := Unitary.star_mul_self_of_mem hunitary
  -- `T` and `star T` both commute with the reflection product, because it *is* `T * T`.
  have hRT : ∀ x : H,
      spectraReflectionProduct U V (T x) = T (spectraReflectionProduct U V x) := by
    intro x
    have h1 : spectraReflectionProduct U V * T = T * spectraReflectionProduct U V := by
      rw [← hsq]; noncomm_ring
    have h := congrArg (fun f : H →L[ℂ] H => f x) h1
    simpa [mul_apply_eq_comp] using h
  have hRsT : ∀ x : H,
      spectraReflectionProduct U V (star T x) = star T (spectraReflectionProduct U V x) := by
    intro x
    have h1 : spectraReflectionProduct U V * star T = star T * spectraReflectionProduct U V := by
      rw [← hsq]
      calc T * T * star T = T * (T * star T) := by noncomm_ring
        _ = T := by rw [hTsT, mul_one]
        _ = star T * T * T := by rw [hsTT, one_mul]
    have h := congrArg (fun f : H →L[ℂ] H => f x) h1
    simpa [mul_apply_eq_comp] using h
  -- The intertwining moves `U` to `V`, and its adjoint moves `V` back to `U`.
  have hTU : ∀ x ∈ U, T x ∈ V := by
    intro x hx
    have h := congrArg (fun f : H →L[ℂ] H => f x) hintertwines
    simp only [mul_apply_eq_comp] at h
    rw [U.starProjection_eq_self_iff.mpr hx] at h
    exact V.starProjection_eq_self_iff.mp h.symm
  have hstarInt : projection U * star T = star T * projection V := by
    have h := congrArg star hintertwines
    rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection V).star_eq] at h
    exact h
  have hsTV : ∀ y ∈ V, star T y ∈ U := by
    intro y hy
    have h := congrArg (fun f : H →L[ℂ] H => f y) hstarInt
    simp only [mul_apply_eq_comp] at h
    rw [V.starProjection_eq_self_iff.mpr hy] at h
    exact U.starProjection_eq_self_iff.mp h
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    refine mem_halmosTargetDefect_of_reflectionProduct_apply_eq_neg U V
      (hTU x (mem_halmosSourceDefect.mp hx).1) ?_
    rw [hRT x, reflectionProduct_apply_eq_neg_of_mem_source U V hx, map_neg]
  · intro y hy
    refine ⟨star T y, ?_, ?_⟩
    · refine mem_halmosSourceDefect_of_reflectionProduct_apply_eq_neg U V
        (hsTV y (mem_halmosTargetDefect.mp hy).2) ?_
      rw [hRsT y, reflectionProduct_apply_eq_neg_of_mem_target U V hy, map_neg]
    · have h := congrArg (fun f : H →L[ℂ] H => f y) hTsT
      simpa [mul_apply_eq_comp] using h

/-- **Davis--Kahan 1970, Proposition 3.3, forward direction, with no acuteness hypothesis.**

Every direct rotation is a principal unitary square root of the reflection product, *and* it
carries the source crossed intersection onto the target one.  The second conclusion is the
mapping condition that the converse takes as a hypothesis; here it comes out rather than
going in (`crossedDefect_image_of_unitary_sq`). -/
theorem proposition3_3_principalSquareRoot_forward
    (hT : IsPaperDirectRotation U V T)
    (hsource_sa : IsSelfAdjoint (projection U * T * projection U))
    (hcomplement_sa :
      IsSelfAdjoint (complementaryProjection U * T * complementaryProjection U)) :
    IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T ∧
      T '' (halmosSourceDefect U V : Set H) = (halmosTargetDefect U V : Set H) := by
  have hsq := sq_eq_spectraReflectionProduct U V T hT.unitary_mem hT.intertwines
    hsource_sa hcomplement_sa hT.crossed_blocks
  have hpos := nonneg_add_star_of_isPaperDirectRotation U V T hT hsource_sa hcomplement_sa
  have hspec := spectrum_re_nonneg_of_nonneg_add_star T hT.unitary_mem hpos
  exact ⟨⟨hT.unitary_mem, hsq, hspec⟩,
    crossedDefect_image_of_unitary_sq U V T hT.unitary_mem hsq hT.intertwines⟩

/-- **Davis--Kahan 1970, Proposition 3.3, forward direction, from the printed hypotheses.**

The source says the direct rotation has **positive diagonal blocks**; this repository's
`IsPaperDirectRotation` records them only through their numerical range, which is strictly
weaker and is why `proposition3_3_principalSquareRoot_forward` has to ask for self-adjointness
separately.  Stated with operator positivity, as printed, no side hypothesis is needed at all:
a positive operator is self-adjoint and its numerical range is nonnegative, so both weaker
conditions come for free. -/
theorem proposition3_3_principalSquareRoot_forward_of_nonneg_blocks
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hintertwines : T * projection U = projection V * T)
    (hcrossed : complementaryProjection U * T * projection U =
      -star (projection U * T * complementaryProjection U))
    (hsource_pos : (0 : H →L[ℂ] H) ≤ projection U * T * projection U)
    (hcomplement_pos :
      (0 : H →L[ℂ] H) ≤ complementaryProjection U * T * complementaryProjection U) :
    IsPaperDirectRotation U V T ∧
      IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T ∧
      T '' (halmosSourceDefect U V : Set H) = (halmosTargetDefect U V : Set H) := by
  have hsp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hsource_pos
  have hcp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hcomplement_pos
  have hT : IsPaperDirectRotation U V T :=
    { unitary_mem := hunitary
      intertwines := hintertwines
      source_compression_nonnegative := fun x => by
        rw [inner_re_symm (𝕜 := ℂ)]
        exact hsp.re_inner_nonneg_left x
      complement_compression_nonnegative := fun x => by
        rw [inner_re_symm (𝕜 := ℂ)]
        exact hcp.re_inner_nonneg_left x
      crossed_blocks := hcrossed }
  exact ⟨hT, proposition3_3_principalSquareRoot_forward U V T hT hsp.isSelfAdjoint
    hcp.isSelfAdjoint⟩

open scoped ComplexOrder in
/-- **Davis--Kahan 1970, Proposition 3.3, as a characterisation**, for an arbitrary pair of
subspaces.

A unitary whose diagonal `U`-compressions are self-adjoint is a direct rotation exactly when it
is a principal square root of the reflection product carrying one crossed intersection onto the
other.

The two hypotheses are needed only for the forward implication; the converse,
`proposition3_3_principalSquareRoot_converse`, holds for *every* principal square root with the
mapping property, and should be used directly when they are not available. -/
theorem proposition3_3_principalSquareRoot_iff
    (hsource_sa : IsSelfAdjoint (projection U * T * projection U))
    (hcomplement_sa :
      IsSelfAdjoint (complementaryProjection U * T * complementaryProjection U)) :
    IsPaperDirectRotation U V T ↔
      (IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T ∧
        T '' (halmosSourceDefect U V : Set H) = (halmosTargetDefect U V : Set H)) :=
  ⟨fun hT => proposition3_3_principalSquareRoot_forward U V T hT hsource_sa hcomplement_sa,
    fun h => proposition3_3_principalSquareRoot_converse U V T h.1 h.2⟩

end PrincipalSquareRoot

end DavisKahan
end TauCeti
