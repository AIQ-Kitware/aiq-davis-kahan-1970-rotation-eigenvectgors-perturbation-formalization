/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Geometry.Angle.PaperOperatorAngle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The literal ambient `tan Θ` of Davis--Kahan

`DavisKahan/Geometry/Angle/PaperOperatorAngle.lean` builds the paper's literal
Hermitian angle `Θ = arcsin |P_U - P_V|` between two closed subspaces and its
sine and cosine.  This module adds the tangent, which is the object the second
conclusion of the Section 2 `tan θ` theorem is about.

The tangent is only an honest `tan` where the angle stays away from `π / 2`.
Mathlib's `Real.tan` is total, with `Real.tan (π / 2) = 0`, so `cfc Real.tan Θ`
is always defined; but the identity `cos Θ · tan Θ = sin Θ` — which is what
makes it *the tangent* — needs uniform transversality of the two subspaces, in
the form `‖sin Θ‖ < 1`.  That hypothesis is exactly what the tangent theorem's
right-hand side supplies when it is finite, so it is not a restriction of the
theory but a statement of where the theory lives.

## Main results

* `TauCeti.DavisKahanExt.paperTanAngleOperatorC`: the literal `tan Θ`.
* `TauCeti.DavisKahanExt.paperTanAngleOperatorC_nonneg`.
* `TauCeti.DavisKahanExt.paperCos_mul_paperTan`: `cos Θ · tan Θ = sin Θ` under
  uniform transversality.
* `TauCeti.DavisKahanExt.paperTanTwoAngleOperatorC`: the literal ambient
  `tan 2Θ`, the object of the second conclusion of the Section 2 `tan 2θ`
  theorem.
* `TauCeti.DavisKahanExt.spectrum_paperAngleOperatorC_lt_pi_div_four` and
  `TauCeti.DavisKahanExt.paperTanTwoAngleOperatorC_nonneg`: under uniform
  *quarter* transversality the doubled angle stays inside the principal branch.
* `TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC`: the **branch-free**
  ambient `|tan 2Θ|`, which is nonnegative with no hypothesis at all and agrees
  with `paperTanTwoAngleOperatorC` on the quarter-acute branch.  A unitarily
  invariant norm sees a self-adjoint operator through its singular values, so
  the two carry the same source conclusion.

## Where the estimates about these objects live

The whole-space `tan Θ` estimate `δ ‖tan Θ‖ ≤ ‖H‖` (Section 2, second
conclusion of the `tan θ` theorem; derived at Section 7 lines around equation
(7.6)) is proved in
`DavisKahan/Sources/DavisKahan1970/TanThetaAmbient.lean`, and the ambient
`tan 2Θ` estimate in
`DavisKahan/Sources/DavisKahan1970/TanTwoThetaAmbient.lean`.  The real-scalar
forms of both, and the real counterparts of the operators defined here, are in
`DavisKahan/Geometry/Angle/PaperOperatorAngleReal.lean` and
`DavisKahan/Sources/DavisKahan1970/AmbientReal.lean`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: the `tan θ` theorem of Section 2
  and Theorem 6.3.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The paper's literal ambient `tan Θ`, obtained by applying `tan` to the
Hermitian operator angle. -/
noncomputable def paperTanAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  cfc Real.tan (paperAngleOperatorC U V)

/-- `tan Θ` is self-adjoint. -/
theorem isSelfAdjoint_paperTanAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (paperTanAngleOperatorC U V) :=
  cfc_predicate _ (paperAngleOperatorC U V)

/-- `tan Θ` is nonnegative: the angle has spectrum in `[0, π/2]`, where the
tangent is nonnegative (and, at the endpoint, is `0` by Mathlib's totalisation
of `Real.tan`). -/
theorem paperTanAngleOperatorC_nonneg (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ paperTanAngleOperatorC U V := by
  refine cfc_nonneg fun t ht => ?_
  have h := spectrum_paperAngleOperatorC_subset_Icc U V ht
  exact Real.tan_nonneg_of_nonneg_of_le_pi_div_two h.1 h.2

/-- Under uniform transversality the angle stays strictly below `π / 2`. -/
theorem spectrum_paperAngleOperatorC_lt_pi_div_two
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hlt : ‖sinAngleOperatorC U V‖ < 1)
    {t : ℝ} (ht : t ∈ spectrum ℝ (paperAngleOperatorC U V)) :
    0 ≤ t ∧ t < Real.pi / 2 := by
  rw [paperAngleOperatorC,
    cfc_map_spectrum (R := ℝ) (f := Real.arcsin)
      (a := sinAngleOperatorC U V) (isSelfAdjoint_sinAngleOperatorC U V)
      Real.continuous_arcsin.continuousOn] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  have hsi := spectrum_sinAngleOperatorC_subset_Icc U V hs
  have hnorm : |s| ≤ ‖sinAngleOperatorC U V‖ * ‖(1 : E →L[ℂ] E)‖ :=
    spectrum.norm_le_norm_mul_of_mem hs
  have hone : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hslt : s < 1 := by
    have : |s| ≤ ‖sinAngleOperatorC U V‖ := by
      refine hnorm.trans ?_
      calc ‖sinAngleOperatorC U V‖ * ‖(1 : E →L[ℂ] E)‖
          ≤ ‖sinAngleOperatorC U V‖ * 1 :=
            mul_le_mul_of_nonneg_left hone (norm_nonneg _)
        _ = ‖sinAngleOperatorC U V‖ := mul_one _
    have hle : s ≤ ‖sinAngleOperatorC U V‖ := (le_abs_self s).trans this
    linarith
  exact ⟨Real.arcsin_nonneg.mpr hsi.1, Real.arcsin_lt_pi_div_two.mpr hslt⟩

/-- The paper's literal ambient `tan 2Θ`, obtained by applying `t ↦ tan (2 t)`
to the Hermitian operator angle.  This is the object the second conclusion of
the Section 2 `tan 2θ` theorem is about; it carries every principal angle
*twice*, so it is not a relabelling of the directed `tan 2Θ₀`. -/
noncomputable def paperTanTwoAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  cfc (fun t : ℝ => Real.tan (2 * t)) (paperAngleOperatorC U V)

/-- `tan 2Θ` is self-adjoint. -/
theorem isSelfAdjoint_paperTanTwoAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (paperTanTwoAngleOperatorC U V) :=
  cfc_predicate _ (paperAngleOperatorC U V)

/-- Under uniform *quarter* transversality the angle stays strictly below
`π / 4`, so the doubled angle stays inside the principal branch of the
tangent.  The threshold `√2 / 2 = sin (π / 4)` is the repository's
`IsQuarterAcute`. -/
theorem spectrum_paperAngleOperatorC_lt_pi_div_four
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hlt : ‖sinAngleOperatorC U V‖ < Real.sqrt 2 / 2)
    {t : ℝ} (ht : t ∈ spectrum ℝ (paperAngleOperatorC U V)) :
    0 ≤ t ∧ t < Real.pi / 4 := by
  rw [paperAngleOperatorC,
    cfc_map_spectrum (R := ℝ) (f := Real.arcsin)
      (a := sinAngleOperatorC U V) (isSelfAdjoint_sinAngleOperatorC U V)
      Real.continuous_arcsin.continuousOn] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  have hsi := spectrum_sinAngleOperatorC_subset_Icc U V hs
  have hnorm : |s| ≤ ‖sinAngleOperatorC U V‖ * ‖(1 : E →L[ℂ] E)‖ :=
    spectrum.norm_le_norm_mul_of_mem hs
  have hone : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hs' : s < Real.sqrt 2 / 2 := by
    have habs : |s| ≤ ‖sinAngleOperatorC U V‖ := by
      refine hnorm.trans ?_
      nlinarith [norm_nonneg (sinAngleOperatorC U V), norm_nonneg (1 : E →L[ℂ] E)]
    have := (le_abs_self s).trans habs
    linarith
  refine ⟨Real.arcsin_nonneg.mpr hsi.1, ?_⟩
  have hmem : Real.pi / 4 ∈ Set.Ioc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> [linarith [Real.pi_pos]; linarith [Real.pi_pos]]
  rw [Real.arcsin_lt_iff_lt_sin' hmem, Real.sin_pi_div_four]
  exact hs'

/-- `tan 2Θ` is nonnegative under uniform quarter transversality: every angle
lies in `[0, π/4)`, so the doubled angle lies in `[0, π/2)`. -/
theorem paperTanTwoAngleOperatorC_nonneg (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hlt : ‖sinAngleOperatorC U V‖ < Real.sqrt 2 / 2) :
    0 ≤ paperTanTwoAngleOperatorC U V := by
  refine cfc_nonneg fun t ht => ?_
  have h := spectrum_paperAngleOperatorC_lt_pi_div_four U V hlt ht
  exact Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith [h.1])
    (by linarith [h.2])

/-- The paper's ambient `|tan 2Θ|`, obtained by applying `t ↦ |tan (2 t)|` to
the Hermitian operator angle.

This is the *branch-free* ambient double-angle tangent.  A unitarily invariant
norm sees an operator only through its singular values, so for the self-adjoint
`tan 2Θ` it sees `|tan 2Θ|`; the two objects therefore carry the same source
conclusion.  They differ exactly when some principal angle exceeds `π/4`, where
`tan 2θ` turns negative — which is precisely the situation the quarter-acute
branch excludes and the printed theorem does not. -/
noncomputable def paperAbsTanTwoAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  cfc (fun t : ℝ => |Real.tan (2 * t)|) (paperAngleOperatorC U V)

/-- `|tan 2Θ|` is self-adjoint. -/
theorem isSelfAdjoint_paperAbsTanTwoAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (paperAbsTanTwoAngleOperatorC U V) :=
  cfc_predicate _ (paperAngleOperatorC U V)

/-- `|tan 2Θ|` is nonnegative, with **no** branch hypothesis: unlike
`paperTanTwoAngleOperatorC_nonneg`, this holds however far the principal angles
run past `π/4`. -/
theorem paperAbsTanTwoAngleOperatorC_nonneg (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ paperAbsTanTwoAngleOperatorC U V :=
  cfc_nonneg fun _ _ => abs_nonneg _

/-- In the quarter-acute branch the branch-free ambient tangent is the literal
one: every principal angle is below `π/4`, so `tan 2θ ≥ 0` throughout the
spectrum. -/
theorem paperAbsTanTwoAngleOperatorC_eq_paperTanTwoAngleOperatorC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hlt : ‖sinAngleOperatorC U V‖ < Real.sqrt 2 / 2) :
    paperAbsTanTwoAngleOperatorC U V = paperTanTwoAngleOperatorC U V := by
  refine cfc_congr fun t ht => ?_
  have h := spectrum_paperAngleOperatorC_lt_pi_div_four U V hlt ht
  exact abs_of_nonneg (Real.tan_nonneg_of_nonneg_of_le_pi_div_two
    (by linarith [h.1]) (by linarith [h.2]))

/-- **`cos Θ · tan Θ = sin Θ`**, under uniform transversality of the two
subspaces.  This is what makes `paperTanAngleOperatorC` the tangent rather than
an arbitrary functional calculus: it is the operator identity the paper uses
whenever it divides a sine block by a cosine block. -/
theorem paperCos_mul_paperTan (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hlt : ‖sinAngleOperatorC U V‖ < 1) :
    paperCosAngleOperatorC U V * paperTanAngleOperatorC U V =
      paperSinAngleOperatorC U V := by
  rw [paperCosAngleOperatorC, paperTanAngleOperatorC, paperSinAngleOperatorC,
    ← cfc_mul Real.cos Real.tan (paperAngleOperatorC U V)
      Real.continuous_cos.continuousOn
      (Real.continuousOn_tan.mono (by
        intro t ht
        have h := spectrum_paperAngleOperatorC_lt_pi_div_two U V hlt ht
        exact ne_of_gt (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [Real.pi_pos, h.1], h.2⟩)))]
  refine cfc_congr fun t ht => ?_
  have h := spectrum_paperAngleOperatorC_lt_pi_div_two U V hlt ht
  have hcos : Real.cos t ≠ 0 := by
    have : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, h.1], h.2⟩
    exact ne_of_gt this
  rw [Real.tan_eq_sin_div_cos]
  field_simp

end

end DavisKahanExt
end TauCeti
