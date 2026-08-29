/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.QuadraticFormBounds
public import ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Complex spectral order and quadratic forms

For bounded self-adjoint operators on complex Hilbert spaces, actual spectral
inclusions imply upper and lower quadratic-form bounds.  The continuous
functional calculus needed for this bridge is currently the scalar-specific
part; consumers such as Davis--Kahan should depend only on the resulting form
bounds.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `df036cd`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Original authors / copyright: Jon Crall, Claude Opus 4.8, GPT 5.6 High; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (enforced by `scripts/check_dependency_layers.py`).
-/

public section

namespace TauCeti
namespace SpectralOrder
namespace Complex

open TauCeti
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A spectral upper bound implies a quadratic-form upper bound. -/
theorem re_inner_le_of_spectrum_subset_Iic
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Iic c) (x : H) :
    RCLike.re ⟪T x, x⟫_ℂ ≤ c * ‖x‖ ^ 2 := by
  have hle : T ≤ algebraMap ℝ (H →L[ℂ] H) c :=
    le_algebraMap_of_spectrum_le (fun r hr => hσ hr) hT
  have hpos : (algebraMap ℝ (H →L[ℂ] H) c - T).IsPositive := by
    rw [← ContinuousLinearMap.nonneg_iff_isPositive]
    exact sub_nonneg.mpr hle
  have hx := hpos.re_inner_nonneg_left x
  have hcx : RCLike.re ⟪c • x, x⟫_ℂ = c * ‖x‖ ^ 2 := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
      RCLike.conj_ofReal, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  simp only [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply,
    one_apply_eq_self, inner_sub_left, map_sub] at hx
  rw [hcx] at hx
  linarith

/-- A spectral lower bound implies a quadratic-form lower bound. -/
theorem le_re_inner_of_spectrum_subset_Ici
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Ici c) (x : H) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_ℂ := by
  have hle : algebraMap ℝ (H →L[ℂ] H) c ≤ T :=
    algebraMap_le_of_le_spectrum (fun r hr => hσ hr) hT
  have hpos : (T - algebraMap ℝ (H →L[ℂ] H) c).IsPositive := by
    rw [← ContinuousLinearMap.nonneg_iff_isPositive]
    exact sub_nonneg.mpr hle
  have hx := hpos.re_inner_nonneg_left x
  have hcx : RCLike.re ⟪c • x, x⟫_ℂ = c * ‖x‖ ^ 2 := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
      RCLike.conj_ofReal, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  simp only [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply,
    one_apply_eq_self, inner_sub_left, map_sub] at hx
  rw [hcx] at hx
  linarith


/-- Spectral upper bound, packaged as a global upper form bound. -/
theorem upperFormBoundOn_top_of_spectrum_subset_Iic
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Iic c) :
    T.UpperFormBoundOn ⊤ c := by
  intro x _
  exact re_inner_le_of_spectrum_subset_Iic T hT hσ x

/-- Spectral lower bound, packaged as a global lower form bound. -/
theorem lowerFormBoundOn_top_of_spectrum_subset_Ici
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Ici c) :
    T.LowerFormBoundOn ⊤ c := by
  intro x _
  exact le_re_inner_of_spectrum_subset_Ici T hT hσ x

/-- A spectral upper bound for the actual restriction gives the corresponding
form bound on the reducing subspace. -/
theorem re_inner_le_on_subspace_of_restriction_spectrum_subset_Iic
    {A : H →L[ℂ] H} (hA : A.IsSymmetric)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Iic c)
    {x : H} (hx : x ∈ U) :
    RCLike.re ⟪A x, x⟫_ℂ ≤ c * ‖x‖ ^ 2 := by
  let : CompleteSpace U :=
    completeSpace_coe_iff_isComplete.mpr U.isComplete_coe_of_hasOrthogonalProjection
  have hres : IsSelfAdjoint (A.restrict hU) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (ContinuousLinearMap.IsSymmetric.restrict_of_invariant (A := A) hA hU)
  have h := re_inner_le_of_spectrum_subset_Iic
    (A.restrict hU) hres hσ (⟨x, hx⟩ : U)
  -- restates the hypothesis with the definition unfolded, the form the following
  -- step matches against.
  change RCLike.re ⟪A x, x⟫_ℂ ≤ c * ‖x‖ ^ 2 at h
  exact h

/-- A spectral lower bound for the actual restriction gives the corresponding
form bound on the reducing subspace. -/
theorem le_re_inner_on_subspace_of_restriction_spectrum_subset_Ici
    {A : H →L[ℂ] H} (hA : A.IsSymmetric)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Ici c)
    {x : H} (hx : x ∈ U) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ := by
  let : CompleteSpace U :=
    completeSpace_coe_iff_isComplete.mpr U.isComplete_coe_of_hasOrthogonalProjection
  have hres : IsSelfAdjoint (A.restrict hU) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (ContinuousLinearMap.IsSymmetric.restrict_of_invariant (A := A) hA hU)
  have h := le_re_inner_of_spectrum_subset_Ici
    (A.restrict hU) hres hσ (⟨x, hx⟩ : U)
  -- restates the hypothesis with the definition unfolded, the form the following
  -- step matches against.
  change c * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ at h
  exact h


/-- Restriction-spectrum upper bridge, packaged as a subspace form bound. -/
theorem upperFormBoundOn_of_restriction_spectrum_subset_Iic
    {A : H →L[ℂ] H} (hA : A.IsSymmetric)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Iic c) :
    A.UpperFormBoundOn U c := by
  intro x hx
  exact re_inner_le_on_subspace_of_restriction_spectrum_subset_Iic hA hU hσ hx

/-- Restriction-spectrum lower bridge, packaged as a subspace form bound. -/
theorem lowerFormBoundOn_of_restriction_spectrum_subset_Ici
    {A : H →L[ℂ] H} (hA : A.IsSymmetric)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Ici c) :
    A.LowerFormBoundOn U c := by
  intro x hx
  exact le_re_inner_on_subspace_of_restriction_spectrum_subset_Ici hA hU hσ hx



end Complex
end SpectralOrder
end TauCeti
