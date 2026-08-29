/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/SpectralTheory/Real/SpectralBridge.lean`.
* Extraction class: **moved**, not restated.  The five theorems are the **real-scalar
  counterparts** of `SpectralOrder/Complex.lean`, name for name, and they were sitting in the
  paper library while depending on nothing from it: their only `DavisKahan` import was the
  alias layer `BoundedOperator/Compat.lean`, whose two names used here -- `Reduces` and
  `opNorm_starProjection_sub_le_of_formBounds` -- resolve into `ForTauCeti` already.
* Namespace: `TauCeti.DavisKahan.Experimental.Foundation.RealSpectralBridge` became
  `TauCeti.SpectralOrder.Real`, matching its complex twin rather than carrying a paper's name
  and a staging word into the library staged for Tau Ceti.
* Original authors / copyright: Jon Crall; Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** -- imports are `ForTauCeti` leaves and Mathlib.
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
public import ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
public import ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# The real spectral-order bridge

From the **spectrum** of a symmetric real operator to **quadratic-form bounds**,
and from there to the real Davis--Kahan estimate on restrictions.  This is the
real-scalar counterpart of `SpectralOrder/Complex.lean`, name for name.

## Main results

* `upperFormBoundOn_top_of_spectrum_subset_Iic` — `spectrum ℝ A ⊆ Iic c` implies
  `A.UpperFormBoundOn ⊤ c`.  This is the bridge; everything below is transport.
* `lowerFormBoundOn_top_of_spectrum_subset_Ici` — its negation.
* `upperFormBoundOn_of_restriction_spectrum_subset_Iic` and
  `lowerFormBoundOn_of_restriction_spectrum_subset_Ici` — the same on a reducing
  subspace.
* `opNorm_starProjection_sub_le_of_restriction_spectra` — the sharp real
  Davis--Kahan bound `‖P_U − P_W‖ ≤ ‖B − A‖ / g` from the spectra of the actual
  restrictions.

## How the bridge is proved, and why not the other way

**Over `ℝ` there is no continuous functional calculus to appeal to**, so the
obvious route — rewrite the complex CFC theorems under real scalars — is not
available: the missing instance *is* the problem.  Two routes were open, a
norm-preserving complexification and constructing the real CFC instance
outright; the proof below takes neither, and instead runs the direct
Rayleigh shift, which needs no new instance at all.

Choose `m > ‖A‖` and set `S = A + m • 1`.  Translating the spectrum
(`spectrum.singleton_add_eq`) puts every spectral value of `S` in `(0, m + c]`;
`ContinuousLinearMap.spectralRadius_eq_nnnorm` for self-adjoint `S`, together
with positivity of that shifted spectrum, gives `‖S‖ ≤ m + c`; then
`abs_re_inner_le_norm` applied to `S x`, minus `m * ‖x‖ ^ 2`, is the claim.

**The seam is the third step, and it is the reason a norm bound will not do.**
`spectralRadius` records *absolute values*, so the argument has to use the
positivity of the shifted spectrum explicitly before it can convert the
spectral-radius supremum into the upper endpoint `c`.  A bound of the form
`‖A‖ ≤ c` loses exactly that sign information and is insufficient.

Downstream real results reduce to this single theorem, so it should not be
replaced by an opaque real-spectrum definition.
-/

public section

namespace TauCeti
namespace SpectralOrder
namespace Real

open TauCeti
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Real spectral upper bound implies a global quadratic-form upper bound.

**This is the bridge**: every other real result in this module is transport off
it.  The proof is the direct Rayleigh shift:

1. choose `m > ‖A‖` and set `S = A + m • 1`;
2. translate the spectrum with `spectrum.singleton_add_eq`, so every spectral
   value of `S` lies in `(0, m + c]`;
3. use `ContinuousLinearMap.spectralRadius_eq_nnnorm` for the self-adjoint
   operator `S` and positivity of its real spectrum to get `‖S‖ ≤ m + c`;
4. apply `abs_re_inner_le_norm` to `S x` and subtract `m * ‖x‖ ^ 2`.

The seam is step 3: `spectralRadius` records absolute values, so the proof uses
the positivity of the shifted spectrum explicitly before converting the
spectral-radius supremum into the upper endpoint `c`.  **A bound of the form
`‖A‖ ≤ c` loses exactly that sign information and does not suffice** -- which is
also why this theorem should not be replaced by an opaque real-spectrum
definition. -/
-- **This proof is 81 lines where `SpectralOrder/Complex.lean`'s counterpart is 2, and the
-- difference is the field, not the factoring.**  The complex file delegates to
-- `re_inner_le_of_spectrum_subset_Iic`, whose whole content is
-- `le_algebraMap_of_spectrum_le` from Mathlib's C⋆-algebra order API.  That route is
-- unavailable here: it needs `StarOrderedRing (E →L[ℝ] E)`, which Mathlib does not
-- provide for a real Hilbert space.  Checked 2026-08-01 by trying it -- the failure is
-- `failed to synthesize StarOrderedRing (E →L[ℝ] E)`, immediate and cheap to reproduce.
-- Hence the shift by `‖A‖ + 1` to positive spectrum and the argument by hand.
theorem upperFormBoundOn_top_of_spectrum_subset_Iic
    (A : E →L[ℝ] E) (hA : A.IsSymmetric) {c : ℝ}
    (hσ : spectrum ℝ A ⊆ Set.Iic c) :
    A.UpperFormBoundOn ⊤ c := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · intro x _
    have hx : x = 0 := Subsingleton.elim x 0
    simp [hx]
  set m : ℝ := ‖A‖ + 1 with hm
  set S : E →L[ℝ] E := A + algebraMap ℝ (E →L[ℝ] E) m with hS
  have hsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hSsa : IsSelfAdjoint S :=
    hsa.add (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all m))
  -- the shifted operator has positive spectrum bounded by `c + m`
  have hSspec : ∀ μ ∈ spectrum ℝ S, 0 < μ ∧ μ ≤ c + m := by
    intro μ hμ
    rw [hS, ← spectrum.add_singleton_eq] at hμ
    obtain ⟨lam, hlam, r, hr, hsum⟩ := Set.mem_add.mp hμ
    rw [Set.mem_singleton_iff] at hr
    subst hr
    have h1 : ‖lam‖ ≤ ‖A‖ := spectrum.norm_le_norm_of_mem hlam
    have h2 : lam ≤ c := hσ hlam
    rw [Real.norm_eq_abs] at h1
    have h3 : -‖A‖ ≤ lam := (abs_le.mp h1).1
    constructor
    · rw [← hsum, hm]; linarith
    · rw [← hsum]; linarith
  have hrad : spectralRadius ℝ S = ‖S‖₊ := S.spectralRadius_eq_nnnorm hSsa
  -- the spectrum of the shifted operator is nonempty
  obtain ⟨μ₀, hμ₀⟩ : (spectrum ℝ S).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have h0 : spectralRadius ℝ S = 0 := by
      rw [spectralRadius, hempty]
      simp
    have hS0 : S = 0 := by
      have h1 : ((‖S‖₊ : ENNReal)) = 0 := by rw [← hrad]; exact h0
      rw [ENNReal.coe_eq_zero, nnnorm_eq_zero] at h1
      exact h1
    have h2 : (0 : ℝ) ∈ spectrum ℝ S := by
      rw [hS0, spectrum.zero_mem_iff]
      exact not_isUnit_zero
    rw [hempty] at h2
    exact h2
  have hcm : 0 < c + m := (hSspec μ₀ hμ₀).1.trans_le (hSspec μ₀ hμ₀).2
  -- the norm of the shifted operator is at most `c + m`
  have hSnorm : ‖S‖ ≤ c + m := by
    have hboundE : spectralRadius ℝ S ≤ ENNReal.ofReal (c + m) := by
      rw [spectralRadius]
      refine iSup₂_le fun μ hμ => ?_
      obtain ⟨hpos, hle⟩ := hSspec μ hμ
      calc ((‖μ‖₊ : ENNReal)) = ‖μ‖ₑ := rfl
        _ = ENNReal.ofReal μ := Real.enorm_eq_ofReal hpos.le
        _ ≤ ENNReal.ofReal (c + m) := ENNReal.ofReal_le_ofReal hle
    rw [hrad] at hboundE
    have h0 : ((‖S‖₊ : ENNReal)) ≤ ((Real.toNNReal (c + m) : ENNReal)) :=
      hboundE
    have h1 : ‖S‖₊ ≤ Real.toNNReal (c + m) := by
      exact_mod_cast h0
    calc ‖S‖ = ((‖S‖₊ : ℝ)) := rfl
      _ ≤ ((Real.toNNReal (c + m) : ℝ)) := by exact_mod_cast h1
      _ = c + m := Real.coe_toNNReal _ hcm.le
  -- Rayleigh estimate and shift back
  intro x _
  have hSx : S x = A x + m • x := by
    rw [hS]
    simp [Algebra.algebraMap_eq_smul_one]
  have hinner : ⟪A x, x⟫_ℝ = ⟪S x, x⟫_ℝ - m * ‖x‖ ^ 2 := by
    rw [hSx, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    ring
  have hupper : ⟪S x, x⟫_ℝ ≤ (c + m) * ‖x‖ ^ 2 := by
    calc ⟪S x, x⟫_ℝ ≤ ‖S x‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ (‖S‖ * ‖x‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (S.le_opNorm x) (norm_nonneg x)
      _ ≤ ((c + m) * ‖x‖) * ‖x‖ := by
          have h := mul_le_mul_of_nonneg_right hSnorm (norm_nonneg x)
          exact mul_le_mul_of_nonneg_right h (norm_nonneg x)
      _ = (c + m) * ‖x‖ ^ 2 := by ring
  -- `UpperFormBoundOn` is a `∀ x ∈ U, _` predicate, so the goal here is already the
  -- pointwise inequality; the `RCLike.re` is definitionally the real inner product.
  have hre : RCLike.re ⟪A x, x⟫_ℝ = ⟪A x, x⟫_ℝ := rfl
  rw [hre, hinner]
  linarith

/-- Real spectral lower bound implies a global quadratic-form lower bound.

This is derived from the upper bridge by negating the operator; it is not a
second spectral-theorem obligation. -/
theorem lowerFormBoundOn_top_of_spectrum_subset_Ici
    (A : E →L[ℝ] E) (hA : A.IsSymmetric) {c : ℝ}
    (hσ : spectrum ℝ A ⊆ Set.Ici c) :
    A.LowerFormBoundOn ⊤ c := by
  have hnegA : (-A).IsSymmetric := by
    intro x y
    change ⟪-A x, y⟫_ℝ = ⟪x, -A y⟫_ℝ
    simpa using congrArg Neg.neg (hA x y)
  have hnegσ : spectrum ℝ (-A) ⊆ Set.Iic (-c) := by
    intro r hr
    have hr' : r ∈ -spectrum ℝ A := by
      rwa [spectrum.neg_eq]
    have hmr : -r ∈ spectrum ℝ A := by
      simpa only [Set.mem_neg] using hr'
    have hcr : c ≤ -r := hσ hmr
    have hrc : r ≤ -c := by
      simpa using neg_le_neg hcr
    exact hrc
  have hupper := upperFormBoundOn_top_of_spectrum_subset_Iic (-A) hnegA hnegσ
  intro x hx
  have hx' := hupper x hx
  simp only [neg_apply, inner_neg_left, map_neg] at hx'
  linarith

/-- Real restriction-spectrum upper bridge on an orthogonally complemented
subspace.  Completeness and symmetry of the actual restriction reduce this to
the global upper bridge. -/
theorem upperFormBoundOn_of_restriction_spectrum_subset_Iic
    {A : E →L[ℝ] E} (hA : A.IsSymmetric)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Iic c) :
    A.UpperFormBoundOn U c := by
  let : CompleteSpace U :=
    completeSpace_coe_iff_isComplete.mpr U.isComplete_coe_of_hasOrthogonalProjection
  have hres : (A.restrict hU).IsSymmetric :=
    ContinuousLinearMap.IsSymmetric.restrict_of_invariant (A := A) hA hU
  have htop := upperFormBoundOn_top_of_spectrum_subset_Iic
    (A.restrict hU) hres hσ
  intro x hx
  have h := htop (⟨x, hx⟩ : U) Submodule.mem_top
  change RCLike.re ⟪A x, x⟫_ℝ ≤ c * ‖x‖ ^ 2 at h
  exact h

/-- Real restriction-spectrum lower bridge on an orthogonally complemented
subspace.  Completeness and symmetry of the actual restriction reduce this to
the global lower bridge. -/
theorem lowerFormBoundOn_of_restriction_spectrum_subset_Ici
    {A : E →L[ℝ] E} (hA : A.IsSymmetric)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Ici c) :
    A.LowerFormBoundOn U c := by
  let : CompleteSpace U :=
    completeSpace_coe_iff_isComplete.mpr U.isComplete_coe_of_hasOrthogonalProjection
  have hres : (A.restrict hU).IsSymmetric :=
    ContinuousLinearMap.IsSymmetric.restrict_of_invariant (A := A) hA hU
  have htop := lowerFormBoundOn_top_of_spectrum_subset_Ici
    (A.restrict hU) hres hσ
  intro x hx
  have h := htop (⟨x, hx⟩ : U) Submodule.mem_top
  change c * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℝ at h
  exact h

/-- The sharp real Davis--Kahan bound, from the spectra of the actual
restrictions: if the two halves of `A` and of `B` are each separated by the gap
`g`, then `‖P_U − P_W‖ ≤ ‖B − A‖ / g`. -/
theorem opNorm_starProjection_sub_le_of_restriction_spectra
    {A B : E →L[ℝ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule ℝ E} [U.HasOrthogonalProjection]
    [W.HasOrthogonalProjection]
    (hU : A.Reduces U) (hW : B.Reduces W)
    {c g : ℝ} (hg : 0 < g)
    (hUhi : spectrum ℝ (A.restrict hU.1) ⊆ Set.Ici (c + g))
    (hUlo : spectrum ℝ (A.restrict hU.2) ⊆ Set.Iic c)
    (hWhi : spectrum ℝ (B.restrict hW.1) ⊆ Set.Ici (c + g))
    (hWlo : spectrum ℝ (B.restrict hW.2) ⊆ Set.Iic c) :
    ‖(U.starProjection - W.starProjection : E →L[ℝ] E)‖ ≤ ‖B - A‖ / g := by
  apply Submodule.opNorm_starProjection_sub_le_of_formBounds hA hB hU hW hg
  · exact lowerFormBoundOn_of_restriction_spectrum_subset_Ici hA hU.1 hUhi
  · exact upperFormBoundOn_of_restriction_spectrum_subset_Iic hA hU.2 hUlo
  · exact lowerFormBoundOn_of_restriction_spectrum_subset_Ici hB hW.1 hWhi
  · exact upperFormBoundOn_of_restriction_spectrum_subset_Iic hB hW.2 hWlo

end Real
end SpectralOrder
end TauCeti
