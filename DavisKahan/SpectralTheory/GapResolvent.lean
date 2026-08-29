/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 5
-/
import DavisKahan.SpectralTheory.PartialMap.Basic
import DavisKahan.Sylvester.ShiftedInverseGauge
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointResolvent

/-!
# Norm-bounded gap resolvents

The unbounded Davis--Kahan development phrases spectral exteriority through the
proof-carrying predicate `TwoSidedShiftedInverseBound A c s`: a bounded
two-sided inverse of `A - c` with norm at most `s⁻¹`.  This module discharges
that predicate from a genuine spectral hypothesis — the spectrum of the operator
avoids the open interval `(c - s, c + s)`.

## History: this was the largest Spectra dependency in the tree

Until 2026-07-28 the bound was obtained from `vendor/Spectra` through the full
spectral-theorem stack: Stone's theorem (`genToGroup`) to manufacture a unitary
group from the self-adjoint operator, that group's projection-valued measure,
the bounded Borel functional calculus, the truncated symbol `(l - c)⁻¹`, and the
sharp calculus norm bound.  Two substantial intermediate theorems lived here to
support it — `spectralProjection_eq_zero_of_forall_mem_resolventSet` and
`exists_norm_le_two_sided_shifted_inverse_of_spectralProjection_Ioo_eq_zero`.

**None of that is necessary.**  The bound is a C⋆-algebra fact about the
*bounded* operator `R = (A - c)⁻¹`:

* resolvent spectral mapping puts `spectrum R \ {0}` inside
  `(· - c)⁻¹ '' spectrum A` — elementary algebra with domain bookkeeping;
* the spectral gap therefore bounds `spectrum R` by `s⁻¹`;
* and for a **self-adjoint** element the norm *is* the spectral radius, which is
  Mathlib's `IsSelfAdjoint.spectralRadius_eq_nnnorm`.

The replacement lives in
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/{Resolvent,ResolventBound,SelfAdjointResolvent}.lean`
and is Spectra-free.  The two intermediate theorems were deleted rather than
kept: they were scaffolding for the PVM route, nothing outside this file used
them, and retaining them would have kept the whole projection-valued-measure
layer on the critical path of `dev/tauceti/spectra-removal-plan.md`.  They
remain in the history at `a58913e`.

This module is Spectra-free, and as the note here used to predict, it has been
relocated now that `Interop/Spectra/` is gone: it is spectral theory, and it sits
with the rest of it.
-/

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace TauCeti
namespace DavisKahan

/-- **A spectral gap gives a norm-bounded two-sided inverse.**  If the spectrum
of a self-adjoint `A` avoids `(c - s, c + s)`, then `A - c` has a bounded
two-sided inverse of norm at most `s⁻¹`. -/
theorem exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {c s : ℝ} (hs : 0 < s)
    (hgap : ∀ lam ∈ Set.Ioo (c - s) (c + s),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum A) :
    ∃ R : H →L[ℂ] H, ‖R‖ ≤ s⁻¹ ∧
      (∀ ψ : A.domain, R (A ψ - (c : ℂ) • (ψ : H)) = (ψ : H)) ∧
      ∀ φ : H, ∃ hmem : R φ ∈ A.domain,
        A ⟨R φ, hmem⟩ - (c : ℂ) • R φ = φ := by
  -- The upstream theorem inverts `c • I - A`; the Davis--Kahan statement is about `A - c`,
  -- so the witness is the negated resolvent.  The norm bound is unaffected.
  obtain ⟨R, hnorm, hleft, hright⟩ :=
    TauCeti.LinearPMap.exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap hA hs hgap
  refine ⟨-R, by simpa using hnorm, fun ψ => ?_, fun φ => ?_⟩
  · have h := hleft ψ
    have harg : A ψ - (c : ℂ) • (ψ : H) = -((c : ℂ) • (ψ : H) - A ψ) := by module
    rw [_root_.neg_apply, harg, map_neg, h, neg_neg]
  · obtain ⟨hmem, hsolve⟩ := hright φ
    refine ⟨neg_mem hmem, ?_⟩
    have hneg : A (⟨(-R) φ, neg_mem hmem⟩ : A.domain) = -(A ⟨R φ, hmem⟩) :=
      _root_.LinearPMap.map_neg A ⟨R φ, hmem⟩
    rw [hneg]
    simp only [_root_.neg_apply]
    linear_combination (norm := module) hsolve

/-- **Genuine spectra discharge the shifted-inverse hypothesis.**  For a DK
closed operator whose canonical `LinearPMap` view is self-adjoint and whose
spectrum avoids `(c - s, c + s)`, the proof-carrying predicate
`TwoSidedShiftedInverseBound A c s` holds.  This connects the honest unbounded
Davis--Kahan hypotheses to the spectral theory. -/
theorem twoSidedShiftedInverseBound_of_spectrum_gap
    {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) {c s : ℝ} (hs : 0 < s)
    (hgap : ∀ lam ∈ Set.Ioo (c - s) (c + s),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum A) :
    TauCeti.DavisKahan.ExactSinTheta.TwoSidedShiftedInverseBound
      A c s := by
  obtain ⟨R, hnorm, hleft, hright⟩ :=
    exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap hA hs hgap
  exact ⟨R, fun z => (hright z).choose,
    fun x => hleft x, fun z => (hright z).choose_spec, hnorm⟩

end DavisKahan
end TauCeti
