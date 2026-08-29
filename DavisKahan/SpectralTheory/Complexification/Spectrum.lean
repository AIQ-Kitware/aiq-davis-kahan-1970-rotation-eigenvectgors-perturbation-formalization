/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.InnerProductSpace.Complexification.Basic
import DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# The spectrum survives complexification

`DavisKahan/SpectralTheory/Complexification/Basic.lean` builds the complexification functor and
transports norms, symmetry and self-adjointness.  It does not transport the *spectrum*, and that
omission is what stalls the bounded `π/2` Sylvester leaf: the bounded route needs
`SpectraSeparated`, a spectral hypothesis, where the unbounded route
(`DavisKahan/Sylvester/RealUnbounded.lean`) only ever needed a form bound.

This file closes that gap.  The statement is

`(r : ℂ) ∈ spectrum ℂ (complexify T) ↔ r ∈ spectrum ℝ T`,

for real `r`, and the two halves are asymmetric:

* **forward** is formal — `complexify` is a unital ring map, so it carries units to units;
* **backward** is the content — an inverse of `complexify T` must be shown to *come from* a real
  operator.  It does, and `realify` is that operator.  The proof does **not** need the usual
  "the inverse commutes with conjugation" argument: evaluating both unit equations at `ofReal x`
  and taking real parts gives the two real identities directly.

`realSpectrum` is defined as the real points of the Banach-algebra spectrum over the *native*
scalar field, so the transport above is exactly a statement that `realSpectrum` is invariant, and
`SpectraSeparated` on `⊤` follows.
-/

namespace TauCeti
namespace DavisKahan
namespace Foundation

namespace RealComplexification

open TauCeti.RealComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Complexification is multiplicative for operator composition written as ring multiplication. -/
@[simp] theorem complexify_mul (S T : E →L[ℝ] E) :
    complexify (S * T) = complexify S * complexify T :=
  complexify_comp S T

/-- Complexification is unital. -/
@[simp] theorem complexify_one :
    complexify (1 : E →L[ℝ] E) = 1 :=
  complexify_id

/-- Complexification is a unital ring map, so it carries units to units. -/
theorem isUnit_complexify_of_isUnit {T : E →L[ℝ] E} (h : IsUnit T) :
    IsUnit (complexify T) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨⟨complexify (u : E →L[ℝ] E), complexify (↑u⁻¹ : E →L[ℝ] E),
      by rw [← complexify_mul, u.mul_inv, complexify_one],
      by rw [← complexify_mul, u.inv_mul, complexify_one]⟩, rfl⟩

/-- **Complexification reflects invertibility.**

The inverse of `complexify T` restricts to an inverse of `T`: `realify` of it works on both
sides, because evaluating each unit equation at `ofReal x` and taking real parts gives exactly
the two real identities.  No "the inverse commutes with conjugation" step is needed. -/
theorem isUnit_of_isUnit_complexify {T : E →L[ℝ] E} (h : IsUnit (complexify T)) :
    IsUnit T := by
  obtain ⟨u, hu⟩ := h
  have hmul : complexify T * (↑u⁻¹ : RealComplexification E →L[ℂ] RealComplexification E) = 1 := by
    rw [← hu]; exact u.mul_inv
  have hinv : (↑u⁻¹ : RealComplexification E →L[ℂ] RealComplexification E) * complexify T = 1 := by
    rw [← hu]; exact u.inv_mul
  refine ⟨⟨T, realify (↑u⁻¹ : RealComplexification E →L[ℂ] RealComplexification E), ?_, ?_⟩, rfl⟩
  · -- `T * realify u⁻¹ = 1`, from `complexify T * u⁻¹ = 1` evaluated at `ofReal x`.
    apply ContinuousLinearMap.ext
    intro x
    have hx : complexify T ((↑u⁻¹ : RealComplexification E →L[ℂ] RealComplexification E)
        (ofReal x)) = ofReal x :=
      congrArg (fun S : RealComplexification E →L[ℂ] RealComplexification E => S (ofReal x)) hmul
    have hre := congrArg re hx
    rw [re_complexify] at hre
    simpa [realify_apply] using hre
  · -- `realify u⁻¹ * T = 1`, from `u⁻¹ * complexify T = 1` evaluated at `ofReal x`.
    apply ContinuousLinearMap.ext
    intro x
    have hx : (↑u⁻¹ : RealComplexification E →L[ℂ] RealComplexification E)
        (complexify T (ofReal x)) = ofReal x :=
      congrArg (fun S : RealComplexification E →L[ℂ] RealComplexification E => S (ofReal x)) hinv
    rw [complexify_ofReal] at hx
    have hre := congrArg re hx
    simpa [realify_apply] using hre

/-- Invertibility is preserved and reflected by complexification. -/
theorem isUnit_complexify_iff {T : E →L[ℝ] E} : IsUnit (complexify T) ↔ IsUnit T :=
  ⟨isUnit_of_isUnit_complexify, isUnit_complexify_of_isUnit⟩

/-- Complexification commutes with the structure maps of the two operator algebras. -/
theorem complexify_algebraMap (r : ℝ) :
    complexify (algebraMap ℝ (E →L[ℝ] E) r) =
      algebraMap ℂ (RealComplexification E →L[ℂ] RealComplexification E) (r : ℂ) := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;>
    simp [Algebra.algebraMap_eq_smul_one]

/-- **The real points of the spectrum survive complexification.** -/
theorem mem_spectrum_complexify_iff (T : E →L[ℝ] E) (r : ℝ) :
    (r : ℂ) ∈ spectrum ℂ (complexify T) ↔ r ∈ spectrum ℝ T := by
  simp only [spectrum.mem_iff]
  rw [← complexify_algebraMap, ← complexify_sub, isUnit_complexify_iff]

/-- `realSpectrum` is invariant under complexification. -/
theorem realSpectrum_complexify (T : E →L[ℝ] E) :
    realSpectrum (complexify T) = realSpectrum T := by
  ext r
  simpa [realSpectrum] using mem_spectrum_complexify_iff T r

/-- **Full-space spectral separation survives complexification.**

`SpectraSeparated _ ⊤ _ ⊤` is a statement about the two real spectra
(`spectraSeparated_top_iff`), and `realSpectrum_complexify` says complexification does not
move either of them, so the separation transports verbatim with the same gap.

This is the bridge the real `π/2` Sylvester estimate needs: the Fourier representation
behind that estimate is intrinsically complex, so a real separation hypothesis has to be
carried across `complexify` before the complex theorem applies.  Only the `⊤` case is
stated, because that is the only one for which `realSpectrum` is the whole story; a
restricted subspace would first need its own complexification and an invariance transport. -/
theorem spectraSeparated_top_complexify
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {A : E →L[ℝ] E} {B : F →L[ℝ] F} {d : ℝ}
    (hsep : SpectraSeparated A (⊤ : Submodule ℝ E) B (⊤ : Submodule ℝ F) d) :
    SpectraSeparated (complexify A) (⊤ : Submodule ℂ (RealComplexification E))
      (complexify B) (⊤ : Submodule ℂ (RealComplexification F)) d := by
  rw [spectraSeparated_top_iff] at hsep ⊢
  intro a ha b hb
  rw [realSpectrum_complexify] at ha
  rw [realSpectrum_complexify] at hb
  exact hsep a ha b hb

end RealComplexification

end Foundation
end DavisKahan
end TauCeti
