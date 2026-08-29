/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForTauCeti.Analysis.InnerProductSpace.Sylvester.SpectralDistance
import DavisKahan.BoundedOperator.Compat
import DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Compatibility bridges for the historical continuous-linear-map API
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

namespace ContinuousLinearMapBridge

/-- Point spectrum carried by vectors in a supplied subspace. This local
compatibility definition keeps the finite continuous-linear-map bridge
independent of the experimental bounded-operator spectrum interfaces. -/
abbrev restrictedSpectrum (A : E →L[𝕜] E) (U : Submodule 𝕜 E) : Set ℝ :=
  {r | ∃ x : E, x ∈ U ∧ x ≠ 0 ∧ A x = ((r : ℝ) : 𝕜) • x}

/-- Separation of the two carried point spectra by at least `d`. -/
abbrev SpectraSeparated (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →L[𝕜] F) (V : Submodule 𝕜 F) (d : ℝ) : Prop :=
  ∀ a ∈ restrictedSpectrum A U, ∀ b ∈ restrictedSpectrum B V, d ≤ |a - b|

end ContinuousLinearMapBridge

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Spectral separation transfers to the underlying linear maps.**

Membership in the top submodule is free, so the eigenvector witnesses carry
across unchanged.  All three bridge theorems below did this inline. -/
private theorem spectraSeparated_toLinearMap
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {d : ℝ}
    (hsep : ContinuousLinearMapBridge.SpectraSeparated A ⊤ B ⊤ d) :
    TauCeti.SpectraSeparated A.toLinearMap ⊤ B.toLinearMap ⊤ d := by
  intro a b ha hb
  rcases TauCeti.mem_restrictedSpectrum_iff.mp ha with ⟨x, -, hx0, hxeig⟩
  rcases TauCeti.mem_restrictedSpectrum_iff.mp hb with ⟨y, -, hy0, hyeig⟩
  exact hsep a ⟨x, Submodule.mem_top, hx0, hxeig⟩
    b ⟨y, Submodule.mem_top, hy0, hyeig⟩

/-- **The Sylvester equation, pushed down to the underlying linear maps.**

All three bridge theorems below restate `sylvesterOperator A B X = C` this way,
over `𝕜`, over `ℂ` and over `ℝ`; the proof is the same three lines each time, so
the lemma carries its own scalar field. -/
private theorem sylvesterOperator_toLinearMap {𝕜' : Type*} [RCLike 𝕜']
    {E' F' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜' E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜' F']
    {A : F' →L[𝕜'] F'} {B : E' →L[𝕜'] E'} {X C : E' →L[𝕜'] F'}
    (hEq : ContinuousLinearMap.sylvesterOperator A B X = C) :
    A.toLinearMap ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ B.toLinearMap =
      C.toLinearMap := by
  ext x
  have hpoint := congrArg (fun T : E' →L[𝕜'] F' => T x) hEq
  change A (X x) - X (B x) = C x at hpoint
  simpa using hpoint

omit [CompleteSpace E] [CompleteSpace F] in
/-- Finite-dimensional rectangular unitarily invariant Sylvester estimate.

For self-adjoint `A` and `B` with spectra separated by `d > 0`, every
rectangular unitarily invariant seminorm satisfies
`d * N X ≤ (π / 2) * N C` whenever `A X - X B = C`.

All reciprocal-multiplier analysis, including the sharp `π / 2` constant,
is supplied unconditionally by the Haagerup--Zsidó kernel through
`kyFan_reciprocalMultiplier_le`.  Coordinate expansion,
singular-value control, the orbit barycenter, and this
continuous-linear-map bridge contain no further analytic argument.-/
theorem ideal_sylvester_le
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (N : RectangularUnitarilyInvariantSeminorm 𝕜 E F)
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : ContinuousLinearMapBridge.SpectraSeparated A ⊤ B ⊤ d)
    (hEq : ContinuousLinearMap.sylvesterOperator A B X = C) :
    d * N X.toLinearMap ≤ (Real.pi / 2) * N C.toLinearMap := by
  let A' : F →ₗ[𝕜] F := A.toLinearMap
  let B' : E →ₗ[𝕜] E := B.toLinearMap
  let X' : E →ₗ[𝕜] F := X.toLinearMap
  let C' : E →ₗ[𝕜] F := C.toLinearMap
  have hA' : A'.IsSymmetric := by
    intro x y
    exact hA x y
  have hB' : B'.IsSymmetric := by
    intro x y
    exact hB x y
  have hsep' : TauCeti.SpectraSeparated A' ⊤ B' ⊤ d :=
    spectraSeparated_toLinearMap hsep
  have hEq' : A' ∘ₗ X' - X' ∘ₗ B' = C' :=
    sylvesterOperator_toLinearMap hEq
  simpa [X', C'] using
    uiNorm_sylvester_le_of_spectralDistance
      N hA' hB' hd hsep' hEq'

/-- **Unconditional complex sharp Sylvester estimate.**  Identical to
`ideal_sylvester_le` at `𝕜 = ℂ`, but proved through the explicit
Haagerup--Zsidó kernel with no open obligation. -/
theorem ideal_sylvester_le_complex
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC] [FiniteDimensional ℂ EC]
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC] [FiniteDimensional ℂ FC]
    (N : RectangularUnitarilyInvariantSeminorm ℂ EC FC)
    {A : FC →L[ℂ] FC} {B : EC →L[ℂ] EC} {X C : EC →L[ℂ] FC}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : ContinuousLinearMapBridge.SpectraSeparated A ⊤ B ⊤ d)
    (hEq : ContinuousLinearMap.sylvesterOperator A B X = C) :
    d * N X.toLinearMap ≤ (Real.pi / 2) * N C.toLinearMap := by
  let A' : FC →ₗ[ℂ] FC := A.toLinearMap
  let B' : EC →ₗ[ℂ] EC := B.toLinearMap
  let X' : EC →ₗ[ℂ] FC := X.toLinearMap
  let C' : EC →ₗ[ℂ] FC := C.toLinearMap
  have hA' : A'.IsSymmetric := by
    intro x y
    exact hA x y
  have hB' : B'.IsSymmetric := by
    intro x y
    exact hB x y
  have hsep' : TauCeti.SpectraSeparated A' ⊤ B' ⊤ d :=
    spectraSeparated_toLinearMap hsep
  have hEq' : A' ∘ₗ X' - X' ∘ₗ B' = C' :=
    sylvesterOperator_toLinearMap hEq
  simpa [X', C'] using
    uiNorm_sylvester_le_of_spectralDistance_complex
      N hA' hB' hd hsep' hEq'

/-- **Unconditional real sharp Sylvester estimate.**  Identical to
`ideal_sylvester_le` at `𝕜 = ℝ`, proved through the doubled orthogonal
descent from the explicit Haagerup--Zsidó kernel. -/
theorem ideal_sylvester_le_real
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [FiniteDimensional ℝ FR]
    (N : RectangularUnitarilyInvariantSeminorm ℝ ER FR)
    {A : FR →L[ℝ] FR} {B : ER →L[ℝ] ER} {X C : ER →L[ℝ] FR}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : ContinuousLinearMapBridge.SpectraSeparated A ⊤ B ⊤ d)
    (hEq : ContinuousLinearMap.sylvesterOperator A B X = C) :
    d * N X.toLinearMap ≤ (Real.pi / 2) * N C.toLinearMap := by
  let A' : FR →ₗ[ℝ] FR := A.toLinearMap
  let B' : ER →ₗ[ℝ] ER := B.toLinearMap
  let X' : ER →ₗ[ℝ] FR := X.toLinearMap
  let C' : ER →ₗ[ℝ] FR := C.toLinearMap
  have hA' : A'.IsSymmetric := by
    intro x y
    exact hA x y
  have hB' : B'.IsSymmetric := by
    intro x y
    exact hB x y
  have hsep' : TauCeti.SpectraSeparated A' ⊤ B' ⊤ d :=
    spectraSeparated_toLinearMap hsep
  have hEq' : A' ∘ₗ X' - X' ∘ₗ B' = C' :=
    sylvesterOperator_toLinearMap hEq
  simpa [X', C'] using
    uiNorm_sylvester_le_of_spectralDistance_real
      N hA' hB' hd hsep' hEq'

end DavisKahanExt
end TauCeti