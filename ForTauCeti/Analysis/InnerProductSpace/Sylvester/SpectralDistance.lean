/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Interval
public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Internal.SpectralBounds
public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Internal.ReciprocalMultiplier

/-!
# Sylvester estimates for arbitrary separated spectra

The reciprocal spectral multiplier, finite orbit certificates, and the sharp
`pi / 2` Ky Fan and arbitrary-UI-norm bounds over real and complex scalars.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Sylvester/SpectralDistance.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-! ## Arbitrary disjoint spectra: the `π/2` scaffold

The Bhatia--Davis--McIntosh extension is factored through the simultaneous Ky
Fan prefix estimate and rectangular Fan dominance.
-/

/-- Entrywise spectral-coordinate form of the Sylvester equation:
`(αᵢ-βⱼ) Xᵢⱼ = Cᵢⱼ`.

This used to be described as exposing "the scalar equation to which the
reciprocal kernel is applied".  There is no reciprocal kernel: the route through
an explicit multiplier `(αᵢ-βⱼ)⁻¹` was abandoned in favour of the Ky Fan prefix
estimate this file actually proves, and the two declarations left over from it
have been removed. -/
theorem sylvester_eigenbasis_coefficient_equation
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hEq : A ∘ₗ X - X ∘ₗ B = C)
    (i : Fin (Module.finrank 𝕜 F)) (j : Fin (Module.finrank 𝕜 E)) :
    ((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜)) *
        ⟪X (hB.eigenvectorBasis rfl j), hA.eigenvectorBasis rfl i⟫_𝕜 =
      ⟪C (hB.eigenvectorBasis rfl j), hA.eigenvectorBasis rfl i⟫_𝕜 := by
  have hpoint := LinearMap.congr_fun hEq (hB.eigenvectorBasis rfl j)
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change A (X (hB.eigenvectorBasis rfl j)) -
      X (B (hB.eigenvectorBasis rfl j)) =
        C (hB.eigenvectorBasis rfl j) at hpoint
  have hinner :
      ⟪X (hB.eigenvectorBasis rfl j),
          A (hA.eigenvectorBasis rfl i)⟫_𝕜 -
        ⟪X (B (hB.eigenvectorBasis rfl j)),
          hA.eigenvectorBasis rfl i⟫_𝕜 =
        ⟪C (hB.eigenvectorBasis rfl j),
          hA.eigenvectorBasis rfl i⟫_𝕜 := by
    calc
      _ = ⟪A (X (hB.eigenvectorBasis rfl j)),
          hA.eigenvectorBasis rfl i⟫_𝕜 -
          ⟪X (B (hB.eigenvectorBasis rfl j)),
            hA.eigenvectorBasis rfl i⟫_𝕜 := by
        rw [← hA (X (hB.eigenvectorBasis rfl j))
          (hA.eigenvectorBasis rfl i)]
      _ = ⟪A (X (hB.eigenvectorBasis rfl j)) -
          X (B (hB.eigenvectorBasis rfl j)),
            hA.eigenvectorBasis rfl i⟫_𝕜 := by
        rw [inner_sub_left]
      _ = _ := congrArg
        (fun z : F => ⟪z, hA.eigenvectorBasis rfl i⟫_𝕜) hpoint
  simpa only [hA.apply_eigenvectorBasis rfl i,
    hB.apply_eigenvectorBasis rfl j, map_smul, inner_smul_left,
    inner_smul_right, RCLike.conj_ofReal, sub_mul] using hinner

/-- Restrict scalars on the Sylvester map space from `𝕜` to `ℝ` so the
barycentric theorem can state real convex-hull membership. -/
local instance realModuleSylvesterMap : Module ℝ (E →ₗ[𝕜] F) :=
  Module.compHom (E →ₗ[𝕜] F) (algebraMap ℝ 𝕜)

/-- **Analytic Ky Fan root of the finite `π/2` front.**  Every singular-value
prefix of a separated self-adjoint Sylvester solution satisfies the
Bhatia--Davis--McIntosh estimate.

This is the weakest field-uniform analytic seam.  The operator-valued
barycenter, exact finite certificate, arbitrary unitarily invariant norm,
residual, and perturbation statements are formal consequences.

This statement deliberately contains no convex-hull or finite-certificate
bookkeeping. -/
theorem kyFan_sylvester_le_of_spectralDistance_analytic
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k C := by
  apply kyFan_reciprocalMultiplier_le
    (eF := hA.eigenvectorBasis rfl)
    (eE := hB.eigenvectorBasis rfl)
    (α := hA.eigenvalues rfl)
    (β := hB.eigenvalues rfl)
    (X := X) (C := C) hδ
  · intro i j
    exact hgap
      (hA.eigenvalues rfl i) (hB.eigenvalues rfl j)
      (eigenvalue_mem_restrictedSpectrum_top hA i)
      (eigenvalue_mem_restrictedSpectrum_top hB j)
  · intro i j
    exact sylvester_eigenbasis_coefficient_equation hA hB hEq i j

/-- The scaled solution of a separated self-adjoint Sylvester equation is a
bounded-mass multiple of a point in the real convex hull of the two-sided
unitary orbit of the defect.

The analytic work is exactly the simultaneous Ky Fan estimate above.  The
rectangular orbit-convexity theorem then converts weak singular-value
majorization into real convex-hull membership uniformly over `ℝ` and `ℂ`.
This avoids placing Fourier integration, phase absorption, normalization, or a
separate real-field descent inside the barycentric theorem.

We choose the maximal allowed mass `p = π / 2` and normalize
`Y = p⁻¹ • (δ • X)`.  Positive homogeneity and the analytic Ky Fan estimate
-- states the goal with the definition unfolded, in the shape the next step needs;
-- there is no `_apply` lemma to rewrite with here.
show every prefix of `Y` is bounded by the corresponding prefix of `C`;
rectangular Fan orbit-convexity gives `Y ∈ conv(orbit(C))`, and the defining
scalar identity recovers `δ • X = p • Y`. -/
theorem sylvester_barycentricOrbitRepresentation_of_spectralDistance
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ Real.pi / 2 ∧
      ∃ Y : E →ₗ[𝕜] F,
        Y ∈ convexHull ℝ
          (RectangularUnitarilyInvariantSeminorm.twoSidedUnitaryOrbit C) ∧
        (((δ : 𝕜)) • X) = ((m : 𝕜)) • Y := by
  let p : ℝ := Real.pi / 2
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hp0 : 0 ≤ p := le_of_lt hp
  have hpinv0 : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0
  let Y : E →ₗ[𝕜] F := (((p⁻¹ : ℝ) : 𝕜)) • (((δ : 𝕜)) • X)
  refine ⟨p, hp0, le_rfl, Y, ?_, ?_⟩
  · apply
      RectangularUnitarilyInvariantSeminorm.mem_convexHull_twoSidedUnitaryOrbit_of_kyFanSum_le
    intro k
    have hcore :=
      kyFan_sylvester_le_of_spectralDistance_analytic
        hA hB hδ hgap hEq k
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change δ *
        RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k X ≤
      p * RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k C at hcore
    calc
      RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k Y =
          p⁻¹ * RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
            (((δ : 𝕜)) • X) := by
        simpa only [Y] using
          RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum_real_smul k
            (((δ : 𝕜)) • X) hpinv0
      _ = p⁻¹ *
          (δ * RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k X) := by
        rw [RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum_real_smul k X (le_of_lt hδ)]
      _ ≤ p⁻¹ *
          (p * RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k C) :=
        mul_le_mul_of_nonneg_left hcore hpinv0
      _ = RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k C := by
        field_simp [ne_of_gt hp]
  · dsimp [Y]
    rw [smul_smul, ← RCLike.ofReal_mul]
    field_simp [ne_of_gt hp]
    simp
/-- A separated self-adjoint Sylvester equation admits a finite two-sided
unitary-orbit certificate of mass at most `π / 2` for the scaled solution
`δ • X` relative to the defect `C`.

Consequently this theorem contains no Fourier, integration, compactness, or
Carathéodory bookkeeping.  The harmonic analysis enters only through the
unconditional reciprocal Ky Fan theorem; this barycentric theorem and the
certificate extraction are finite-algebra and orbit-convexity
consequences, and they attain the exact mass `π / 2` for the particular
Sylvester solution even though the universal undoubled multiplier
certificate at that mass is refuted. -/
theorem sylvester_hasFiniteUnitaryOrbitCertificate_of_spectralDistance
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    RectangularUnitarilyInvariantSeminorm.HasFiniteUnitaryOrbitCertificate
      (Real.pi / 2) (((δ : 𝕜)) • X) C := by
  rcases sylvester_barycentricOrbitRepresentation_of_spectralDistance
      hA hB hδ hgap hEq with ⟨m, hm, hmass, Y, hY, hXY⟩
  exact
    RectangularUnitarilyInvariantSeminorm.hasFiniteUnitaryOrbitCertificate_of_smul_mem_convexHull
      hm hmass hY hXY

/-- Every Ky Fan prefix satisfies the arbitrary-disjoint-spectrum Sylvester
bound.  This public theorem is the stable API alias for the analytic root;
the barycentric and finite-certificate layers are downstream consequences,
not proof dependencies. -/
theorem kyFan_sylvester_le_of_spectralDistance
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k C :=
  kyFan_sylvester_le_of_spectralDistance_analytic
    hA hB hδ hgap hEq k

/-- General disjoint-spectrum extension with the Bhatia--Davis--McIntosh
constant `π/2`, lifted from the finite orbit certificate through Ky Fan
prefixes and rectangular Fan dominance.
-/
theorem uiNorm_sylvester_le_of_spectralDistance
    (N : RectangularUnitarilyInvariantSeminorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ (Real.pi / 2) * N C := by
  let p : ℝ := Real.pi / 2
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hscaled : N (((δ : 𝕜)) • X) ≤ N (((p : 𝕜)) • C) := by
    apply N.apply_le_of_kyFanSum_le
    intro k
    rw [RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum_real_smul k X hδ0,
      RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum_real_smul k C hp0]
    simpa [p] using
      kyFan_sylvester_le_of_spectralDistance hA hB hδ hgap hEq k
  calc
    δ * N X = N (((δ : 𝕜)) • X) := by
      rw [N.smul_eq, RCLike.norm_ofReal, abs_of_pos hδ]
    _ ≤ N (((p : 𝕜)) • C) := hscaled
    _ = p * N C := by
      rw [N.smul_eq, RCLike.norm_ofReal, abs_of_nonneg hp0]
    _ = (Real.pi / 2) * N C := by rfl

/-! ### Unconditional field-specific endpoints

The explicit Haagerup--Zsidó kernel closes the analytic root over `ℂ`
directly and over `ℝ` through the doubled orthogonal descent.  The theorems
below repeat the sharp arbitrary-separated-spectrum statements at the two
concrete scalar fields with no open obligation.  The generic `RCLike`
versions above remain routed through the finite orbit-interpolation seam,
which is still an open obligation. -/

/-- Unconditional complex Ky Fan Sylvester estimate. -/
theorem kyFan_sylvester_le_of_spectralDistance_complex
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC] [FiniteDimensional ℂ EC]
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC] [FiniteDimensional ℂ FC]
    {A : FC →ₗ[ℂ] FC} {B : EC →ₗ[ℂ] EC} {X C : EC →ₗ[ℂ] FC}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k C := by
  apply kyFan_reciprocalMultiplier_le_complex
    (eF := hA.eigenvectorBasis rfl)
    (eE := hB.eigenvectorBasis rfl)
    (α := hA.eigenvalues rfl)
    (β := hB.eigenvalues rfl)
    (X := X) (C := C) hδ
  · intro i j
    exact hgap
      (hA.eigenvalues rfl i) (hB.eigenvalues rfl j)
      (eigenvalue_mem_restrictedSpectrum_top hA i)
      (eigenvalue_mem_restrictedSpectrum_top hB j)
  · intro i j
    exact sylvester_eigenbasis_coefficient_equation hA hB hEq i j

/-- Unconditional real Ky Fan Sylvester estimate. -/
theorem kyFan_sylvester_le_of_spectralDistance_real
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [FiniteDimensional ℝ FR]
    {A : FR →ₗ[ℝ] FR} {B : ER →ₗ[ℝ] ER} {X C : ER →ₗ[ℝ] FR}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k C := by
  apply kyFan_reciprocalMultiplier_le_real
    (eF := hA.eigenvectorBasis rfl)
    (eE := hB.eigenvectorBasis rfl)
    (alpha := hA.eigenvalues rfl)
    (beta := hB.eigenvalues rfl)
    (X := X) (C := C) hδ
  · intro i j
    exact hgap
      (hA.eigenvalues rfl i) (hB.eigenvalues rfl j)
      (eigenvalue_mem_restrictedSpectrum_top hA i)
      (eigenvalue_mem_restrictedSpectrum_top hB j)
  · intro i j
    have h := sylvester_eigenbasis_coefficient_equation hA hB hEq i j
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using h

/-- Unconditional complex arbitrary-UI-norm Sylvester estimate. -/
theorem uiNorm_sylvester_le_of_spectralDistance_complex
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC] [FiniteDimensional ℂ EC]
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC] [FiniteDimensional ℂ FC]
    (N : RectangularUnitarilyInvariantSeminorm ℂ EC FC)
    {A : FC →ₗ[ℂ] FC} {B : EC →ₗ[ℂ] EC} {X C : EC →ₗ[ℂ] FC}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ (Real.pi / 2) * N C := by
  let p : ℝ := Real.pi / 2
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hscaled : N (((δ : ℂ)) • X) ≤ N (((p : ℂ)) • C) := by
    apply N.apply_le_of_kyFanSum_le
    intro k
    have hX : RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
          (((δ : ℂ)) • X) =
        δ * RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k X :=
      RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum_real_smul k X hδ0
    have hC : RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
          (((p : ℂ)) • C) =
        p * RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k C :=
      RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum_real_smul k C hp0
    rw [hX, hC]
    simpa [p] using
      kyFan_sylvester_le_of_spectralDistance_complex hA hB hδ hgap hEq k
  calc
    δ * N X = N (((δ : ℂ)) • X) := by
      rw [N.smul_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    _ ≤ N (((p : ℂ)) • C) := hscaled
    _ = p * N C := by
      rw [N.smul_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
    _ = (Real.pi / 2) * N C := by rfl

/-- Unconditional real arbitrary-UI-norm Sylvester estimate. -/
theorem uiNorm_sylvester_le_of_spectralDistance_real
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [FiniteDimensional ℝ FR]
    (N : RectangularUnitarilyInvariantSeminorm ℝ ER FR)
    {A : FR →ₗ[ℝ] FR} {B : ER →ₗ[ℝ] ER} {X C : ER →ₗ[ℝ] FR}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ (Real.pi / 2) * N C := by
  let p : ℝ := Real.pi / 2
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hscaled : N (δ • X) ≤ N (p • C) := by
    apply N.apply_le_of_kyFanSum_le
    intro k
    have hX := RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum_real_smul
      (𝕜 := ℝ) k X hδ0
    have hC := RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum_real_smul
      (𝕜 := ℝ) k C hp0
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hX hC
    rw [hX, hC]
    simpa [p] using
      kyFan_sylvester_le_of_spectralDistance_real hA hB hδ hgap hEq k
  calc
    δ * N X = N (δ • X) := by
      rw [N.smul_eq, Real.norm_eq_abs, abs_of_pos hδ]
    _ ≤ N (p • C) := hscaled
    _ = p * N C := by
      rw [N.smul_eq, Real.norm_eq_abs, abs_of_nonneg hp0]
    _ = (Real.pi / 2) * N C := by rfl

/-! ## Arbitrary disjoint spectra: the sharp Hilbert--Schmidt estimate

The `π/2` loss above is unavoidable for a general unitarily invariant norm, but
the Frobenius norm loses nothing under arbitrary positive separation.  The
coordinate equation `(αᵢ-βⱼ) Xᵢⱼ = Cᵢⱼ` divides entrywise, and Parseval in the
two eigenbases sums the squares.  This is the estimate behind the
Hilbert--Schmidt form of Davis--Kahan Theorem 6.2.
-/

/-- **Frobenius Sylvester estimate, constant one.**  Under arbitrary positive
spectral separation the Hilbert--Schmidt norm of a Sylvester solution is
controlled by the residual with no dimensional or analytic loss. -/
theorem frobenius_sylvester_le_of_spectraSeparated
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * RectangularUnitarilyInvariantSeminorm.frobenius X ≤
      RectangularUnitarilyInvariantSeminorm.frobenius C := by
  classical
  set bA := hA.eigenvectorBasis rfl with hbA
  set bB := hB.eigenvectorBasis rfl with hbB
  -- the coordinate equation divides by a denominator of size at least `δ`
  have hentry : ∀ (i : Fin (Module.finrank 𝕜 F)) (j : Fin (Module.finrank 𝕜 E)),
      δ * ‖⟪X (bB j), bA i⟫_𝕜‖ ≤ ‖⟪C (bB j), bA i⟫_𝕜‖ := by
    intro i j
    have hcoef := sylvester_eigenbasis_coefficient_equation hA hB hEq i j
    have hsep : δ ≤ |hA.eigenvalues rfl i - hB.eigenvalues rfl j| :=
      hgap _ _ (eigenvalue_mem_restrictedSpectrum_top hA i)
        (eigenvalue_mem_restrictedSpectrum_top hB j)
    have hnorm :
        ‖((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜))‖ =
          |hA.eigenvalues rfl i - hB.eigenvalues rfl j| := by
      rw [show ((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜)) =
        ((hA.eigenvalues rfl i - hB.eigenvalues rfl j : ℝ) : 𝕜) by push_cast; ring]
      exact RCLike.norm_ofReal _
    calc
      δ * ‖⟪X (bB j), bA i⟫_𝕜‖
          ≤ |hA.eigenvalues rfl i - hB.eigenvalues rfl j| *
              ‖⟪X (bB j), bA i⟫_𝕜‖ := by
            gcongr
      _ = ‖((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜))‖ *
              ‖⟪X (bB j), bA i⟫_𝕜‖ := by rw [hnorm]
      _ = ‖((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜)) *
              ⟪X (bB j), bA i⟫_𝕜‖ := (norm_mul _ _).symm
      _ = ‖⟪C (bB j), bA i⟫_𝕜‖ := by rw [hcoef]
  -- Parseval in the codomain eigenbasis turns the entry bound into a column bound
  have hcol : ∀ j : Fin (Module.finrank 𝕜 E),
      δ ^ 2 * ‖X (bB j)‖ ^ 2 ≤ ‖C (bB j)‖ ^ 2 := by
    intro j
    rw [← bA.sum_sq_norm_inner_left (X (bB j)),
      ← bA.sum_sq_norm_inner_left (C (bB j)), Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc
      δ ^ 2 * ‖⟪X (bB j), bA i⟫_𝕜‖ ^ 2
          = (δ * ‖⟪X (bB j), bA i⟫_𝕜‖) ^ 2 := by ring
      _ ≤ ‖⟪C (bB j), bA i⟫_𝕜‖ ^ 2 :=
          pow_le_pow_left₀ (by positivity) (hentry i j) 2
  have htot : δ ^ 2 * (∑ j, ‖X (bB j)‖ ^ 2) ≤ ∑ j, ‖C (bB j)‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hcol j
  rw [RectangularUnitarilyInvariantSeminorm.frobenius_apply X bB,
    RectangularUnitarilyInvariantSeminorm.frobenius_apply C bB,
    ← Real.sqrt_sq hδ.le, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt htot

end TauCeti
