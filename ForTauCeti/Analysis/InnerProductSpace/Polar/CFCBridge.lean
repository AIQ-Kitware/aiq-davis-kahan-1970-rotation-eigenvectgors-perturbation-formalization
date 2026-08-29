/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

CFC bridge for the finite-dimensional operator polar decomposition.
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Polar.Decomposition
public import ForTauCeti.Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

public section

namespace TauCeti

open scoped InnerProductSpace
open LinearMap InnerProductSpace

/-! ### CFC bridge — the ℂ / ContinuousLinearMap headline (`|A| = CFC.abs A`)

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.PolarDecomposition`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `3676b55`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

section CFCBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H]

/-- **Endomorphisms and bounded operators are the same algebra in finite dimension.**

Every linear endomorphism of a finite-dimensional normed space is continuous, so
`LinearMap.toContinuousLinearMap` is a linear equivalence; composition is the multiplication
on both sides, which makes it an algebra equivalence. Mathlib has the linear equivalence but
not this upgrade, and `AlgEquiv.spectrum_eq` across it is what carries eigenvalue facts about
a `Module.End` over to the `ContinuousLinearMap` the functional calculus is stated for. -/
noncomputable def endAlgEquivContinuousLinearMap : Module.End ℂ H ≃ₐ[ℂ] (H →L[ℂ] H) :=
  AlgEquiv.ofLinearEquiv LinearMap.toContinuousLinearMap (by ext x; rfl)
    (fun f g => by ext x; rfl)

omit [CompleteSpace H] in
/-- **Each eigenvalue lies in the real spectrum of the bounded operator.**

The containment the continuous functional calculus bridge needs: it lets a
`g : C(spectrum ℝ T.toContinuousLinearMap, ℝ)` be extended off the spectrum without changing
the finite calculus, and turns the Parseval bound of
`norm_selfAdjointFunctionalCalculus_apply_le` into `‖φ g‖ ≤ ‖g‖_∞`. -/
theorem eigenvalues_mem_spectrum_toContinuousLinearMap {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℂ H)) :
    (hT.eigenvalues rfl i : ℝ) ∈ spectrum ℝ T.toContinuousLinearMap := by
  have hvec : Module.End.HasEigenvector T ((hT.eigenvalues rfl i : ℝ) : ℂ)
      (hT.eigenvectorBasis rfl i) := by
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      exact hT.apply_eigenvectorBasis rfl i
    · simpa using (hT.eigenvectorBasis rfl).orthonormal.ne_zero i
  have hev := Module.End.hasEigenvalue_of_hasEigenvector hvec
  have hC : ((hT.eigenvalues rfl i : ℝ) : ℂ) ∈ spectrum ℂ T.toContinuousLinearMap := by
    have hsp := AlgEquiv.spectrum_eq endAlgEquivContinuousLinearMap T
    rw [show T.toContinuousLinearMap = endAlgEquivContinuousLinearMap T from rfl, hsp]
    exact hev.mem_spectrum
  rw [← spectrum.preimage_algebraMap (R := ℝ) ℂ]
  exact hC

open scoped Classical in
/-- **The finite calculus as a continuous star-algebra homomorphism.**

The bundle `cfcHom_eq_of_continuous_of_map_id` consumes. A symbol on the spectrum is extended
by zero; `selfAdjointFunctionalCalculus_indicator` together with the eigenvalue containment
makes that extension invisible, so each field is the corresponding algebraic lemma about the
calculus. -/
noncomputable def calculusStarAlgHom {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric) :
    C(spectrum ℝ T.toContinuousLinearMap, ℝ) →⋆ₐ[ℝ] (H →L[ℂ] H) where
  toFun g := (selfAdjointFunctionalCalculus hT (extendSymbol g)).toContinuousLinearMap
  map_one' := by
    rw [extendSymbol_one_eq_indicator,
      selfAdjointFunctionalCalculus_indicator hT
        (eigenvalues_mem_spectrum_toContinuousLinearMap hT),
      selfAdjointFunctionalCalculus_one hT]
    ext x; rfl
  map_mul' g₁ g₂ := by
    -- explicit arguments: the lambda pattern in `_comp` defeats higher-order unification
    rw [extendSymbol_mul,
      ← selfAdjointFunctionalCalculus_comp hT (extendSymbol g₁) (extendSymbol g₂)]
    ext x; rfl
  map_zero' := by
    rw [extendSymbol_zero, selfAdjointFunctionalCalculus_zero hT]
    ext x; rfl
  map_add' g₁ g₂ := by
    rw [extendSymbol_add, selfAdjointFunctionalCalculus_add hT]
    ext x; rfl
  commutes' r := by
    have hr : extendSymbol (algebraMap ℝ C(spectrum ℝ T.toContinuousLinearMap, ℝ) r)
        = (spectrum ℝ T.toContinuousLinearMap).indicator (fun _ => r) := by
      exact extendSymbol_eq_indicator _ _ fun _ _ => rfl
    rw [hr, selfAdjointFunctionalCalculus_indicator hT
        (eigenvalues_mem_spectrum_toContinuousLinearMap hT),
      show (fun _ : ℝ => r) = r • (fun _ : ℝ => (1 : ℝ)) from by funext _; simp,
      selfAdjointFunctionalCalculus_smul hT, selfAdjointFunctionalCalculus_one hT]
    ext x; simp [Algebra.algebraMap_eq_smul_one]
  map_star' g := by
    have hstar : star g = g := rfl
    rw [hstar]
    refine (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ?_).symm
    intro x y
    exact selfAdjointFunctionalCalculus_isSymmetric hT (extendSymbol g) x y

/-- The bundle sends the identity symbol to the operator, one of the two hypotheses of
`cfcHom_eq_of_continuous_of_map_id`. -/
theorem calculusStarAlgHom_id {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric) :
    calculusStarAlgHom hT
        (ContinuousMap.restrict (spectrum ℝ T.toContinuousLinearMap) (ContinuousMap.id ℝ))
      = T.toContinuousLinearMap := by
  have hmem := eigenvalues_mem_spectrum_toContinuousLinearMap hT
  have hext : extendSymbol
      (ContinuousMap.restrict (spectrum ℝ T.toContinuousLinearMap) (ContinuousMap.id ℝ))
      = (spectrum ℝ T.toContinuousLinearMap).indicator (id : ℝ → ℝ) := by
    exact extendSymbol_eq_indicator _ _ fun _ _ => rfl
  have key : (selfAdjointFunctionalCalculus hT (extendSymbol
      (ContinuousMap.restrict (spectrum ℝ T.toContinuousLinearMap)
        (ContinuousMap.id ℝ)))).toContinuousLinearMap = T.toContinuousLinearMap := by
    rw [hext, selfAdjointFunctionalCalculus_indicator hT hmem,
      selfAdjointFunctionalCalculus_id hT]
  exact key

/-- The bundle is bounded by the sup norm of the symbol, hence continuous: the other
hypothesis of `cfcHom_eq_of_continuous_of_map_id`. -/
theorem norm_calculusStarAlgHom_le {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric)
    (g : C(spectrum ℝ T.toContinuousLinearMap, ℝ)) :
    ‖calculusStarAlgHom hT g‖ ≤ ‖g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) fun x => ?_
  refine norm_selfAdjointFunctionalCalculus_apply_le hT _ (norm_nonneg g) (fun i => ?_) x
  have hmem := eigenvalues_mem_spectrum_toContinuousLinearMap hT i
  rw [extendSymbol_apply_of_mem _ hmem]
  simpa using g.norm_coe_le_norm ⟨_, hmem⟩

/-- **The two calculi agree**: the `RCLike` finite functional calculus, transported to bounded
operators, is Mathlib's continuous functional calculus.

Part A's milestone.  `calculusStarAlgHom` is continuous and sends the identity symbol to the
operator, so `cfcHom_eq_of_continuous_of_map_id` identifies it with `cfcHom`; the extension of
a symbol off the spectrum is invisible to the finite calculus, by
`selfAdjointFunctionalCalculus_indicator` and the eigenvalue containment. -/
theorem selfAdjointFunctionalCalculus_toContinuousLinearMap_eq_cfc {T : H →ₗ[ℂ] H}
    (hT : T.IsSymmetric) (f : ℝ → ℝ) (hf : Continuous f) :
    (selfAdjointFunctionalCalculus hT f).toContinuousLinearMap
      = cfc f T.toContinuousLinearMap := by
  have ha : IsSelfAdjoint T.toContinuousLinearMap :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have hcont : Continuous (calculusStarAlgHom hT) :=
    AddMonoidHomClass.continuous_of_bound (calculusStarAlgHom hT) 1 fun g => by
      rw [one_mul]; exact norm_calculusStarAlgHom_le hT g
  have hhom : cfcHom ha = calculusStarAlgHom hT :=
    cfcHom_eq_of_continuous_of_map_id ha _ hcont (calculusStarAlgHom_id hT)
  rw [cfc_apply f T.toContinuousLinearMap ha hf.continuousOn, hhom]
  have key : (selfAdjointFunctionalCalculus hT
      (extendSymbol (⟨_, hf.continuousOn.domRestrict⟩ :
        C(spectrum ℝ T.toContinuousLinearMap, ℝ)))).toContinuousLinearMap
      = (selfAdjointFunctionalCalculus hT f).toContinuousLinearMap := by
    congr 1
    refine selfAdjointFunctionalCalculus_congr hT fun i => ?_
    rw [extendSymbol_apply_of_mem _ (eigenvalues_mem_spectrum_toContinuousLinearMap hT i)]
    rfl
  exact key.symm

/-- The spectral modulus agrees with the C⋆-algebra `CFC.abs` on `E →L[ℂ] E`,
transported across
the definitional `LinearMap ↔ ContinuousLinearMap` adjoint bridge (`adjoint_toContinuousLinearMap`
is `rfl`). This is what makes the decomposition literally "via CFC". -/
theorem operatorAbs_toContinuousLinearMap_eq_cfcAbs (A : H →ₗ[ℂ] H) :
    (operatorAbs A).toContinuousLinearMap = CFC.abs A.toContinuousLinearMap := by
  refine (CFC.sqrt_unique ?_ ?_).symm
  · -- `|A|.toCLM * |A|.toCLM = star A.toCLM * A.toCLM`, transported from
    -- `operatorAbs_mul_self` across
    -- the definitional `LinearMap ↔ ContinuousLinearMap` adjoint bridge.
    ext x
    exact congrArg (fun f : H →ₗ[ℂ] H => f x) (operatorAbs_mul_self A)
  · exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      ((LinearMap.isPositive_toContinuousLinearMap_iff (operatorAbs A)).mpr
        (isPositive_operatorAbs A))

/-- **Headline (via CFC):** every `A : H →L[ℂ] H` factors as `A = U ∘L CFC.abs A` with `U` a
partial isometry. -/
theorem continuousLinearMap_polar_decomposition (A : H →L[ℂ] H) :
    ∃ U : H →L[ℂ] H, IsPartialIsometry U ∧ A = U ∘L CFC.abs A := by
  refine ⟨(polarFactor (A : H →ₗ[ℂ] H)).toContinuousLinearMap, ?_, ?_⟩
  · -- transport `IsPartialIsometry` across the (definitional) star-monoid bridge
    have h := isPartialIsometry_polarFactor (A : H →ₗ[ℂ] H)
    ext x
    exact congrArg (fun f : H →ₗ[ℂ] H => f x) h
  · rw [show CFC.abs A = CFC.abs ((A : H →ₗ[ℂ] H)).toContinuousLinearMap from rfl,
      ← operatorAbs_toContinuousLinearMap_eq_cfcAbs (A : H →ₗ[ℂ] H)]
    ext x
    exact congrArg (fun f : H →ₗ[ℂ] H => f x) (polar_decomposition (A : H →ₗ[ℂ] H))

end CFCBridge

end TauCeti
