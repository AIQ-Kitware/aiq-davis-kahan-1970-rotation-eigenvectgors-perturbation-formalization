/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.KyFan
public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
public import ForTauCeti.Analysis.InnerProductSpace.Gram.Matrix
public import ForTauCeti.Analysis.InnerProductSpace.RectangularSingularValues
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Convex.Caratheodory

/-!
# Rectangular unitarily invariant norms: the structure and its basic laws

The structure itself, the finite Ky Fan sums of singular values, the two-sided unitary
orbit with its finiteness certificates, and transport of a norm along an isometry of
the domain or the codomain.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm`,
  split out on 2026-07-28 because that file had grown to 2124 lines while Tau Ceti's
  `lean_lib` enforces a hard 1500-line ceiling, and 1000 for a newly added file.
* Extraction class: **split**.  No statement, proof or declaration name changed; only
  `exists_unitary_factorization_of_singularValues_eq` was promoted from `private` to
  public, because the split puts its users in a different module.
* Original authors / copyright: Jon Crall, Claude Fable 5;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [FiniteDimensional 𝕜 G]

/-- A unitarily invariant seminorm on rectangular linear maps.

As in the existing square `UnitarilyInvariantSeminorm`, definiteness is deliberately
not bundled: the Davis--Kahan inequalities and Fan dominance use only
subadditivity, absolute homogeneity, and two-sided unitary invariance. -/
structure RectangularUnitarilyInvariantSeminorm (𝕜 E F : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] where
  toFun : (E →ₗ[𝕜] F) → ℝ
  add_le' : ∀ A B, toFun (A + B) ≤ toFun A + toFun B
  smul' : ∀ (a : 𝕜) A, toFun (a • A) = ‖a‖ * toFun A
  invariant' : ∀ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) A,
    toFun (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) = toFun A

namespace RectangularUnitarilyInvariantSeminorm

/-- Prefix sum of singular values for a rectangular map. -/
@[expose]
noncomputable def rectangularKyFanSum (k : ℕ) (A : E →ₗ[𝕜] F) : ℝ :=
  ∑ i : Fin k, A.singularValues (i : ℕ)

/-- Apply a rectangular UI seminorm directly to a map, writing `N A` for `N.toFun A`. -/
instance : CoeFun (RectangularUnitarilyInvariantSeminorm 𝕜 E F)
    fun _ => (E →ₗ[𝕜] F) → ℝ :=
  ⟨RectangularUnitarilyInvariantSeminorm.toFun⟩

variable (N : RectangularUnitarilyInvariantSeminorm 𝕜 E F)


/-- A rectangular UI seminorm vanishes at zero. -/
@[simp] theorem apply_zero : N (0 : E →ₗ[𝕜] F) = 0 := by
  have h := N.smul' 0 (0 : E →ₗ[𝕜] F)
  simpa using h


/-- A rectangular UI seminorm is nonnegative -- derived from subadditivity applied to `A` and `-A`,
not assumed as a field. -/
theorem nonneg (A : E →ₗ[𝕜] F) : 0 ≤ N A := by
  have h := N.add_le' A (-A)
  rw [add_neg_cancel] at h
  have hneg : N.toFun (-A) = N.toFun A := by
    have h1 := N.smul' (-1) A
    simpa using h1
  have hz : N.toFun (0 : E →ₗ[𝕜] F) = 0 := apply_zero N
  rw [hz, hneg] at h
  linarith


/-- Subadditivity. -/
theorem add_le (A B : E →ₗ[𝕜] F) : N (A + B) ≤ N A + N B :=
  N.add_le' A B

/-- A rectangular UI seminorm of a finite sum is bounded by the sum of the
individual seminorms.

This is the finite replacement for the integral triangle inequality in the
unitary-orbit proof of the `π/2` Sylvester theorem. -/
theorem sum_le {ι : Type*} (s : Finset ι) (A : ι → E →ₗ[𝕜] F) :
    N (∑ i ∈ s, A i) ≤ ∑ i ∈ s, N (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (N.add_le _ _).trans (add_le_add_right ih _)

/-- The two-sided unitary orbit of a rectangular map.

A point of `twoSidedUnitaryOrbit C` has the form `U ∘ C ∘ V` with unitary
left and right factors.  The phase of a complex Fourier coefficient is intended
to be absorbed into `U`, so the convex hull of this set is the correct
barycentric target for the arbitrary-spectrum `π/2` proof.

The definition is field-uniform: over `ℝ`, the only scalar phases absorbed into
the orbit are the real unitary signs, while a complex proof must descend to a
real orbit before invoking this API. -/
@[expose]
def twoSidedUnitaryOrbit (C : E →ₗ[𝕜] F) : Set (E →ₗ[𝕜] F) :=
  {Y | ∃ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E),
    Y = U.toLinearMap ∘ₗ C ∘ₗ V.toLinearMap}

/-- A finite two-sided unitary-orbit certificate for bounding `X` by `C`.

A certificate of mass `mass` writes `X` as a finite linear combination of maps
`Uᵢ ∘ C ∘ Vᵢ`, where each `Uᵢ` and `Vᵢ` is unitary and the sum of coefficient
norms is at most `mass`.

For the arbitrary-spectrum `π/2` theorem, the difficult analytic task is exactly
to construct such a certificate for `((δ : 𝕜) • X)` from the Sylvester defect
`C` with mass `π / 2`. -/
@[expose]
def HasFiniteUnitaryOrbitCertificate
    (mass : ℝ) (X C : E →ₗ[𝕜] F) : Prop :=
  ∃ n : ℕ, ∃ a : Fin n → 𝕜,
    ∃ U : Fin n → F ≃ₗᵢ[𝕜] F,
      ∃ V : Fin n → E ≃ₗᵢ[𝕜] E,
        X = ∑ i, a i •
          ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap) ∧
        ∑ i, ‖a i‖ ≤ mass

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Reindex a finite certificate candidate from an arbitrary finite type by `Fin n`.

This lemma keeps all `Fin n` bookkeeping out of the convex-geometric proof.
It is purely finite algebra and has no analytic or field-specific content. -/
theorem hasFiniteUnitaryOrbitCertificate_of_fintype
    {ι : Type*} [Fintype ι] {mass : ℝ} {X C : E →ₗ[𝕜] F}
    (a : ι → 𝕜) (U : ι → F ≃ₗᵢ[𝕜] F) (V : ι → E ≃ₗᵢ[𝕜] E)
    (hX : X = ∑ i, a i •
      ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap))
    (hmass : ∑ i, ‖a i‖ ≤ mass) :
    HasFiniteUnitaryOrbitCertificate mass X C := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun j => a (e j), fun j => U (e j),
    fun j => V (e j), ?_, ?_⟩
  · calc
      X = ∑ i, a i •
          ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap) := hX
      _ = ∑ j, a (e j) •
          ((U (e j)).toLinearMap ∘ₗ C ∘ₗ (V (e j)).toLinearMap) :=
        (e.sum_comp (fun i => a i •
          ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap))).symm
  · calc
      ∑ j, ‖a (e j)‖ = ∑ i, ‖a i‖ :=
        e.sum_comp (fun i => ‖a i‖)
      _ ≤ mass := hmass

/-- Restrict scalars on the rectangular-map space from `𝕜` to `ℝ` for the
real convex-hull argument. -/
local instance realModuleLinearMap : Module ℝ (E →ₗ[𝕜] F) :=
  Module.compHom (E →ₗ[𝕜] F) (algebraMap ℝ 𝕜)

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Convert an exact convex-hull barycentric representation into a finite
unitary-orbit certificate.

Suppose `Y` lies in the real convex hull of the two-sided unitary orbit of `C`,
and `X = m • Y` for a nonnegative real mass `m ≤ mass`.  Then `X` has a finite
unitary-orbit certificate of mass `mass`.

This theorem discharges the entire exact finite-dimensional convex-combination
stage of the `π/2` proof.  The remaining analytic theorem only has to produce a
bounded-mass barycentric orbit representation.  The argument is valid over
both `ℝ` and `ℂ`; any complexification/descent issue must already have been
resolved before establishing the real convex-hull hypothesis. -/
theorem hasFiniteUnitaryOrbitCertificate_of_smul_mem_convexHull
    {m mass : ℝ} (hm : 0 ≤ m) (hmass : m ≤ mass)
    {X Y C : E →ₗ[𝕜] F}
    (hY : Y ∈ convexHull ℝ (twoSidedUnitaryOrbit C))
    (hX : X = ((m : 𝕜)) • Y) :
    HasFiniteUnitaryOrbitCertificate mass X C := by
  classical
  rcases (mem_convexHull_iff_exists_fintype.mp hY) with
    ⟨ι, instι, w, z, hw, hwsum, hz, hzsum⟩
  let : Fintype ι := instι
  have hz' : ∀ i, ∃ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E),
      z i = U.toLinearMap ∘ₗ C ∘ₗ V.toLinearMap := by
    intro i
    exact hz i
  choose U V hUV using hz'
  refine hasFiniteUnitaryOrbitCertificate_of_fintype
    (a := fun i => (((m * w i : ℝ) : 𝕜))) U V ?_ ?_
  · have real_smul_linearMap_eq (r : ℝ) (T : E →ₗ[𝕜] F) :
        r • T = ((r : 𝕜)) • T := by
      -- The local real module was defined by `Module.compHom` along
      -- `algebraMap ℝ 𝕜`, and the `RCLike` coercion is that algebra map.
      -- Hence the two bundled-map scalar actions are definitionally equal;
      -- no real module or scalar-tower instance on the codomain is needed.
      change (algebraMap ℝ 𝕜 r) • T = ((r : 𝕜)) • T
      rfl
    have hzsum' : ∑ i, (((w i : ℝ) : 𝕜)) • z i = Y := by
      calc
        ∑ i, (((w i : ℝ) : 𝕜)) • z i = ∑ i, w i • z i := by
          apply Finset.sum_congr rfl
          intro i _
          exact (real_smul_linearMap_eq (w i) (z i)).symm
        _ = Y := hzsum
    calc
      X = ((m : 𝕜)) • Y := hX
      _ = ((m : 𝕜)) • ∑ i, (((w i : ℝ) : 𝕜)) • z i := by rw [hzsum']
      _ = ∑ i, (((m * w i : ℝ) : 𝕜)) • z i := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul, RCLike.ofReal_mul]
      _ = ∑ i, (((m * w i : ℝ) : 𝕜)) •
          ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hUV i]
  · calc
      ∑ i, ‖(((m * w i : ℝ) : 𝕜))‖ = ∑ i, m * w i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [RCLike.norm_ofReal, abs_of_nonneg (mul_nonneg hm (hw i))]
      _ = m * ∑ i, w i := by rw [Finset.mul_sum]
      _ = m := by rw [hwsum, mul_one]
      _ ≤ mass := hmass


/-- Absolute homogeneity. -/
theorem smul_eq (a : 𝕜) (A : E →ₗ[𝕜] F) : N (a • A) = ‖a‖ * N A :=
  N.smul' a A

/-- A rectangular UI seminorm is invariant under negation. -/
@[simp] theorem apply_neg (A : E →ₗ[𝕜] F) : N (-A) = N A := by
  have h := N.smul_eq (-1 : 𝕜) A
  simpa using h


/-- Two-sided unitary invariance, with `U` acting on the codomain and `V` on the domain.  Note the
argument order follows the composition `U ∘ A ∘ V`, not the alphabet. -/
theorem invariant (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E)
    (A : E →ₗ[𝕜] F) :
    N (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) = N A :=
  N.invariant' U V A

/-- Every rectangular UI seminorm is bounded by the mass of a finite two-sided
unitary-orbit certificate.

This theorem deliberately contains all norm-theoretic content needed by the
`π/2` front. The remaining hard theorem may therefore focus solely on
constructing the orbit certificate. -/
theorem apply_le_of_finiteUnitaryOrbitCertificate
    {mass : ℝ} {X C : E →ₗ[𝕜] F}
    (hcert : HasFiniteUnitaryOrbitCertificate mass X C) :
    N X ≤ mass * N C := by
  classical
  rcases hcert with ⟨n, a, U, V, hX, hmass⟩
  rw [hX]
  calc
    N (∑ i, a i •
        ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap)) ≤
        ∑ i, N (a i •
          ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap)) :=
      N.sum_le (Finset.univ : Finset (Fin n))
        (fun i => a i •
          ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap))
    _ = ∑ i, ‖a i‖ * N C := by
      apply Finset.sum_congr rfl
      intro i _
      rw [N.smul_eq, N.invariant (U i) (V i) C]
    _ = (∑ i, ‖a i‖) * N C := by
      rw [Finset.sum_mul]
    _ ≤ mass * N C :=
      mul_le_mul_of_nonneg_right hmass (N.nonneg C)


/-- Equal singular-value data determines a rectangular map up to left and right
unitary factors.  The right unitary aligns the two Gram eigenbases; Gram
rigidity then supplies the left unitary. -/
theorem exists_unitary_factorization_of_singularValues_eq
    {A B : E →ₗ[𝕜] F} (hσ : A.singularValues = B.singularValues) :
    ∃ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E),
      A = U.toLinearMap ∘ₗ B ∘ₗ V.toLinearMap := by
  let hA := A.isSymmetric_adjoint_comp_self
  let hB := B.isSymmetric_adjoint_comp_self
  let bA := hA.eigenvectorBasis rfl
  let bB := hB.eigenvectorBasis rfl
  let K := bB.equiv bA (Equiv.refl _)
  have hKb : ∀ i, K (bB i) = bA i := fun i => by
    simp [K, bA, bB]
  have hKsymm : ∀ i, K.symm (bA i) = bB i := fun i => by
    rw [← hKb i, LinearIsometryEquiv.symm_apply_apply]
  have heig : hA.eigenvalues rfl = hB.eigenvalues rfl := by
    funext i
    rw [← A.sq_singularValues_fin rfl i,
      ← B.sq_singularValues_fin rfl i, hσ]
  have hgram_conj : A.adjoint ∘ₗ A =
      K.toLinearMap ∘ₗ (B.adjoint ∘ₗ B) ∘ₗ K.symm.toLinearMap := by
    refine bA.toBasis.ext fun i => ?_
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change (A.adjoint ∘ₗ A) (bA i) =
      K ((B.adjoint ∘ₗ B) (K.symm (bA i)))
    rw [hKsymm i]
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change (A.adjoint ∘ₗ A) (hA.eigenvectorBasis rfl i) =
      K ((B.adjoint ∘ₗ B) (hB.eigenvectorBasis rfl i))
    rw [hA.apply_eigenvectorBasis rfl i,
      hB.apply_eigenvectorBasis rfl i, map_smul, hKb i,
      congrFun heig i]
  have hgram : B.adjoint ∘ₗ B =
      (A ∘ₗ K.toLinearMap).adjoint ∘ₗ (A ∘ₗ K.toLinearMap) := by
    ext x
    have hx := congrArg K.symm (LinearMap.congr_fun hgram_conj (K x))
    simpa only [LinearMap.adjoint_comp, K.adjoint_toLinearMap_eq_symm,
      LinearMap.comp_apply,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
      LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.apply_symm_apply] using hx.symm
  have hinner : ∀ x y,
      ⟪B x, B y⟫_𝕜 = ⟪(A ∘ₗ K.toLinearMap) x, (A ∘ₗ K.toLinearMap) y⟫_𝕜 := by
    intro x y
    calc
      ⟪B x, B y⟫_𝕜 = ⟪(B.adjoint ∘ₗ B) x, y⟫_𝕜 := by
        rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
      _ = ⟪((A ∘ₗ K.toLinearMap).adjoint ∘ₗ
          (A ∘ₗ K.toLinearMap)) x, y⟫_𝕜 := by rw [hgram]
      _ = ⟪(A ∘ₗ K.toLinearMap) x, (A ∘ₗ K.toLinearMap) y⟫_𝕜 := by
        rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  obtain ⟨U, hU⟩ := exists_linearIsometryEquiv_map_eq_of_inner_eq
    (φ := fun x : E => B x)
    (ψ := fun x : E => (A ∘ₗ K.toLinearMap) x) hinner
  refine ⟨U, K.symm, ?_⟩
  ext x
  simpa only [LinearMap.comp_apply,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
    LinearIsometryEquiv.apply_symm_apply] using (hU (K.symm x)).symm

/-- A rectangular unitarily invariant norm depends only on the complete
singular-value sequence. -/
theorem apply_eq_of_singularValues_eq {A B : E →ₗ[𝕜] F}
    (hσ : A.singularValues = B.singularValues) : N A = N B := by
  obtain ⟨U, V, hfac⟩ :=
    exists_unitary_factorization_of_singularValues_eq hσ
  rw [hfac]
  exact N.invariant U V B

/-- Pull a rectangular UI norm back along an isometric embedding of the
codomain.  The transported norm measures `A : E → H` by measuring
`ι ∘ A : E → F`. -/
@[expose]
noncomputable def codomainIsometryTransport
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : RectangularUnitarilyInvariantSeminorm 𝕜 E F)
    (ι : H →ₗᵢ[𝕜] F) :
    RectangularUnitarilyInvariantSeminorm 𝕜 E H where
  toFun A := N (ι.toLinearMap ∘ₗ A)
  add_le' A B := by
    have hmap : ι.toLinearMap ∘ₗ (A + B) =
        (ι.toLinearMap ∘ₗ A) + (ι.toLinearMap ∘ₗ B) := by
      ext x
      simp
    rw [hmap]
    exact N.add_le _ _
  smul' a A := by
    have hmap : ι.toLinearMap ∘ₗ (a • A) =
        a • (ι.toLinearMap ∘ₗ A) := by
      ext x
      simp
    rw [hmap]
    exact N.smul_eq _ _
  invariant' U V A := by
    apply N.apply_eq_of_singularValues_eq
    calc
      (ι.toLinearMap ∘ₗ (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)).singularValues =
          (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).singularValues :=
        singularValues_linearIsometry_comp ι _
      _ = A.singularValues := by
        rw [singularValues_unitary_comp, singularValues_comp_unitary]
      _ = (ι.toLinearMap ∘ₗ A).singularValues :=
        (singularValues_linearIsometry_comp ι A).symm

/-- Codomain transport, unfolded. -/
@[simp] theorem codomainIsometryTransport_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : RectangularUnitarilyInvariantSeminorm 𝕜 E F)
    (ι : H →ₗᵢ[𝕜] F) (A : E →ₗ[𝕜] H) :
    N.codomainIsometryTransport ι A = N (ι.toLinearMap ∘ₗ A) :=
  (rfl)

/-- Pull a rectangular UI norm back along the adjoint of an isometric
embedding of the domain.  The transported norm measures `A : H → F` by the
zero-padded map `A ∘ ι⋆ : E → F`. -/
@[expose]
noncomputable def domainIsometryTransport
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : RectangularUnitarilyInvariantSeminorm 𝕜 E F)
    (ι : H →ₗᵢ[𝕜] E) :
    RectangularUnitarilyInvariantSeminorm 𝕜 H F where
  toFun A := N (A ∘ₗ LinearMap.adjoint ι.toLinearMap)
  add_le' A B := by
    have hmap : (A + B) ∘ₗ LinearMap.adjoint ι.toLinearMap =
        (A ∘ₗ LinearMap.adjoint ι.toLinearMap) +
          (B ∘ₗ LinearMap.adjoint ι.toLinearMap) := by
      ext x
      simp
    rw [hmap]
    exact N.add_le _ _
  smul' a A := by
    have hmap : (a • A) ∘ₗ LinearMap.adjoint ι.toLinearMap =
        a • (A ∘ₗ LinearMap.adjoint ι.toLinearMap) := by
      ext x
      simp
    rw [hmap]
    exact N.smul_eq _ _
  invariant' U V A := by
    apply N.apply_eq_of_singularValues_eq
    calc
      ((U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) ∘ₗ
          LinearMap.adjoint ι.toLinearMap).singularValues =
          (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).singularValues :=
        singularValues_comp_adjoint_linearIsometry ι _
      _ = A.singularValues := by
        rw [singularValues_unitary_comp, singularValues_comp_unitary]
      _ = (A ∘ₗ LinearMap.adjoint ι.toLinearMap).singularValues :=
        (singularValues_comp_adjoint_linearIsometry ι A).symm

/-- Domain transport, unfolded. -/
@[simp] theorem domainIsometryTransport_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : RectangularUnitarilyInvariantSeminorm 𝕜 E F)
    (ι : H →ₗᵢ[𝕜] E) (A : H →ₗ[𝕜] F) :
    N.domainIsometryTransport ι A =
      N (A ∘ₗ LinearMap.adjoint ι.toLinearMap) :=
  (rfl)


end RectangularUnitarilyInvariantSeminorm


end TauCeti
