/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm.BlockSum

/-!
# Concrete rectangular unitarily invariant norms

Adjoint transport, composition bounds, the zero extension, and the operator, Frobenius,
Ky Fan and nuclear norms, together with the bridges to and from the square
`UnitarilyInvariantSeminorm`.

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

namespace RectangularUnitarilyInvariantSeminorm

variable (N : RectangularUnitarilyInvariantSeminorm 𝕜 E F)

/- `Module ℝ (E →ₗ[𝕜] F)` is a *local* instance in `Basic`, so it does not survive the
import.  Re-enable it here; making it global would put a second `Module ℝ` structure on
every `𝕜`-linear map space, which is why it is local in the first place. -/
attribute [local instance] realModuleLinearMap


/-- Adjoint transport to the transposed rectangular norm. -/
noncomputable def adjointTransport
    (N : RectangularUnitarilyInvariantSeminorm 𝕜 E F) :
    RectangularUnitarilyInvariantSeminorm 𝕜 F E where
  toFun A := N A.adjoint
  add_le' A B := by
    simpa only [map_add] using N.add_le A.adjoint B.adjoint
  smul' a A := by
    rw [map_smulₛₗ]
    calc
      N ((starRingEnd 𝕜) a • A.adjoint) =
          ‖(starRingEnd 𝕜) a‖ * N A.adjoint :=
        N.smul_eq ((starRingEnd 𝕜) a) A.adjoint
      _ = ‖a‖ * N A.adjoint := by
        congr 1
        -- names the application so the norm bound applies to it directly.
        change ‖star a‖ = ‖a‖
        exact norm_star a
  invariant' U V A := by
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change N (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).adjoint = N A.adjoint
    simpa only [LinearMap.adjoint_comp,
      V.adjoint_toLinearMap_eq_symm, U.adjoint_toLinearMap_eq_symm,
      LinearMap.comp_assoc] using
      N.invariant V.symm U.symm A.adjoint


/-- The transported norm evaluated at an adjoint returns the original norm of
the operator — the defining property of `adjointTransport`. -/
@[simp] theorem adjointTransport_apply (A : E →ₗ[𝕜] F) :
    (adjointTransport N).toFun A.adjoint = N.toFun A := by
  simp only [adjointTransport, LinearMap.adjoint_adjoint]

/-- `adjointTransport_apply` in the **coerced** form, which is how call sites write it.

The `.toFun` form above cannot be rewritten with at a
call site that says `(adjointTransport N) A.adjoint`: the rewrite reports *"did not find an
occurrence of the pattern"*, because the goal carries the `CoeFun` application rather than
the projection. Consumers were working around that with `change`, which is the
`proof-quality` rubric's code smell — the lemma existed but was unusable as stated. -/
@[simp] theorem adjointTransport_coe_apply (A : E →ₗ[𝕜] F) :
    (adjointTransport N) A.adjoint = N A := adjointTransport_apply N A

/-- The transported norm of a *negated* adjoint.

`adjointTransport_coe_apply` cannot fire on this: it matches an argument of the
form `A.adjoint`, and `-C.adjoint` has `Neg.neg` at the head, so simp sees no
adjoint to cancel.  Callers that reverse a Sylvester equation land on exactly
this shape — the reversal introduces the sign — and before 2026-07-30 two proofs
in `Sylvester/Interval.lean` each carried an eight-line comment explaining the
failure followed by the same `change`/`map_neg`/`adjoint_adjoint` fix by hand. -/
@[simp] theorem adjointTransport_neg_adjoint_apply (C : E →ₗ[𝕜] F) :
    (adjointTransport N) (-C.adjoint) = N C := by
  change N ((-C.adjoint).adjoint) = N C
  rw [map_neg, LinearMap.adjoint_adjoint, N.apply_neg]


/-- Left ideal property.  This is Fan dominance applied to the pointwise
singular-value bound for composition by a bounded left factor. -/
theorem comp_le_opNorm_mul (C : F →ₗ[𝕜] F) (A : E →ₗ[𝕜] F) :
    N (C ∘ₗ A) ≤ ‖C.toContinuousLinearMap‖ * N A := by
  let c : ℝ := ‖C.toContinuousLinearMap‖
  have hc : 0 ≤ c := norm_nonneg _
  calc
    N (C ∘ₗ A) ≤ N (((c : 𝕜)) • A) :=
      N.apply_le_of_singularValues_le fun i => by
        rw [singularValues_real_smul A hc i]
        exact singularValues_comp_le hc
          (fun y => C.toContinuousLinearMap.le_opNorm y) A i
    _ = c * N A := by
      rw [N.smul_eq, RCLike.norm_ofReal, abs_of_nonneg hc]
    _ = ‖C.toContinuousLinearMap‖ * N A := by rfl

/-- Right ideal property, obtained from the left ideal property by adjoint
transport. -/
theorem comp_le_mul_opNorm (A : E →ₗ[𝕜] F) (C : E →ₗ[𝕜] E) :
    N (A ∘ₗ C) ≤ N A * ‖C.toContinuousLinearMap‖ := by
  have h := comp_le_opNorm_mul (adjointTransport N) C.adjoint A.adjoint
  rw [← LinearMap.adjoint_comp, adjointTransport_apply,
    adjointTransport_apply, LinearMap.adjoint_toContinuousLinearMap,
    LinearIsometryEquiv.norm_map] at h
  simpa only [mul_comm] using h

/-- Product-coordinate form of the zero extension, `(x,y) ↦ (0,A x)`. -/
private noncomputable def zeroExtensionProd (A : E →ₗ[𝕜] F) :
    (E × F) →ₗ[𝕜] (E × F) where
  toFun z := (0, A z.1)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Zero extension of a rectangular map to a square endomorphism. -/
noncomputable def zeroExtension (A : E →ₗ[𝕜] F) :
    WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
    zeroExtensionProd A ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- The zero extension places `A` in the second component and zero in the
first, which is what makes a rectangular operator into a square one without
changing its singular values. -/
@[simp] theorem zeroExtension_apply (A : E →ₗ[𝕜] F)
    (z : WithLp 2 (E × F)) :
    zeroExtension A z = WithLp.toLp 2 (0, A (WithLp.ofLp z).1) := by
  rfl

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Zero extension is additive. -/
theorem zeroExtension_add (A B : E →ₗ[𝕜] F) :
    zeroExtension (A + B) = zeroExtension A + zeroExtension B := by
  ext z
  simp only [zeroExtension_apply, LinearMap.add_apply]
  simpa using
    (WithLp.toLp_add (p := 2)
      ((0, A (WithLp.ofLp z).1) : E × F)
      ((0, B (WithLp.ofLp z).1) : E × F))

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Zero extension commutes with scalar multiplication. -/
theorem zeroExtension_smul (a : 𝕜) (A : E →ₗ[𝕜] F) :
    zeroExtension (a • A) = a • zeroExtension A := by
  ext z
  simp only [zeroExtension_apply, LinearMap.smul_apply]
  simpa [smul_zero] using
    (WithLp.toLp_smul (p := 2) a ((0, A (WithLp.ofLp z).1) : E × F))

/-- Isometric embedding into the first coordinate of the `L²` product. -/
private noncomputable def zeroExtensionInl :
    E →ₗᵢ[𝕜] WithLp 2 (E × F) :=
  (((WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
      LinearMap.inl 𝕜 E F)).isometryOfInner (by
    intro x y
    simp [WithLp.prod_inner_apply])

/-- Isometric embedding into the second coordinate of the `L²` product. -/
private noncomputable def zeroExtensionInr :
    F →ₗᵢ[𝕜] WithLp 2 (E × F) :=
  (((WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
      LinearMap.inr 𝕜 E F)).isometryOfInner (by
    intro x y
    simp [WithLp.prod_inner_apply])

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
@[simp] private theorem zeroExtensionInl_apply (x : E) :
    zeroExtensionInl (𝕜 := 𝕜) (F := F) x = WithLp.toLp 2 (x, 0) := by
  rfl

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
@[simp] private theorem zeroExtensionInr_apply (y : F) :
    zeroExtensionInr (𝕜 := 𝕜) (E := E) y = WithLp.toLp 2 (0, y) := by
  rfl

@[simp]
private theorem zeroExtensionInl_adjoint_apply
    (z : WithLp 2 (E × F)) :
    LinearMap.adjoint (zeroExtensionInl (𝕜 := 𝕜) (F := F)).toLinearMap z = z.fst := by
  apply ext_inner_right 𝕜
  intro x
  rw [LinearMap.adjoint_inner_left]
  simp [WithLp.prod_inner_apply]

/-- Singular values are unchanged by zero extension, apart from zero padding.
-/
theorem singularValues_zeroExtension (A : E →ₗ[𝕜] F) :
    (zeroExtension A).singularValues = A.singularValues := by
  let ιE : E →ₗᵢ[𝕜] WithLp 2 (E × F) :=
    zeroExtensionInl (𝕜 := 𝕜) (E := E) (F := F)
  let ιF : F →ₗᵢ[𝕜] WithLp 2 (E × F) :=
    zeroExtensionInr (𝕜 := 𝕜) (E := E) (F := F)
  have hfactor : zeroExtension A =
      ιF.toLinearMap ∘ₗ
        (A ∘ₗ LinearMap.adjoint ιE.toLinearMap) := by
    ext z
    simp only [LinearMap.comp_apply, zeroExtension_apply, ιE, ιF,
      LinearIsometry.coe_toLinearMap, zeroExtensionInr_apply,
      zeroExtensionInl_adjoint_apply, WithLp.ofLp_fst]
  rw [hfactor]
  calc
    (ιF.toLinearMap ∘ₗ
        (A ∘ₗ LinearMap.adjoint ιE.toLinearMap)).singularValues =
        (A ∘ₗ LinearMap.adjoint ιE.toLinearMap).singularValues :=
      singularValues_linearIsometry_comp ιF _
    _ = A.singularValues :=
      singularValues_comp_adjoint_linearIsometry ιE A

/-- Operator norm as a rectangular UI norm. -/
@[expose]
noncomputable def opNorm : RectangularUnitarilyInvariantSeminorm 𝕜 E F where
  toFun A := ‖A.toContinuousLinearMap‖
  add_le' A B := by
    rw [map_add]
    exact norm_add_le _ _
  smul' a A := by
    rw [map_smul]
    exact norm_smul a _
  invariant' U V A := by
    have hcomp :
        (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).toContinuousLinearMap =
          (U : F →L[𝕜] F) ∘L A.toContinuousLinearMap ∘L (V : E →L[𝕜] E) := by
      ext x
      simp
    rw [hcomp]
    simp

/-- The rectangular operator norm is the ordinary operator norm of the
continuous-linear-map view, definitionally. -/
@[simp] theorem opNorm_apply (A : E →ₗ[𝕜] F) :
    opNorm A = ‖A.toContinuousLinearMap‖ := (rfl)

/-- Frobenius/Hilbert--Schmidt norm as a rectangular UI norm. -/
@[expose]
noncomputable def frobenius : RectangularUnitarilyInvariantSeminorm 𝕜 E F where
  toFun A := Real.sqrt
    (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)
  add_le' A B := by
    have hmono :
        Real.sqrt (∑ i, ‖(A + B) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) ≤
          Real.sqrt (∑ i, (‖A (stdOrthonormalBasis 𝕜 E i)‖ +
            ‖B (stdOrthonormalBasis 𝕜 E i)‖) ^ 2) := by
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      rw [LinearMap.add_apply]
      exact norm_add_le _ _
    exact hmono.trans (UnitarilyInvariantSeminorm.sqrt_sum_add_sq_le _ _)
  smul' a A := by
    have h : ∀ i, ‖(a • A) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 =
        ‖a‖ ^ 2 * ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 := fun i => by
      rw [LinearMap.smul_apply, norm_smul, mul_pow]
    rw [show (∑ i, ‖(a • A) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) =
        ‖a‖ ^ 2 * ∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => h i,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg a)]
  invariant' U V A := by
    have key : ∀ i,
        ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)
            (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 =
          ‖A (V (stdOrthonormalBasis 𝕜 E i))‖ ^ 2 := fun i => by
      rw [show (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)
          (stdOrthonormalBasis 𝕜 E i) =
          U (A (V (stdOrthonormalBasis 𝕜 E i))) from rfl,
        U.norm_map]
    rw [show (∑ i, ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)
          (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) =
        ∑ i, ‖A (V (stdOrthonormalBasis 𝕜 E i))‖ ^ 2 from
        Finset.sum_congr rfl fun i _ => key i,
      sum_sq_norm_apply_unitary_comp A V rfl (stdOrthonormalBasis 𝕜 E)]

/-- Singular values scale by the norm of an arbitrary scalar. -/
theorem singularValues_smul_rect (a : 𝕜) (A : E →ₗ[𝕜] F) (i : ℕ) :
    (a • A).singularValues i = ‖a‖ * A.singularValues i := by
  have hgram : (a • A).adjoint ∘ₗ (a • A) =
      (((‖a‖ : ℝ) : 𝕜) • A).adjoint ∘ₗ (((‖a‖ : ℝ) : 𝕜) • A) := by
    ext x
    apply ext_inner_right 𝕜
    intro y
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
      LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right,
      RCLike.conj_ofReal]
    rw [← mul_assoc, RCLike.mul_conj]
    ring
  calc
    (a • A).singularValues i =
        (((‖a‖ : ℝ) : 𝕜) • A).singularValues i :=
      congrArg (fun s : ℕ →₀ ℝ => s i)
        (singularValues_eq_of_gram_eq hgram)
    _ = ‖a‖ * A.singularValues i :=
      singularValues_real_smul A (norm_nonneg a) i


/-- Bundled singular-value sequence of a scalar multiple.  This is the
Finsupp-level companion to `singularValues_smul_rect`; it is convenient when
a unitarily invariant norm is compared through its complete gauge sequence. -/
theorem singularValues_smul (a : 𝕜) (A : E →ₗ[𝕜] F) :
    (a • A).singularValues = ‖a‖ • A.singularValues := by
  ext i
  simp [singularValues_smul_rect]

/-- Prefix sums stabilize once the prefix length reaches the domain dimension. -/
theorem rectangularKyFanSum_eq_finrank_of_finrank_le
    (A : E →ₗ[𝕜] F) {k : ℕ} (hk : finrank 𝕜 E ≤ k) :
    rectangularKyFanSum k A = rectangularKyFanSum (finrank 𝕜 E) A := by
  unfold rectangularKyFanSum
  rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono hk)
  intro i hi hiE
  rw [A.singularValues_of_finrank_le]
  exact Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hiE)

private theorem rectangularKyFanSum_eq_zeroExtension
    (k : ℕ) (A : E →ₗ[𝕜] F) :
    rectangularKyFanSum k A = kyFanSum k (zeroExtension A) := by
  rw [kyFanSum_eq_sum_fin]
  unfold rectangularKyFanSum
  rw [singularValues_zeroExtension]

/-- **Rectangular Ky Fan variational principle, upper bound.**

For orthonormal domain and codomain families, the real part of the paired
matrix coefficient sum is bounded by the corresponding singular-value prefix.
The proof embeds both families in the two coordinates of the `L²` product and
applies the square Ky Fan variational principle to `zeroExtension A`. -/
theorem re_sum_inner_map_le_rectangularKyFanSum
    {A : E →ₗ[𝕜] F} {k : ℕ} (hk : k ≤ finrank 𝕜 E)
    {u : Fin k → F} {v : Fin k → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) ≤ rectangularKyFanSum k A := by
  let u' : Fin k → WithLp 2 (E × F) :=
    fun i => WithLp.toLp 2 (0, u i)
  let v' : Fin k → WithLp 2 (E × F) :=
    fun i => WithLp.toLp 2 (v i, 0)
  have hu' : Orthonormal 𝕜 u' := by
    rw [orthonormal_iff_ite] at hu ⊢
    intro i j
    simpa [u', WithLp.prod_inner_apply] using hu i j
  have hv' : Orthonormal 𝕜 v' := by
    rw [orthonormal_iff_ite] at hv ⊢
    intro i j
    simpa [v', WithLp.prod_inner_apply] using hv i j
  have hfin : finrank 𝕜 (WithLp 2 (E × F)) =
      finrank 𝕜 E + finrank 𝕜 F := by
    calc
      finrank 𝕜 (WithLp 2 (E × F)) = finrank 𝕜 (E × F) :=
        (WithLp.linearEquiv 2 𝕜 (E × F)).finrank_eq
      _ = finrank 𝕜 E + finrank 𝕜 F := by
        simp [Module.finrank_prod]
  have hk' : k ≤ finrank 𝕜 (WithLp 2 (E × F)) := by
    rw [hfin]
    omega
  have h := TauCeti.re_sum_inner_map_le_sum_singularValues
    (A := zeroExtension A) hk' hu' hv'
  simpa [u', v', zeroExtension_apply, WithLp.prod_inner_apply,
    rectangularKyFanSum, singularValues_zeroExtension] using h

/-- A convenient witness form of the rectangular Ky Fan upper bound. -/
theorem sum_le_rectangularKyFanSum_of_orthonormal
    {A : E →ₗ[𝕜] F} {k : ℕ} (hk : k ≤ finrank 𝕜 E)
    {u : Fin k → F} {v : Fin k → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) {t : Fin k → ℝ}
    (ht : ∀ i, t i ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜) :
    ∑ i, t i ≤ rectangularKyFanSum k A := by
  calc
    ∑ i, t i ≤ ∑ i, RCLike.re ⟪u i, A (v i)⟫_𝕜 :=
      Finset.sum_le_sum fun i _ => ht i
    _ = RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) := by
      rw [map_sum]
    _ ≤ rectangularKyFanSum k A :=
      re_sum_inner_map_le_rectangularKyFanSum hk hu hv

omit [FiniteDimensional 𝕜 F] in
/-- Rescaling an orthonormal family by unimodular scalars leaves it
orthonormal. -/
theorem orthonormal_unimodular_smul {ι : Type*} {u : ι → F}
    (hu : Orthonormal 𝕜 u) {c : ι → 𝕜} (hc : ∀ i, ‖c i‖ = 1) :
    Orthonormal 𝕜 fun i => c i • u i := by
  classical
  rw [orthonormal_iff_ite] at hu ⊢
  intro i j
  rw [inner_smul_left, inner_smul_right, hu i j]
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, mul_one, RCLike.conj_mul, hc i]
    norm_num
  · rw [ite_eq_right h, mul_zero, mul_zero]

/-- **Absolute-value witness form of the rectangular Ky Fan upper bound.**
Because the two orthonormal families may be rephased independently, the Ky Fan
prefix dominates the sum of the *magnitudes* of the matched coefficients, not
merely their signed real parts.  This is the form needed whenever the sign of
each matched coefficient is dictated by the geometry rather than chosen. -/
theorem sum_abs_le_rectangularKyFanSum_of_orthonormal
    {A : E →ₗ[𝕜] F} {k : ℕ} (hk : k ≤ finrank 𝕜 E)
    {u : Fin k → F} {v : Fin k → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) {t : Fin k → ℝ}
    (ht : ∀ i, t i ≤ |RCLike.re ⟪u i, A (v i)⟫_𝕜|) :
    ∑ i, t i ≤ rectangularKyFanSum k A := by
  classical
  set ε : Fin k → 𝕜 := fun i =>
    if 0 ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜 then 1 else -1 with hε
  have hεnorm : ∀ i, ‖ε i‖ = 1 := by
    intro i
    rw [hε]
    by_cases h : 0 ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜 <;> simp [h]
  refine sum_le_rectangularKyFanSum_of_orthonormal hk
    (orthonormal_unimodular_smul hu hεnorm) hv (t := t) fun i => ?_
  have hval : RCLike.re ⟪ε i • u i, A (v i)⟫_𝕜 =
      |RCLike.re ⟪u i, A (v i)⟫_𝕜| := by
    rw [inner_smul_left, hε]
    by_cases h : 0 ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜
    · simp [h, abs_of_nonneg h]
    · simp [h, abs_of_neg (not_le.mp h)]
  rw [hval]
  exact ht i

/-- **Rectangular Ky Fan variational principle, achievability.**

For `A : E →ₗ[𝕜] F` between finite-dimensional inner product spaces and any `k` no larger
than either dimension, the upper bound `re_sum_inner_map_le_rectangularKyFanSum` is attained:
there are orthonormal `k`-families `v` in the domain and `u` in the codomain with
`re ∑ᵢ ⟪uᵢ, A vᵢ⟫ = ∑_{i<k} σᵢ(A)`.

Both dimension hypotheses are needed, and neither is an artefact of the proof: the statement
asserts the existence of orthonormal `k`-tuples in `E` and in `F`, so it is false as soon as
`k` exceeds either dimension.

The domain family is read off the eigenbasis of `A⋆A`, exactly as in the square case
`exists_orthonormal_re_sum_inner_map_eq`.  The codomain family cannot be obtained from a
unitary the way the square case obtains it from the polar factor, because `A` need not have
one; instead the normalized images `σᵢ⁻¹ • A vᵢ` of the directions with `σᵢ ≠ 0` are an
orthonormal family in `F`, and `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`
completes it.  The directions with `σᵢ = 0` contribute nothing to either side, since
`‖A vᵢ‖ = σᵢ`. -/
theorem exists_orthonormal_re_sum_inner_map_eq_rectangularKyFanSum
    (A : E →ₗ[𝕜] F) {k : ℕ} (hkE : k ≤ finrank 𝕜 E) (hkF : k ≤ finrank 𝕜 F) :
    ∃ (u : Fin k → F) (v : Fin k → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) = rectangularKyFanSum k A := by
  classical
  set hS := A.isSymmetric_adjoint_comp_self with hSdef
  set b := hS.eigenvectorBasis (rfl : finrank 𝕜 E = finrank 𝕜 E) with hbdef
  set v : Fin k → E := fun i => b (Fin.castLE hkE i) with hvdef
  have hv : Orthonormal 𝕜 v := b.orthonormal.comp _ (Fin.castLE_injective hkE)
  -- the Gram relation of the singular directions
  have hgram : ∀ i j : Fin k, ⟪A (v i), A (v j)⟫_𝕜
      = ((A.singularValues (i : ℕ) ^ 2 : ℝ) : 𝕜) * (if i = j then (1 : 𝕜) else 0) := by
    intro i j
    have h1 : ⟪A (v i), A (v j)⟫_𝕜 = ⟪(A.adjoint ∘ₗ A) (v i), v j⟫_𝕜 := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    have h2 : (A.adjoint ∘ₗ A) (v i)
        = ((hS.eigenvalues rfl (Fin.castLE hkE i) : ℝ) : 𝕜) • v i :=
      hS.apply_eigenvectorBasis (rfl : finrank 𝕜 E = finrank 𝕜 E) (Fin.castLE hkE i)
    have h3 : (A.singularValues (i : ℕ) ^ 2 : ℝ)
        = hS.eigenvalues rfl (Fin.castLE hkE i) :=
      A.sq_singularValues_fin (rfl : finrank 𝕜 E = finrank 𝕜 E) (Fin.castLE hkE i)
    rw [h1, h2, inner_smul_left, RCLike.conj_ofReal, h3]
    rw [orthonormal_iff_ite.mp hv i j]
  -- norms of the images
  have hnorm : ∀ i : Fin k, ‖A (v i)‖ = A.singularValues (i : ℕ) := by
    intro i
    have h := hgram i i
    rw [ite_eq_left rfl, mul_one] at h
    have h2 : ‖A (v i)‖ ^ 2 = A.singularValues (i : ℕ) ^ 2 := by
      have := congrArg (RCLike.re (K := 𝕜)) h
      rw [inner_self_eq_norm_sq_to_K] at this
      simpa using this
    have := A.singularValues_nonneg (i : ℕ)
    nlinarith [norm_nonneg (A (v i))]
  -- the codomain family, defined on the indices with a nonzero singular value
  set w : Fin (finrank 𝕜 F) → F := fun j =>
    if h : (j : ℕ) < k then ((A.singularValues (j : ℕ) : ℝ) : 𝕜)⁻¹ • A (v ⟨j, h⟩) else 0
    with hwdef
  set s : Set (Fin (finrank 𝕜 F)) :=
    {j | (j : ℕ) < k ∧ A.singularValues (j : ℕ) ≠ 0} with hsdef
  have hws : Orthonormal 𝕜 (s.domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨j, hj⟩ ⟨j', hj'⟩
    obtain ⟨hjk, hjne⟩ := hj
    obtain ⟨hj'k, hj'ne⟩ := hj'
    have hwj : w j = ((A.singularValues (j : ℕ) : ℝ) : 𝕜)⁻¹ • A (v ⟨j, hjk⟩) := by
      simp [hwdef, hjk]
    have hwj' : w j' = ((A.singularValues (j' : ℕ) : ℝ) : 𝕜)⁻¹ • A (v ⟨j', hj'k⟩) := by
      simp [hwdef, hj'k]
    change ⟪w j, w j'⟫_𝕜 = _
    rw [hwj, hwj', inner_smul_left, inner_smul_right, hgram ⟨j, hjk⟩ ⟨j', hj'k⟩]
    have hj0 : ((A.singularValues (j : ℕ) : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hjne
    rcases eq_or_ne j j' with hjj | hjj
    · subst hjj
      simp only [map_inv₀, RCLike.conj_ofReal]
      push_cast
      field_simp
    · have h1 : (⟨(j : ℕ), hjk⟩ : Fin k) ≠ ⟨(j' : ℕ), hj'k⟩ := by
        simp only [ne_eq, Fin.mk.injEq]
        exact fun hh => hjj (Fin.ext hh)
      simp [h1, hjj, Subtype.ext_iff]
  obtain ⟨c, hc⟩ := hws.exists_orthonormalBasis_extension_of_card_eq
    (Fintype.card_fin _).symm
  set u : Fin k → F := fun i => c (Fin.castLE hkF i) with hudef
  have hu : Orthonormal 𝕜 u := c.orthonormal.comp _ (Fin.castLE_injective hkF)
  refine ⟨u, v, hu, hv, ?_⟩
  have hterm : ∀ i : Fin k, ⟪u i, A (v i)⟫_𝕜 = ((A.singularValues (i : ℕ) : ℝ) : 𝕜) := by
    intro i
    by_cases hz : A.singularValues (i : ℕ) = 0
    · have hA0 : A (v i) = 0 := by
        have h := hnorm i
        rw [hz] at h
        exact norm_eq_zero.mp h
      rw [hA0, inner_zero_right, hz, RCLike.ofReal_zero]
    · have hlt : ((Fin.castLE hkF i : Fin (finrank 𝕜 F)) : ℕ) < k := i.isLt
      have hmem : (Fin.castLE hkF i) ∈ s := ⟨hlt, hz⟩
      have hwv : w (Fin.castLE hkF i) = ((A.singularValues (i : ℕ) : ℝ) : 𝕜)⁻¹ • A (v i) := by
        simp only [hwdef, dite_eq_left hlt]
        rfl
      have h0 : ((A.singularValues (i : ℕ) : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hz
      change ⟪c (Fin.castLE hkF i), A (v i)⟫_𝕜 = _
      rw [hc _ hmem, hwv, inner_smul_left, hgram i i]
      simp only [map_inv₀, RCLike.conj_ofReal]
      push_cast
      field_simp
  rw [Finset.sum_congr rfl fun (i : Fin k) (_ : i ∈ Finset.univ) => hterm i]
  rw [show (∑ i : Fin k, ((A.singularValues (i : ℕ) : ℝ) : 𝕜))
      = ((∑ i : Fin k, A.singularValues (i : ℕ) : ℝ) : 𝕜) by push_cast; rfl,
    RCLike.ofReal_re]
  rfl

/-- **Rectangular Ky Fan subadditivity**: the `k`-th Ky Fan sum of a sum of
operators is at most the sum of the two Ky Fan sums.

Public rather than `private` since 2026-07-30.  `SchattenNorm.lean` carried a
second declaration with *the same fully-qualified name*, legal only because
this one was private and therefore mangled; that one is gone and this is the
declaration every consumer now sees. -/
theorem rectangularKyFanSum_add_le (k : ℕ)
    (A B : E →ₗ[𝕜] F) :
    rectangularKyFanSum k (A + B) ≤
      rectangularKyFanSum k A + rectangularKyFanSum k B := by
  have hadd : zeroExtension (A + B) =
      zeroExtension A + zeroExtension B := by
    ext z
    simp only [zeroExtension_apply, LinearMap.add_apply]
    simpa using
      (WithLp.toLp_add (p := 2)
        ((0, A (WithLp.ofLp z).1) : E × F)
        ((0, B (WithLp.ofLp z).1) : E × F))
  rw [rectangularKyFanSum_eq_zeroExtension,
    rectangularKyFanSum_eq_zeroExtension,
    rectangularKyFanSum_eq_zeroExtension, hadd]
  exact kyFanSum_add_le k _ _

/-- Ky Fan `k`-norm. -/
@[expose]
noncomputable def kyFan (k : ℕ) : RectangularUnitarilyInvariantSeminorm 𝕜 E F where
  toFun A := rectangularKyFanSum k A
  add_le' A B := rectangularKyFanSum_add_le k A B
  smul' a A := by
    unfold rectangularKyFanSum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => singularValues_smul_rect a A (i : ℕ)
  invariant' U V A := by
    unfold rectangularKyFanSum
    rw [singularValues_unitary_comp, singularValues_comp_unitary]

/-- Nuclear/trace norm. -/
@[expose]
noncomputable def nuclear : RectangularUnitarilyInvariantSeminorm 𝕜 E F :=
  kyFan (finrank 𝕜 E)

/-- The rectangular Frobenius norm is the square root of the sum of squared
column norms in any orthonormal basis of the domain.
-/
@[simp]
theorem frobenius_apply (A : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :
    frobenius A = Real.sqrt (∑ i, ‖A (b i)‖ ^ 2) := by
  -- names the application so the norm bound applies to it directly.
  change Real.sqrt (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) = _
  rw [← sum_sq_singularValues A rfl (stdOrthonormalBasis 𝕜 E),
    ← sum_sq_singularValues A rfl b]

/-- Postcomposition by a linear isometry preserves the Frobenius norm. -/
theorem frobenius_linearIsometry_comp
    (ι : F →ₗᵢ[𝕜] G) (A : E →ₗ[𝕜] F) :
    frobenius (ι.toLinearMap ∘ₗ A) = frobenius A := by
  rw [frobenius_apply _ (stdOrthonormalBasis 𝕜 E),
    frobenius_apply _ (stdOrthonormalBasis 𝕜 E)]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap, ι.norm_map]

/-- Orthogonal projection on the codomain is contractive for the Frobenius norm. -/
theorem frobenius_projection_comp_le
    (U : Submodule 𝕜 F) [U.HasOrthogonalProjection] (A : E →ₗ[𝕜] F) :
    frobenius (((U.starProjection : F →L[𝕜] F) : F →ₗ[𝕜] F) ∘ₗ A) ≤ frobenius A := by
  rw [frobenius_apply _ (stdOrthonormalBasis 𝕜 E),
    frobenius_apply _ (stdOrthonormalBasis 𝕜 E)]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun i _ => ?_
  exact pow_le_pow_left₀ (norm_nonneg _) (U.norm_starProjection_apply_le _) 2

/-- Passing from a subtype-valued map to its ambient inclusion preserves the
Frobenius norm. -/
theorem frobenius_subtype_comp
    (U : Submodule 𝕜 F) (A : E →ₗ[𝕜] U) :
    frobenius (U.subtypeₗᵢ.toLinearMap ∘ₗ A) = frobenius A :=
  frobenius_linearIsometry_comp U.subtypeₗᵢ A

/-- The Ky Fan norm evaluates to the prefix sum of singular values.
-/
@[simp]
theorem kyFan_apply (k : ℕ) (A : E →ₗ[𝕜] F) :
    kyFan k A = rectangularKyFanSum k A :=
  (rfl)

/-- A finite two-sided unitary-orbit certificate bounds every rectangular
Ky Fan prefix by the same certificate mass.

This is the exact bridge used by the arbitrary-spectrum Sylvester theorem. -/
theorem rectangularKyFanSum_le_of_finiteUnitaryOrbitCertificate
    {mass : ℝ} {X C : E →ₗ[𝕜] F} (k : ℕ)
    (hcert : HasFiniteUnitaryOrbitCertificate mass X C) :
    rectangularKyFanSum k X ≤ mass * rectangularKyFanSum k C := by
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change kyFan k X ≤ mass * kyFan k C
  exact (kyFan k).apply_le_of_finiteUnitaryOrbitCertificate hcert

/-- The nuclear norm is the full domain-length singular-value sum; singular
values past the rank are zero automatically. -/
@[simp]
theorem nuclear_apply (A : E →ₗ[𝕜] F) :
    nuclear A = ∑ i : Fin (finrank 𝕜 E), A.singularValues (i : ℕ) :=
  (rfl)

/-- The rectangular Frobenius norm is the Euclidean norm of the complete
finite singular-value list. -/
theorem frobenius_eq_sqrt_sum_sq_singularValues (A : E →ₗ[𝕜] F) :
    frobenius A = Real.sqrt
      (∑ i : Fin (finrank 𝕜 E), A.singularValues (i : ℕ) ^ 2) := by
  rw [frobenius_apply A (stdOrthonormalBasis 𝕜 E),
    sum_sq_singularValues A rfl (stdOrthonormalBasis 𝕜 E)]



/-- The nuclear norm of a Gram operator is the squared Frobenius energy, written
as a column-norm sum in any orthonormal basis. -/
theorem nuclear_adjoint_comp_self_eq_sum_sq_norm
    (A : E →ₗ[𝕜] E)
    (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :
    nuclear (A.adjoint ∘ₗ A) = ∑ i, ‖A (b i)‖ ^ 2 := by
  let G := A.adjoint ∘ₗ A
  have hG : G.IsPositive := LinearMap.isPositive_adjoint_comp_self A
  have hGabs : TauCeti.operatorAbs G = G := by
    symm
    exact (LinearMap.isPositive_adjoint_comp_self G).sqrt_unique hG (by
      rw [hG.adjoint_eq])
  rw [nuclear_apply,
    ← sum_re_inner_abs_self_eq_sum_singularValues G rfl b,
    hGabs]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [G, LinearMap.comp_apply, LinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq]

/-- The nuclear norm is bounded by the square root of the domain dimension
times the Frobenius norm.  This is the finite Cauchy--Schwarz inequality for
the complete singular-value list, including its trailing zeros. -/
theorem nuclear_le_sqrt_finrank_mul_frobenius (A : E →ₗ[𝕜] F) :
    nuclear A ≤ Real.sqrt (finrank 𝕜 E) * frobenius A := by
  rw [nuclear_apply, frobenius_eq_sqrt_sum_sq_singularValues]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (s := Finset.univ)
    (f := fun _ : Fin (finrank 𝕜 E) => (1 : ℝ))
    (g := fun i : Fin (finrank 𝕜 E) => A.singularValues (i : ℕ))
  simpa [one_mul, one_pow, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    using hcs

end RectangularUnitarilyInvariantSeminorm

/-- Restrict a rectangular UI norm to square maps. -/
@[expose]
noncomputable def RectangularUnitarilyInvariantSeminorm.toSquare
    (N : RectangularUnitarilyInvariantSeminorm 𝕜 E E) :
    UnitarilyInvariantSeminorm 𝕜 E where
  toFun := N.toFun
  add_le' := N.add_le'
  smul' := N.smul'
  invariant' := N.invariant'


namespace UnitarilyInvariantSeminorm


variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Embed the existing square abstraction into the rectangular API. -/
@[expose]
noncomputable def toRectangular
    (N : UnitarilyInvariantSeminorm 𝕜 E) :
    RectangularUnitarilyInvariantSeminorm 𝕜 E E where
  toFun := N.toFun
  add_le' := N.add_le'
  smul' := N.smul'
  invariant' := N.invariant'


/-- A square unitarily invariant norm, read as a rectangular one, agrees with
itself on square operators. -/
@[simp] theorem toRectangular_apply
    (N : UnitarilyInvariantSeminorm 𝕜 E) (A : E →ₗ[𝕜] E) :
    N.toRectangular A = N A :=
  (rfl)

/-- **The square Frobenius norm is the square restriction of the rectangular one.**

There are two Frobenius constructions in this library — `UnitarilyInvariantSeminorm.frobenius`
on square maps and `RectangularUnitarilyInvariantSeminorm.frobenius` on rectangular ones —
written independently, with byte-identical bodies, neither derived from the other.  This
identifies them.  It is `rfl`: both evaluate `A ↦ √(∑ᵢ ‖A bᵢ‖²)` over the same
`stdOrthonormalBasis`.  That it is `rfl` is the point — the duplication is real, not merely
apparent.

The rest of the finite-dimensional chain is proved elsewhere and hangs off the *rectangular*
construction: `RectangularUnitarilyInvariantSeminorm.schattenNorm_two_apply` identifies the
Schatten `S₂` norm with it, and `hilbertSchmidtEnergy_eq_ofReal_frobenius_sq` identifies the
Hilbert--Schmidt energy with its square.  In that sense the rectangular one is the canonical
reusable owner.

**But it is not the literal implementation owner, and the difference is not cosmetic.** Two
`def`s remain; this theorem relates them, it does not remove one.  Making the square norm
*be* `.toSquare` of the rectangular one is blocked in both available directions:

* In place, it is an import cycle.  The rectangular structure is introduced in
  `RectangularUnitarilyInvariantSeminorm/Basic.lean`, which imports
  `UnitarilyInvariantSeminorm.lean` — the module the square `frobenius` lives in — and this
  file is three modules further down again:
  `Instances → BlockSum → Majorization → Basic → UnitarilyInvariantSeminorm`.
* Moving the square `frobenius` down here instead does compile, but it moves the canonical
  example of a unitarily invariant norm out of the roadmap topic that introduces unitarily
  invariant norms (T05, `UnitarilyInvariantSeminorm.lean`) and into the rectangular topic
  (T07, this file).  Tau Ceti submits one topic per PR against an accepted base, so T05 would
  then propose the abstraction with no instance of it, and every square-only consumer would
  take the entire rectangular closure just to name the Frobenius norm.

Removing the second `def` therefore requires the square seminorm *structure* to be split out
of `UnitarilyInvariantSeminorm.lean` into a module upstream of `Rectangular.../Basic.lean`.
That is a foundational restructure of a 630-line module, not a Frobenius question, and it is
not attempted here. -/
theorem frobenius_toSquare_eq :
    (RectangularUnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E)).toSquare =
      UnitarilyInvariantSeminorm.frobenius 𝕜 E :=
  (rfl)

end UnitarilyInvariantSeminorm
end TauCeti
