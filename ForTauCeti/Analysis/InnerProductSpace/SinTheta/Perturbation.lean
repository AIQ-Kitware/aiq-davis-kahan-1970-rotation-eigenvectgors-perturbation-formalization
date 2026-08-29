/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace
public import ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap
public import ForTauCeti.Analysis.InnerProductSpace.Residual.Ritz
public import ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Interval
public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.SpectralDistance
public import ForTauCeti.Analysis.InnerProductSpace.Residual.AngleEmbedding
public import ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm
public import ForTauCeti.Analysis.InnerProductSpace.RectangularSingularValues
public import ForTauCeti.Analysis.InnerProductSpace.SinTheta.UnitarilyInvariant
public import ForTauCeti.Analysis.InnerProductSpace.SinTheta.OperatorNorm
public import ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.SinTheta
public import ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
public import ForTauCeti.Analysis.InnerProductSpace.SinTheta.DirectedBounds

/-!
# The complete finite-dimensional `sin Θ` theorem family

Literature map:

* `prose/core-arguments/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Section 7, "The sin Theta theorem".
* Davis--Kahan (1970), Section 2 (`sin Θ`) and Section 6 (proof and symmetric
  extension).
* `prose/core-arguments/Yu-Wang-Samworth-2014-core-arguments.tex`,
  Sections "The symmetric-matrix variant" and "Lower bound on the residual".

The residual theorem is the numerical analyst's form.  The perturbation
version is the operator theorist's form.  Both are stated for every relevant
unitarily invariant norm, followed by the interval, spectral-projector, and
concrete-norm corollaries expected from the final API.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/SinTheta/Perturbation.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

## The split

This file held all four sections in 1110 lines, over Tau Ceti's stated 1000-line
limit for a new file (`ForTauCeti/README.md` §4) — the last module in the library
over it. It is divided at its own `## Perturbation form` boundary:

* the residual, directed and two-sided projector-difference bounds are now in
  `ForTauCeti.Analysis.InnerProductSpace.SinTheta.DirectedBounds`, which this
  module imports;
* this file keeps the **perturbation form** — the six private lemmas transporting
  a bound across the canonical isometric inclusion of a subspace, and the wrappers
  built on them: `sinTheta_perturbation_le`, `sinAngleOperator_perturbation_le`,
  `sinTheta_perturbation_le_of_orderedGap`, `sinTheta_spectralSubspace_le`,
  `opNorm_sinThetaMap_le_of_intervalGap`,
  `frobenius_sinTheta_residual_le_of_spectralDistance`,
  `opNorm_projection_sub_projection_le`,
  `opNorm_spectralProjection_sub_spectralProjection_le`, `frobenius_sinTheta_le`,
  `kyFan_sinTheta_le` and `sinTheta_perturbation_le_of_spectralDistance`.

The seam is that transport: nothing in `DirectedBounds` mentions a domain
isometry, and everything kept here does. **No statement, signature, proof,
attribute or declaration name changed**, and a consumer's
`import ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation` still
resolves to the whole development.
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

/-! ## Perturbation form -/

/-- The adjoint of the canonical isometric inclusion of a subspace is its
orthogonal projection onto that subspace.  This is the finite-dimensional
bridge used by `domainIsometryTransport` in the perturbation wrappers below. -/
private theorem adjoint_subtype_eq_orthogonalProjectionOnto
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.adjoint U.subtypeₗᵢ.toLinearMap =
      U.orthogonalProjectionOnto.toLinearMap := by
  rw [eq_comm]
  apply (LinearMap.eq_adjoint_iff
    U.orthogonalProjectionOnto.toLinearMap U.subtype).2
  intro x y
  -- states the inner-product goal against the projection's defining property.
  change ⟪U.starProjection x, (y : E)⟫_𝕜 = ⟪x, (y : E)⟫_𝕜
  rw [U.inner_starProjection_left_eq_right,
    U.starProjection_eq_self_iff.mpr y.2]

omit [FiniteDimensional 𝕜 E] in
/-- The linear map underlying the canonical isometric inclusion is the
ordinary submodule inclusion. -/
private theorem subtypeₗᵢ_toLinearMap_eq_subtype
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    U.subtypeₗᵢ.toLinearMap = U.subtype := by
  ext x
  rfl

/-- The adjoint of the ordinary submodule inclusion is orthogonal projection
onto that subspace. -/
private theorem adjoint_subtypeLinearMap_eq_orthogonalProjectionOnto
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.adjoint U.subtype =
      U.orthogonalProjectionOnto.toLinearMap := by
  rw [← subtypeₗᵢ_toLinearMap_eq_subtype U]
  exact adjoint_subtype_eq_orthogonalProjectionOnto U

/-- The adjoint of orthogonal projection onto a subspace, viewed as a map into
that subspace, is the canonical inclusion. -/
private theorem adjoint_orthogonalProjectionOnto_eq_subtype
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.adjoint U.orthogonalProjectionOnto.toLinearMap = U.subtype := by
  rw [← adjoint_subtype_eq_orthogonalProjectionOnto U,
    LinearMap.adjoint_adjoint,
    subtypeₗᵢ_toLinearMap_eq_subtype]

/-- **The adjoint of a cross-block map.**  Projecting onto `W` after including `V` transposes to
projecting onto `V` after including `W`.

Both `sin Θ` block arguments in this file form the two off-diagonal blocks of a perturbation and
then need each one's adjoint; without this the same three-lemma `simp only` is written once per
block. -/
private theorem adjoint_orthogonalProjectionOnto_comp_subtype
    (W V : Submodule 𝕜 E) [W.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    LinearMap.adjoint (W.orthogonalProjectionOnto.toLinearMap ∘ₗ V.subtype) =
      V.orthogonalProjectionOnto.toLinearMap ∘ₗ W.subtype := by
  simp only [LinearMap.adjoint_comp, adjoint_subtypeLinearMap_eq_orthogonalProjectionOnto,
    adjoint_orthogonalProjectionOnto_eq_subtype]

/-- The same transposition with a symmetric operator inserted between the projection and the
inclusion. -/
private theorem adjoint_orthogonalProjectionOnto_comp_op_subtype
    (W V : Submodule 𝕜 E) [W.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {T : E →ₗ[𝕜] E} (hT : LinearMap.adjoint T = T) :
    LinearMap.adjoint (W.orthogonalProjectionOnto.toLinearMap ∘ₗ (T ∘ₗ V.subtype)) =
      (V.orthogonalProjectionOnto.toLinearMap ∘ₗ T) ∘ₗ W.subtype := by
  simp only [LinearMap.adjoint_comp, hT,
    adjoint_subtypeLinearMap_eq_orthogonalProjectionOnto,
    adjoint_orthogonalProjectionOnto_eq_subtype, LinearMap.comp_assoc]

/-- Transporting the rectangular sine embedding on `U` back to the ambient
square space gives the one-sided sine cross projection `P_{Vᗮ} P_U`. -/
@[simp]
private theorem domainTransport_sinThetaEmbedding_apply
    (N : UnitarilyInvariantSeminorm 𝕜 E)
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    (N.toRectangular.domainIsometryTransport U.subtypeₗᵢ)
        (sinThetaEmbedding V U.subtypeₗᵢ) = N (sinThetaMap U V) := by
  -- states the goal with the local definitions unfolded, in the exact shape the
  -- following rewrite needs. `simp only` on those definitions normalises further
  -- and the rewrite then has nothing to match -- tried, and it fails here.
  change N ((sinThetaEmbedding V U.subtypeₗᵢ) ∘ₗ
      LinearMap.adjoint U.subtypeₗᵢ.toLinearMap) = N (sinThetaMap U V)
  rw [adjoint_subtype_eq_orthogonalProjectionOnto]
  congr 1

/-- The transported residual of the reducing inclusion is bounded by the
ambient perturbation norm. -/
private theorem domainTransport_residual_le
    (N : UnitarilyInvariantSeminorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U) :
    (N.toRectangular.domainIsometryTransport U.subtypeₗᵢ)
        (residual B U.subtypeₗᵢ (A.restrict hU)) ≤ N (B - A) := by
  have hres : residual B U.subtypeₗᵢ (A.restrict hU) =
      (B - A) ∘ₗ U.subtype := by
    ext x
    -- states the goal with the local definitions unfolded, in the exact shape the
    -- following rewrite needs. `simp only` on those definitions normalises further
    -- and the rewrite then has nothing to match -- tried, and it fails here.
    change B (x : E) - A (x : E) = (B - A) (x : E)
    rfl
  -- states the goal with the local definitions unfolded, in the exact shape the
  -- following rewrite needs. `simp only` on those definitions normalises further
  -- and the rewrite then has nothing to match -- tried, and it fails here.
  change N ((residual B U.subtypeₗᵢ (A.restrict hU)) ∘ₗ
      LinearMap.adjoint U.subtypeₗᵢ.toLinearMap) ≤ N (B - A)
  rw [hres, adjoint_subtype_eq_orthogonalProjectionOnto]
  have hcomp : ((B - A) ∘ₗ U.subtype) ∘ₗ
      U.orthogonalProjectionOnto.toLinearMap =
      (B - A) ∘ₗ projection U := by
    ext x
    rfl
  rw [hcomp]
  calc
    N ((B - A) ∘ₗ projection U) ≤ N (B - A) * 1 :=
      N.apply_comp_le' zero_le_one fun x => by
        -- states the norm goal against the local definition so the operator-norm bound
        -- applies directly; `simp only` would unfold the composition further than the
        -- bound lemma expects.
        change ‖U.starProjection x‖ ≤ 1 * ‖x‖
        simpa using U.norm_starProjection_apply_le x
    _ = N (B - A) := mul_one _


/-- **Davis--Kahan `sin Θ`, perturbation form, every square UI norm.**
-/
theorem sinTheta_perturbation_le
    (N : UnitarilyInvariantSeminorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    δ * N (sinThetaMap U V) ≤ N (B - A) := by
  let NU : RectangularUnitarilyInvariantSeminorm 𝕜 U E :=
    N.toRectangular.domainIsometryTransport U.subtypeₗᵢ
  have hM : (A.restrict hU).IsSymmetric := isSymmetric_restrict hA hU
  have hMspec : SpectrumIn (A.restrict hU) ⊤ (Set.Icc a b) :=
    (spectrumIn_restrict_iff A hU (Set.Icc a b)).2 hgap.1
  have hres :
      δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) ≤
        NU (residual B U.subtypeₗᵢ (A.restrict hU)) :=
    sinTheta_residual_le (A := B) (U := V) (M := A.restrict hU)
      NU hB hV U.subtypeₗᵢ hM hδ hMspec hgap.2
  have hsin :
      NU (sinThetaEmbedding V U.subtypeₗᵢ) = N (sinThetaMap U V) :=
    domainTransport_sinThetaEmbedding_apply N U V
  have hresBound :
      NU (residual B U.subtypeₗᵢ (A.restrict hU)) ≤ N (B - A) :=
    domainTransport_residual_le (B := B) N hU
  calc
    δ * N (sinThetaMap U V) =
        δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) := by rw [hsin]
    _ ≤ NU (residual B U.subtypeₗᵢ (A.restrict hU)) := hres
    _ ≤ N (B - A) := hresBound

/-- **The scaled compression of a reducing block is Ky Fan dominated by its
residual.**  For symmetric `A`, `B` with `U` invariant under `A` and `Wᗮ`
invariant under `B`, an interval/exterior gap of width `δ` gives

`Σₖ σ (δ • P_{Wᗮ}|_U) ≤ Σₖ σ (P_{Wᗮ} (B - A)|_U)`

at every `k`.  The proof restricts both operators to their blocks, transports the
gap through `spectrumIn_restrict_iff`, checks the Sylvester equation
`B|_{Wᗮ} X - X A|_U = C`, and applies `kyFan_sylvester_le_of_intervalGap`.

`sinAngleOperator_perturbation_le` needs this on both diagonals — once as
`(A, B, U, V)` and once as `(B, A, V, U)` — and built it twice inline. -/
private theorem kyFanSum_smul_compression_le_of_intervalExteriorGap
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 E} [W.HasOrthogonalProjection]
    (hU : IsInvariant A U) (hWperp : IsInvariant B Wᗮ)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U W a b δ) (k : ℕ) :
    RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
        (((δ : ℝ) : 𝕜) •
          (Wᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype)) ≤
      RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
        (Wᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ ((B - A) ∘ₗ U.subtype)) := by
  set AU : U →ₗ[𝕜] U := A.restrict hU with hAUdef
  set BWperp : Wᗮ →ₗ[𝕜] Wᗮ := B.restrict hWperp with hBWdef
  set X : U →ₗ[𝕜] Wᗮ :=
    Wᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype with hXdef
  set C : U →ₗ[𝕜] Wᗮ :=
    Wᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ ((B - A) ∘ₗ U.subtype) with hCdef
  have hAU : AU.IsSymmetric := isSymmetric_restrict hA hU
  have hBWperp : BWperp.IsSymmetric := isSymmetric_restrict hB hWperp
  have hgap' : IntervalSylvesterGap BWperp AU a b δ := by
    constructor
    · exact (spectrumIn_restrict_iff A hU (Set.Icc a b)).2 hgap.1
    · exact (spectrumIn_restrict_iff B hWperp
        {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}).2 hgap.2
  have hEq : BWperp ∘ₗ X - X ∘ₗ AU = C := by
    ext x
    have hcomm := projection_apply_comm_of_isInvariant hB hWperp (x : E)
    -- states the goal with the local definitions unfolded, in the exact shape the
    -- following rewrite needs. `simp only` on those definitions normalises further
    -- and the rewrite then has nothing to match -- tried, and it fails here.
    change Wᗮ.starProjection (B (x : E)) =
      B (Wᗮ.starProjection (x : E)) at hcomm
    -- and the goal, in the matching shape: `simp only` on the local definitions
    -- normalises further and leaves the rewrite below nothing to match.
    change B (Wᗮ.starProjection (x : E)) -
        Wᗮ.starProjection (A (x : E)) =
      Wᗮ.starProjection ((B - A) (x : E))
    rw [← hcomm]
    simp only [LinearMap.sub_apply, map_sub]
  -- states the goal with the local definitions unfolded, in the exact shape the
  -- following rewrite needs. `simp only` on those definitions normalises further
  -- and the rewrite then has nothing to match -- tried, and it fails here.
  change (RectangularUnitarilyInvariantSeminorm.kyFan k) (((δ : ℝ) : 𝕜) • X) ≤
    (RectangularUnitarilyInvariantSeminorm.kyFan k) C
  rw [(RectangularUnitarilyInvariantSeminorm.kyFan k).smul_eq,
    RCLike.norm_ofReal, abs_of_nonneg hδ.le]
  exact kyFan_sylvester_le_of_intervalGap hBWperp hAU hδ hgap' hEq k

/-- **The orthogonal block sum turns the two diagonal Ky Fan bounds into a bound
on the projector difference.**  Transport the two compressions into
`WithLp 2 (U × Uᗮ) → WithLp 2 (Vᗮ × V)` coordinates, take the orthogonal block
sum, and read the result back through the ambient norm.

This is the middle third of `sinAngleOperator_perturbation_le`, stated
separately because it is one step: everything between "the diagonals are Ky Fan
dominated" and "the projector difference is norm dominated" belongs to it, and
none of it mentions the spectral gap that produced the diagonal bounds.

**Why it is still long after that split.**  Roughly a third of the body is ten
`let`s naming the block-coordinate data: the two cross blocks `XUV`/`XVU` and
their residuals `CUV`/`CVU`, the two orthogonal decompositions `EU`/`EV`, the
transported norm `NB`, the two assembled block maps, and `liftBlock`.  Those are
not intermediate *steps* and factoring them out means passing all ten back in as
arguments, which trades length for a signature nobody can read.  The argument
proper is four moves: block the two sides, scale out `δ`, transport the norm
through `liftBlock`, and identify the two lifted blocks with the operators in
the statement. -/
private theorem uiNorm_projection_sub_le_of_kyFanSum_le
    (N : UnitarilyInvariantSeminorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ)
    (hkyUV : ∀ k, RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
        (((δ : ℝ) : 𝕜) •
          (Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype)) ≤
      RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
        (Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ ((B - A) ∘ₗ U.subtype)))
    (hkyVU : ∀ k, RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
        (((δ : ℝ) : 𝕜) •
          (-(Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ V.subtype).adjoint)) ≤
      RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
        (Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ
          ((A - B) ∘ₗ V.subtype)).adjoint) :
    δ * N (projection U - projection V) ≤
      N ((B - A) ∘ₗ projection U - projection V ∘ₗ (B - A)) := by
  let XUV : U →ₗ[𝕜] Vᗮ :=
    Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype
  let CUV : U →ₗ[𝕜] Vᗮ :=
    Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ ((B - A) ∘ₗ U.subtype)
  let XVU : V →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ V.subtype
  let CVU : V →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ ((A - B) ∘ₗ V.subtype)
  let EU : E ≃ₗᵢ[𝕜] WithLp 2 (U × Uᗮ) := U.orthogonalDecomposition
  let EV : E ≃ₗᵢ[𝕜] WithLp 2 (Vᗮ × V) :=
    V.orthogonalDecomposition.trans
      (LinearIsometryEquiv.withLpProdComm 2 𝕜 V Vᗮ)
  let NB : RectangularUnitarilyInvariantSeminorm 𝕜
      (WithLp 2 (U × Uᗮ)) (WithLp 2 (Vᗮ × V)) :=
    RectangularUnitarilyInvariantSeminorm.domainIsometryTransport
      (N.toRectangular.codomainIsometryTransport EV.symm.toLinearIsometry)
      EU.symm.toLinearIsometry
  let Xblock := RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum
    XUV (-XVU.adjoint)
  let Cblock := RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum
    CUV CVU.adjoint
  have hNBscaled : NB (((δ : ℝ) : 𝕜) • Xblock) ≤ NB Cblock := by
    have h :=
      RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum_apply_le_of_kyFanSum_le
        NB hkyUV hkyVU
    -- states the goal with the local definitions unfolded, in the exact shape the
    -- following rewrite needs. `simp only` on those definitions normalises further
    -- and the rewrite then has nothing to match -- tried, and it fails here.
    change NB (((δ : ℝ) : 𝕜) •
        RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum
          XUV (-XVU.adjoint)) ≤
      NB (RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum
        CUV CVU.adjoint)
    rw [← RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum_smul]
    exact h
  have hNB : δ * NB Xblock ≤ NB Cblock := by
    rw [NB.smul_eq, RCLike.norm_ofReal, abs_of_nonneg hδ.le] at hNBscaled
    exact hNBscaled
  -- The ambient operator represented by a block map in the `U ⊕ Uᗮ` domain
  -- and `Vᗮ ⊕ V` codomain coordinates.  This uses the exact adjoint appearing
  -- in `domainIsometryTransport`, so the norm identity below is definitional.
  let liftBlock :
      ((WithLp 2 (U × Uᗮ)) →ₗ[𝕜] (WithLp 2 (Vᗮ × V))) →
        (E →ₗ[𝕜] E) := fun T =>
    EV.symm.toLinearIsometry.toLinearMap ∘ₗ T ∘ₗ
      LinearMap.adjoint EU.symm.toLinearIsometry.toLinearMap
  have hNB_apply (T : WithLp 2 (U × Uᗮ) →ₗ[𝕜]
      WithLp 2 (Vᗮ × V)) : NB T = N (liftBlock T) := by
    rfl
  have hEUadj :
      LinearMap.adjoint EU.symm.toLinearIsometry.toLinearMap =
        EU.toLinearMap := by
    -- states the goal with the local definitions unfolded, in the exact shape the
    -- following rewrite needs. `simp only` on those definitions normalises further
    -- and the rewrite then has nothing to match -- tried, and it fails here.
    change LinearMap.adjoint EU.symm.toLinearMap = EU.toLinearMap
    exact (EU.symm).adjoint_toLinearMap_eq_symm
  have hXVUadj :
      XVU.adjoint =
        V.orthogonalProjectionOnto.toLinearMap ∘ₗ Uᗮ.subtype :=
    adjoint_orthogonalProjectionOnto_comp_subtype Uᗮ V
  have hCVUadj :
      CVU.adjoint =
        (V.orthogonalProjectionOnto.toLinearMap ∘ₗ (A - B)) ∘ₗ
          Uᗮ.subtype :=
    adjoint_orthogonalProjectionOnto_comp_op_subtype Uᗮ V
      (by simp only [map_sub, hA.adjoint_eq, hB.adjoint_eq])
  have hXlift : liftBlock Xblock = projection U - projection V := by
    ext x
    simp [liftBlock, Xblock, EU, EV, hEUadj, hXVUadj, XUV,
      RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum,
      projection, Submodule.orthogonalDecomposition_apply,
      LinearMap.comp_apply]
  have hClift : liftBlock Cblock =
      (B - A) ∘ₗ projection U - projection V ∘ₗ (B - A) := by
    ext x
    (simp [liftBlock, Cblock, EU, EV, hEUadj, CUV, hCVUadj,
      RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum,
      projection, Submodule.orthogonalDecomposition_apply,
      LinearMap.comp_apply]; module)
  rw [hNB_apply, hNB_apply, hXlift, hClift] at hNB
  exact hNB

/-- **Symmetric sharp `sin Θ` theorem.**  The full-space angle operator
contains both one-sided sine blocks.  For a general UI norm the constant-one
conclusion therefore requires a forward and reverse interval/exterior gap;
two arbitrary mixed spectral-distance gaps support only the separate
`π/2` theory.  A single interval/exterior gap controls only
`sinThetaMap U V` (except in the operator norm).  This is the finite
Davis--Kahan Proposition 6.1 configuration.
-/
theorem sinAngleOperator_perturbation_le
    (N : UnitarilyInvariantSeminorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b c d δ : ℝ} (hδ : 0 < δ)
    (hgapUV : IntervalExteriorGap A B U V a b δ)
    (hgapVU : IntervalExteriorGap B A V U c d δ) :
    δ * N (sinAngleOperator U V) ≤ N (B - A) := by
  classical
  have hUperp : IsInvariant A Uᗮ := isInvariant_orthogonal_of_isSymmetric hA hU
  have hVperp : IsInvariant B Vᗮ := isInvariant_orthogonal_of_isSymmetric hB hV
  -- The two compressions the block-sum below is built from.
  let XUV : U →ₗ[𝕜] Vᗮ :=
    Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype
  let CUV : U →ₗ[𝕜] Vᗮ :=
    Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ
      ((B - A) ∘ₗ U.subtype)
  have hkyUV : ∀ k,
      RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
          (((δ : ℝ) : 𝕜) • XUV) ≤
        RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k CUV :=
    kyFanSum_smul_compression_le_of_intervalExteriorGap hA hB hU hVperp hδ hgapUV
  -- The mirrored compression, for the other diagonal.
  let XVU : V →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ V.subtype
  let CVU : V →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ
      ((A - B) ∘ₗ V.subtype)
  have hkyVU : ∀ k,
      RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
          (((δ : ℝ) : 𝕜) • (-XVU.adjoint)) ≤
        RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k CVU.adjoint := by
    intro k
    have hbase0 :=
      kyFanSum_smul_compression_le_of_intervalExteriorGap hB hA hV hUperp hδ hgapVU k
    have hbase : δ * RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k XVU ≤
        RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k CVU := by
      -- the extracted lemma states the bound with `δ` inside the norm; this pulls it
      -- out, which is the form the adjoint manipulations below expect.
      rw [show RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
              (((δ : ℝ) : 𝕜) • XVU) =
            δ * RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k XVU from by
          -- `rectangularKyFanSum` is `kyFan` under a different name; naming the `kyFan`
          -- form is what lets `smul_eq` fire on the scalar.
          change (RectangularUnitarilyInvariantSeminorm.kyFan k) (((δ : ℝ) : 𝕜) • XVU) = _
          rw [(RectangularUnitarilyInvariantSeminorm.kyFan k).smul_eq,
            RCLike.norm_ofReal, abs_of_nonneg hδ.le]
          rfl] at hbase0
      exact hbase0
    have hleft :
        RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
            (-XVU.adjoint) =
          RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k XVU := by
      calc
        RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
            (-XVU.adjoint) =
            RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
              XVU.adjoint := by
          exact (RectangularUnitarilyInvariantSeminorm.kyFan k).apply_neg XVU.adjoint
        _ = RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k XVU := by
          unfold RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum
          exact Finset.sum_congr rfl fun i _ =>
            XVU.singularValues_adjoint_apply (i : ℕ)
    have hright :
        RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k CVU.adjoint =
          RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k CVU := by
      unfold RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum
      exact Finset.sum_congr rfl fun i _ =>
        CVU.singularValues_adjoint_apply (i : ℕ)
    calc
      RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
          (((δ : ℝ) : 𝕜) • (-XVU.adjoint)) =
          δ * RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k
            (-XVU.adjoint) :=
        RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum_real_smul
          k (-XVU.adjoint) hδ.le
      _ = δ * RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k XVU := by
        rw [hleft]
      _ ≤ RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k CVU := hbase
      _ = RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum k CVU.adjoint :=
        hright.symm
  -- Orthogonal decompositions of the ambient space along each subspace.
  have hNB : δ * N (projection U - projection V) ≤
      N ((B - A) ∘ₗ projection U - projection V ∘ₗ (B - A)) :=
    uiNorm_projection_sub_le_of_kyFanSum_le N hA hB hδ hkyUV hkyVU
  rw [uiNorm_projection_sub_eq_sinAngleOperator N U V] at hNB
  -- The perturbation and the two block reflections.
  let H : E →ₗ[𝕜] E := B - A
  let JU : E ≃ₗᵢ[𝕜] E := U.reflection
  let JV : E ≃ₗᵢ[𝕜] E := V.reflection
  have hchecker : H ∘ₗ projection U - projection V ∘ₗ H =
      (((2 : ℝ)⁻¹ : ℝ) : 𝕜) •
        (H ∘ₗ JU.toLinearMap - JV.toLinearMap ∘ₗ H) := by
    ext x
    simp [H, JU, JV, projection, Submodule.reflection_apply,
      LinearMap.comp_apply]
    module
  have hcheckerNorm :
      N (H ∘ₗ projection U - projection V ∘ₗ H) ≤ N H := by
    rw [hchecker, N.smul_eq, RCLike.norm_ofReal,
      abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹)]
    calc
      (2 : ℝ)⁻¹ * N (H ∘ₗ JU.toLinearMap - JV.toLinearMap ∘ₗ H) ≤
          (2 : ℝ)⁻¹ *
            (N (H ∘ₗ JU.toLinearMap) + N (-(JV.toLinearMap ∘ₗ H))) := by
        gcongr
        simpa [sub_eq_add_neg] using
          N.add_le (H ∘ₗ JU.toLinearMap) (-(JV.toLinearMap ∘ₗ H))
      _ = (2 : ℝ)⁻¹ * (N H + N H) := by
        rw [N.apply_neg, N.invariant_right JU H, N.invariant_left JV H]
      _ = N H := by ring
  exact hNB.trans (by simpa [H] using hcheckerNorm)

/-- Ordered half-line perturbation form.
-/
theorem sinTheta_perturbation_le_of_orderedGap
    (N : UnitarilyInvariantSeminorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedGap A U B Vᗮ δ) :
    δ * N (sinThetaMap U V) ≤ N (B - A) := by
  let NU : RectangularUnitarilyInvariantSeminorm 𝕜 U E :=
    N.toRectangular.domainIsometryTransport U.subtypeₗᵢ
  have hM : (A.restrict hU).IsSymmetric := isSymmetric_restrict hA hU
  have hgap' : OrderedGap (A.restrict hU) ⊤ B Vᗮ δ := by
    intro lam μ hlam hμ
    apply hgap lam μ
    · rw [← restrictedSpectrum_restrict A hU]
      exact hlam
    · exact hμ
  have hres :
      δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) ≤
        NU (residual B U.subtypeₗᵢ (A.restrict hU)) :=
    sinTheta_residual_le_of_orderedGap
      (A := B) (U := V) (M := A.restrict hU) NU hB hV
      U.subtypeₗᵢ hM hδ hgap'
  have hsin :
      NU (sinThetaEmbedding V U.subtypeₗᵢ) = N (sinThetaMap U V) :=
    domainTransport_sinThetaEmbedding_apply N U V
  have hresBound :
      NU (residual B U.subtypeₗᵢ (A.restrict hU)) ≤ N (B - A) :=
    domainTransport_residual_le (B := B) N hU
  calc
    δ * N (sinThetaMap U V) =
        δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) := by rw [hsin]
    _ ≤ NU (residual B U.subtypeₗᵢ (A.restrict hU)) := hres
    _ ≤ N (B - A) := hresBound

/-- Canonical spectral-projector statement with no eigenbasis in the API.
-/
theorem sinTheta_spectralSubspace_le
    (N : UnitarilyInvariantSeminorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hBoutside : SpectrumIn B (spectralSubspace B (Set.Icc a b))ᗮ
      {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * N (sinThetaMap (spectralSubspace A (Set.Icc a b))
        (spectralSubspace B (Set.Icc a b))) ≤ N (B - A) := by
  exact sinTheta_perturbation_le N hA hB
    (isInvariant_spectralSubspace A (Set.Icc a b))
    (isInvariant_spectralSubspace B (Set.Icc a b)) hδ
    ⟨spectrumIn_spectralSubspace A (Set.Icc a b), hBoutside⟩

/-- **Sharp one-sided interval/exterior `sin Θ` bound in operator norm.**

The analytic estimate is delegated to the polar-absorption Sylvester theorem.
Finite dimensionality enters only through restriction of the two diagonal
blocks and the finite spectral bridge used by that theorem. -/
theorem opNorm_sinThetaMap_le_of_intervalGap
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    δ * ‖(sinThetaMap U V).toContinuousLinearMap‖ ≤
      ‖(B - A).toContinuousLinearMap‖ := by
  have hVperp : IsInvariant B Vᗮ := isInvariant_orthogonal_of_isSymmetric hB hV
  let AU : U →ₗ[𝕜] U := A.restrict hU
  let BVperp : Vᗮ →ₗ[𝕜] Vᗮ := B.restrict hVperp
  let X : U →ₗ[𝕜] Vᗮ :=
    Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype
  let C : U →ₗ[𝕜] Vᗮ :=
    Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ ((B - A) ∘ₗ U.subtype)
  have hAU : AU.IsSymmetric := isSymmetric_restrict hA hU
  have hBVperp : BVperp.IsSymmetric := isSymmetric_restrict hB hVperp
  have hgap' : IntervalSylvesterGap BVperp AU a b δ := by
    constructor
    · exact (spectrumIn_restrict_iff A hU (Set.Icc a b)).2 hgap.1
    · exact (spectrumIn_restrict_iff B hVperp
        {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}).2 hgap.2
  have hEq : BVperp ∘ₗ X - X ∘ₗ AU = C := by
    ext x
    have hcomm := projection_apply_comm_of_isInvariant hB hVperp (x : E)
    -- states the goal with the local definitions unfolded, in the exact shape the
    -- following rewrite needs. `simp only` on those definitions normalises further
    -- and the rewrite then has nothing to match -- tried, and it fails here.
    change Vᗮ.starProjection (B (x : E)) =
      B (Vᗮ.starProjection (x : E)) at hcomm
    -- states the goal with the local definitions unfolded, in the exact shape the
    -- following rewrite needs. `simp only` on those definitions normalises further
    -- and the rewrite then has nothing to match -- tried, and it fails here.
    change B (Vᗮ.starProjection (x : E)) -
        Vᗮ.starProjection (A (x : E)) =
      Vᗮ.starProjection ((B - A) (x : E))
    rw [← hcomm]
    simp only [LinearMap.sub_apply, map_sub]
  have hXnorm : ‖X.toContinuousLinearMap‖ =
      ‖(sinThetaMap U V).toContinuousLinearMap‖ := by
    apply le_antisymm
    · refine X.toContinuousLinearMap.opNorm_le_bound
        (norm_nonneg (sinThetaMap U V).toContinuousLinearMap) fun x => ?_
      have hxU : U.starProjection (x : E) = (x : E) :=
        U.starProjection_eq_self_iff.mpr x.2
      have hfull := (sinThetaMap U V).toContinuousLinearMap.le_opNorm (x : E)
      -- states the norm goal against the local definition so the operator-norm bound
      -- applies directly; `simp only` would unfold the composition further than the
      -- bound lemma expects.
      change ‖Vᗮ.starProjection (U.starProjection (x : E))‖ ≤
        ‖(sinThetaMap U V).toContinuousLinearMap‖ * ‖x‖ at hfull
      rw [hxU] at hfull
      exact hfull
    · refine (sinThetaMap U V).toContinuousLinearMap.opNorm_le_bound
        (norm_nonneg X.toContinuousLinearMap) fun x => ?_
      let ux : U := ⟨U.starProjection x, U.starProjection_apply_mem x⟩
      have hXu := X.toContinuousLinearMap.le_opNorm ux
      -- states the norm goal against the local definition so the operator-norm bound
      -- applies directly; `simp only` would unfold the composition further than the
      -- bound lemma expects.
      change ‖Vᗮ.starProjection (U.starProjection x)‖ ≤
        ‖X.toContinuousLinearMap‖ * ‖U.starProjection x‖ at hXu
      -- states the norm goal against the local definition so the operator-norm bound
      -- applies directly; `simp only` would unfold the composition further than the
      -- bound lemma expects.
      change ‖Vᗮ.starProjection (U.starProjection x)‖ ≤
        ‖X.toContinuousLinearMap‖ * ‖x‖
      exact hXu.trans (mul_le_mul_of_nonneg_left
        (U.norm_starProjection_apply_le x) (norm_nonneg X.toContinuousLinearMap))
  have hCnorm : ‖C.toContinuousLinearMap‖ ≤
      ‖(B - A).toContinuousLinearMap‖ := by
    refine C.toContinuousLinearMap.opNorm_le_bound
      (norm_nonneg (B - A).toContinuousLinearMap) fun x => ?_
    -- states the norm goal against the local definition so the operator-norm bound
    -- applies directly; `simp only` would unfold the composition further than the
    -- bound lemma expects.
    change ‖Vᗮ.starProjection ((B - A) (x : E))‖ ≤
      ‖(B - A).toContinuousLinearMap‖ * ‖x‖
    exact (Vᗮ.norm_starProjection_apply_le ((B - A) (x : E))).trans
      ((B - A).toContinuousLinearMap.le_opNorm (x : E))
  have hSylvester := opNorm_sylvester_le_of_intervalGap
    hBVperp hAU hδ hgap' hEq
  rw [hXnorm] at hSylvester
  exact hSylvester.trans hCnorm

/-- General disjoint-spectrum residual form for the Frobenius norm, with
the sharp constant one.  Unlike a general symmetric gauge, the square norm
can be estimated entrywise in eigenbases of the two compressed operators. -/
theorem frobenius_sinTheta_residual_le_of_spectralDistance
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated M ⊤ A Uᗮ δ) :
    δ * RectangularUnitarilyInvariantSeminorm.frobenius
        (sinThetaEmbedding U X) ≤
      RectangularUnitarilyInvariantSeminorm.frobenius (residual A X M) := by
  have hUperp : IsInvariant A Uᗮ := isInvariant_orthogonal_of_isSymmetric hA hU
  let AU : Uᗮ →ₗ[𝕜] Uᗮ := A.restrict hUperp
  let Y : F →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ X.toLinearMap
  let C : F →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ residual A X M
  have hAU : AU.IsSymmetric := isSymmetric_restrict hA hUperp
  have hgap' : SpectraSeparated AU ⊤ M ⊤ δ := by
    intro lam mu hlam hmu
    have hlam' : lam ∈ restrictedSpectrum A Uᗮ := by
      rw [← restrictedSpectrum_restrict A hUperp]
      exact hlam
    have hsep := hgap mu lam hmu hlam'
    simpa [abs_sub_comm] using hsep
  have hEq : AU ∘ₗ Y - Y ∘ₗ M = C :=
    sylvester_projectedResidual_eq hA hU hUperp X M
  have hSylv := frobenius_sylvester_le_of_spectraSeparated
    hAU hM hδ hgap' hEq
  have hY : RectangularUnitarilyInvariantSeminorm.frobenius Y =
      RectangularUnitarilyInvariantSeminorm.frobenius (sinThetaEmbedding U X) := by
    rw [← RectangularUnitarilyInvariantSeminorm.frobenius_subtype_comp Uᗮ Y]
    congr 1
  have hC : RectangularUnitarilyInvariantSeminorm.frobenius C ≤
      RectangularUnitarilyInvariantSeminorm.frobenius (residual A X M) := by
    exact RectangularUnitarilyInvariantSeminorm.frobenius_projection_comp_le
      Uᗮ (residual A X M)
  rw [hY] at hSylv
  exact hSylv.trans hC

/-- Difference-of-projectors operator-norm form.
-/
theorem opNorm_projection_sub_projection_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    (hrank : finrank 𝕜 U = finrank 𝕜 V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    δ * ‖(projection U - projection V).toContinuousLinearMap‖ ≤
      ‖(B - A).toContinuousLinearMap‖ := by
  rw [opNorm_projection_sub_eq_opNorm_sinThetaMap U V hrank]
  exact opNorm_sinThetaMap_le_of_intervalGap hA hB hU hV hδ hgap

/-- **Canonical finite spectral-projector Davis--Kahan theorem.**

This is the standard interval/exterior projector statement with canonical
spectral subspaces.  The equal-rank hypothesis is exactly what turns the
one-sided cross-projection estimate into the norm of the full projector
difference. -/
theorem opNorm_spectralProjection_sub_spectralProjection_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hrank : finrank 𝕜 (spectralSubspace A (Set.Icc a b)) =
      finrank 𝕜 (spectralSubspace B (Set.Icc a b)))
    (hBoutside : SpectrumIn B (spectralSubspace B (Set.Icc a b))ᗮ
      {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * ‖(spectralProjection A (Set.Icc a b) -
        spectralProjection B (Set.Icc a b)).toContinuousLinearMap‖ ≤
      ‖(B - A).toContinuousLinearMap‖ := by
  simpa [spectralProjection, projection] using
    opNorm_projection_sub_projection_le hA hB
      (isInvariant_spectralSubspace A (Set.Icc a b))
      (isInvariant_spectralSubspace B (Set.Icc a b))
      hrank hδ ⟨spectrumIn_spectralSubspace A (Set.Icc a b), hBoutside⟩

/-- Frobenius form.
-/
theorem frobenius_sinTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    δ * UnitarilyInvariantSeminorm.frobenius 𝕜 E (sinThetaMap U V) ≤
      UnitarilyInvariantSeminorm.frobenius 𝕜 E (B - A) := by
  exact sinTheta_perturbation_le (UnitarilyInvariantSeminorm.frobenius 𝕜 E)
    hA hB hU hV hδ hgap

/-- Ky Fan form, simultaneously controlling every singular-value prefix.
-/
theorem kyFan_sinTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) (k : ℕ) :
    δ * kyFanSum k (sinThetaMap U V) ≤ kyFanSum k (B - A) := by
  let NK : UnitarilyInvariantSeminorm 𝕜 E :=
    (RectangularUnitarilyInvariantSeminorm.kyFan
      (𝕜 := 𝕜) (E := E) (F := E) k).toSquare
  have h := sinTheta_perturbation_le NK hA hB hU hV hδ hgap
  simpa [NK, RectangularUnitarilyInvariantSeminorm.toSquare,
    RectangularUnitarilyInvariantSeminorm.kyFan_apply,
    RectangularUnitarilyInvariantSeminorm.rectangularKyFanSum,
    kyFanSum_eq_sum_fin] using h

/-- General two-sided spectral separation with the `π/2` constant.  The
ambient transport proof is complete; the only open analytic input is the Ky Fan
separated reciprocal-multiplier theorem in `Sylvester.lean`.
-/
theorem sinTheta_perturbation_le_of_spectralDistance
    (N : UnitarilyInvariantSeminorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A U B Vᗮ δ) :
    δ * N (sinThetaMap U V) ≤ (Real.pi / 2) * N (B - A) := by
  let NU : RectangularUnitarilyInvariantSeminorm 𝕜 U E :=
    N.toRectangular.domainIsometryTransport U.subtypeₗᵢ
  have hM : (A.restrict hU).IsSymmetric := isSymmetric_restrict hA hU
  have hgap' : SpectraSeparated (A.restrict hU) ⊤ B Vᗮ δ := by
    intro lam μ hlam hμ
    apply hgap lam μ
    · rw [← restrictedSpectrum_restrict A hU]
      exact hlam
    · exact hμ
  have hres :
      δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) ≤
        (Real.pi / 2) * NU (residual B U.subtypeₗᵢ (A.restrict hU)) :=
    sinTheta_residual_le_of_spectralDistance
      (A := B) (U := V) (M := A.restrict hU) NU hB hV
      U.subtypeₗᵢ hM hδ hgap'
  have hsin :
      NU (sinThetaEmbedding V U.subtypeₗᵢ) = N (sinThetaMap U V) :=
    domainTransport_sinThetaEmbedding_apply N U V
  have hresBound :
      NU (residual B U.subtypeₗᵢ (A.restrict hU)) ≤ N (B - A) :=
    domainTransport_residual_le (B := B) N hU
  calc
    δ * N (sinThetaMap U V) =
        δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) := by rw [hsin]
    _ ≤ (Real.pi / 2) *
        NU (residual B U.subtypeₗᵢ (A.restrict hU)) := hres
    _ ≤ (Real.pi / 2) * N (B - A) :=
      mul_le_mul_of_nonneg_left hresBound (by positivity)

end TauCeti
