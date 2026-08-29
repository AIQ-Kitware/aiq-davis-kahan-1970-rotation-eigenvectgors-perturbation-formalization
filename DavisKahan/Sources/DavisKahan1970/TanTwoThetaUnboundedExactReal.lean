/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedAmbientExact
import DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedGramReal
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.ComplexificationGauge

/-!
# Exact real unbounded `tan 2Theta` source wrappers

The hard unbounded estimate is already proved over `ℂ`, while the repository's
real complexification layer proves exact preservation of spectral subspaces,
reflection blocks, approximation singular values, and every paper unitarily
invariant norm.  This module performs only that source-facing descent.

The key implementation point is that directed corners live between subtype
spaces.  We therefore do not rewrite equal spectral submodules through a
`HasOrthogonalProjection`-indexed corner.  Instead we compare each typed corner
with its ambient projection block, complexify that ambient operator exactly, and
then return to the typed corner.  This keeps the transport proof small and avoids
dependent-rewrite elaboration blowups.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.ApproximationNumber
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open RealComplexification

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

local instance instCompleteSpaceCoeOfHasOrthogonalProjectionUnboundedExactReal
    {k : Type*} [RCLike k] {G : Type u} [NormedAddCommGroup G]
    [InnerProductSpace k G] [CompleteSpace G]
    (W : Submodule k G) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

/-! ## Lightweight norm transport for directed corners -/

/-- Approximation singular values of a real directed corner are unchanged by
complexification, with the orthogonal codomain handled through the ambient
projection block so no dependent subtype rewrite is needed. -/
private theorem approximationSingularValue_directedCorner_complexify
    (U : Submodule ℝ E) [U.HasOrthogonalProjection] (K : E →L[ℝ] E) (n : ℕ) :
    approximationSingularValue n
        (paperBlockCompression (complexifySubmodule U)ᗮ (complexifySubmodule U)
          (complexify K)) =
      approximationSingularValue n (paperBlockCompression Uᗮ U K) := by
  have hc := paperProjectionBlock_same_compression (complexifySubmodule U)ᗮ
    (complexifySubmodule U) (complexify K)
  have hr := paperProjectionBlock_same_compression Uᗮ U K
  calc
    approximationSingularValue n
        (paperBlockCompression (complexifySubmodule U)ᗮ (complexifySubmodule U)
          (complexify K)) =
        approximationSingularValue n
          (paperProjectionBlock (complexifySubmodule U)ᗮ (complexifySubmodule U)
            (complexify K)) := (hc n).symm
    _ = approximationSingularValue n (complexify (paperProjectionBlock Uᗮ U K)) := by
      rw [paperProjectionBlock_complexifySubmodule U K]
    _ = approximationSingularValue n (paperProjectionBlock Uᗮ U K) :=
      ComplexificationApproximation.approximationSingularValue_complexify
        (paperProjectionBlock Uᗮ U K) n
    _ = approximationSingularValue n (paperBlockCompression Uᗮ U K) := hr n

/-- Every paper norm gives the same extended value to a real directed corner
and to the corresponding corner of the complexified subspace. -/
private theorem directedCorner_extendedGauge_complexify
    (N : PaperUnitaryInvariantNorm)
    (U : Submodule ℝ E) [U.HasOrthogonalProjection] (K : E →L[ℝ] E) :
    N.extendedGauge
        (paperBlockCompression (complexifySubmodule U)ᗮ (complexifySubmodule U)
          (complexify K)) =
      N.extendedGauge (paperBlockCompression Uᗮ U K) := by
  unfold PaperUnitaryInvariantNorm.extendedGauge
  apply iSup_congr
  intro n
  apply congrArg ENNReal.ofReal
  unfold PaperUnitaryInvariantNorm.prefixGauge PaperUnitaryInvariantNorm.approximationPrefix
  apply congrArg (N.finiteGauge n)
  funext i
  exact approximationSingularValue_directedCorner_complexify U K i

private theorem directedCorner_mem_complexify_iff
    (N : PaperUnitaryInvariantNorm)
    (U : Submodule ℝ E) [U.HasOrthogonalProjection] (K : E →L[ℝ] E) :
    N.Mem
        (paperBlockCompression (complexifySubmodule U)ᗮ (complexifySubmodule U)
          (complexify K)) ↔
      N.Mem (paperBlockCompression Uᗮ U K) := by
  unfold PaperUnitaryInvariantNorm.Mem
  rw [directedCorner_extendedGauge_complexify N U K]

private theorem directedCorner_gauge_complexify
    (N : PaperUnitaryInvariantNorm)
    (U : Submodule ℝ E) [U.HasOrthogonalProjection] (K : E →L[ℝ] E) :
    N.gauge
        (paperBlockCompression (complexifySubmodule U)ᗮ (complexifySubmodule U)
          (complexify K)) =
      N.gauge (paperBlockCompression Uᗮ U K) := by
  unfold PaperUnitaryInvariantNorm.gauge
  rw [directedCorner_extendedGauge_complexify N U K]

/-- The ambient reflection tangent depends only on the value of the source
subspace.  This packages proof irrelevance for its projection instance. -/
private theorem reflectionResidualCorner_mem_congr_unboundedExactReal
    {k : Type*} [RCLike k] {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace k G] [CompleteSpace G]
    (N : PaperUnitaryInvariantNorm)
    {U V : Submodule k G} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U = V) (B : G →L[k] G) :
    N.Mem (reflectionResidualCorner U B) ↔ N.Mem (reflectionResidualCorner V B) := by
  subst h
  rfl

private theorem reflectionTangentCorner_mem_congr_unboundedExactReal
    {k : Type*} [RCLike k] {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace k G] [CompleteSpace G]
    (N : PaperUnitaryInvariantNorm)
    {U V : Submodule k G} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U = V) (Z : G →L[k] G) :
    N.Mem (reflectionTangentCorner U Z) ↔ N.Mem (reflectionTangentCorner V Z) := by
  subst h
  rfl

private theorem reflectionResidualCorner_gauge_congr_unboundedExactReal
    {k : Type*} [RCLike k] {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace k G] [CompleteSpace G]
    (N : PaperUnitaryInvariantNorm)
    {U V : Submodule k G} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U = V) (B : G →L[k] G) :
    N.gauge (reflectionResidualCorner U B) = N.gauge (reflectionResidualCorner V B) := by
  subst h
  rfl

private theorem reflectionTangentCorner_gauge_congr_unboundedExactReal
    {k : Type*} [RCLike k] {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace k G] [CompleteSpace G]
    (N : PaperUnitaryInvariantNorm)
    {U V : Submodule k G} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U = V) (Z : G →L[k] G) :
    N.gauge (reflectionTangentCorner U Z) = N.gauge (reflectionTangentCorner V Z) := by
  subst h
  rfl

private theorem unboundedReflectionTangent_congr_unboundedExactReal
    {k : Type*} [RCLike k] {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace k G] [CompleteSpace G]
    {U V : Submodule k G} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U = V) (Z : G →L[k] G) :
    unboundedReflectionTangent U Z = unboundedReflectionTangent V Z := by
  subst h
  rfl

/-! ## Shared real-to-complex hypothesis transport -/

omit [CompleteSpace E] in
/-- The domain commutation relation complexifies coordinatewise. -/
private theorem complexified_reducing_commutation
    {A : E →ₗ.[ℝ] E} {B Z : E →L[ℝ] E}
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : E), hZdom x⟩ + B (Z (x : E)) = Z (A x) + Z (B (x : E))) :
    ∀ x : (TauCeti.LinearPMap.complexifyReal A).domain,
      TauCeti.LinearPMap.complexifyReal A
          ⟨complexify Z (x : RealComplexification E), mapsDomainTo_complexifyReal hZdom x⟩ +
        complexify B (complexify Z (x : RealComplexification E)) =
      complexify Z (TauCeti.LinearPMap.complexifyReal A x) +
        complexify Z (complexify B (x : RealComplexification E)) := by
  intro y
  have hcoord := (TauCeti.LinearPMap.mem_complexifyReal_domain_iff A
    (y : RealComplexification E)).mp y.2
  refine RealComplexification.ext ?_ ?_
  · exact hZcomm ⟨re (y : RealComplexification E), hcoord.1⟩
  · exact hZcomm ⟨im (y : RealComplexification E), hcoord.2⟩

/-! ## Exact directed residual endpoint -/

/-- **Paper-exact unbounded directed `tan 2Theta₀` theorem over real scalars.**

The caller sees exactly the real source data.  The complexification used in the
proof is discharged completely: the conclusion is a real directed corner, its
real pole certificate, and the same paper unitarily invariant norm. -/
theorem tanTwoTheta_unbounded_directedResidual_paperUINorm_real_exact
    (N : PaperUnitaryInvariantNorm)
    {A : E →ₗ.[ℝ] E} {B Z : E →L[ℝ] E} {a b c : ℝ}
    (hA : _root_.IsSelfAdjoint A)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : E), hZdom x⟩ + B (Z (x : E)) = Z (A x) + Z (B (x : E)))
    (hUa : ∀ x : A.domain,
      (x : E) ∈ TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic →
      ⟪A x, (x : E)⟫_ℝ ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : E) ∈
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ)
    (hab : a < b)
    (hRmem : N.Mem (reflectionResidualCorner
      (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) B)) :
    IsUnit
        ((TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z *
          (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z) ∧
      N.Mem (reflectionTangentCorner
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) Z) ∧
      (b - a) * N.gauge (reflectionTangentCorner
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) Z) ≤
        2 * N.gauge (reflectionResidualCorner
          (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) B) := by
  classical
  let U : Submodule ℝ E :=
    TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic
  have hAc : _root_.IsSelfAdjoint (TauCeti.LinearPMap.complexifyReal A) :=
    TauCeti.LinearPMap.isSelfAdjoint_complexifyReal hA
  have hUeq : complexifySubmodule U =
      TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic := by
    simpa only [U] using
      complexifySubmodule_realSpecRange hA (Set.Iic c) measurableSet_Iic
  have hB' : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic)
      (complexify B) := hUeq ▸ isOddFor_complexifySubmodule hB
  have hZdom' := mapsDomainTo_complexifyReal hZdom
  have hZcomm' := complexified_reducing_commutation hZdom hZcomm
  have hUa' : ∀ y : (TauCeti.LinearPMap.complexifyReal A).domain,
      (y : RealComplexification E) ∈
        TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic →
      (⟪TauCeti.LinearPMap.complexifyReal A y,
          (y : RealComplexification E)⟫_ℂ).re ≤
        a * ‖(y : RealComplexification E)‖ ^ 2 := by
    intro y hy
    rw [← hUeq, mem_complexifySubmodule] at hy
    have hcoord := (TauCeti.LinearPMap.mem_complexifyReal_domain_iff A
      (y : RealComplexification E)).mp y.2
    have h1 := hUa ⟨re (y : RealComplexification E), hcoord.1⟩ hy.1
    have h2 := hUa ⟨im (y : RealComplexification E), hcoord.2⟩ hy.2
    have hsplit : (⟪TauCeti.LinearPMap.complexifyReal A y,
          (y : RealComplexification E)⟫_ℂ).re =
        ⟪A ⟨re (y : RealComplexification E), hcoord.1⟩,
            re (y : RealComplexification E)⟫_ℝ +
          ⟪A ⟨im (y : RealComplexification E), hcoord.2⟩,
            im (y : RealComplexification E)⟫_ℝ := rfl
    rw [hsplit, RealComplexification.norm_sq, mul_add]
    linarith
  have hUb' : ∀ y : (TauCeti.LinearPMap.complexifyReal A).domain,
      (y : RealComplexification E) ∈
        (TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(y : RealComplexification E)‖ ^ 2 ≤
        (⟪TauCeti.LinearPMap.complexifyReal A y,
          (y : RealComplexification E)⟫_ℂ).re := by
    intro y hy
    rw [← hUeq, ← complexifySubmodule_orthogonal, mem_complexifySubmodule] at hy
    have hcoord := (TauCeti.LinearPMap.mem_complexifyReal_domain_iff A
      (y : RealComplexification E)).mp y.2
    have h1 := hUb ⟨re (y : RealComplexification E), hcoord.1⟩ hy.1
    have h2 := hUb ⟨im (y : RealComplexification E), hcoord.2⟩ hy.2
    have hsplit : (⟪TauCeti.LinearPMap.complexifyReal A y,
          (y : RealComplexification E)⟫_ℂ).re =
        ⟪A ⟨re (y : RealComplexification E), hcoord.1⟩,
            re (y : RealComplexification E)⟫_ℝ +
          ⟪A ⟨im (y : RealComplexification E), hcoord.2⟩,
            im (y : RealComplexification E)⟫_ℝ := rfl
    rw [hsplit, RealComplexification.norm_sq, mul_add]
    linarith
  have hZsa' : IsSelfAdjoint (complexify Z) :=
    (complexify_isSelfAdjoint_iff Z).2 hZsa
  have hZ2' : complexify Z * complexify Z = 1 := by
    rw [← complexify_mul, hZ2, complexify_one]
  have hRmem0 : N.Mem
      (reflectionResidualCorner (complexifySubmodule U) (complexify B)) := by
    exact (directedCorner_mem_complexify_iff N U B).2 hRmem
  have hRmem' : N.Mem
      (reflectionResidualCorner
        (TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic)
        (complexify B)) :=
    (reflectionResidualCorner_mem_congr_unboundedExactReal
      N hUeq (complexify B)).1 hRmem0
  have hc := tanTwoTheta_unbounded_directedResidual_paperUINorm_exact
    N hAc hB' hZsa' hZ2' hZdom' hZcomm' hUa' hUb' hab hRmem'
  have hCCc := hc.1
  have hdiag :
      (TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic).diagonalPart
          (complexify Z) = complexify (U.diagonalPart Z) := by
    rw [← diagonalPart_congr hUeq (complexify Z)]
    exact diagonalPart_complexifySubmodule U Z
  rw [hdiag, ← complexify_mul, isUnit_complexify_iff] at hCCc
  have hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z) := hCCc
  have hTmemc : N.Mem
      (reflectionTangentCorner (complexifySubmodule U) (complexify Z)) :=
    (reflectionTangentCorner_mem_congr_unboundedExactReal
      N hUeq (complexify Z)).2 hc.2.1
  have hTcomplex :
      unboundedReflectionTangent (complexifySubmodule U) (complexify Z) =
        complexify (unboundedReflectionTangent U Z) :=
    unboundedReflectionTangent_complexifySubmodule U Z hCC
  change N.Mem
      (paperBlockCompression (complexifySubmodule U)ᗮ (complexifySubmodule U)
        (unboundedReflectionTangent (complexifySubmodule U) (complexify Z))) at hTmemc
  rw [hTcomplex] at hTmemc
  have hTmem : N.Mem (reflectionTangentCorner U Z) :=
    (directedCorner_mem_complexify_iff N U (unboundedReflectionTangent U Z)).1 hTmemc
  have hineqc := hc.2.2
  have htangauge := reflectionTangentCorner_gauge_congr_unboundedExactReal
    N hUeq (complexify Z)
  have hresgauge := reflectionResidualCorner_gauge_congr_unboundedExactReal
    N hUeq (complexify B)
  rw [← htangauge, ← hresgauge] at hineqc
  change (b - a) * N.gauge
      (paperBlockCompression (complexifySubmodule U)ᗮ (complexifySubmodule U)
        (unboundedReflectionTangent (complexifySubmodule U) (complexify Z))) ≤
    2 * N.gauge
      (paperBlockCompression (complexifySubmodule U)ᗮ (complexifySubmodule U)
        (complexify B)) at hineqc
  rw [hTcomplex,
    directedCorner_gauge_complexify N U (unboundedReflectionTangent U Z),
    directedCorner_gauge_complexify N U B] at hineqc
  change IsUnit (U.diagonalPart Z * U.diagonalPart Z) ∧
      N.Mem (reflectionTangentCorner U Z) ∧
      (b - a) * N.gauge (reflectionTangentCorner U Z) ≤
        2 * N.gauge (reflectionResidualCorner U B)
  exact ⟨hCC, hTmem, hineqc⟩

/-! ## Exact ambient endpoint -/

/-- **Paper-exact unbounded ambient `tan 2Theta` theorem over real scalars.**

This is a genuine real-Hilbert-space statement.  The complex ambient theorem is
used only internally; its reflection tangent and source norm descend exactly to
the real operators. -/
theorem tanTwoTheta_unbounded_ambient_paperUINorm_real_exact
    (N : PaperUnitaryInvariantNorm)
    {A : E →ₗ.[ℝ] E} {B Z : E →L[ℝ] E} {a b c : ℝ}
    (hA : _root_.IsSelfAdjoint A)
    (hBsa : IsSelfAdjoint B)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : E), hZdom x⟩ + B (Z (x : E)) = Z (A x) + Z (B (x : E)))
    (hUa : ∀ x : A.domain,
      (x : E) ∈ TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic →
      ⟪A x, (x : E)⟫_ℝ ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : E) ∈
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ)
    (hab : a < b) (hBmem : N.Mem B) :
    IsUnit
        ((TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z *
          (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z) ∧
      N.Mem (unboundedReflectionTangent
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) Z) ∧
      (b - a) * N.gauge (unboundedReflectionTangent
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) Z) ≤
        2 * N.gauge B := by
  classical
  let U : Submodule ℝ E :=
    TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic
  have hAc : _root_.IsSelfAdjoint (TauCeti.LinearPMap.complexifyReal A) :=
    TauCeti.LinearPMap.isSelfAdjoint_complexifyReal hA
  have hUeq : complexifySubmodule U =
      TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic := by
    simpa only [U] using
      complexifySubmodule_realSpecRange hA (Set.Iic c) measurableSet_Iic
  have hB' : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic)
      (complexify B) := hUeq ▸ isOddFor_complexifySubmodule hB
  have hZdom' := mapsDomainTo_complexifyReal hZdom
  have hZcomm' := complexified_reducing_commutation hZdom hZcomm
  have hUa' : ∀ y : (TauCeti.LinearPMap.complexifyReal A).domain,
      (y : RealComplexification E) ∈
        TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic →
      (⟪TauCeti.LinearPMap.complexifyReal A y,
          (y : RealComplexification E)⟫_ℂ).re ≤
        a * ‖(y : RealComplexification E)‖ ^ 2 := by
    intro y hy
    rw [← hUeq, mem_complexifySubmodule] at hy
    have hcoord := (TauCeti.LinearPMap.mem_complexifyReal_domain_iff A
      (y : RealComplexification E)).mp y.2
    have h1 := hUa ⟨re (y : RealComplexification E), hcoord.1⟩ hy.1
    have h2 := hUa ⟨im (y : RealComplexification E), hcoord.2⟩ hy.2
    have hsplit : (⟪TauCeti.LinearPMap.complexifyReal A y,
          (y : RealComplexification E)⟫_ℂ).re =
        ⟪A ⟨re (y : RealComplexification E), hcoord.1⟩,
            re (y : RealComplexification E)⟫_ℝ +
          ⟪A ⟨im (y : RealComplexification E), hcoord.2⟩,
            im (y : RealComplexification E)⟫_ℝ := rfl
    rw [hsplit, RealComplexification.norm_sq, mul_add]
    linarith
  have hUb' : ∀ y : (TauCeti.LinearPMap.complexifyReal A).domain,
      (y : RealComplexification E) ∈
        (TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(y : RealComplexification E)‖ ^ 2 ≤
        (⟪TauCeti.LinearPMap.complexifyReal A y,
          (y : RealComplexification E)⟫_ℂ).re := by
    intro y hy
    rw [← hUeq, ← complexifySubmodule_orthogonal, mem_complexifySubmodule] at hy
    have hcoord := (TauCeti.LinearPMap.mem_complexifyReal_domain_iff A
      (y : RealComplexification E)).mp y.2
    have h1 := hUb ⟨re (y : RealComplexification E), hcoord.1⟩ hy.1
    have h2 := hUb ⟨im (y : RealComplexification E), hcoord.2⟩ hy.2
    have hsplit : (⟪TauCeti.LinearPMap.complexifyReal A y,
          (y : RealComplexification E)⟫_ℂ).re =
        ⟪A ⟨re (y : RealComplexification E), hcoord.1⟩,
            re (y : RealComplexification E)⟫_ℝ +
          ⟪A ⟨im (y : RealComplexification E), hcoord.2⟩,
            im (y : RealComplexification E)⟫_ℝ := rfl
    rw [hsplit, RealComplexification.norm_sq, mul_add]
    linarith
  have hZsa' : IsSelfAdjoint (complexify Z) :=
    (complexify_isSelfAdjoint_iff Z).2 hZsa
  have hBsa' : IsSelfAdjoint (complexify B) :=
    (complexify_isSelfAdjoint_iff B).2 hBsa
  have hZ2' : complexify Z * complexify Z = 1 := by
    rw [← complexify_mul, hZ2, complexify_one]
  have hBmem' : N.Mem (complexify B) := (N.mem_complexify_iff B).2 hBmem
  have hc := tanTwoTheta_unbounded_ambient_paperUINorm_exact
    N hAc hBsa' hB' hZsa' hZ2' hZdom' hZcomm' hUa' hUb' hab hBmem'
  have hCCc := hc.1
  have hdiag :
      (TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic).diagonalPart
          (complexify Z) = complexify (U.diagonalPart Z) := by
    rw [← diagonalPart_congr hUeq (complexify Z)]
    exact diagonalPart_complexifySubmodule U Z
  rw [hdiag, ← complexify_mul, isUnit_complexify_iff] at hCCc
  have hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z) := hCCc
  have hTsub :
      unboundedReflectionTangent
          (TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic)
          (complexify Z) =
        unboundedReflectionTangent (complexifySubmodule U) (complexify Z) :=
    (unboundedReflectionTangent_congr_unboundedExactReal hUeq (complexify Z)).symm
  have hTcomplex :
      unboundedReflectionTangent
          (TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic)
          (complexify Z) =
        complexify (unboundedReflectionTangent U Z) :=
    hTsub.trans (unboundedReflectionTangent_complexifySubmodule U Z hCC)
  have hTmemc := hc.2.1
  rw [hTcomplex] at hTmemc
  have hTmem : N.Mem (unboundedReflectionTangent U Z) :=
    (N.mem_complexify_iff (unboundedReflectionTangent U Z)).1 hTmemc
  have hineq := hc.2.2
  rw [hTcomplex, N.gauge_complexify, N.gauge_complexify] at hineq
  change IsUnit (U.diagonalPart Z * U.diagonalPart Z) ∧
      N.Mem (unboundedReflectionTangent U Z) ∧
      (b - a) * N.gauge (unboundedReflectionTangent U Z) ≤ 2 * N.gauge B
  exact ⟨hCC, hTmem, hineq⟩

end

end DavisKahan1970
end TauCeti
