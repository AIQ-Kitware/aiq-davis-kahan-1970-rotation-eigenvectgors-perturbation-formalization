/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.Ideals.RankOneNormalization
import DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtFrobenius
import DavisKahan.Sources.DavisKahan1970.SineTheta.Theorem61Universal
import DavisKahan.Geometry.Angle.OperatorAngleReal
import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
import ForTauCeti.Analysis.InnerProductSpace.OperatorModulus

/-!
# Source-faithful sharpness and the one-gap counterexample

The single-angle constant is already attained on a two-dimensional reducing
model.  The residual and the directed sine block are scalar multiples of the
same rank-one isometry, so equality holds simultaneously for every normalized
source norm.  Orthogonal finite sums retain the same scalar operator identity.

The final section records the explicit matrix counterexample printed directly
before Proposition 6.1: one directional gap does not imply the symmetric
square-norm estimate.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators

open TauCeti.DavisKahan.Foundation
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

universe u

variable {𝕜 : Type u} [RCLike 𝕜]

/-- The two-dimensional model space `𝕜²` carrying the planar equality configuration. -/
abbrev PaperPlane (𝕜 : Type u) [RCLike 𝕜] := EuclideanSpace 𝕜 (Fin 2)

/-- First standard vector of the planar equality model. -/
def paperPlaneE0 : PaperPlane 𝕜 :=
  EuclideanSpace.single (0 : Fin 2) 1

/-- Second standard vector of the planar equality model. -/
def paperPlaneE1 : PaperPlane 𝕜 :=
  EuclideanSpace.single (1 : Fin 2) 1

/-- Scalar-to-vector map used for all one-dimensional model blocks. -/
noncomputable def paperScalarColumn (v : PaperPlane 𝕜) :
    𝕜 →L[𝕜] PaperPlane 𝕜 :=
  (ContinuousLinearMap.id 𝕜 𝕜).smulRight v

/-- Exact spectral inclusion. -/
noncomputable def paperPlanarExactMap :
    𝕜 →L[𝕜] PaperPlane 𝕜 :=
  paperScalarColumn paperPlaneE0

/-- Complementary spectral inclusion. -/
noncomputable def paperPlanarComplementMap :
    𝕜 →L[𝕜] PaperPlane 𝕜 :=
  paperScalarColumn paperPlaneE1

/-- Trial inclusion at angle `theta`. -/
noncomputable def paperPlanarTrialMap (theta : ℝ) :
    𝕜 →L[𝕜] PaperPlane 𝕜 :=
  paperScalarColumn
    ((Real.cos theta : 𝕜) • paperPlaneE0 +
      (Real.sin theta : 𝕜) • paperPlaneE1)

/-- Two-level self-adjoint operator with gap `delta`. -/
noncomputable def paperPlanarAmbient (delta : ℝ) :
    PaperPlane 𝕜 →L[𝕜] PaperPlane 𝕜 :=
  (Matrix.toEuclideanLin
    !![(0 : 𝕜), 0; 0, (delta : 𝕜)]).toContinuousLinearMap

/-- Zero trial operator. -/
noncomputable def paperPlanarTrialOperator : 𝕜 →L[𝕜] 𝕜 := 0

/-- Literal directed sine block of the planar model. -/
noncomputable def paperPlanarSineBlock (theta : ℝ) :
    𝕜 →L[𝕜] PaperPlane 𝕜 :=
  ((Real.sin theta : 𝕜) • paperPlanarComplementMap)

/-- Residual of the planar equality model. -/
noncomputable def paperPlanarResidual (delta theta : ℝ) :
    𝕜 →L[𝕜] PaperPlane 𝕜 :=
  ((delta * Real.sin theta : ℝ) : 𝕜) • paperPlanarComplementMap

/-- The first model vector is a unit vector. -/
@[simp]
theorem norm_paperPlaneE0 : ‖paperPlaneE0 (𝕜 := 𝕜)‖ = 1 := by
  simp [paperPlaneE0]

/-- The second model vector is a unit vector. -/
@[simp]
theorem norm_paperPlaneE1 : ‖paperPlaneE1 (𝕜 := 𝕜)‖ = 1 := by
  simp [paperPlaneE1]

/-- The adjoint of a scalar column reads off the corresponding coordinate.

Every block identity below needs this; without it the adjoint stays an opaque
term and no component computation closes. -/
theorem adjoint_paperScalarColumn_apply (i : Fin 2) (x : PaperPlane 𝕜) :
    (paperScalarColumn (EuclideanSpace.single i (1 : 𝕜))).adjoint x =
      x.ofLp i := by
  -- Identify the adjoint by the defining inner-product identity, evaluated on
  -- the coordinate functional `x ↦ x i`.
  have hadj :
      (ContinuousLinearMap.id 𝕜 𝕜).smulRight
            (EuclideanSpace.single i (1 : 𝕜)) =
          ((EuclideanSpace.proj i : PaperPlane 𝕜 →L[𝕜] 𝕜)).adjoint := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro z y
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      inner_smul_left, EuclideanSpace.inner_single_left]
    simp [RCLike.inner_apply, mul_comm]
  have := congrArg (fun T : 𝕜 →L[𝕜] PaperPlane 𝕜 => T.adjoint) hadj
  simp only [ContinuousLinearMap.adjoint_adjoint] at this
  rw [paperScalarColumn, this]
  rfl

/-- Pointwise formula: the scalar column sends `z` to `z • v`. -/
@[simp]
theorem paperScalarColumn_apply (v : PaperPlane 𝕜) (z : 𝕜) :
    paperScalarColumn v z = z • v := rfl

/-- Pointwise formula for the exact-subspace embedding: `z ↦ z • e₀`. -/
@[simp]
theorem paperPlanarExactMap_apply (z : 𝕜) :
    paperPlanarExactMap (𝕜 := 𝕜) z = z • paperPlaneE0 := rfl

/-- Pointwise formula for the complement embedding: `z ↦ z • e₁`. -/
@[simp]
theorem paperPlanarComplementMap_apply (z : 𝕜) :
    paperPlanarComplementMap (𝕜 := 𝕜) z = z • paperPlaneE1 := rfl

/-- Pointwise formula for the trial embedding: `z` times the unit vector at angle
`theta` in the `e₀`-`e₁` frame. -/
@[simp]
theorem paperPlanarTrialMap_apply (theta : ℝ) (z : 𝕜) :
    paperPlanarTrialMap (𝕜 := 𝕜) theta z =
      z • ((Real.cos theta : 𝕜) • paperPlaneE0 +
        (Real.sin theta : 𝕜) • paperPlaneE1) := rfl

/-- The adjoint of the exact embedding reads off the zeroth coordinate. -/
@[simp]
theorem adjoint_paperPlanarExactMap_apply (x : PaperPlane 𝕜) :
    (paperPlanarExactMap (𝕜 := 𝕜)).adjoint x = x.ofLp 0 :=
  adjoint_paperScalarColumn_apply 0 x

/-- The adjoint of the complement embedding reads off the first coordinate. -/
@[simp]
theorem adjoint_paperPlanarComplementMap_apply (x : PaperPlane 𝕜) :
    (paperPlanarComplementMap (𝕜 := 𝕜)).adjoint x = x.ofLp 1 :=
  adjoint_paperScalarColumn_apply 1 x

/-- The trial column is isometric for every real angle. -/
theorem paperPlanarTrialMap_isometry (theta : ℝ) :
    IsometricEmbedding (paperPlanarTrialMap (𝕜 := 𝕜) theta) := by
  intro z
  simp only [paperPlanarTrialMap, paperScalarColumn,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
  rw [norm_smul]
  have horth :
      ⟪paperPlaneE0 (𝕜 := 𝕜), paperPlaneE1 (𝕜 := 𝕜)⟫_𝕜 = 0 := by
    simp [paperPlaneE0, paperPlaneE1, EuclideanSpace.inner_single_left]
  have horthSmul :
      ⟪(Real.cos theta : 𝕜) • paperPlaneE0 (𝕜 := 𝕜),
        (Real.sin theta : 𝕜) • paperPlaneE1 (𝕜 := 𝕜)⟫_𝕜 = 0 := by
    rw [inner_smul_left, inner_smul_right, horth]
    ring
  have hunitSq :
      ‖(Real.cos theta : 𝕜) • paperPlaneE0 (𝕜 := 𝕜) +
          (Real.sin theta : 𝕜) • paperPlaneE1 (𝕜 := 𝕜)‖ ^ 2 = 1 := by
    -- Pythagoras is stated in `mul_self` form, so the square is opened first.
    have hpyth :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horthSmul
    simp only [norm_smul, norm_smul, norm_paperPlaneE0, norm_paperPlaneE1, mul_one,
      mul_one, RCLike.norm_ofReal, RCLike.norm_ofReal] at hpyth
    rw [sq, hpyth, ← sq, ← sq, sq_abs, sq_abs]
    exact Real.cos_sq_add_sin_sq theta
  have hunit :
      ‖(Real.cos theta : 𝕜) • paperPlaneE0 (𝕜 := 𝕜) +
          (Real.sin theta : 𝕜) • paperPlaneE1 (𝕜 := 𝕜)‖ = 1 := by
    calc
      ‖(Real.cos theta : 𝕜) • paperPlaneE0 (𝕜 := 𝕜) +
            (Real.sin theta : 𝕜) • paperPlaneE1 (𝕜 := 𝕜)‖ =
          Real.sqrt
            (‖(Real.cos theta : 𝕜) • paperPlaneE0 (𝕜 := 𝕜) +
              (Real.sin theta : 𝕜) • paperPlaneE1 (𝕜 := 𝕜)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = 1 := by rw [hunitSq, Real.sqrt_one]
  rw [hunit, mul_one]

/-- Exact and complementary columns form the coordinate orthogonal
decomposition. -/
theorem paperPlanar_exact_decomposition :
    OrthogonalExactDecomposition
      (paperPlanarExactMap (𝕜 := 𝕜))
      (paperPlanarComplementMap (𝕜 := 𝕜)) := by
  refine {
    isometry₀ := ?_
    isometry₁ := ?_
    orthogonal := ?_
    projection_sum := ?_ }
  · intro z
    simp [paperPlanarExactMap, paperScalarColumn, norm_smul]
  · intro z
    simp [paperPlanarComplementMap, paperScalarColumn, norm_smul]
  · ext
    simp [paperPlaneE1]
  · ext x i
    fin_cases i <;>
      simp [paperPlaneE0, paperPlaneE1]

/-- Direct matrix calculation of the planar residual identity. -/
theorem paperPlanar_residual_identity (delta theta : ℝ) :
    paperPlanarAmbient (𝕜 := 𝕜) delta ∘L
        paperPlanarTrialMap (𝕜 := 𝕜) theta -
      paperPlanarTrialMap (𝕜 := 𝕜) theta ∘L
        paperPlanarTrialOperator (𝕜 := 𝕜) =
      paperPlanarResidual (𝕜 := 𝕜) delta theta := by
  ext i
  fin_cases i <;>
    simp [paperPlanarAmbient, paperPlanarTrialOperator, paperPlanarResidual,
      paperPlaneE0, paperPlaneE1, Matrix.toLpLin_apply,
      mul_comm]

/-- The projection residual is literally the rank-one sine block. -/
theorem paperPlanar_directedSine_identity (theta : ℝ) :
    (ContinuousLinearMap.id 𝕜 (PaperPlane 𝕜) -
        paperPlanarExactMap (𝕜 := 𝕜) ∘L
          (paperPlanarExactMap (𝕜 := 𝕜)).adjoint) ∘L
      paperPlanarTrialMap (𝕜 := 𝕜) theta =
        paperPlanarSineBlock (𝕜 := 𝕜) theta := by
  ext i
  fin_cases i <;>
    simp [paperPlanarSineBlock, paperPlaneE0, paperPlaneE1]

/-- The complement inclusion is a norm-one rank-one map. -/
theorem paperPlanarComplementMap_norm_rank :
    ‖paperPlanarComplementMap (𝕜 := 𝕜)‖ = 1 ∧
      (paperPlanarComplementMap (𝕜 := 𝕜)).rank ≤ (1 : Cardinal) := by
  constructor
  · rw [paperPlanarComplementMap, paperScalarColumn,
      ContinuousLinearMap.norm_smulRight_apply,
      ContinuousLinearMap.norm_id, one_mul, norm_paperPlaneE1]
  · exact (LinearMap.rank_le_domain
      (paperPlanarComplementMap (𝕜 := 𝕜)).toLinearMap).trans_eq (by simp)

/-- Equality in Theorem 6.1 is attained simultaneously for every normalized
source norm. -/
theorem paperTheorem61_planar_equality_every_norm
    (N : PaperUnitaryInvariantNorm)
    {delta theta : ℝ} (hdelta : 0 ≤ delta) :
    N.gauge (paperPlanarResidual (𝕜 := 𝕜) delta theta) =
      delta * N.gauge (paperPlanarSineBlock (𝕜 := 𝕜) theta) := by
  have hV := paperPlanarComplementMap_norm_rank (𝕜 := 𝕜)
  have hVmem := N.mem_rankOne hV.1 hV.2
  rw [paperPlanarResidual, paperPlanarSineBlock,
    N.gauge_smul _ hVmem, N.gauge_smul _ hVmem]
  simp [abs_of_nonneg hdelta]
  ring

/-- At every nonzero acute angle the sine block has strictly positive source
norm. -/
theorem paperPlanarSineBlock_gauge_pos
    (N : PaperUnitaryInvariantNorm)
    {theta : ℝ} (h0 : 0 < theta) (h1 : theta < Real.pi) :
    0 < N.gauge (paperPlanarSineBlock (𝕜 := 𝕜) theta) := by
  have hV := paperPlanarComplementMap_norm_rank (𝕜 := 𝕜)
  have hVmem := N.mem_rankOne hV.1 hV.2
  rw [paperPlanarSineBlock, N.gauge_smul _ hVmem,
    N.gauge_rankOne hV.1 hV.2, mul_one, RCLike.norm_ofReal]
  exact abs_pos.mpr (Real.sin_pos_of_pos_of_lt_pi h0 h1).ne'

/-- No constant strictly below one can replace the source constant in the
single-angle theorem. -/
theorem paperSinTheta_constant_one_optimal
    (N : PaperUnitaryInvariantNorm) :
    ∀ c : ℝ, c < 1 →
      ∃ delta theta : ℝ,
        0 < delta ∧ 0 < theta ∧ theta < Real.pi / 2 ∧
        c * N.gauge (paperPlanarResidual (𝕜 := 𝕜) delta theta) <
          delta * N.gauge (paperPlanarSineBlock (𝕜 := 𝕜) theta) := by
  intro c hc
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi42 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  refine ⟨1, Real.pi / 4, zero_lt_one, hpi4, hpi42, ?_⟩
  rw [paperTheorem61_planar_equality_every_norm N zero_le_one]
  have hpos := paperPlanarSineBlock_gauge_pos (𝕜 := 𝕜) N
    hpi4 (by linarith [Real.pi_pos])
  nlinarith

/-- Scalar homogeneity of the paper gauge on a finite-dimensional operator.

This is a supporting identity for a future finite-multiplicity extremal model;
it is not itself that model. -/
theorem paperFiniteDimensional_scalar_homogeneity
    {m : ℕ} (N : PaperUnitaryInvariantNorm)
    (S : EuclideanSpace 𝕜 (Fin m) →L[𝕜] EuclideanSpace 𝕜 (Fin m))
    {delta : ℝ} (hdelta : 0 ≤ delta) (hS : N.Mem S) :
    N.gauge (((delta : ℝ) : 𝕜) • S) = delta * N.gauge S := by
  rw [N.gauge_smul _ hS]
  simp [abs_of_nonneg hdelta]

section Counterexample

/-- The real two-dimensional model space `ℝ²` carrying the one-gap counterexample. -/
abbrev PaperRealPlane := EuclideanSpace ℝ (Fin 2)

/-- The real model plane is two-dimensional. -/
theorem paperRealPlane_finrank : Module.finrank ℝ PaperRealPlane = 2 := by simp

/-!
### The real coordinate frame

Every quantity in the printed counterexample is a combination of the two
coordinate vectors, so the whole calculation reduces to one orthonormality fact
and one Pythagoras step.  Deriving those once keeps the individual proofs from
having to unfold `EuclideanSpace` coordinates, where the simp set rewrites
`⟪x, x⟫_ℝ` back into `‖x‖ ^ 2` and stalls.
-/

private theorem paperReal_inner_e0_e1 :
    ⟪paperPlaneE0 (𝕜 := ℝ), paperPlaneE1 (𝕜 := ℝ)⟫_ℝ = 0 := by
  simp [paperPlaneE0, paperPlaneE1, EuclideanSpace.inner_single_left]

/-- Squared length of a combination of the two coordinate vectors. -/
private theorem paperReal_norm_sq_combo (a b : ℝ) :
    ‖a • paperPlaneE0 (𝕜 := ℝ) + b • paperPlaneE1 (𝕜 := ℝ)‖ ^ 2 =
      a ^ 2 + b ^ 2 := by
  have horth :
      ⟪a • paperPlaneE0 (𝕜 := ℝ), b • paperPlaneE1 (𝕜 := ℝ)⟫_ℝ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, paperReal_inner_e0_e1]
    ring
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  simp only [norm_smul, norm_smul, norm_paperPlaneE0, norm_paperPlaneE1, mul_one,
    mul_one, Real.norm_eq_abs, Real.norm_eq_abs] at hpyth
  rw [sq, hpyth, ← sq, ← sq, sq_abs, sq_abs]

/-- The trial direction written in the coordinate frame. -/
private theorem paperReal_diff_eq_combo :
    paperPlaneE0 (𝕜 := ℝ) - paperPlaneE1 (𝕜 := ℝ) =
      (1 : ℝ) • paperPlaneE0 (𝕜 := ℝ) + (-1 : ℝ) • paperPlaneE1 (𝕜 := ℝ) := by
  rw [one_smul, neg_one_smul, sub_eq_add_neg]

private theorem paperReal_inner_diff_e0 :
    ⟪paperPlaneE0 (𝕜 := ℝ) - paperPlaneE1 (𝕜 := ℝ),
      paperPlaneE0 (𝕜 := ℝ)⟫_ℝ = 1 := by
  rw [inner_sub_left]
  simp [paperPlaneE0, paperPlaneE1, EuclideanSpace.inner_single_left]

private theorem paperReal_inner_diff_e1 :
    ⟪paperPlaneE0 (𝕜 := ℝ) - paperPlaneE1 (𝕜 := ℝ),
      paperPlaneE1 (𝕜 := ℝ)⟫_ℝ = -1 := by
  rw [inner_sub_left]
  simp [paperPlaneE0, paperPlaneE1, EuclideanSpace.inner_single_left]

/-- The perturbed operator of the counterexample: `diag(0, 1)`. -/
noncomputable def paperCounterexampleA :
    PaperRealPlane →L[ℝ] PaperRealPlane :=
  (Matrix.toEuclideanLin !![(0 : ℝ), 0; 0, 1]).toContinuousLinearMap

/-- The perturbation of the counterexample: the off-diagonal involution `!![1,1;1,0]`. -/
noncomputable def paperCounterexampleH :
    PaperRealPlane →L[ℝ] PaperRealPlane :=
  (Matrix.toEuclideanLin !![(1 : ℝ), 1; 1, 0]).toContinuousLinearMap

/-- The exact subspace of the counterexample: the line spanned by `e₀`. -/
noncomputable def paperCounterexampleExact : Submodule ℝ PaperRealPlane :=
  Submodule.span ℝ {paperPlaneE0 (𝕜 := ℝ)}

/-- Unit vector spanning the trial line in the printed counterexample. -/
noncomputable def paperCounterexampleTrialVector : PaperRealPlane :=
  (1 / Real.sqrt 2) •
    (paperPlaneE0 (𝕜 := ℝ) - paperPlaneE1 (𝕜 := ℝ))

/-- The trial subspace of the counterexample: the line spanned by the unit vector
along `e₀ - e₁`, i.e. at `π/4` to the exact subspace. -/
noncomputable def paperCounterexampleTrial : Submodule ℝ PaperRealPlane :=
  Submodule.span ℝ {paperCounterexampleTrialVector}

/-- The counterexample's exact subspace is orthogonally complemented. -/
noncomputable instance paperCounterexampleExact_projection :
    paperCounterexampleExact.HasOrthogonalProjection := inferInstance

/-- The counterexample's trial subspace is orthogonally complemented. -/
noncomputable instance paperCounterexampleTrial_projection :
    paperCounterexampleTrial.HasOrthogonalProjection := inferInstance

/-- Orthogonal projection onto a unit-generated real line. -/
private theorem starProjection_span_singleton_apply_of_norm_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (v x : E) (hv : ‖v‖ = 1) :
    (Submodule.span ℝ {v}).starProjection x = ⟪v, x⟫_ℝ • v := by
  classical
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span (by simp))
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        have hyv : y = v := by simpa using hy
        subst y
        simp [inner_sub_left, inner_smul_left,
          hv, real_inner_comm]
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_right, ha, mul_zero]

/-- The trial generator in the printed counterexample is a unit vector. -/
theorem norm_paperCounterexampleTrialVector :
    ‖paperCounterexampleTrialVector‖ = 1 := by
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hdiffsq : ‖paperPlaneE0 (𝕜 := ℝ) - paperPlaneE1‖ ^ 2 = 2 := by
    rw [paperReal_diff_eq_combo, paperReal_norm_sq_combo]
    norm_num
  have hdiff : ‖paperPlaneE0 (𝕜 := ℝ) - paperPlaneE1‖ = Real.sqrt 2 := by
    calc
      ‖paperPlaneE0 (𝕜 := ℝ) - paperPlaneE1‖ =
          Real.sqrt (‖paperPlaneE0 (𝕜 := ℝ) - paperPlaneE1‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt 2 := by rw [hdiffsq]
  rw [paperCounterexampleTrialVector, norm_smul, hdiff,
    Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hsqrt2)]
  field_simp [ne_of_gt hsqrt2]

/-- The exact subspace fixes `e₀`, being the line it spans. -/
@[simp]
theorem paperCounterexampleExact_starProjection_e0 :
    paperCounterexampleExact.starProjection (paperPlaneE0 (𝕜 := ℝ)) =
      paperPlaneE0 := by
  -- The orthogonal-projection instance is indexed by the submodule itself, so
  -- rewriting the submodule has no type-correct motive.  Instantiate the
  -- general lemma at the definitional unfolding instead.
  have h : paperCounterexampleExact.starProjection (paperPlaneE0 (𝕜 := ℝ)) =
      ⟪paperPlaneE0 (𝕜 := ℝ), paperPlaneE0 (𝕜 := ℝ)⟫_ℝ •
        paperPlaneE0 (𝕜 := ℝ) :=
    starProjection_span_singleton_apply_of_norm_one _ _ norm_paperPlaneE0
  rw [h]
  simp [paperPlaneE0]

/-- The exact subspace annihilates `e₁`, which is orthogonal to it. -/
@[simp]
theorem paperCounterexampleExact_starProjection_e1 :
    paperCounterexampleExact.starProjection (paperPlaneE1 (𝕜 := ℝ)) = 0 := by
  have h : paperCounterexampleExact.starProjection (paperPlaneE1 (𝕜 := ℝ)) =
      ⟪paperPlaneE0 (𝕜 := ℝ), paperPlaneE1 (𝕜 := ℝ)⟫_ℝ •
        paperPlaneE0 (𝕜 := ℝ) :=
    starProjection_span_singleton_apply_of_norm_one _ _ norm_paperPlaneE0
  rw [h, paperReal_inner_e0_e1, zero_smul]

/-- Pointwise formula for the orthogonal projection onto the trial line. -/
@[simp]
theorem paperCounterexampleTrial_starProjection_apply (x : PaperRealPlane) :
    paperCounterexampleTrial.starProjection x =
      ⟪paperCounterexampleTrialVector, x⟫_ℝ •
        paperCounterexampleTrialVector :=
  starProjection_span_singleton_apply_of_norm_one _ _
    norm_paperCounterexampleTrialVector

/-- Value of the trial projection at `e₀`: the `π/4` angle splits it evenly. -/
@[simp]
theorem paperCounterexampleTrial_starProjection_e0 :
    paperCounterexampleTrial.starProjection (paperPlaneE0 (𝕜 := ℝ)) =
      (1 / 2 : ℝ) •
        (paperPlaneE0 (𝕜 := ℝ) - paperPlaneE1 (𝕜 := ℝ)) := by
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  rw [paperCounterexampleTrial_starProjection_apply]
  have hinner :
      ⟪paperCounterexampleTrialVector, paperPlaneE0 (𝕜 := ℝ)⟫_ℝ =
        1 / Real.sqrt 2 := by
    rw [paperCounterexampleTrialVector, real_inner_smul_left,
      paperReal_inner_diff_e0, mul_one]
  rw [hinner, paperCounterexampleTrialVector, smul_smul]
  have hcoeff :
      (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1 / 2 := by
    field_simp [ne_of_gt hsqrt2]
    nlinarith
  rw [hcoeff]

/-- Value of the trial projection at `e₁`: the `π/4` angle splits it evenly. -/
@[simp]
theorem paperCounterexampleTrial_starProjection_e1 :
    paperCounterexampleTrial.starProjection (paperPlaneE1 (𝕜 := ℝ)) =
      (-1 / 2 : ℝ) •
        (paperPlaneE0 (𝕜 := ℝ) - paperPlaneE1 (𝕜 := ℝ)) := by
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  rw [paperCounterexampleTrial_starProjection_apply]
  have hinner :
      ⟪paperCounterexampleTrialVector, paperPlaneE1 (𝕜 := ℝ)⟫_ℝ =
        -1 / Real.sqrt 2 := by
    rw [paperCounterexampleTrialVector, real_inner_smul_left,
      paperReal_inner_diff_e1]
    ring
  rw [hinner, paperCounterexampleTrialVector, smul_smul]
  have hcoeff :
      (-1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = -1 / 2 := by
    field_simp [ne_of_gt hsqrt2]
    nlinarith
  rw [hcoeff]

/-- The projection difference on the first coordinate vector. -/
theorem paperCounterexample_projectionDifference_e0 :
    (paperCounterexampleExact.starProjection -
        paperCounterexampleTrial.starProjection) (paperPlaneE0 (𝕜 := ℝ)) =
      (1 / 2 : ℝ) • paperPlaneE0 (𝕜 := ℝ) +
        (1 / 2 : ℝ) • paperPlaneE1 (𝕜 := ℝ) := by
  rw [sub_apply,
    paperCounterexampleExact_starProjection_e0,
    paperCounterexampleTrial_starProjection_e0]
  module

/-- The projection difference on the second coordinate vector. -/
theorem paperCounterexample_projectionDifference_e1 :
    (paperCounterexampleExact.starProjection -
        paperCounterexampleTrial.starProjection) (paperPlaneE1 (𝕜 := ℝ)) =
      (1 / 2 : ℝ) • paperPlaneE0 (𝕜 := ℝ) +
        (-(1 / 2) : ℝ) • paperPlaneE1 (𝕜 := ℝ) := by
  rw [sub_apply,
    paperCounterexampleExact_starProjection_e1,
    paperCounterexampleTrial_starProjection_e1]
  module

/-- The printed perturbation on the first coordinate vector. -/
theorem paperCounterexampleH_e0 :
    paperCounterexampleH (paperPlaneE0 (𝕜 := ℝ)) =
      (1 : ℝ) • paperPlaneE0 (𝕜 := ℝ) + (1 : ℝ) • paperPlaneE1 (𝕜 := ℝ) := by
  ext i
  fin_cases i <;>
    simp [paperCounterexampleH, paperPlaneE0, paperPlaneE1,
      Matrix.toLpLin_apply]

/-- The printed perturbation on the second coordinate vector. -/
theorem paperCounterexampleH_e1 :
    paperCounterexampleH (paperPlaneE1 (𝕜 := ℝ)) =
      (1 : ℝ) • paperPlaneE0 (𝕜 := ℝ) + (0 : ℝ) • paperPlaneE1 (𝕜 := ℝ) := by
  ext i
  fin_cases i <;>
    simp [paperCounterexampleH, paperPlaneE0, paperPlaneE1,
      Matrix.toLpLin_apply]

/-- The real complexified sine operator has the same paper square norm as the
real projection difference from which it is constructed. -/
theorem paperHilbertSchmidtNorm_sinAngleOperatorRC_eq_projectionDifference
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperHilbertSchmidtNorm
        (TauCeti.DavisKahanExt.Real.sinAngleOperatorRC U V) =
      paperHilbertSchmidtNorm (U.starProjection - V.starProjection) := by
  rw [TauCeti.DavisKahanExt.Real.sinAngleOperatorRC,
    TauCeti.DavisKahanExt.sinAngleOperatorC]
  calc
    paperHilbertSchmidtNorm
        (ContinuousLinearMap.modulus
          ((complexifySubmodule U).starProjection -
            (complexifySubmodule V).starProjection)) =
        paperHilbertSchmidtNorm
          ((complexifySubmodule U).starProjection -
            (complexifySubmodule V).starProjection) :=
      SameApproximationSingularSequence.paperHilbertSchmidtNorm_eq
        (modulus_hasSameApproximationNumbers _)
    _ = paperHilbertSchmidtNorm
        (complexify (U.starProjection - V.starProjection)) := by
      rw [starProjection_complexifySubmodule,
        starProjection_complexifySubmodule, complexify_sub]
    _ = paperHilbertSchmidtNorm
        (U.starProjection - V.starProjection) :=
      paperHilbertSchmidtNorm_complexify _

/-- The source counterexample has angle `pi/4`, hence square sine norm one. -/
theorem paperCounterexample_sine_square_norm :
    paperHilbertSchmidtNorm
      (TauCeti.DavisKahanExt.Real.sinAngleOperatorRC
        paperCounterexampleExact paperCounterexampleTrial) = 1 := by
  rw [paperHilbertSchmidtNorm_sinAngleOperatorRC_eq_projectionDifference,
    paperHilbertSchmidtNorm_eq_frobenius,
    TauCeti.UnitarilyInvariantSeminorm.frobenius_apply
    ℝ PaperRealPlane
    (paperCounterexampleExact.starProjection -
      paperCounterexampleTrial.starProjection).toLinearMap
    paperRealPlane_finrank (EuclideanSpace.basisFun (Fin 2) ℝ)]
  rw [Fin.sum_univ_two]
  simp only [EuclideanSpace.basisFun_apply]
  change Real.sqrt
    (‖(paperCounterexampleExact.starProjection -
          paperCounterexampleTrial.starProjection) (paperPlaneE0 (𝕜 := ℝ))‖ ^ 2 +
      ‖(paperCounterexampleExact.starProjection -
          paperCounterexampleTrial.starProjection) (paperPlaneE1 (𝕜 := ℝ))‖ ^ 2) = 1
  rw [paperCounterexample_projectionDifference_e0,
    paperCounterexample_projectionDifference_e1,
    paperReal_norm_sq_combo, paperReal_norm_sq_combo]
  norm_num

/-- The perturbation in the printed counterexample has square norm `sqrt 3`. -/
theorem paperCounterexample_perturbation_square_norm :
    paperHilbertSchmidtNorm paperCounterexampleH = Real.sqrt 3 := by
  rw [paperHilbertSchmidtNorm_eq_frobenius,
    TauCeti.UnitarilyInvariantSeminorm.frobenius_apply
    ℝ PaperRealPlane paperCounterexampleH.toLinearMap
    paperRealPlane_finrank (EuclideanSpace.basisFun (Fin 2) ℝ)]
  rw [Fin.sum_univ_two]
  simp only [EuclideanSpace.basisFun_apply]
  change Real.sqrt
    (‖paperCounterexampleH (paperPlaneE0 (𝕜 := ℝ))‖ ^ 2 +
      ‖paperCounterexampleH (paperPlaneE1 (𝕜 := ℝ))‖ ^ 2) = Real.sqrt 3
  rw [paperCounterexampleH_e0, paperCounterexampleH_e1,
    paperReal_norm_sq_combo, paperReal_norm_sq_combo]
  norm_num

/-- The single directional gap `delta=2` does not imply the symmetric
square-norm estimate. -/
theorem paperOneGap_does_not_imply_symmetric_square_estimate :
    paperHilbertSchmidtNorm paperCounterexampleH <
      2 * paperHilbertSchmidtNorm
        (TauCeti.DavisKahanExt.Real.sinAngleOperatorRC
          paperCounterexampleExact paperCounterexampleTrial) := by
  rw [paperCounterexample_sine_square_norm,
    paperCounterexample_perturbation_square_norm]
  have hsqrt3 : Real.sqrt 3 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
  nlinarith

end Counterexample

end

end ExactSinTheta
end DavisKahan
end TauCeti