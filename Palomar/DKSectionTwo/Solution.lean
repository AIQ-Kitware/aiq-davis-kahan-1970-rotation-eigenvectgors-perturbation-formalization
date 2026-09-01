/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import Mathlib
import DavisKahan.All
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.ScalarTransport
import ForTauCeti.Analysis.InnerProductSpace.Projection.ScalarTransport
import ForTauCeti.Analysis.RCLike.ScalarTransportIsometry

/-!
# Solution: the four Section 2 theorems of Davis and Kahan

The compared declarations are stated exactly as in the challenge module: the
vocabulary is repeated verbatim, and `RotationOfEigenvectors.sinTheta`,
`.tanTheta`, `.sinTwoTheta` and `.tanTwoTheta` are declared here at those same
types with proofs.  This module does **not** import the challenge.

The perturbation argument is not restated.  It lives in the development imported
above; what is here is the bridge -- the Challenge's vocabulary shown to *be* the
development's, clause by clause -- and then the scalar transport that carries the
development's fixed-field endpoints to an arbitrary `RCLike` field.

Three things are worth naming, because each was a defect an earlier draft of this
entry contained.

* **A tangent is a function of an angle, presented by its sine.**  `tanSeq` is
  applied to sine operators only, never to a residual.
* **A doubled angle is presented by its own sine.**  `t ↦ sin 2t` is not
  monotone on `[0, π/2]`, so no indexwise map carries `aₙ(sin Θ)` to
  `aₙ(sin 2Θ)`; principal angles `75°` and `30°` already order the two
  sequences oppositely.  The `tan 2Θ` clauses read their sequences off
  `directedDoubleSine` and `ambientDoubleSine` through the monotone
  `u ↦ tan (arcsin u)`.
* **The pole exclusion is a conclusion.**  Lean's `Real.tan` is total, so a pole
  would be silently valued at zero; each tangent clause therefore *concludes*
  `TangentDefined`, as the source derives it.
-/

namespace RotationOfEigenvectors


open scoped InnerProductSpace NNReal ENNReal

universe u v w

/-! ## 1. Singular values -/

section SingularValues

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type w} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The `n`-th singular value of a bounded operator, zero-based: the
operator-norm distance from `T` to the operators of rank at most `n`.  `a₀ T =
‖T‖`, and for a compact operator this is the usual decreasing sequence. -/
noncomputable def singularValue (T : E →L[𝕜] F) (n : ℕ) : ℝ :=
  ⨅ R : {R : E →L[𝕜] F // LinearMap.rank (R.1 : E →ₗ[𝕜] F) ≤ (n : Cardinal)},
    ‖T - R.1‖

end SingularValues

/-! ## 2. Unitarily invariant norms

An arbitrary unitarily invariant norm in Davis and Kahan's sense: a symmetric
norming function on singular values, given as a two-sided unitarily invariant
seminorm on `n × n` complex matrices for every `n`, normalised on a rank-one
matrix and unchanged by appending a zero singular value.  Its value on a sequence
is the supremum over prefixes, and on an operator its value on the
singular-value sequence. -/

section Norms

/-- The operator with real diagonal `x` in an orthonormal basis. -/
noncomputable def diagOp {n : ℕ} {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : OrthonormalBasis (Fin n) ℂ E) (x : Fin n → ℝ) :
    E →ₗ[ℂ] E :=
  ∑ i, ((x i : ℝ) : ℂ) • (InnerProductSpace.rankOne ℂ (b i) (b i)).toLinearMap

/-- A two-sided unitarily invariant seminorm on the operators of a
finite-dimensional complex inner product space. -/
structure UISeminorm (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] where
  /-- The underlying function on operators. -/
  toFun : (E →ₗ[ℂ] E) → ℝ
  /-- Subadditivity. -/
  add_le : ∀ A B, toFun (A + B) ≤ toFun A + toFun B
  /-- Absolute homogeneity. -/
  smul : ∀ (a : ℂ) (A), toFun (a • A) = ‖a‖ * toFun A
  /-- Two-sided unitary invariance -- the defining property. -/
  invariant : ∀ (U V : E ≃ₗᵢ[ℂ] E) (A),
    toFun (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) = toFun A

/-- The symmetric gauge: the seminorm's value on the diagonal operator. -/
noncomputable def UISeminorm.gauge {n : ℕ} {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (N : UISeminorm E)
    (b : OrthonormalBasis (Fin n) ℂ E) (x : Fin n → ℝ) : ℝ :=
  N.toFun (diagOp b x)

/-- Append one trailing zero to a finite vector of singular values. -/
def zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.lastCases 0 x

/-- **A unitarily invariant norm in Davis and Kahan's sense.** -/
structure UINorm where
  /-- A unitarily invariant seminorm in each finite dimension. -/
  finiteNorm : ∀ n : ℕ, UISeminorm (EuclideanSpace ℂ (Fin n))
  /-- Normalisation on a single unit singular value. -/
  normalized :
    (finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) (fun _ => 1) = 1
  /-- Appending a zero singular value does not change the value. -/
  zero_pad : ∀ {n : ℕ} (x : Fin n → ℝ),
    (finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
        (zeroPad x) =
      (finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x

/-- **The extended value of a unitarily invariant norm on a scalar sequence**:
the supremum over the sequence's prefixes.  This is the primitive; a norm of
`tan Θ` is the norm of the sequence `tan θ₁, tan θ₂, …`. -/
noncomputable def UINorm.evalSeq (N : UINorm) (s : ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal
    ((N.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ)
      (fun i => s (i : ℕ)))

/-- The sequence lies in the norm's ideal. -/
def UINorm.SeqFinite (N : UINorm) (s : ℕ → ℝ) : Prop := N.evalSeq s ≠ ⊤

/-- The real-valued norm of a sequence, meaningful on the ideal. -/
noncomputable def UINorm.seqNorm (N : UINorm) (s : ℕ → ℝ) : ℝ :=
  (N.evalSeq s).toReal

section NormEval

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The norm's extended value on an operator: its value on the singular-value
sequence, and `⊤` exactly off the norm's ideal. -/
noncomputable def UINorm.eval (N : UINorm) (T : E →L[𝕜] F) : ℝ≥0∞ :=
  N.evalSeq (fun n => singularValue T n)

/-- The operator lies in the norm's ideal. -/
def UINorm.Finite (N : UINorm) (T : E →L[𝕜] F) : Prop := N.eval T ≠ ⊤

/-- The real-valued norm, meaningful on the ideal. -/
noncomputable def UINorm.norm (N : UINorm) (T : E →L[𝕜] F) : ℝ := (N.eval T).toReal

end NormEval

end Norms

/-- A subspace with an orthogonal projection is closed, hence complete. -/
local instance instCompleteSpaceOfHasOrthogonalProjection {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (W : Submodule 𝕜 E) [W.HasOrthogonalProjection] : CompleteSpace W := by
  have hclosed : IsClosed (W : Set E) := by
    rw [← Submodule.orthogonal_orthogonal W]
    exact Submodule.isClosed_orthogonal _
  exact hclosed.completeSpace_coe

/-! ## 3. The paper's block data

Section 1 fixes a self-adjoint `A`, a bounded self-adjoint perturbation `H`, and
two reducing decompositions: `E₀` spans the trial subspace with block `A₀`, and
`F₀, F₁` span the exact subspaces of `A + H` with complementary block `Λ₁`.  The
residual is `R = (A + H) E₀ − E₀ A₀`.  Neither decomposition is assumed
spectral. -/

section BlockData

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- A coordinate map is an isometry onto its range. -/
def IsIsometric (T : E →L[𝕜] F) : Prop := ∀ x, ‖T x‖ = ‖x‖

/-- The trial-coordinate half of the setup: `E₀` is an isometric coordinate map
for the trial subspace and `R` the residual `A E₀ − E₀ A₀`; `A₀` is a partial
map, so it may be unbounded. -/
structure IsTrialResidual (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F)
    (E₀ : F →L[𝕜] E) (R : F →L[𝕜] E) : Prop where
  /-- The trial coordinate map is isometric. -/
  isometry : IsIsometric E₀
  /-- It carries the trial domain into the ambient domain. -/
  mapsDomain : ∀ x : A₀.domain, E₀ (x : F) ∈ A.domain
  /-- `R` is the residual there. -/
  residualEquation : ∀ x : A₀.domain,
    A ⟨E₀ (x : F), mapsDomain x⟩ - E₀ (A₀ x) = R (x : F)

/-- The exact-coordinate half: `F₀` and `F₁` are complementary exhaustive
isometries and `F₁` intertwines `A` with the complementary block `Λ₁`. -/
structure IsExactDecomposition (A : E →ₗ.[𝕜] E) (Λ₁ : G →ₗ.[𝕜] G)
    (F₀ : K →L[𝕜] E) (F₁ : G →L[𝕜] E) : Prop where
  /-- The desired coordinate map is isometric. -/
  desiredIsometry : IsIsometric F₀
  /-- The complementary coordinate map is isometric. -/
  complementIsometry : IsIsometric F₁
  /-- The two ranges are orthogonal. -/
  orthogonal : F₀.adjoint ∘L F₁ = 0
  /-- Together they exhaust the space. -/
  complete : F₀ ∘L F₀.adjoint + F₁ ∘L F₁.adjoint = ContinuousLinearMap.id 𝕜 E
  /-- `F₁` carries the block domain into the ambient domain. -/
  mapsDomain : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain
  /-- and intertwines the two operators there. -/
  intertwines : ∀ y : Λ₁.domain, A ⟨F₁ (y : G), mapsDomain y⟩ = F₁ (Λ₁ y)

/-- **The trial data of a subspace**, in the source's own shape `(1.8)`:
a trial operator `A₀` on the subspace, possibly unbounded, and a *bounded*
residual `R` with `A z = A₀ z + R z` on the trial domain.  The compression is a
partial map because the Appendix to Section 6 allows the tangent theorem's `A₀`
to be unbounded. -/
structure TrialBlock (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] where
  /-- The trial block `A₀`, a partial map on the trial subspace. -/
  compression : U →ₗ.[𝕜] U
  /-- `A₀` is self-adjoint. -/
  compression_selfAdjoint : IsSelfAdjoint compression
  /-- The bounded residual `R`. -/
  residual : U →L[𝕜] E
  /-- Trial vectors in the compression's domain lie in the ambient domain. -/
  mem_domain : ∀ z : compression.domain, ((z : U) : E) ∈ A.domain
  /-- and there `A z = A₀ z + R z`, which is `(1.8)`. -/
  action_eq : ∀ z : compression.domain,
    A ⟨((z : U) : E), mem_domain z⟩ =
      ((compression z : U) : E) + residual ((z : U))

/-- **The trial data of a subspace with a bounded compression**, in the source's
shape `(1.8)`: a bounded self-adjoint `A₀` on a trial subspace inside `dom A`,
and a bounded residual `R` with `A z = A₀ z + R z` there.

The Appendix to Section 6 relaxes the sine family -- the `sin Θ` theorem,
Proposition 6.1 and Theorem 6.1 -- to allow **one** of `A₀`, `Λ₁` to be
unbounded, and reserves "both may be unbounded" for the tangent theorem.  Here
the unwanted exact block is the unbounded one. -/
structure BoundedTrialBlock (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] where
  /-- The trial block `A₀`, bounded on the trial subspace. -/
  compression : U →L[𝕜] U
  /-- `A₀` is self-adjoint. -/
  compression_selfAdjoint : IsSelfAdjoint compression
  /-- The bounded residual `R`. -/
  residual : U →L[𝕜] E
  /-- The trial subspace lies inside the ambient domain. -/
  mem_domain : ∀ z : U, ((z : U) : E) ∈ A.domain
  /-- and there `A z = A₀ z + R z`, which is `(1.8)`. -/
  action_eq : ∀ z : U,
    A ⟨((z : U) : E), mem_domain z⟩ = ((compression z : U) : E) + residual z

/-- **Rayleigh--Ritz trial data**: trial data whose residual is orthogonal to the
trial subspace.  This is the source's `H₀ = 0` in the form `(1.8)` takes when
`A₀ = E₀^*(A+H)E₀`, the extra hypothesis the `tan Θ` theorem imposes and the
`sin Θ` and `sin 2Θ` theorems do not. -/
structure RitzData (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] extends TrialBlock A U where
  /-- The residual is orthogonal to the trial subspace. -/
  residual_orthogonal : ∀ z z' : U, ⟪residual z, ((z' : U) : E)⟫_𝕜 = 0

end BlockData

/-! ## 4. The source separation -/

section Separation

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The real resolvent set: the shifted operator has a bounded two-sided
inverse. -/
def realResolventSet (A : E →ₗ.[𝕜] E) : Set ℝ :=
  {lam : ℝ | ∃ R : E →L[𝕜] E,
      (∀ x : A.domain, R (A x - (lam : 𝕜) • (x : E)) = (x : E)) ∧
      (∀ y : E, ∃ h : R y ∈ A.domain,
        A ⟨R y, h⟩ - (lam : 𝕜) • R y = y)}

/-- The real spectrum. -/
def realSpectrum (A : E →ₗ.[𝕜] E) : Set ℝ := (realResolventSet A)ᶜ

/-- The quadratic form of `A` is at least `c` on its domain. -/
def SemiboundedBelow (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop :=
  ∀ x : A.domain, c * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜

/-- The quadratic form of `A` is at most `c` on its domain. -/
def SemiboundedAbove (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop :=
  ∀ x : A.domain, RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ c * ‖(x : E)‖ ^ 2

/-- **The source separation of two blocks by a gap of width `δ`.**
`intervalExterior` is the printed interval/exterior condition, symmetric in the
two blocks; the two ordered constructors are the half-infinite configurations the
source explicitly permits, in which both blocks may have unbounded spectrum. -/
inductive SylvesterGap (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) : Prop where
  | intervalExterior {β α : ℝ} (hβα : β ≤ α)
      (hgap :
        (realSpectrum A ⊆ Set.Icc β α ∧
          realSpectrum B ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x}) ∨
        (realSpectrum B ⊆ Set.Icc β α ∧
          realSpectrum A ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x}))
  | leftAboveRightBelow (c : ℝ)
      (hA : SemiboundedBelow A (c + δ)) (hB : SemiboundedAbove B c)
  | leftBelowRightAbove (c : ℝ)
      (hA : SemiboundedAbove A c) (hB : SemiboundedBelow B (c + δ))

end Separation

/-! ## 5. Reducing subspaces and their blocks

Section 1 says in as many words that neither `P` nor `Q` is assumed to be a
spectral projector: what the theorems assume is that the decomposition *reduces*
the operator and that its two blocks are separated. -/

section Reducing

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A subspace reduces a partial map when both projections preserve its domain
and both summands are invariant. -/
def Reduces (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    Prop :=
  (∀ x : A.domain, U.starProjection (x : E) ∈ A.domain) ∧
  (∀ x : A.domain, Uᗮ.starProjection (x : E) ∈ A.domain) ∧
  (∀ x : A.domain, (x : E) ∈ U → A x ∈ U) ∧
  (∀ x : A.domain, (x : E) ∈ Uᗮ → A x ∈ Uᗮ)

/-- The block of `A` on a reducing subspace. -/
noncomputable def block (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (h : Reduces A U) : U →ₗ.[𝕜] U where
  domain :=
    { carrier := {x : U | (x : E) ∈ A.domain}
      zero_mem' := A.domain.zero_mem
      add_mem' := fun hx hy => A.domain.add_mem hx hy
      smul_mem' := fun c _ hx => A.domain.smul_mem c hx }
  toFun :=
    { toFun := fun x => ⟨A ⟨((x : U) : E), x.2⟩, h.2.2.1 _ ((x : U)).2⟩
      map_add' := fun x y => by
        apply Subtype.ext
        exact congrArg (fun z : A.domain => (A z : E)) (Subtype.ext rfl) |>.trans
          (A.map_add ⟨((x : U) : E), x.2⟩ ⟨((y : U) : E), y.2⟩)
      map_smul' := fun c x => by
        apply Subtype.ext
        exact congrArg (fun z : A.domain => (A z : E)) (Subtype.ext rfl) |>.trans
          (A.map_smul c ⟨((x : U) : E), x.2⟩) }

/-- Adding a bounded operator to a partial map, on the same domain. -/
noncomputable def addBounded (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) : E →ₗ.[𝕜] E where
  domain := A.domain
  toFun := A.toFun + V.toLinearMap.domRestrict A.domain

omit [CompleteSpace E] in
/-- The orthogonal complement of a reducing subspace also reduces the operator,
so the ambient separation hypothesis can name both blocks. -/
theorem Reduces.orthogonal {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (h : Reduces A U) : Reduces A Uᗮ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨h₂, ?_, h₄, ?_⟩
  · intro x
    simpa only [Submodule.orthogonal_orthogonal] using h₁ x
  · intro x hx
    rw [Submodule.orthogonal_orthogonal] at hx ⊢
    exact h₃ x hx

end Reducing

/-! ## 6. The angle quantities

The *sines* are explicit operators; the *tangents* are sequences, `‖tan Θ‖` being
the norm's value on `tan θ₁, tan θ₂, …`. -/

section Angles

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- `sin Θ₀` in coordinates: the part of the trial coordinate map that misses the
exact subspace, the source's `Q^⊥E₀`. -/
noncomputable def directedSine (E₀ : F →L[𝕜] E) (F₀ : K →L[𝕜] E) : F →L[𝕜] E :=
  (ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀

/-- `sin Θ₀` for a trial *subspace*: `Q^⊥E₀ = P_{Vᗮ}|_U`. -/
noncomputable def directedSineBlock (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[𝕜] E :=
  Vᗮ.starProjection ∘L U.subtypeL

/-- `sin Θ`, the ambient sine: the projector difference, whose singular values
are the sines of the principal angles, each occurring twice. -/
noncomputable def ambientSine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  V.starProjection - U.starProjection

/-- `sin 2Θ`, the ambient double-angle sine: the projector difference between `U`
and its mirror image in `V`.  Reflecting `U` in `V` doubles every principal
angle. -/
noncomputable def ambientDoubleSine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  (U.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection - U.starProjection

/-- `sin 2Θ₀`, the directed double-angle sine. -/
noncomputable def directedDoubleSine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  U.starProjection ∘L
    (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection

/-! ### Tangents of an angle presented by its sine

The argument of `tanSeq` is always a sine: `tan Θ₀` is a trigonometric function
of the *angle*, presented here by an operator whose singular values are its
sines.  The residual is the right-hand side and has nothing to do with the
left.

**A doubled angle is presented by its own sine, never by doubling the ordered
sines of the single angle.**  `θ ↦ sin 2θ` is not monotone on `[0, π/2]`, so
`n ↦ sin (2 arcsin (aₙ(sin Θ)))` need not be the ordered singular-value sequence
of `sin 2Θ` -- at principal angles `75°` and `30°` the two sequences are in
opposite order.  The `tan 2Θ` clauses below therefore read the doubled tangent
off `ambientDoubleSine` and `directedDoubleSine`, through the same monotone
`u ↦ tan (arcsin u)` that `tan Θ` uses, and `|tan 2θ| = tan (arcsin |sin 2θ|)`
supplies the source's absolute value with no branch choice. -/

/-- The sequence `tan θ₀, tan θ₁, …`, where `sin θₙ` is the `n`-th singular value
of the sine operator `S`. -/
noncomputable def tanSeq {X Y : Type v}
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  Real.tan (Real.arcsin (singularValue S n))

/-- **No principal angle of `S` is a right angle**, so every `tan θₙ` is a
genuine tangent rather than the value Lean's field division assigns at a pole.
Equivalently `‖S‖ < 1`, since `a₀ S = ‖S‖`.  Davis and Kahan derive this rather
than assuming it, so it appears below as a conclusion -- for the double-angle
clauses too, where `S` is the double-angle sine and the condition is the
quarter-turn exclusion `‖sin 2Θ‖ < 1`. -/
def TangentDefined {X Y : Type v}
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    (S : X →L[𝕜] Y) : Prop :=
  ∀ n, Real.cos (Real.arcsin (singularValue S n)) ≠ 0

/-- The crossed defect subspaces are isometrically isomorphic: the source's
standing condition (3.5), assumed from Section 3 onward, which is what makes the
ambient angle meaningful when the subspaces are not acute. -/
def CrossedDefectsEquivalent (U V : Submodule 𝕜 E) : Prop :=
  Nonempty ((U ⊓ Vᗮ : Submodule 𝕜 E) ≃ₗᵢ[𝕜] (Uᗮ ⊓ V : Submodule 𝕜 E))

end Angles

/-! ## 7. The four theorems of Section 2

Davis and Kahan open with four unnumbered theorems.  Three of them print two
conclusions -- one *directed*, comparing the trial subspace with the exact one
through the residual, and one *ambient*, comparing the two subspaces through the
whole perturbation.  Each printed clause quantifies its own data and its own
hypotheses, so the three two-clause theorems conclude in a record whose fields
are the printed clauses; sharing a membership premise across both would make each
clause carry the other's. -/

section Theorems

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]


/-! ### `tan Θ` -/

/-- **The two printed conclusions of the `tan Θ` theorem**, each with its own
data and hypotheses: `δ ‖tan Θ₀‖ ≤ ‖R‖` for every trial subspace with
Rayleigh--Ritz data, needing only the *residual* in the norm's ideal, and
`δ ‖tan Θ‖ ≤ ‖H‖` for a bounded self-adjoint perturbation with vanishing trial
diagonal block, needing the *perturbation*.  Each clause also concludes that its
tangent has no pole. -/
structure TanThetaResult (N : UINorm) (A : E →ₗ.[𝕜] E)
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection] (α δ : ℝ) : Prop where
  /-- `δ ‖tan Θ₀‖ ≤ ‖R‖`: the directed conclusion, on the residual alone. -/
  directed : ∀ {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
      (D : RitzData A U), SemiboundedAbove D.compression α →
      N.Finite D.residual →
        TangentDefined (directedSineBlock U V) ∧
          N.SeqFinite (tanSeq (directedSineBlock U V)) ∧
          δ * N.seqNorm (tanSeq (directedSineBlock U V)) ≤ N.norm D.residual
  /-- `δ ‖tan Θ‖ ≤ ‖H‖`: the ambient conclusion, on the whole perturbation. -/
  ambient : ∀ {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
      (D : RitzData A U), SemiboundedAbove D.compression α →
      ∀ (H : E →L[𝕜] E), IsSelfAdjoint H →
      D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL →
      CrossedDefectsEquivalent U V →
      N.Finite H →
        TangentDefined (ambientSine U V) ∧
          N.SeqFinite (tanSeq (ambientSine U V)) ∧
          δ * N.seqNorm (tanSeq (ambientSine U V)) ≤ N.norm H


/-! ### `sin 2Θ` -/

/-- **The two printed conclusions of the `sin 2Θ` theorem**, for a subspace `U`
reducing `A` whose two blocks are separated by `δ`: `δ ‖sin 2Θ₀‖ ≤ 2 ‖R‖` for
every trial subspace with a residual, needing only the residual in the ideal, and
`δ ‖sin 2Θ‖ ≤ 2 ‖H‖` for every bounded self-adjoint perturbation and every
subspace reducing the perturbed operator, needing the perturbation.

The factor two is the paper's, and is sharp.  Unlike `tan Θ` no Rayleigh--Ritz
condition is imposed, and unlike `tan Θ` the Appendix does not extend this
theorem to an unbounded trial compression. -/
structure SinTwoThetaResult (N : UINorm) (A : E →ₗ.[𝕜] E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (δ : ℝ) : Prop where
  /-- `δ ‖sin 2Θ₀‖ ≤ 2 ‖R‖`: the directed conclusion, on the residual alone. -/
  directed : ∀ {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
      (D : BoundedTrialBlock A V), N.Finite D.residual →
        N.Finite (directedDoubleSine U V) ∧
          δ * N.norm (directedDoubleSine U V) ≤ 2 * N.norm D.residual
  /-- `δ ‖sin 2Θ‖ ≤ 2 ‖H‖`: the ambient conclusion, on the whole perturbation. -/
  ambient : ∀ (H : E →L[𝕜] E), IsSelfAdjoint H →
      ∀ {V : Submodule 𝕜 E} [V.HasOrthogonalProjection],
      Reduces (addBounded A H) V → N.Finite H →
        N.Finite (ambientDoubleSine U V) ∧
          δ * N.norm (ambientDoubleSine U V) ≤ 2 * N.norm H


/-! ### `tan 2Θ` -/

/-- **The two printed conclusions of the `tan 2Θ` theorem**, for `U` reducing `A`
ordered below `α` with its complement above `α + δ` and `H` a bounded
self-adjoint perturbation off-diagonal for that splitting -- the source's
`H₀ = H₁ = 0`: `δ ‖tan 2Θ₀‖ ≤ 2 ‖R‖` with `R` the corner `P_{Uᗮ} H P_U` and only
that corner in the ideal, and `δ ‖tan 2Θ‖ ≤ 2 ‖H‖` with the whole perturbation.

No hypothesis excluding the poles of `tan 2Θ` is part of the printed theorem:
Section 7 derives the nonvanishing of the relevant `cos 2θⱼ`, which appears here
as `TangentDefined` of the double-angle sine -- the quarter-turn exclusion
`‖sin 2Θ‖ < 1`, uniform over the whole angle rather than read off a
singular-value sequence of the single angle. -/
structure TanTwoThetaResult (N : UINorm) (A : E →ₗ.[𝕜] E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (H : E →L[𝕜] E) (δ : ℝ) : Prop where
  /-- `δ ‖tan 2Θ₀‖ ≤ 2 ‖R‖`: the directed conclusion, on the residual corner. -/
  directed : ∀ {V : Submodule 𝕜 E} [V.HasOrthogonalProjection],
      Reduces (addBounded A H) V →
      N.Finite (Uᗮ.starProjection ∘L H ∘L U.starProjection) →
        TangentDefined (directedDoubleSine U V) ∧
          N.SeqFinite (tanSeq (directedDoubleSine U V)) ∧
          δ * N.seqNorm (tanSeq (directedDoubleSine U V)) ≤
            2 * N.norm (Uᗮ.starProjection ∘L H ∘L U.starProjection)
  /-- `δ ‖tan 2Θ‖ ≤ 2 ‖H‖`: the ambient conclusion, on the whole perturbation. -/
  ambient : ∀ {V : Submodule 𝕜 E} [V.HasOrthogonalProjection],
      Reduces (addBounded A H) V → N.Finite H →
        TangentDefined (ambientDoubleSine U V) ∧
          N.SeqFinite (tanSeq (ambientDoubleSine U V)) ∧
          δ * N.seqNorm (tanSeq (ambientDoubleSine U V)) ≤ 2 * N.norm H


end Theorems


open TauCeti
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.ApproximationNumber

open scoped InnerProductSpace

noncomputable section


/-- A subspace with an orthogonal projection inside a complete space is
complete; the Challenge's own `local instance` does not cross the import. -/
local instance instCompleteSpaceOfHasOrthogonalProjectionSolution {𝕜 : Type u}
    [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (W : Submodule 𝕜 E) [W.HasOrthogonalProjection] :
    CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

/-! ## 1. The norm vocabulary is the development's -/

section NormBridge

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Challenge's singular values are the development's approximation
numbers, definitionally. -/
theorem singularValue_eq_approximationNumber (T : E →L[𝕜] F) (n : ℕ) :
    singularValue T n = T.approximationNumber n := rfl

/-- A Challenge unitarily invariant seminorm is one of the development's. -/
def UISeminorm.toTauCeti {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] (N : UISeminorm G) :
    TauCeti.UnitarilyInvariantSeminorm ℂ G where
  toFun := N.toFun
  add_le' := N.add_le
  smul' := N.smul
  invariant' := N.invariant

/-- The Challenge's diagonal operator is the development's. -/
theorem diagOp_eq {n : ℕ} {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
    (b : OrthonormalBasis (Fin n) ℂ G) (x : Fin n → ℝ) :
    diagOp b x = TauCeti.diagOp b x := rfl

/-- Hence so is its symmetric gauge. -/
theorem UISeminorm.gauge_eq {n : ℕ} {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] (N : UISeminorm G)
    (b : OrthonormalBasis (Fin n) ℂ G) (x : Fin n → ℝ) :
    N.gauge b x = N.toTauCeti.gauge b x := rfl

/-- **A Challenge unitarily invariant norm is a source unitarily invariant norm.**

Field for field: the finite seminorms, the normalisation and the zero-padding
axiom transfer with no adjustment, because the two definitions are the same
definition. -/
def UINorm.toPaper (N : UINorm) : PaperUnitaryInvariantNorm where
  finiteNorm n := (N.finiteNorm n).toTauCeti
  normalized := N.normalized
  zero_pad := N.zero_pad

/-- The two norms take the same value on every operator.

The Challenge evaluates its norm on the *sequence* of singular values and the
development on the operator, so this equation is also the statement that the
sequence-level and operator-level readings agree. -/
theorem UINorm.eval_eq (N : UINorm) (T : E →L[𝕜] F) :
    N.eval T = N.toPaper.extendedGauge T := rfl

/-- The sequence norm of an operator's singular values is the operator norm --
which is what makes `UINorm.seqNorm` the right home for `‖tan Θ‖`. -/
theorem UINorm.evalSeq_singularValue (N : UINorm) (T : E →L[𝕜] F) :
    N.evalSeq (fun n => singularValue T n) = N.toPaper.extendedGauge T := rfl

/-- **A sequence that is an operator's singular-value sequence is measured by
the operator's norm.**  This is the bridge every tangent conclusion needs: a
representative with the right approximation numbers turns a sequence norm into
an operator norm. -/
theorem UINorm.evalSeq_eq_of_approximationNumber (N : UINorm) (s : ℕ → ℝ)
    (T : E →L[𝕜] F) (h : ∀ n, T.approximationNumber n = s n) :
    N.evalSeq s = N.toPaper.extendedGauge T := by
  refine iSup_congr fun n => ?_
  congr 1
  exact congrArg _ (funext fun i => (h (i : ℕ)).symm)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `TangentDefined S` is `‖S‖ < 1` read off the singular-value sequence: the
`n`-th cosine vanishes exactly when the `n`-th singular value is one. -/
theorem tangentDefined_of_approximationNumber_lt_one (S : E →L[𝕜] F)
    (h : ∀ n, S.approximationNumber n < 1) : TangentDefined S := by
  intro n
  rw [Real.cos_arcsin]
  have h0 : 0 ≤ singularValue S n := S.approximationNumber_nonneg n
  have h1 : singularValue S n < 1 := h n
  exact ne_of_gt (Real.sqrt_pos.mpr (by nlinarith))

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Everything the Challenge measures is a function of the singular-value
sequence.**  Two operators -- over different fields, between different spaces --
with the same sequence are indistinguishable to a unitarily invariant norm, to
`tanSeq`, and to `TangentDefined`.  This is what makes the scalar transport a
one-line argument at each clause. -/
theorem tangentDefined_congr {𝕂 : Type w} [RCLike 𝕂] {X Y : Type v}
    [NormedAddCommGroup X] [InnerProductSpace 𝕂 X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕂 Y]
    {S : E →L[𝕜] F} {S' : X →L[𝕂] Y}
    (h : ∀ n, singularValue S' n = singularValue S n) (hS' : TangentDefined S') :
    TangentDefined S := fun n => by rw [← h n]; exact hS' n

omit [CompleteSpace E] [CompleteSpace F] in
/-- The tangent sequence depends only on the singular values. -/
theorem tanSeq_congr {𝕂 : Type w} [RCLike 𝕂] {X Y : Type v}
    [NormedAddCommGroup X] [InnerProductSpace 𝕂 X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕂 Y]
    {S : E →L[𝕜] F} {S' : X →L[𝕂] Y}
    (h : ∀ n, singularValue S' n = singularValue S n) : tanSeq S' = tanSeq S :=
  funext fun n => congrArg (fun r => Real.tan (Real.arcsin r)) (h n)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The norm's extended value depends only on the singular values. -/
theorem UINorm.eval_congr (N : UINorm) {𝕂 : Type w} [RCLike 𝕂] {X Y : Type v}
    [NormedAddCommGroup X] [InnerProductSpace 𝕂 X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕂 Y]
    {S : E →L[𝕜] F} {S' : X →L[𝕂] Y}
    (h : ∀ n, singularValue S' n = singularValue S n) : N.eval S' = N.eval S :=
  congrArg N.evalSeq (funext h)

/-- The two ideals are the same ideal. -/
theorem UINorm.finite_iff (N : UINorm) (T : E →L[𝕜] F) :
    N.Finite T ↔ N.toPaper.Mem T := Iff.rfl

/-- The two real-valued norms agree. -/
theorem UINorm.norm_eq (N : UINorm) (T : E →L[𝕜] F) :
    N.norm T = N.toPaper.gauge T := rfl

end NormBridge

/-! ## 2. The block data and the separation are the development's -/

section VocabularyBridge

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Challenge's isometry condition is the development's. -/
theorem isIsometric_iff (T : F →L[𝕜] E) :
    IsIsometric T ↔ TauCeti.DavisKahan.IsometricEmbedding T := Iff.rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Challenge's trial-residual data is the development's. -/
theorem isTrialResidual_iff (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F)
    (E₀ R : F →L[𝕜] E) :
    IsTrialResidual A A₀ E₀ R ↔ _root_.DavisKahan1970.IsTrialResidual A A₀ E₀ R := by
  constructor
  · exact fun h => ⟨h.isometry, h.mapsDomain, h.residualEquation⟩
  · exact fun h => ⟨h.isometry, h.mapsDomain, h.residualEquation⟩

/-- The Challenge's exact decomposition is the development's. -/
theorem isExactDecomposition_iff (A : E →ₗ.[𝕜] E) (Λ₁ : G →ₗ.[𝕜] G)
    (F₀ : K →L[𝕜] E) (F₁ : G →L[𝕜] E) :
    IsExactDecomposition A Λ₁ F₀ F₁ ↔
      _root_.DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ := by
  constructor
  · exact fun h => ⟨h.desiredIsometry, h.complementIsometry, h.orthogonal, h.complete,
      h.mapsDomain, h.intertwines⟩
  · exact fun h => ⟨h.desiredIsometry, h.complementIsometry, h.orthogonal, h.complete,
      h.mapsDomain, h.intertwines⟩

omit [CompleteSpace E] in
/-- The Challenge's real resolvent set is the development's. -/
theorem realResolventSet_eq (A : E →ₗ.[𝕜] E) :
    realResolventSet A = TauCeti.LinearPMap.realResolventSet A := by
  ext lam
  rw [TauCeti.LinearPMap.mem_realResolventSet_iff]
  rfl

omit [CompleteSpace E] in
/-- Hence so is the real spectrum. -/
theorem realSpectrum_eq (A : E →ₗ.[𝕜] E) :
    realSpectrum A = TauCeti.LinearPMap.realSpectrum A := by
  ext lam
  rw [TauCeti.LinearPMap.mem_realSpectrum_iff, realSpectrum, Set.mem_compl_iff,
    realResolventSet_eq]

omit [CompleteSpace E] in
/-- The Challenge's lower form bound is the development's. -/
theorem semiboundedBelow_iff (A : E →ₗ.[𝕜] E) (c : ℝ) :
    SemiboundedBelow A c ↔ TauCeti.LinearPMap.SemiboundedBelow A c := by
  rw [TauCeti.LinearPMap.semiboundedBelow_iff]
  exact Iff.rfl

omit [CompleteSpace E] in
/-- The Challenge's upper form bound is the development's. -/
theorem semiboundedAbove_iff (A : E →ₗ.[𝕜] E) (c : ℝ) :
    SemiboundedAbove A c ↔ TauCeti.LinearPMap.SemiboundedAbove A c := by
  rw [TauCeti.LinearPMap.semiboundedAbove_iff]
  exact Iff.rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Challenge's separation is the development's**, constructor by
constructor -- including both half-infinite configurations. -/
theorem sylvesterGap_iff (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) :
    SylvesterGap A B δ ↔ FormBoundedSylvesterGap A B δ := by
  constructor
  · rintro (⟨hβα, hgap⟩ | ⟨c, hA, hB⟩ | ⟨c, hA, hB⟩)
    · refine .intervalExterior hβα ?_
      rw [RealSpectrumIntervalExteriorGap, ← realSpectrum_eq, ← realSpectrum_eq]
      exact hgap
    · exact .leftAboveRightBelow c ((semiboundedBelow_iff _ _).1 hA)
        ((semiboundedAbove_iff _ _).1 hB)
    · exact .leftBelowRightAbove c ((semiboundedAbove_iff _ _).1 hA)
        ((semiboundedBelow_iff _ _).1 hB)
  · rintro (⟨hβα, hgap⟩ | ⟨c, hA, hB⟩ | ⟨c, hA, hB⟩)
    · refine .intervalExterior hβα ?_
      rw [RealSpectrumIntervalExteriorGap] at hgap
      rw [← realSpectrum_eq, ← realSpectrum_eq] at hgap
      exact hgap
    · exact .leftAboveRightBelow c ((semiboundedBelow_iff _ _).2 hA)
        ((semiboundedAbove_iff _ _).2 hB)
    · exact .leftBelowRightAbove c ((semiboundedAbove_iff _ _).2 hA)
        ((semiboundedBelow_iff _ _).2 hB)

end VocabularyBridge

/-! ## 3. Reduction, blocks and the perturbed operator -/

section ReducingBridge

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The Challenge's reduction predicate is the development's. -/
theorem reduces_iff (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    Reduces A U ↔ TauCeti.LinearPMap.ReducesSubspace A U := by
  constructor
  · exact fun h => TauCeti.LinearPMap.ReducesSubspace.of_components h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact fun h => ⟨h.projection_mem_domain, h.orthogonalProjection_mem_domain,
      h.invariant, h.orthogonal_invariant⟩

omit [CompleteSpace E] in
/-- **The Challenge's block is the development's reducing restriction**, as an
equality of partial maps: same domain, same action. -/
theorem block_eq (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (h : Reduces A U) :
    block A U h = TauCeti.LinearPMap.reducingRestriction A U ((reduces_iff A U).1 h) := by
  refine LinearPMap.ext ?_ ?_
  · refine Submodule.ext fun x => ?_
    rw [TauCeti.LinearPMap.reducingRestriction_domain,
      TauCeti.LinearPMap.mem_reducingRestrictionDomain_iff]
    exact Iff.rfl
  · intro x hf hg
    refine Subtype.ext ?_
    exact (TauCeti.LinearPMap.coe_reducingRestriction_apply A U
      ((reduces_iff A U).1 h) x hg).symm

omit [CompleteSpace E] in
/-- The Challenge's bounded perturbation of a partial map is the
development's. -/
theorem addBounded_eq (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    addBounded A V = TauCeti.LinearPMap.addBounded A V := by
  refine LinearPMap.ext ?_ ?_
  · rw [TauCeti.LinearPMap.addBounded_domain]
    rfl
  · intro x hf hg
    rw [TauCeti.LinearPMap.addBounded_apply]
    rfl


/-- **A Challenge Rayleigh--Ritz bundle is the development's unbounded Ritz
pair**, field for field.  The compression stays a partial map, so the Appendix
scope in which the Ritz operator is unbounded survives the translation. -/
def RitzData.toUnboundedRitzPair {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (D : RitzData A U) :
    TauCeti.DavisKahan.UnboundedRitzPair A U where
  trial :=
    { compression := D.compression
      compression_isSelfAdjoint := D.compression_selfAdjoint
      residual := D.residual
      residual_orthogonal := D.residual_orthogonal }
  mem_domain := D.mem_domain
  action_eq := fun z => (D.action_eq z).symm

omit [CompleteSpace E] in
/-- The Challenge's two vanishing diagonal blocks are the development's
odd-for-the-splitting condition: this is the source's `H₀ = H₁ = 0`. -/
theorem isOddFor_of_offDiagonal {H : E →L[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection]
    (h₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (h₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0) :
    TauCeti.IsOddFor U H := by
  constructor
  · intro x hx
    refine (Submodule.starProjection_apply_eq_zero_iff U).1 ?_
    have hx0 := congrArg (fun T : E →L[𝕜] E => T x) h₀
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at hx0
    rwa [Submodule.starProjection_eq_self_iff.mpr hx] at hx0
  · intro x hx
    rw [← Submodule.orthogonal_orthogonal U]
    refine (Submodule.starProjection_apply_eq_zero_iff Uᗮ).1 ?_
    have hx1 := congrArg (fun T : E →L[𝕜] E => T x) h₁
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at hx1
    rwa [Submodule.starProjection_eq_self_iff.mpr hx] at hx1

/-- **A subspace reducing the perturbed operator gives the reflection data the
ambient double-angle theorems consume.** -/
theorem reflectionIntertwines_of_reduces {A : E →ₗ.[𝕜] E} {H : E →L[𝕜] E}
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V) :
    TauCeti.DavisKahan.ReflectionIntertwines A H V :=
  TauCeti.DavisKahan.ReflectionIntertwines.ofReducesSubspace
    (by rw [← addBounded_eq]; exact (reduces_iff _ _).1 hV)

omit [CompleteSpace E] in
/-- The ordered form bound on the trial block, in the ambient indexing the
development's ordered-gap endpoints take.  Reading the bound ambiently rather
than through `block` is what lets it cross a change of scalar field with no
transport of the subspace's own Hilbert structure. -/
theorem formBound_upper_of_semiboundedAbove {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U) {α : ℝ}
    (hlow : SemiboundedAbove (block A U hU) α) :
    ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ α * ‖(x : E)‖ ^ 2 := fun x hxU =>
  hlow ⟨⟨(x : E), hxU⟩, x.2⟩

omit [CompleteSpace E] in
/-- The ordered form bound on the complementary block, likewise. -/
theorem formBound_lower_of_semiboundedBelow {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U) {c : ℝ}
    (hhigh : SemiboundedBelow (block A Uᗮ hU.orthogonal) c) :
    ∀ x : A.domain, (x : E) ∈ Uᗮ →
      c * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜 := fun x hxU =>
  hhigh ⟨⟨(x : E), hxU⟩, x.2⟩

end ReducingBridge

/-! ## 4. The `sin Θ` theorem

Every Challenge object above is the development's, so the Challenge statement is
the development's statement.  What is left is the scalar field: the development
proves this at `ℝ` and at `ℂ`, and its `RCLike`-generic form carries two
capability binders that are instances at exactly those two fields. -/

section SinTheta

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- **The Challenge's `sin Θ` statement, discharged from the development at an
arbitrary `RCLike` field.**

There are no capability binders: `ContinuousLinearMap.hasMinMaxLowerBoundEverywhere`
and `ExactSinTheta.hasUnboundedSylvesterKyFan` are now instances at every `RCLike`
field, proved by transport through `TauCeti.ScalarTransport`.  So this is the
Challenge's `sinTheta` statement with nothing assumed beyond the source
hypotheses. -/
theorem sinTheta_proof
    (N : UINorm)
    {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {Λ₁ : G →ₗ.[𝕜] G}
    {E₀ : F →L[𝕜] E} {F₀ : K →L[𝕜] E} {F₁ : G →L[𝕜] E} {R : F →L[𝕜] E}
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (hres : IsTrialResidual A A₀ E₀ R) (hdec : IsExactDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SylvesterGap A₀ Λ₁ δ) (hR : N.Finite R) :
    N.Finite (directedSine E₀ F₀) ∧
      δ * N.norm (directedSine E₀ F₀) ≤ N.norm R :=
  _root_.DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike
    N.toPaper A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁
    ((isTrialResidual_iff A A₀ E₀ R).1 hres)
    ((isExactDecomposition_iff A Λ₁ F₀ F₁).1 hdec)
    hδ ((sylvesterGap_iff A₀ Λ₁ δ).1 hgap) hR

end SinTheta

/-! ## 5. The ambient clause of `sin 2Θ`

This is the clause that fixes the reducing-versus-spectral question in the
Challenge's favour: the development's ambient double-angle theorem is already
stated for an *arbitrary* reducing subspace, and the source's `Q` reduces
`A + H`, so no spectral selection is needed on either side.  The only piece the
Challenge has to supply is that reflection through `V` preserves `dom A` and
intertwines, which is `reflectionIntertwines_of_reduces`. -/

section SinTwoThetaAmbient

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **The ambient clause of the Challenge's `sin 2Θ` theorem, discharged from the
development**, at an arbitrary reducing subspace and the full source gap.

`δ ‖sin 2Θ‖ ≤ 2 ‖H‖`, with the angle read as the projector difference between
`U` and its mirror image in `V` -- which is exactly the Challenge's
`ambientDoubleSine`. -/
theorem sinTwoTheta_ambient_proof
    (N : UINorm) {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SylvesterGap (block A U hU) (block A Uᗮ hU.orthogonal) δ)
    (H : E →L[𝕜] E) (hH : IsSelfAdjoint H)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V) (hHmem : N.Finite H) :
    N.Finite (ambientDoubleSine U V) ∧
      δ * N.norm (ambientDoubleSine U V) ≤ 2 * N.norm H := by
  have hUred : TauCeti.LinearPMap.ReducesSubspace A U := (reduces_iff A U).1 hU
  have hRI := reflectionIntertwines_of_reduces hV
  have hHsym : TauCeti.DavisKahan.IsSelfAdjointOperator H :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH
  have hgap' : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hUred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hUred.orthogonal) δ := by
    rw [block_eq A U hU, block_eq A Uᗮ hU.orthogonal] at hgap
    exact (sylvesterGap_iff _ _ _).1 hgap
  refine TauCeti.DavisKahan1970.sinTwoTheta_ambient_reflection_projectorDifference_paperUINorm
    N.toPaper hA H hHsym hUred hRI.mapsDomain ?_ hδ hgap' hHmem
  intro x
  have hc := hRI.commutes x
  have hD : TauCeti.DavisKahan.reflectionPerturbation V H
        (V.reflectionOperator ((x : E))) =
      H (V.reflectionOperator ((x : E))) - V.reflectionOperator (H ((x : E))) := by
    show H _ - TauCeti.DavisKahan.boundedUnitaryConjugate V.reflection H _ = _
    rw [TauCeti.DavisKahan.boundedUnitaryConjugate_apply, V.reflection_symm]
    change H (V.reflection ((x : E))) -
      V.reflection (H (V.reflection (V.reflection ((x : E))))) = _
    rw [Submodule.reflection_reflection]
    rfl
  rw [TauCeti.LinearPMap.addBounded_apply, hD, ← add_sub_assoc]
  exact sub_eq_iff_eq_add.mpr hc

end SinTwoThetaAmbient

/-! ## 6. The ambient tangent correspondence

The Challenge's ambient `tan Θ` quantity is `N.seqNorm (tanSeq (ambientSine U V))`: the
norm's value on the sequence `tan θ₀, tan θ₁, …` of tangents of the principal angles.  The
development's ambient `tan Θ` estimate is about the *operator*
`paperTanAngleOperatorC U V`.  These carry the same content exactly when the operator's
approximation numbers are that sequence, which
`DavisKahan1970.approximationNumber_paperTanAngleOperatorC` now proves.

That closes the correspondence over `ℂ`; only the scalar field separates it from the
Challenge's clause. -/

section AmbientTangentBridge

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (U V : Submodule ℂ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **The Challenge's ambient tangent sequence is the development's tangent operator's
singular-value sequence.** -/
theorem tanSeq_ambientSine_eq_approximationNumber
    (htr : ‖TauCeti.DavisKahanExt.sinAngleOperatorC U V‖ < 1) (n : ℕ) :
    tanSeq (ambientSine U V) n =
      (TauCeti.DavisKahanExt.paperTanAngleOperatorC U V).approximationNumber n := by
  rw [TauCeti.DavisKahan1970.approximationNumber_paperTanAngleOperatorC U V htr n,
    TauCeti.DavisKahan1970.approximationNumber_sinAngleOperatorC U V n]
  rfl

/-- **Under uniform transversality no principal angle is a right angle**, so the
Challenge's `TangentDefined` conclusion holds. -/
theorem tangentDefined_ambientSine
    (htr : ‖TauCeti.DavisKahanExt.sinAngleOperatorC U V‖ < 1) :
    TangentDefined (ambientSine U V) := by
  intro n
  have hnorm : ‖ambientSine U V‖ < 1 := by
    have h : ‖TauCeti.DavisKahanExt.sinAngleOperatorC U V‖ = ‖ambientSine U V‖ := by
      rw [TauCeti.DavisKahanExt.sinAngleOperatorC, ContinuousLinearMap.norm_modulus,
        norm_sub_rev]
      rfl
    rwa [h] at htr
  have hle : singularValue (ambientSine U V) n ≤ ‖ambientSine U V‖ :=
    (ambientSine U V).approximationNumber_le_norm n
  have h0 : 0 ≤ singularValue (ambientSine U V) n :=
    (ambientSine U V).approximationNumber_nonneg n
  have hlt : singularValue (ambientSine U V) n < 1 := lt_of_le_of_lt hle hnorm
  rw [Real.cos_arcsin]
  exact ne_of_gt (Real.sqrt_pos.mpr (by nlinarith))

/-- **The Challenge's ambient tangent sequence norm is the development's paper norm of
`tan Θ`.**  This is the bridge the ambient `tan Θ` clause consumes. -/
theorem evalSeq_tanSeq_ambientSine (N : UINorm)
    (htr : ‖TauCeti.DavisKahanExt.sinAngleOperatorC U V‖ < 1) :
    N.evalSeq (tanSeq (ambientSine U V)) =
      N.toPaper.extendedGauge (TauCeti.DavisKahanExt.paperTanAngleOperatorC U V) :=
  N.evalSeq_eq_of_approximationNumber _ _
    (fun n => (tanSeq_ambientSine_eq_approximationNumber U V htr n).symm)

end AmbientTangentBridge

/-! ## 7. The directed `tan Θ` clause, over `ℂ`

The directed clause is the one whose left-hand side is a *sequence* norm with no operator
in sight, so it is the clearest test of the Challenge's tangent convention.  The
development supplies all three parts of it at the Appendix's own scope — the pole
exclusion, a representative with exactly the paper's approximation numbers, and the
inequality — in `tanTheta_directed_unboundedRitz_paperUINorm_exists_complex`.  What is
left here is the translation, and the scalar field. -/

section DirectedTangent

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The Challenge's directed sine block *is* the development's. -/
theorem directedSineBlock_eq (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedSineBlock U V = TauCeti.DavisKahan.ExactTanTheta.theorem63DirectedSineBlock U V :=
  rfl

/-- **The directed clause of the Challenge's `tan Θ` theorem, discharged from the
development over `ℂ`.**

All three printed parts: the tangent has no pole, the tangent sequence lies in the norm's
ideal, and `δ ‖tan Θ₀‖ ≤ ‖R‖`.  The compression is a partial map, the ambient operator is
an unbounded self-adjoint partial map, only the residual is bounded, the dimension is
arbitrary, the separation is the half-infinite ordered one, and the norm is arbitrary. -/
theorem tanTheta_directed_proof_complex (N : UINorm)
    {A : E →ₗ.[ℂ] E} {V : Submodule ℂ E} [V.HasOrthogonalProjection]
    (hV : Reduces A V) {α δ : ℝ} (hδ : 0 < δ)
    (hunwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    {U : Submodule ℂ E} [U.HasOrthogonalProjection] (D : RitzData A U)
    (hupper : SemiboundedAbove D.compression α) (hR : N.Finite D.residual) :
    TangentDefined (directedSineBlock U V) ∧
      N.SeqFinite (tanSeq (directedSineBlock U V)) ∧
      δ * N.seqNorm (tanSeq (directedSineBlock U V)) ≤ N.norm D.residual := by
  have hUnwanted := hunwanted
  obtain ⟨hlt, tanTheta0, htan, hmem, hbound⟩ :=
    TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_paperUINorm_exists_complex
      N.toPaper D.toUnboundedRitzPair
      (TauCeti.DavisKahan.ReducingComplement.ofReducesSubspace ((reduces_iff A V).1 hV))
      hδ ((semiboundedAbove_iff _ _).1 hupper) hUnwanted hR
  -- the Challenge's sequence is the representative's approximation-number sequence
  have hseq : ∀ n, (tanTheta0.approximationNumber n) = tanSeq (directedSineBlock U V) n :=
    fun n => htan n
  have heval : N.evalSeq (tanSeq (directedSineBlock U V)) =
      N.toPaper.extendedGauge tanTheta0 :=
    N.evalSeq_eq_of_approximationNumber _ _ hseq
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have h := hlt n
    rw [Real.cos_arcsin]
    have h0 : 0 ≤ singularValue (directedSineBlock U V) n :=
      (directedSineBlock U V).approximationNumber_nonneg n
    exact ne_of_gt (Real.sqrt_pos.mpr (by
      have : singularValue (directedSineBlock U V) n < 1 := h
      nlinarith))
  · show N.evalSeq (tanSeq (directedSineBlock U V)) ≠ ⊤
    rw [heval]
    exact hmem
  · show δ * (N.evalSeq (tanSeq (directedSineBlock U V))).toReal ≤ N.norm D.residual
    rw [heval]
    exact hbound

end DirectedTangent

/-! ## 8. The ambient `tan Θ` clause, over `ℂ` -/

section AmbientTangentClause

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The ambient clause of the Challenge's `tan Θ` theorem, discharged from the
development over `ℂ`.**

`δ ‖tan Θ‖ ≤ ‖H‖` on the tangent *sequence* of the ambient angle, with the pole exclusion
as a conclusion.  Uniform transversality is derived from the two form bounds and the
standing condition (3.5) by
`DavisKahan1970.norm_sinAngleOperatorC_lt_one_of_unboundedRitz`, and the sequence is
identified with the development's operator `tan Θ` by
`DavisKahan1970.approximationNumber_paperTanAngleOperatorC`. -/
theorem tanTheta_ambient_proof_complex (N : UINorm)
    {A : E →ₗ.[ℂ] E} {V : Submodule ℂ E} [V.HasOrthogonalProjection]
    (hV : Reduces A V) {α δ : ℝ} (hδ : 0 < δ)
    (hunwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    {U : Submodule ℂ E} [U.HasOrthogonalProjection] (D : RitzData A U)
    (hupper : SemiboundedAbove D.compression α)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (hres : D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (h35 : CrossedDefectsEquivalent U V) (hHmem : N.Finite H) :
    TangentDefined (ambientSine U V) ∧
      N.SeqFinite (tanSeq (ambientSine U V)) ∧
      δ * N.seqNorm (tanSeq (ambientSine U V)) ≤ N.norm H := by
  have hUnwanted := hunwanted
  have hVc : TauCeti.DavisKahan.ReducingComplement A V :=
    TauCeti.DavisKahan.ReducingComplement.ofReducesSubspace ((reduces_iff A V).1 hV)
  have hupper' : TauCeti.LinearPMap.SemiboundedAbove
      D.toUnboundedRitzPair.trial.compression α := (semiboundedAbove_iff _ _).1 hupper
  have htr : ‖TauCeti.DavisKahanExt.sinAngleOperatorC U V‖ < 1 :=
    TauCeti.DavisKahan1970.norm_sinAngleOperatorC_lt_one_of_unboundedRitz
      D.toUnboundedRitzPair hVc hδ hupper' hUnwanted h35
  obtain ⟨hmem, hbound⟩ :=
    TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_paperUINorm_complex
      N.toPaper D.toUnboundedRitzPair hVc H hH hδ hupper' hUnwanted h35 hres hHmem
  have heval := evalSeq_tanSeq_ambientSine U V N htr
  refine ⟨tangentDefined_ambientSine U V htr, ?_, ?_⟩
  · show N.evalSeq (tanSeq (ambientSine U V)) ≠ ⊤
    rw [heval]; exact hmem
  · show δ * (N.evalSeq (tanSeq (ambientSine U V))).toReal ≤ N.norm H
    rw [heval]; exact hbound

end AmbientTangentClause

/-! ## 9. The two `tan 2Θ` clauses, over `ℂ`

Both clauses read the doubled tangent off the **double-angle sine**, through the
same monotone `u ↦ tan (arcsin u)` that `tan Θ` uses.  That is forced: the map
`θ ↦ sin 2θ` is not monotone on `[0, π/2]`, so `n ↦ sin (2 arcsin aₙ(sin Θ))` is
not in general the ordered singular-value sequence of `sin 2Θ` — principal angles
`75°` and `30°` already invert the order — and no indexwise theorem can carry a
doubled angle from the single-angle sine at arbitrary dimension.

The development supplies both halves.  For the ambient clause,
`approximationNumber_paperAbsTanTwoAngleOperatorC_projectorDifference` says the
paper's `|tan 2Θ|` has exactly the sequence `tan (arcsin aₙ(sin 2Θ))`; for the
directed clause,
`tanTwoTheta_directed_unboundedResidual_reducing_derivedReflection_paperUINorm_complex`
says the same of the directed corner against `sin 2Θ₀`, with each directed
principal angle counted once. -/

section TanTwoThetaClauses

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The Challenge's directed double-angle sine *is* the development's directed
`sin 2Θ₀` block. -/
theorem directedDoubleSine_eq (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedDoubleSine U V = TauCeti.DavisKahan.sinTwoThetaIdealBlock U V := rfl

omit [CompleteSpace E] in
/-- The Challenge's ambient double-angle sine is the development's projector
difference between `U` and its mirror image in `V`. -/
theorem ambientDoubleSine_eq (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ambientDoubleSine U V =
      (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection -
        U.starProjection := rfl

/-- **The directed clause of the Challenge's `tan 2Θ` theorem, discharged from
the development over `ℂ`.**

`δ ‖tan 2Θ₀‖ ≤ 2 ‖R‖` on the residual corner alone, with the pole exclusion as a
conclusion and each directed principal angle counted once.  The trial subspace is
any subspace reducing `A` with the ordered separation; no spectral selection. -/
theorem tanTwoTheta_directed_proof_complex (N : UINorm)
    {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {U : Submodule ℂ E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[ℂ] E)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ α * ‖(x : E)‖ ^ 2)
    (hhigh : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    {V : Submodule ℂ E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V)
    (hRmem : N.Finite (Uᗮ.starProjection ∘L H ∘L U.starProjection)) :
    TangentDefined (directedDoubleSine U V) ∧
      N.SeqFinite (tanSeq (directedDoubleSine U V)) ∧
      δ * N.seqNorm (tanSeq (directedDoubleSine U V)) ≤
        2 * N.norm (Uᗮ.starProjection ∘L H ∘L U.starProjection) := by
  have hblk : TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H =
      Uᗮ.starProjection ∘L H ∘L U.starProjection := rfl
  have hgap : N.toPaper.extendedGauge
      (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) =
      N.toPaper.extendedGauge (TauCeti.DavisKahan.ExactSinTheta.paperBlockCompression Uᗮ U H) :=
    N.toPaper.extendedGauge_eq_of_hasSameApproximationNumbers
      (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock_same_compression Uᗮ U H)
  have hRmem0 : N.toPaper.Mem
      (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) := by
    rw [hblk]
    exact (N.finite_iff _).1 hRmem
  have hRmem' : N.toPaper.Mem
      (TauCeti.DavisKahan.ExactSinTheta.paperBlockCompression Uᗮ U H) := by
    unfold PaperUnitaryInvariantNorm.Mem at hRmem0 ⊢
    rwa [← hgap]
  obtain ⟨hlt, hseq, hmem, hle⟩ :=
    TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_reducing_derivedReflection_paperUINorm_complex
      N.toPaper V hA ((reduces_iff A U).1 hU)
      (isOddFor_of_offDiagonal hoffdiag₀ hoffdiag₁)
      (reflectionIntertwines_of_reduces hV)
      hlow hhigh (by linarith) hRmem'
  have heval : N.evalSeq (tanSeq (directedDoubleSine U V)) =
      N.toPaper.extendedGauge (TauCeti.DavisKahan1970.reflectionTangentCorner U
        V.reflectionOperator) :=
    N.evalSeq_eq_of_approximationNumber _ _ hseq
  refine ⟨tangentDefined_of_approximationNumber_lt_one _ hlt, ?_, ?_⟩
  · show N.evalSeq (tanSeq (directedDoubleSine U V)) ≠ ⊤
    rw [heval]; exact hmem
  · have hg : N.toPaper.gauge (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) =
        N.toPaper.gauge (TauCeti.DavisKahan.ExactSinTheta.paperBlockCompression Uᗮ U H) := by
      unfold PaperUnitaryInvariantNorm.gauge
      rw [hgap]
    have hδeq : α + δ - α = δ := by ring
    rw [hδeq] at hle
    have hgoal : δ * (N.evalSeq (tanSeq (directedDoubleSine U V))).toReal ≤
        2 * N.toPaper.gauge
          (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) := by
      rw [heval, hg]
      exact hle
    rw [← hblk]
    exact hgoal

/-- **The ambient clause of the Challenge's `tan 2Θ` theorem, discharged from the
development over `ℂ`.**

`δ ‖tan 2Θ‖ ≤ 2 ‖H‖` on the whole perturbation, with each ambient principal angle
counted with its ambient multiplicity, and the quarter-turn exclusion derived. -/
theorem tanTwoTheta_ambient_proof_complex (N : UINorm)
    {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {U : Submodule ℂ E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ α * ‖(x : E)‖ ^ 2)
    (hhigh : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    {V : Submodule ℂ E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V) (hHmem : N.Finite H) :
    TangentDefined (ambientDoubleSine U V) ∧
      N.SeqFinite (tanSeq (ambientDoubleSine U V)) ∧
      δ * N.seqNorm (tanSeq (ambientDoubleSine U V)) ≤ 2 * N.norm H := by
  obtain ⟨hcos, hmem, hle⟩ :=
    TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_reducing_paperUINorm_complex
      N.toPaper V hA ((reduces_iff A U).1 hU) hH
      (isOddFor_of_offDiagonal hoffdiag₀ hoffdiag₁)
      (reflectionIntertwines_of_reduces hV)
      hlow hhigh (by linarith) hHmem
  have hseq : ∀ n,
      (TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC U V).approximationNumber n =
        tanSeq (ambientDoubleSine U V) n := fun n =>
    TauCeti.DavisKahan1970.approximationNumber_paperAbsTanTwoAngleOperatorC_projectorDifference
      U V hcos n
  have heval : N.evalSeq (tanSeq (ambientDoubleSine U V)) =
      N.toPaper.extendedGauge
        (TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC U V) :=
    N.evalSeq_eq_of_approximationNumber _ _ hseq
  refine ⟨tangentDefined_of_approximationNumber_lt_one _ (fun n =>
    TauCeti.DavisKahan1970.approximationNumber_projectorDifference_lt_one U V hcos n), ?_, ?_⟩
  · show N.evalSeq (tanSeq (ambientDoubleSine U V)) ≠ ⊤
    rw [heval]; exact hmem
  · have hδeq : α + δ - α = δ := by ring
    rw [hδeq] at hle
    have hgoal : δ * (N.evalSeq (tanSeq (ambientDoubleSine U V))).toReal ≤
        2 * N.toPaper.gauge H := by
      rw [heval]; exact hle
    exact hgoal

end TanTwoThetaClauses

section TanTwoThetaDirectedReal

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The directed clause of the Challenge's `tan 2Θ` theorem, discharged from
the development over `ℝ`.**

`δ ‖tan 2Θ₀‖ ≤ 2 ‖R‖` on the residual corner alone, with the pole exclusion as a
conclusion and each directed principal angle counted once.  The trial subspace is
any subspace reducing `A` with the ordered separation; no spectral selection. -/
theorem tanTwoTheta_directed_proof_real (N : UINorm)
    {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[ℝ] E)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_ℝ ≤ α * ‖(x : E)‖ ^ 2)
    (hhigh : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℝ)
    {V : Submodule ℝ E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V)
    (hRmem : N.Finite (Uᗮ.starProjection ∘L H ∘L U.starProjection)) :
    TangentDefined (directedDoubleSine U V) ∧
      N.SeqFinite (tanSeq (directedDoubleSine U V)) ∧
      δ * N.seqNorm (tanSeq (directedDoubleSine U V)) ≤
        2 * N.norm (Uᗮ.starProjection ∘L H ∘L U.starProjection) := by
  have hblk : TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H =
      Uᗮ.starProjection ∘L H ∘L U.starProjection := rfl
  have hgap : N.toPaper.extendedGauge
      (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) =
      N.toPaper.extendedGauge (TauCeti.DavisKahan.ExactSinTheta.paperBlockCompression Uᗮ U H) :=
    N.toPaper.extendedGauge_eq_of_hasSameApproximationNumbers
      (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock_same_compression Uᗮ U H)
  have hRmem0 : N.toPaper.Mem
      (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) := by
    rw [hblk]
    exact (N.finite_iff _).1 hRmem
  have hRmem' : N.toPaper.Mem
      (TauCeti.DavisKahan.ExactSinTheta.paperBlockCompression Uᗮ U H) := by
    unfold PaperUnitaryInvariantNorm.Mem at hRmem0 ⊢
    rwa [← hgap]
  have hlow' : ∀ x : A.domain, (x : E) ∈ U →
      ⟪A x, (x : E)⟫_ℝ ≤ α * ‖(x : E)‖ ^ 2 := by
    intro x hx; simpa using hlow x hx
  have hhigh' : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ := by
    intro x hx; simpa using hhigh x hx
  obtain ⟨hlt, hseq, hmem, hle⟩ :=
    TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_reducing_sineSequence_paperUINorm_real
      N.toPaper V hA ((reduces_iff A U).1 hU)
      (isOddFor_of_offDiagonal hoffdiag₀ hoffdiag₁)
      (reflectionIntertwines_of_reduces hV)
      hlow' hhigh' (by linarith) hRmem'
  have heval : N.evalSeq (tanSeq (directedDoubleSine U V)) =
      N.toPaper.extendedGauge (TauCeti.DavisKahan1970.reflectionTangentCorner U
        V.reflectionOperator) :=
    N.evalSeq_eq_of_approximationNumber _ _ hseq
  refine ⟨tangentDefined_of_approximationNumber_lt_one _ hlt, ?_, ?_⟩
  · show N.evalSeq (tanSeq (directedDoubleSine U V)) ≠ ⊤
    rw [heval]; exact hmem
  · have hg : N.toPaper.gauge (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) =
        N.toPaper.gauge (TauCeti.DavisKahan.ExactSinTheta.paperBlockCompression Uᗮ U H) := by
      unfold PaperUnitaryInvariantNorm.gauge
      rw [hgap]
    have hδeq : α + δ - α = δ := by ring
    rw [hδeq] at hle
    have hgoal : δ * (N.evalSeq (tanSeq (directedDoubleSine U V))).toReal ≤
        2 * N.toPaper.gauge
          (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) := by
      rw [heval, hg]
      exact hle
    rw [← hblk]
    exact hgoal


end TanTwoThetaDirectedReal


/-! ## 10. The directed clause of `sin 2Θ`, over `ℂ`

The clause the Appendix bounds by a **bounded** trial compression: `V` sits
inside `dom A`, so `M` is bounded by the closed-graph theorem and the two are the
same hypothesis.  What is *not* assumed is that `U` was selected spectrally --
`sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_paperUINorm_complex`
takes any subspace reducing `A`, which is the source's own hypothesis. -/

section SinTwoThetaDirected

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The directed clause of the Challenge's `sin 2Θ` theorem, discharged from
the development over `ℂ`.**

`δ ‖sin 2Θ₀‖ ≤ 2 ‖R‖` on the residual alone, at an arbitrary reducing `U` and
the full form-bounded gap, so the separating interval may be half-infinite. -/
theorem sinTwoTheta_directed_proof_complex
    (N : UINorm) {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {U : Submodule ℂ E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SylvesterGap (block A U hU) (block A Uᗮ hU.orthogonal) δ)
    {V : Submodule ℂ E} [V.HasOrthogonalProjection] (D : BoundedTrialBlock A V)
    (hRmem : N.Finite D.residual) :
    N.Finite (directedDoubleSine U V) ∧
      δ * N.norm (directedDoubleSine U V) ≤ 2 * N.norm D.residual := by
  have hUred : TauCeti.LinearPMap.ReducesSubspace A U := (reduces_iff A U).1 hU
  have hgap' : TauCeti.DavisKahan.ExactSinTheta.FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hUred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hUred.orthogonal) δ := by
    rw [block_eq A U hU, block_eq A Uᗮ hU.orthogonal] at hgap
    exact (sylvesterGap_iff _ _ _).1 hgap
  have hres : ∀ v : V, A ⟨(v : E), D.mem_domain v⟩ =
      D.residual v + ((D.compression v : V) : E) := fun v =>
    (D.action_eq v).trans (add_comm _ _)
  exact TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_paperUINorm_complex
    N.toPaper hA hUred D.mem_domain hres hδ hgap' hRmem

end SinTwoThetaDirected

/-! ## 11. The scalar field

Every Challenge quantity above is a function of an operator's singular-value
sequence, and `TauCeti.ScalarTransport` changes neither the vectors, the norm,
the operators, nor therefore that sequence.  So a clause proved at `ℝ` and at `ℂ`
is a clause at every `RCLike` field: `RCLike.I_eq_zero_or_im_I_eq_one` says there
is an isomorphism onto one of the two, and the dictionary below carries the
statement across it. -/

section Transport

open TauCeti.ScalarTransport

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] {e : TauCeti.RCLikeIso 𝕜 𝕂}
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The transport is multiplicative on composable operators. -/
theorem clm_comp {G : Type v} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (X : F →L[𝕜] G) (Y : E →L[𝕜] F) :
    clm (e := e) (X ∘L Y) = clm (e := e) X ∘L clm (e := e) Y := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The transport of the zero operator. -/
theorem clm_zero : clm (e := e) (0 : E →L[𝕜] F) = 0 := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The transport preserves every value a unitarily invariant norm takes.**
Both sides read the same singular-value sequence. -/
theorem UINorm.eval_clm (N : UINorm) (T : E →L[𝕜] F) :
    N.eval (clm (e := e) T) = N.eval T :=
  congrArg N.evalSeq (funext fun n => approximationNumber_clm (e := e) T n)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Ideal membership is unchanged by the transport. -/
theorem UINorm.finite_clm_iff (N : UINorm) (T : E →L[𝕜] F) :
    N.Finite (clm (e := e) T) ↔ N.Finite T := by
  unfold UINorm.Finite
  rw [UINorm.eval_clm]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The real-valued norm is unchanged by the transport. -/
theorem UINorm.norm_clm (N : UINorm) (T : E →L[𝕜] F) :
    N.norm (clm (e := e) T) = N.norm T := by
  unfold UINorm.norm
  rw [UINorm.eval_clm]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Challenge's reducing predicate transports. -/
theorem reduces_pmap_iff {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] :
    Reduces (pmap (e := e) A) (submodule (e := e) U) ↔ Reduces A U := by
  rw [reduces_iff, reduces_iff, reducesSubspace_pmap_iff]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Challenge's bounded perturbation transports. -/
theorem addBounded_pmap {A : E →ₗ.[𝕜] E} (T : E →L[𝕜] E) :
    pmap (e := e) (addBounded A T) =
      addBounded (pmap (e := e) A) (clm (e := e) T) := by
  rw [addBounded_eq, addBounded_eq, pmap_addBounded]

omit [CompleteSpace F] in
omit [CompleteSpace E] in
/-- The ambient double-angle sine transports. -/
theorem ambientDoubleSine_pmap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ambientDoubleSine (submodule (e := e) U) (submodule (e := e) V) =
      clm (e := e) (ambientDoubleSine U V) := by
  show ((submodule (e := e) U).map _).starProjection -
      (submodule (e := e) U).starProjection = _
  rw [Submodule.starProjection_congr (submodule_map_reflection (e := e) U V).symm,
    starProjection_clm, starProjection_clm, ← clm_sub]
  rfl

omit [CompleteSpace F] in
omit [CompleteSpace E] in
/-- The directed double-angle sine transports. -/
theorem directedDoubleSine_pmap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedDoubleSine (submodule (e := e) U) (submodule (e := e) V) =
      clm (e := e) (directedDoubleSine U V) := by
  have hmap : ((submodule (e := e) U)ᗮ).map
      (((submodule (e := e) V).reflection.toLinearEquiv :
        ScalarTransport e E →ₗ[𝕂] ScalarTransport e E)) =
      submodule (e := e) (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)) := by
    rw [submodule_orthogonal]
    exact (submodule_map_reflection (e := e) Uᗮ V).symm
  show (submodule (e := e) U).starProjection ∘L
      ((submodule (e := e) U)ᗮ.map _).starProjection = _
  rw [Submodule.starProjection_congr hmap, starProjection_clm, starProjection_clm,
    ← clm_comp]
  rfl

omit [CompleteSpace F] in
omit [CompleteSpace E] in
/-- `TangentDefined` reads only the singular-value sequence, so it transports. -/
theorem tangentDefined_clm_iff (T : E →L[𝕜] F) :
    TangentDefined (clm (e := e) T) ↔ TangentDefined T := by
  constructor <;> intro h n
  · have := h n
    rwa [show singularValue (clm (e := e) T) n = singularValue T n from
      approximationNumber_clm (e := e) T n] at this
  · have := h n
    rwa [show singularValue (clm (e := e) T) n = singularValue T n from
      approximationNumber_clm (e := e) T n]

omit [CompleteSpace F] in
omit [CompleteSpace E] in
/-- and so does the tangent sequence itself. -/
theorem tanSeq_clm (T : E →L[𝕜] F) :
    tanSeq (clm (e := e) T) = tanSeq T :=
  funext fun n => congrArg (fun r => Real.tan (Real.arcsin r))
    (approximationNumber_clm (e := e) T n)


omit [CompleteSpace E] [CompleteSpace F] in
/-- The Challenge's semibounded-above predicate transports across any partial
map: both sides read the same real part of the same inner product. -/
theorem semiboundedAbove_pmap' {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] {M : G →ₗ.[𝕜] G} {c : ℝ}
    (h : SemiboundedAbove M c) : SemiboundedAbove (pmap (e := e) M) c := by
  intro y
  have h' := h ⟨out (e := e) (y : ScalarTransport e G), y.2⟩
  show RCLike.re (inner 𝕂
      (of (e := e) (M ⟨out (e := e) (y : ScalarTransport e G), y.2⟩))
      (of (e := e) (out (e := e) (y : ScalarTransport e G)))) ≤
    c * ‖out (e := e) (y : ScalarTransport e G)‖ ^ 2
  rw [re_inner_of]
  exact h'

omit [CompleteSpace E] [CompleteSpace F] in
/-- and so does the semibounded-below predicate. -/
theorem semiboundedBelow_pmap' {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] {M : G →ₗ.[𝕜] G} {c : ℝ}
    (h : SemiboundedBelow M c) : SemiboundedBelow (pmap (e := e) M) c := by
  intro y
  have h' := h ⟨out (e := e) (y : ScalarTransport e G), y.2⟩
  show c * ‖out (e := e) (y : ScalarTransport e G)‖ ^ 2 ≤
    RCLike.re (inner 𝕂
      (of (e := e) (M ⟨out (e := e) (y : ScalarTransport e G), y.2⟩))
      (of (e := e) (out (e := e) (y : ScalarTransport e G))))
  rw [re_inner_of]
  exact h'

omit [CompleteSpace F] in
omit [CompleteSpace E] in
/-- The Challenge's block of a reducing subspace transports. -/
theorem block_pmap {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (hU' : Reduces (pmap (e := e) A) (submodule (e := e) U)) :
    pmap (e := e) (block A U hU) =
      block (pmap (e := e) A) (submodule (e := e) U) hU' :=
  LinearPMap.ext rfl fun _ _ _ => rfl

omit [CompleteSpace F] in
omit [CompleteSpace E] in
/-- The Challenge's semibounded-above predicate transports along the block. -/
theorem semiboundedAbove_block_pmap {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] {hU : Reduces A U}
    {hU' : Reduces (pmap (e := e) A) (submodule (e := e) U)} {c : ℝ}
    (h : SemiboundedAbove (block A U hU) c) :
    SemiboundedAbove (block (pmap (e := e) A) (submodule (e := e) U) hU') c := by
  rw [← block_pmap (e := e) hU hU']
  exact semiboundedAbove_pmap' h

omit [CompleteSpace F] in
omit [CompleteSpace E] in
/-- and so does the semibounded-below predicate. -/
theorem semiboundedBelow_block_pmap {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] {hU : Reduces A U}
    {hU' : Reduces (pmap (e := e) A) (submodule (e := e) U)} {c : ℝ}
    (h : SemiboundedBelow (block A U hU) c) :
    SemiboundedBelow (block (pmap (e := e) A) (submodule (e := e) U) hU') c := by
  rw [← block_pmap (e := e) hU hU']
  exact semiboundedBelow_pmap' h

omit [CompleteSpace F] in
/-- **A Rayleigh--Ritz bundle transports.**

The compression is a partial map on the trial subspace and the residual a bounded
map out of it.  The trial subspace needs no separate carrier: `ScalarTransport e
↥U` and `↥(ScalarTransport.submodule e U)` are the same space with the same
structure. -/
def RitzData.pmap {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (D : RitzData A U) :
    RitzData (TauCeti.ScalarTransport.pmap (e := e) A)
      (TauCeti.ScalarTransport.submodule (e := e) U) where
  compression := TauCeti.ScalarTransport.pmap (e := e) D.compression
  compression_selfAdjoint :=
    (isSelfAdjoint_pmap_iff (e := e)).mpr D.compression_selfAdjoint
  residual := clm (e := e) D.residual
  mem_domain := fun z => D.mem_domain z
  action_eq := fun z => congrArg (of (e := e)) (D.action_eq z)
  residual_orthogonal := fun z z' => by
    show inner 𝕂 (of (e := e) (D.residual (out (e := e) z)))
      (of (e := e) (((out (e := e) z' : ↥U) : E))) = 0
    rw [inner_of, D.residual_orthogonal (out (e := e) z) (out (e := e) z'), map_zero]

omit [CompleteSpace F] in
/-- **A bounded trial block transports**, likewise. -/
def BoundedTrialBlock.pmap {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (D : BoundedTrialBlock A U) :
    BoundedTrialBlock (TauCeti.ScalarTransport.pmap (e := e) A)
      (TauCeti.ScalarTransport.submodule (e := e) U) where
  compression := clm (e := e) D.compression
  compression_selfAdjoint :=
    (isSelfAdjoint_clm_iff (e := e)).mpr D.compression_selfAdjoint
  residual := clm (e := e) D.residual
  mem_domain := fun z => D.mem_domain z
  action_eq := fun z => congrArg (of (e := e)) (D.action_eq z)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The directed sine block transports. -/
theorem directedSineBlock_pmap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedSineBlock (submodule (e := e) U) (submodule (e := e) V) =
      clm (e := e) (directedSineBlock U V) := by
  show (submodule (e := e) V)ᗮ.starProjection ∘L
    (submodule (e := e) U).subtypeL = _
  rw [Submodule.starProjection_congr (submodule_orthogonal (e := e) V),
    starProjection_clm]
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The ambient sine transports. -/
theorem ambientSine_pmap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ambientSine (submodule (e := e) U) (submodule (e := e) V) =
      clm (e := e) (ambientSine U V) := by
  show (submodule (e := e) V).starProjection -
    (submodule (e := e) U).starProjection = _
  rw [starProjection_clm, starProjection_clm, ← clm_sub]
  rfl


omit [CompleteSpace E] [CompleteSpace F] in
/-- The inclusion of a transported subspace is the transport of the inclusion. -/
theorem subtypeL_pmap (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (submodule (e := e) U).subtypeL =
      (clm (e := e) U.subtypeL : ↥(submodule (e := e) U) →L[𝕂] ScalarTransport e E) :=
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The crossed-defect standing condition (3.5) transports.**

It says two defect subspaces are isometrically isomorphic, and neither the
subspaces nor an isometry between them sees the scalar field. -/
theorem crossedDefectsEquivalent_pmap {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h35 : CrossedDefectsEquivalent U V) :
    CrossedDefectsEquivalent (submodule (e := e) U) (submodule (e := e) V) := by
  obtain ⟨f⟩ := h35
  have hL : submodule (e := e) (U ⊓ Vᗮ) =
      submodule (e := e) U ⊓ (submodule (e := e) V)ᗮ := by
    rw [submodule_inf, submodule_orthogonal]
  have hR : submodule (e := e) (Uᗮ ⊓ V) =
      (submodule (e := e) U)ᗮ ⊓ submodule (e := e) V := by
    rw [submodule_inf, submodule_orthogonal]
  exact ⟨((submoduleEquivOfEq hL).symm.trans
    (linearIsometryEquiv (e := e) f)).trans (submoduleEquivOfEq hR)⟩


omit [CompleteSpace F] in
omit [CompleteSpace E] in
/-- The Challenge's real spectrum transports. -/
theorem realSpectrum_pmap' (A : E →ₗ.[𝕜] E) :
    realSpectrum (pmap (e := e) A) = realSpectrum A := by
  rw [realSpectrum_eq, realSpectrum_eq, TauCeti.ScalarTransport.realSpectrum_pmap]

omit [CompleteSpace F] in
omit [CompleteSpace E] in
/-- The Challenge's real spectrum transports for an operator on a subspace,
stated at the transported subspace's own instance path. -/
theorem realSpectrum_pmap_subspace (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (M : ↥U →ₗ.[𝕜] ↥U) :
    realSpectrum ((pmap (e := e) M :
        ↥(submodule (e := e) U) →ₗ.[𝕂] ↥(submodule (e := e) U))) =
      realSpectrum M :=
  realSpectrum_pmap' (e := e) M

omit [CompleteSpace F] in
omit [CompleteSpace E] in
/-- The Challenge's real spectrum of a block transports. -/
theorem realSpectrum_block_pmap {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] {hU : Reduces A U}
    {hU' : Reduces (pmap (e := e) A) (submodule (e := e) U)} :
    realSpectrum (block (pmap (e := e) A) (submodule (e := e) U) hU') =
      realSpectrum (block A U hU) := by
  rw [← block_pmap (e := e) hU hU']
  exact realSpectrum_pmap_subspace (e := e) U (block A U hU)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Replacing a block's subspace by an equal one leaves the separation
unchanged: the two blocks are the same partial map, and the reducing witness and
the projection instance are propositions. -/
theorem sylvesterGap_congr_right {X : Type v} [NormedAddCommGroup X]
    [InnerProductSpace 𝕜 X] {A' : X →ₗ.[𝕜] X} {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] {B : G →ₗ.[𝕜] G}
    {W W' : Submodule 𝕜 X} [W.HasOrthogonalProjection] [W'.HasOrthogonalProjection]
    (hWW : W = W') {hW : Reduces A' W} {hW' : Reduces A' W'} {δ : ℝ}
    (h : SylvesterGap B (block A' W hW) δ) :
    SylvesterGap B (block A' W' hW') δ := by
  subst hWW
  exact h

omit [CompleteSpace F] in
omit [CompleteSpace E] in
/-- **The Challenge's separation transports**, constructor by constructor. -/
theorem sylvesterGap_block_pmap {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] {hU : Reduces A U}
    {hU' : Reduces (pmap (e := e) A) (submodule (e := e) U)}
    {hUc' : Reduces (pmap (e := e) A) (submodule (e := e) Uᗮ)} {δ : ℝ}
    (h : SylvesterGap (block A U hU) (block A Uᗮ hU.orthogonal) δ) :
    SylvesterGap (block (pmap (e := e) A) (submodule (e := e) U) hU')
      (block (pmap (e := e) A) (submodule (e := e) Uᗮ) hUc') δ := by
  cases h with
  | intervalExterior hβα hgap =>
      refine SylvesterGap.intervalExterior hβα ?_
      rw [realSpectrum_block_pmap (e := e) (hU := hU) (hU' := hU'),
        realSpectrum_block_pmap (e := e) (hU := hU.orthogonal) (hU' := hUc')]
      exact hgap
  | leftAboveRightBelow c hA' hB' =>
      exact SylvesterGap.leftAboveRightBelow c
        (semiboundedBelow_block_pmap (e := e) (hU := hU) (hU' := hU') hA')
        (semiboundedAbove_block_pmap (e := e) (hU := hU.orthogonal) (hU' := hUc') hB')
  | leftBelowRightAbove c hA' hB' =>
      exact SylvesterGap.leftBelowRightAbove c
        (semiboundedAbove_block_pmap (e := e) (hU := hU) (hU' := hU') hA')
        (semiboundedBelow_block_pmap (e := e) (hU := hU.orthogonal) (hU' := hUc') hB')

end Transport

/-! ## 12. The ambient `tan 2Θ` clause over `ℝ`, and at every `RCLike` field -/

section TanTwoThetaAmbientGeneric

/-- **The ambient clause of the Challenge's `tan 2Θ` theorem, over `ℝ`.**

The real sibling of `tanTwoTheta_ambient_proof_complex`, discharged from
`tanTwoTheta_ambient_unbounded_reducing_sineSequence_paperUINorm_real`, whose
proof is the complex one applied to the complexification. -/
theorem tanTwoTheta_ambient_proof_real (N : UINorm)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[ℝ] E) (hH : IsSelfAdjoint H)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_ℝ ≤ α * ‖(x : E)‖ ^ 2)
    (hhigh : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℝ)
    {V : Submodule ℝ E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V) (hHmem : N.Finite H) :
    TangentDefined (ambientDoubleSine U V) ∧
      N.SeqFinite (tanSeq (ambientDoubleSine U V)) ∧
      δ * N.seqNorm (tanSeq (ambientDoubleSine U V)) ≤ 2 * N.norm H := by
  have hlow' : ∀ x : A.domain, (x : E) ∈ U →
      ⟪A x, (x : E)⟫_ℝ ≤ α * ‖(x : E)‖ ^ 2 := by
    intro x hx
    simpa using hlow x hx
  have hhigh' : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ := by
    intro x hx
    simpa using hhigh x hx
  obtain ⟨hlt, hseq, hmem, hle⟩ :=
    TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_reducing_sineSequence_paperUINorm_real
      hA ((reduces_iff A U).1 hU) (isOddFor_of_offDiagonal hoffdiag₀ hoffdiag₁)
      hlow' hhigh' (by linarith : α < α + δ) N.toPaper V hH
      (reflectionIntertwines_of_reduces hV) hHmem
  have hlt' : ∀ n, (ambientDoubleSine U V).approximationNumber n < 1 := hlt
  have hseq' : ∀ n,
      (TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorR U V).approximationNumber n =
        tanSeq (ambientDoubleSine U V) n := hseq
  have heval : N.evalSeq (tanSeq (ambientDoubleSine U V)) =
      N.toPaper.extendedGauge
        (TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorR U V) :=
    N.evalSeq_eq_of_approximationNumber _ _ hseq'
  refine ⟨tangentDefined_of_approximationNumber_lt_one _ hlt', ?_, ?_⟩
  · show N.evalSeq (tanSeq (ambientDoubleSine U V)) ≠ ⊤
    rw [heval]; exact hmem
  · have hδeq : α + δ - α = δ := by ring
    rw [hδeq] at hle
    have hgoal : δ * (N.evalSeq (tanSeq (ambientDoubleSine U V))).toReal ≤
        2 * N.toPaper.gauge H := by
      rw [heval]; exact hle
    exact hgoal

open TauCeti.ScalarTransport in
/-- **The shared hypothesis package of the ordered-gap clauses, transported.**

Self-adjointness, reducing, the two vanishing diagonal blocks, the two ordered
form bounds and the reduction of the perturbed operator, all read at the
transported field.  Nothing here is specific to a single clause: it is the
Section 2 ordered-gap data. -/
theorem orderedGap_hypotheses_pmap {𝕜 : Type u} {𝕂 : Type} [RCLike 𝕜] [RCLike 𝕂]
    (e : TauCeti.RCLikeIso 𝕜 𝕂)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[𝕜] E)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ}
    (hlow : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ α * ‖(x : E)‖ ^ 2)
    (hhigh : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V) :
      IsSelfAdjoint (pmap (e := e) A) ∧
      Reduces (pmap (e := e) A) (submodule (e := e) U) ∧
      ((submodule (e := e) U).starProjection ∘L clm (e := e) H ∘L
        (submodule (e := e) U).starProjection = 0) ∧
      ((submodule (e := e) U)ᗮ.starProjection ∘L clm (e := e) H ∘L
        (submodule (e := e) U)ᗮ.starProjection = 0) ∧
      (∀ y : (pmap (e := e) A).domain,
        (y : ScalarTransport e E) ∈ submodule (e := e) U →
        RCLike.re ⟪pmap (e := e) A y, (y : ScalarTransport e E)⟫_𝕂 ≤
          α * ‖(y : ScalarTransport e E)‖ ^ 2) ∧
      (∀ y : (pmap (e := e) A).domain,
        (y : ScalarTransport e E) ∈ (submodule (e := e) U)ᗮ →
        (α + δ) * ‖(y : ScalarTransport e E)‖ ^ 2 ≤
          RCLike.re ⟪pmap (e := e) A y, (y : ScalarTransport e E)⟫_𝕂) ∧
      Reduces (addBounded (pmap (e := e) A) (clm (e := e) H))
        (submodule (e := e) V) := by
  refine ⟨(isSelfAdjoint_pmap_iff (e := e)).mpr hA,
    (reduces_pmap_iff (e := e)).mpr hU, ?_, ?_, ?_, ?_, ?_⟩
  · rw [starProjection_clm, ← clm_comp, ← clm_comp, hoffdiag₀, clm_zero]
  · rw [Submodule.starProjection_congr (submodule_orthogonal (e := e) U),
      starProjection_clm, ← clm_comp, ← clm_comp, hoffdiag₁, clm_zero]
  · intro y hy
    have hmem : out (e := e) (y : ScalarTransport e E) ∈ A.domain := y.2
    have h := hlow ⟨out (e := e) (y : ScalarTransport e E), hmem⟩
      ((mem_submodule (e := e)).mp hy)
    show RCLike.re (inner 𝕂
        (of (e := e) (A ⟨out (e := e) (y : ScalarTransport e E), hmem⟩))
        (of (e := e) (out (e := e) (y : ScalarTransport e E)))) ≤
      α * ‖out (e := e) (y : ScalarTransport e E)‖ ^ 2
    rw [re_inner_of]
    exact h
  · intro y hy
    have hmem : out (e := e) (y : ScalarTransport e E) ∈ A.domain := y.2
    have hy' : out (e := e) (y : ScalarTransport e E) ∈ Uᗮ := by
      rw [← mem_submodule (e := e), ← submodule_orthogonal (e := e) U]
      exact hy
    have h := hhigh ⟨out (e := e) (y : ScalarTransport e E), hmem⟩ hy'
    show (α + δ) * ‖out (e := e) (y : ScalarTransport e E)‖ ^ 2 ≤
      RCLike.re (inner 𝕂
        (of (e := e) (A ⟨out (e := e) (y : ScalarTransport e E), hmem⟩))
        (of (e := e) (out (e := e) (y : ScalarTransport e E))))
    rw [re_inner_of]
    exact h
  · rw [← addBounded_pmap (e := e) H]
    exact (reduces_pmap_iff (e := e)).mpr hV

open TauCeti.ScalarTransport in
/-- **The ambient clause of the Challenge's `tan 2Θ` theorem, at an arbitrary
`RCLike` field.**

The two fixed-field proofs above, read through `TauCeti.ScalarTransport`.  Every
hypothesis is a statement about vectors, norms, inner-product real parts,
subspaces and operators, all of which the transport carries verbatim; every
conclusion is a function of one operator's singular-value sequence, which it also
carries.  So the case split of `RCLike.I_eq_zero_or_im_I_eq_one` is the whole
argument. -/
theorem tanTwoTheta_ambient_proof (N : UINorm)
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[𝕜] E) (hH : IsSelfAdjoint H)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ α * ‖(x : E)‖ ^ 2)
    (hhigh : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V) (hHmem : N.Finite H) :
    TangentDefined (ambientDoubleSine U V) ∧
      N.SeqFinite (tanSeq (ambientDoubleSine U V)) ∧
      δ * N.seqNorm (tanSeq (ambientDoubleSine U V)) ≤ 2 * N.norm H := by
  -- the transported statement, whichever of the two fields we land in
  have key : ∀ {𝕂 : Type} [RCLike 𝕂] (e : TauCeti.RCLikeIso 𝕜 𝕂),
      (TangentDefined (ambientDoubleSine (submodule (e := e) U) (submodule (e := e) V)) ∧
        N.SeqFinite (tanSeq (ambientDoubleSine (submodule (e := e) U)
          (submodule (e := e) V))) ∧
        δ * N.seqNorm (tanSeq (ambientDoubleSine (submodule (e := e) U)
          (submodule (e := e) V))) ≤ 2 * N.norm (clm (e := e) H)) →
      TangentDefined (ambientDoubleSine U V) ∧
        N.SeqFinite (tanSeq (ambientDoubleSine U V)) ∧
        δ * N.seqNorm (tanSeq (ambientDoubleSine U V)) ≤ 2 * N.norm H := by
    intro 𝕂 _ e h
    rw [ambientDoubleSine_pmap (e := e) U V, tanSeq_clm, tangentDefined_clm_iff,
      UINorm.norm_clm] at h
    exact h
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
  · set e := TauCeti.RCLikeIso.real (𝕜 := 𝕜) hI with he
    obtain ⟨h1, h2, h4, h5, h6, h7, h8⟩ :=
      orderedGap_hypotheses_pmap e hA hU H hoffdiag₀ hoffdiag₁ hlow hhigh hV
    exact key (𝕂 := ℝ) e
      (tanTwoTheta_ambient_proof_real N h1 h2 _ ((isSelfAdjoint_clm_iff (e := e)).mpr hH)
        h4 h5 hδ h6 h7 h8 ((UINorm.finite_clm_iff (e := e) N H).mpr hHmem))
  · set e := TauCeti.RCLikeIso.complex (𝕜 := 𝕜) hI with he
    obtain ⟨h1, h2, h4, h5, h6, h7, h8⟩ :=
      orderedGap_hypotheses_pmap e hA hU H hoffdiag₀ hoffdiag₁ hlow hhigh hV
    exact key (𝕂 := ℂ) e
      (tanTwoTheta_ambient_proof_complex N h1 h2 _ ((isSelfAdjoint_clm_iff (e := e)).mpr hH)
        h4 h5 hδ h6 h7 h8 ((UINorm.finite_clm_iff (e := e) N H).mpr hHmem))


open TauCeti.ScalarTransport in
/-- The residual corner `P_{Uᗮ} H P_U` transports. -/
theorem residualCorner_pmap {𝕜 : Type u} {𝕂 : Type} [RCLike 𝕜] [RCLike 𝕂]
    {e : TauCeti.RCLikeIso 𝕜 𝕂} {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (H : E →L[𝕜] E) :
    (submodule (e := e) U)ᗮ.starProjection ∘L clm (e := e) H ∘L
        (submodule (e := e) U).starProjection =
      clm (e := e) (Uᗮ.starProjection ∘L H ∘L U.starProjection) := by
  rw [Submodule.starProjection_congr (submodule_orthogonal (e := e) U),
    starProjection_clm, starProjection_clm, ← clm_comp, ← clm_comp]

open TauCeti.ScalarTransport in
/-- **The directed clause of the Challenge's `tan 2Θ` theorem, at an arbitrary
`RCLike` field.** -/
theorem tanTwoTheta_directed_proof (N : UINorm)
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[𝕜] E)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ α * ‖(x : E)‖ ^ 2)
    (hhigh : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      (α + δ) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V)
    (hRmem : N.Finite (Uᗮ.starProjection ∘L H ∘L U.starProjection)) :
    TangentDefined (directedDoubleSine U V) ∧
      N.SeqFinite (tanSeq (directedDoubleSine U V)) ∧
      δ * N.seqNorm (tanSeq (directedDoubleSine U V)) ≤
        2 * N.norm (Uᗮ.starProjection ∘L H ∘L U.starProjection) := by
  have key : ∀ {𝕂 : Type} [RCLike 𝕂] (e : TauCeti.RCLikeIso 𝕜 𝕂),
      (TangentDefined (directedDoubleSine (submodule (e := e) U) (submodule (e := e) V)) ∧
        N.SeqFinite (tanSeq (directedDoubleSine (submodule (e := e) U)
          (submodule (e := e) V))) ∧
        δ * N.seqNorm (tanSeq (directedDoubleSine (submodule (e := e) U)
          (submodule (e := e) V))) ≤
          2 * N.norm ((submodule (e := e) U)ᗮ.starProjection ∘L clm (e := e) H ∘L
            (submodule (e := e) U).starProjection)) →
      TangentDefined (directedDoubleSine U V) ∧
        N.SeqFinite (tanSeq (directedDoubleSine U V)) ∧
        δ * N.seqNorm (tanSeq (directedDoubleSine U V)) ≤
          2 * N.norm (Uᗮ.starProjection ∘L H ∘L U.starProjection) := by
    intro 𝕂 _ e h
    rw [directedDoubleSine_pmap (e := e) U V, tanSeq_clm, tangentDefined_clm_iff,
      residualCorner_pmap (e := e) U H, UINorm.norm_clm] at h
    exact h
  have pushR : ∀ {𝕂 : Type} [RCLike 𝕂] (e : TauCeti.RCLikeIso 𝕜 𝕂),
      N.Finite ((submodule (e := e) U)ᗮ.starProjection ∘L clm (e := e) H ∘L
        (submodule (e := e) U).starProjection) := by
    intro 𝕂 _ e
    rw [residualCorner_pmap (e := e) U H]
    exact (UINorm.finite_clm_iff (e := e) N _).mpr hRmem
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
  · set e := TauCeti.RCLikeIso.real (𝕜 := 𝕜) hI with he
    obtain ⟨h1, h2, h4, h5, h6, h7, h8⟩ :=
      orderedGap_hypotheses_pmap e hA hU H hoffdiag₀ hoffdiag₁ hlow hhigh hV
    exact key (𝕂 := ℝ) e
      (tanTwoTheta_directed_proof_real N h1 h2 _ h4 h5 hδ h6 h7 h8 (pushR (𝕂 := ℝ) e))
  · set e := TauCeti.RCLikeIso.complex (𝕜 := 𝕜) hI with he
    obtain ⟨h1, h2, h4, h5, h6, h7, h8⟩ :=
      orderedGap_hypotheses_pmap e hA hU H hoffdiag₀ hoffdiag₁ hlow hhigh hV
    exact key (𝕂 := ℂ) e
      (tanTwoTheta_directed_proof_complex N h1 h2 _ h4 h5 hδ h6 h7 h8 (pushR (𝕂 := ℂ) e))

end TanTwoThetaAmbientGeneric


/-! ## The two `tan Θ` clauses over `ℝ`, and at every `RCLike` field -/

section TanThetaReal

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The Challenge's directed sine block is the development's, over `ℝ`. -/
theorem directedSineBlock_eq_real (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedSineBlock U V =
      TauCeti.DavisKahan1970.theorem63DirectedSineBlockReal U V := rfl

/-- **The directed clause of the Challenge's `tan Θ` theorem, over `ℝ`.** -/
theorem tanTheta_directed_proof_real (N : UINorm)
    {A : E →ₗ.[ℝ] E} {V : Submodule ℝ E} [V.HasOrthogonalProjection]
    (hV : Reduces A V) {α δ : ℝ} (hδ : 0 < δ)
    (hunwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℝ)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection] (D : RitzData A U)
    (hupper : SemiboundedAbove D.compression α) (hR : N.Finite D.residual) :
    TangentDefined (directedSineBlock U V) ∧
      N.SeqFinite (tanSeq (directedSineBlock U V)) ∧
      δ * N.seqNorm (tanSeq (directedSineBlock U V)) ≤ N.norm D.residual := by
  have hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ := by
    intro y hyV hy; simpa using hunwanted y hyV hy
  obtain ⟨hlt, tanTheta0, htan, hmem, hbound⟩ :=
    TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_paperUINorm_exists_real
      N.toPaper D.toUnboundedRitzPair
      (TauCeti.DavisKahan.ReducingComplement.ofReducesSubspace ((reduces_iff A V).1 hV))
      hδ ((semiboundedAbove_iff _ _).1 hupper) hUnwanted hR
  have hseq : ∀ n, tanTheta0.approximationNumber n = tanSeq (directedSineBlock U V) n :=
    fun n => htan n
  have heval : N.evalSeq (tanSeq (directedSineBlock U V)) =
      N.toPaper.extendedGauge tanTheta0 :=
    N.evalSeq_eq_of_approximationNumber _ _ hseq
  refine ⟨tangentDefined_of_approximationNumber_lt_one _ (fun n => hlt n), ?_, ?_⟩
  · show N.evalSeq (tanSeq (directedSineBlock U V)) ≠ ⊤
    rw [heval]; exact hmem
  · show δ * (N.evalSeq (tanSeq (directedSineBlock U V))).toReal ≤ N.norm D.residual
    rw [heval]; exact hbound


/-- **The ambient clause of the Challenge's `tan Θ` theorem, over `ℝ`.** -/
theorem tanTheta_ambient_proof_real (N : UINorm)
    {A : E →ₗ.[ℝ] E} {V : Submodule ℝ E} [V.HasOrthogonalProjection]
    (hV : Reduces A V) {α δ : ℝ} (hδ : 0 < δ)
    (hunwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℝ)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection] (D : RitzData A U)
    (hupper : SemiboundedAbove D.compression α)
    (H : E →L[ℝ] E) (hH : IsSelfAdjoint H)
    (hres : D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (h35 : CrossedDefectsEquivalent U V) (hHmem : N.Finite H) :
    TangentDefined (ambientSine U V) ∧
      N.SeqFinite (tanSeq (ambientSine U V)) ∧
      δ * N.seqNorm (tanSeq (ambientSine U V)) ≤ N.norm H := by
  have hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ := by
    intro y hyV hy; simpa using hunwanted y hyV hy
  have hVc : TauCeti.DavisKahan.ReducingComplement A V :=
    TauCeti.DavisKahan.ReducingComplement.ofReducesSubspace ((reduces_iff A V).1 hV)
  have hupper' : TauCeti.LinearPMap.SemiboundedAbove
      D.toUnboundedRitzPair.trial.compression α := (semiboundedAbove_iff _ _).1 hupper
  have htr : ‖TauCeti.DavisKahanExt.paperSinAngleOperatorR U V‖ < 1 :=
    TauCeti.DavisKahan1970.norm_paperSinAngleOperatorR_lt_one_of_unboundedCompression_crossedDefectsEquivalent
      D.toUnboundedRitzPair.trial hδ hupper'
      (D.toUnboundedRitzPair.trial.crossed_lower_of_reducing V A
        D.toUnboundedRitzPair.mem_domain D.toUnboundedRitzPair.action_eq
        hVc.mapsDomain hVc.commutes hUnwanted) h35
  obtain ⟨hmem, hbound⟩ :=
    TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_paperUINorm_real
      N.toPaper D.toUnboundedRitzPair hVc H hH hδ hupper' hUnwanted h35 hres hHmem
  have hseq : ∀ n,
      (TauCeti.DavisKahanExt.paperTanAngleOperatorR U V).approximationNumber n =
        tanSeq (ambientSine U V) n := fun n =>
    TauCeti.DavisKahan1970.approximationNumber_paperTanAngleOperatorR U V htr n
  have heval : N.evalSeq (tanSeq (ambientSine U V)) =
      N.toPaper.extendedGauge (TauCeti.DavisKahanExt.paperTanAngleOperatorR U V) :=
    N.evalSeq_eq_of_approximationNumber _ _ hseq
  refine ⟨tangentDefined_of_approximationNumber_lt_one _ (fun n =>
    TauCeti.DavisKahan1970.approximationNumber_projectorDifference_lt_one_real U V htr n),
    ?_, ?_⟩
  · show N.evalSeq (tanSeq (ambientSine U V)) ≠ ⊤
    rw [heval]; exact hmem
  · show δ * (N.evalSeq (tanSeq (ambientSine U V))).toReal ≤ N.norm H
    rw [heval]; exact hbound

end TanThetaReal

open TauCeti.ScalarTransport in
/-- **The directed clause of the Challenge's `tan Θ` theorem, at an arbitrary
`RCLike` field.** -/
theorem tanTheta_directed_proof (N : UINorm)
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {A : E →ₗ.[𝕜] E} {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces A V) {α δ : ℝ} (hδ : 0 < δ)
    (hunwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_𝕜)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (D : RitzData A U)
    (hupper : SemiboundedAbove D.compression α) (hR : N.Finite D.residual) :
    TangentDefined (directedSineBlock U V) ∧
      N.SeqFinite (tanSeq (directedSineBlock U V)) ∧
      δ * N.seqNorm (tanSeq (directedSineBlock U V)) ≤ N.norm D.residual := by
  have key : ∀ {𝕂 : Type} [RCLike 𝕂] (e : TauCeti.RCLikeIso 𝕜 𝕂),
      (TangentDefined (directedSineBlock (submodule (e := e) U) (submodule (e := e) V)) ∧
        N.SeqFinite (tanSeq (directedSineBlock (submodule (e := e) U)
          (submodule (e := e) V))) ∧
        δ * N.seqNorm (tanSeq (directedSineBlock (submodule (e := e) U)
          (submodule (e := e) V))) ≤ N.norm (clm (e := e) D.residual)) →
      TangentDefined (directedSineBlock U V) ∧
        N.SeqFinite (tanSeq (directedSineBlock U V)) ∧
        δ * N.seqNorm (tanSeq (directedSineBlock U V)) ≤ N.norm D.residual := by
    intro 𝕂 _ e h
    obtain ⟨h1, h2, h3⟩ := h
    have hsv : ∀ n,
        singularValue (directedSineBlock (submodule (e := e) U)
          (submodule (e := e) V)) n = singularValue (directedSineBlock U V) n := by
      intro n
      rw [directedSineBlock_pmap (e := e) U V]
      exact approximationNumber_clm (e := e) (directedSineBlock U V) n
    have hres : ∀ n,
        singularValue (clm (e := e) D.residual) n = singularValue D.residual n :=
      fun n => approximationNumber_clm (e := e) D.residual n
    have htan := tanSeq_congr hsv
    refine ⟨tangentDefined_congr hsv h1, ?_, ?_⟩
    · show N.evalSeq (tanSeq (directedSineBlock U V)) ≠ ⊤
      rw [← htan]; exact h2
    · show δ * (N.evalSeq (tanSeq (directedSineBlock U V))).toReal ≤ N.norm D.residual
      have hn : N.norm (clm (e := e) D.residual) = N.norm D.residual := by
        unfold UINorm.norm
        rw [N.eval_congr hres]
      rw [← htan, ← hn]
      exact h3
  have unw : ∀ {𝕂 : Type} [RCLike 𝕂] (e : TauCeti.RCLikeIso 𝕜 𝕂),
      ∀ y ∈ (submodule (e := e) V)ᗮ, ∀ hy : y ∈ (pmap (e := e) A).domain,
        (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪pmap (e := e) A ⟨y, hy⟩, y⟫_𝕂 := by
    intro 𝕂 _ e y hyV hy
    have hyV' : out (e := e) y ∈ Vᗮ := by
      rw [← mem_submodule (e := e), ← submodule_orthogonal (e := e) V]
      exact hyV
    have hmem : out (e := e) y ∈ A.domain := hy
    have h := hunwanted (out (e := e) y) hyV' hmem
    show (α + δ) * ‖out (e := e) y‖ ^ 2 ≤
      RCLike.re (inner 𝕂 (of (e := e) (A ⟨out (e := e) y, hmem⟩))
        (of (e := e) (out (e := e) y)))
    rw [re_inner_of]
    exact h
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
  · set e := TauCeti.RCLikeIso.real (𝕜 := 𝕜) hI with he
    exact key (𝕂 := ℝ) e
      (tanTheta_directed_proof_real N ((reduces_pmap_iff (e := e)).mpr hV) hδ
        (unw (𝕂 := ℝ) e) (RitzData.pmap (e := e) D)
        (semiboundedAbove_pmap' (e := e) hupper)
        ((UINorm.finite_clm_iff (e := e) N D.residual).mpr hR))
  · set e := TauCeti.RCLikeIso.complex (𝕜 := 𝕜) hI with he
    exact key (𝕂 := ℂ) e
      (tanTheta_directed_proof_complex N ((reduces_pmap_iff (e := e)).mpr hV) hδ
        (unw (𝕂 := ℂ) e) (RitzData.pmap (e := e) D)
        (semiboundedAbove_pmap' (e := e) hupper)
        ((UINorm.finite_clm_iff (e := e) N D.residual).mpr hR))


open TauCeti.ScalarTransport in
/-- **The ambient clause of the Challenge's `tan Θ` theorem, at an arbitrary
`RCLike` field.** -/
theorem tanTheta_ambient_proof (N : UINorm)
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {A : E →ₗ.[𝕜] E} {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces A V) {α δ : ℝ} (hδ : 0 < δ)
    (hunwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_𝕜)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (D : RitzData A U)
    (hupper : SemiboundedAbove D.compression α)
    (H : E →L[𝕜] E) (hH : IsSelfAdjoint H)
    (hres : D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (h35 : CrossedDefectsEquivalent U V) (hHmem : N.Finite H) :
    TangentDefined (ambientSine U V) ∧
      N.SeqFinite (tanSeq (ambientSine U V)) ∧
      δ * N.seqNorm (tanSeq (ambientSine U V)) ≤ N.norm H := by
  have key : ∀ {𝕂 : Type} [RCLike 𝕂] (e : TauCeti.RCLikeIso 𝕜 𝕂),
      (TangentDefined (ambientSine (submodule (e := e) U) (submodule (e := e) V)) ∧
        N.SeqFinite (tanSeq (ambientSine (submodule (e := e) U) (submodule (e := e) V))) ∧
        δ * N.seqNorm (tanSeq (ambientSine (submodule (e := e) U)
          (submodule (e := e) V))) ≤ N.norm (clm (e := e) H)) →
      TangentDefined (ambientSine U V) ∧
        N.SeqFinite (tanSeq (ambientSine U V)) ∧
        δ * N.seqNorm (tanSeq (ambientSine U V)) ≤ N.norm H := by
    intro 𝕂 _ e h
    rw [ambientSine_pmap (e := e) U V, tanSeq_clm, tangentDefined_clm_iff,
      UINorm.norm_clm] at h
    exact h
  have unw : ∀ {𝕂 : Type} [RCLike 𝕂] (e : TauCeti.RCLikeIso 𝕜 𝕂),
      ∀ y ∈ (submodule (e := e) V)ᗮ, ∀ hy : y ∈ (pmap (e := e) A).domain,
        (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪pmap (e := e) A ⟨y, hy⟩, y⟫_𝕂 := by
    intro 𝕂 _ e y hyV hy
    have hyV' : out (e := e) y ∈ Vᗮ := by
      rw [← mem_submodule (e := e), ← submodule_orthogonal (e := e) V]
      exact hyV
    have hmem : out (e := e) y ∈ A.domain := hy
    have h := hunwanted (out (e := e) y) hyV' hmem
    show (α + δ) * ‖out (e := e) y‖ ^ 2 ≤
      RCLike.re (inner 𝕂 (of (e := e) (A ⟨out (e := e) y, hmem⟩))
        (of (e := e) (out (e := e) y)))
    rw [re_inner_of]
    exact h
  have hres' : ∀ {𝕂 : Type} [RCLike 𝕂] (e : TauCeti.RCLikeIso 𝕜 𝕂),
      (RitzData.pmap (e := e) D).residual =
        (submodule (e := e) U)ᗮ.starProjection ∘L clm (e := e) H ∘L
          (submodule (e := e) U).subtypeL := by
    intro 𝕂 _ e
    refine ContinuousLinearMap.ext fun z => ?_
    show of (e := e) (D.residual (out (e := e) z)) =
      (submodule (e := e) U)ᗮ.starProjection
        (of (e := e) (H (((out (e := e) z : ↥U) : E))))
    rw [starProjection_orthogonal_of, hres]
    rfl
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
  · set e := TauCeti.RCLikeIso.real (𝕜 := 𝕜) hI with he
    exact key (𝕂 := ℝ) e
      (tanTheta_ambient_proof_real N ((reduces_pmap_iff (e := e)).mpr hV) hδ
        (unw (𝕂 := ℝ) e) (RitzData.pmap (e := e) D)
        (semiboundedAbove_pmap' (e := e) hupper) _
        ((isSelfAdjoint_clm_iff (e := e)).mpr hH) (hres' (𝕂 := ℝ) e)
        (crossedDefectsEquivalent_pmap (e := e) h35)
        ((UINorm.finite_clm_iff (e := e) N H).mpr hHmem))
  · set e := TauCeti.RCLikeIso.complex (𝕜 := 𝕜) hI with he
    exact key (𝕂 := ℂ) e
      (tanTheta_ambient_proof_complex N ((reduces_pmap_iff (e := e)).mpr hV) hδ
        (unw (𝕂 := ℂ) e) (RitzData.pmap (e := e) D)
        (semiboundedAbove_pmap' (e := e) hupper) _
        ((isSelfAdjoint_clm_iff (e := e)).mpr hH) (hres' (𝕂 := ℂ) e)
        (crossedDefectsEquivalent_pmap (e := e) h35)
        ((UINorm.finite_clm_iff (e := e) N H).mpr hHmem))


section SinTwoThetaDirectedReal

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The directed clause of the Challenge's `sin 2Θ` theorem, discharged from
the development over `ℝ`.**

`δ ‖sin 2Θ₀‖ ≤ 2 ‖R‖` on the residual alone, at an arbitrary reducing `U` and
the full form-bounded gap, so the separating interval may be half-infinite. -/
theorem sinTwoTheta_directed_proof_real
    (N : UINorm) {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SylvesterGap (block A U hU) (block A Uᗮ hU.orthogonal) δ)
    {V : Submodule ℝ E} [V.HasOrthogonalProjection] (D : BoundedTrialBlock A V)
    (hRmem : N.Finite D.residual) :
    N.Finite (directedDoubleSine U V) ∧
      δ * N.norm (directedDoubleSine U V) ≤ 2 * N.norm D.residual := by
  have hUred : TauCeti.LinearPMap.ReducesSubspace A U := (reduces_iff A U).1 hU
  have hgap' : TauCeti.DavisKahan.ExactSinTheta.FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hUred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hUred.orthogonal) δ := by
    rw [block_eq A U hU, block_eq A Uᗮ hU.orthogonal] at hgap
    exact (sylvesterGap_iff _ _ _).1 hgap
  have hres : ∀ v : V, A ⟨(v : E), D.mem_domain v⟩ =
      D.residual v + ((D.compression v : V) : E) := fun v =>
    (D.action_eq v).trans (add_comm _ _)
  exact TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_paperUINorm_real
    N.toPaper hA hUred D.mem_domain hres hδ hgap' hRmem


end SinTwoThetaDirectedReal

open TauCeti.ScalarTransport in
/-- **The directed clause of the Challenge's `sin 2Θ` theorem, at an arbitrary
`RCLike` field.** -/
theorem sinTwoTheta_directed_proof
    (N : UINorm) {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SylvesterGap (block A U hU) (block A Uᗮ hU.orthogonal) δ)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (D : BoundedTrialBlock A V)
    (hRmem : N.Finite D.residual) :
    N.Finite (directedDoubleSine U V) ∧
      δ * N.norm (directedDoubleSine U V) ≤ 2 * N.norm D.residual := by
  have key : ∀ {𝕂 : Type} [RCLike 𝕂] (e : TauCeti.RCLikeIso 𝕜 𝕂),
      (N.Finite (directedDoubleSine (submodule (e := e) U) (submodule (e := e) V)) ∧
        δ * N.norm (directedDoubleSine (submodule (e := e) U)
          (submodule (e := e) V)) ≤ 2 * N.norm (clm (e := e) D.residual)) →
      N.Finite (directedDoubleSine U V) ∧
        δ * N.norm (directedDoubleSine U V) ≤ 2 * N.norm D.residual := by
    intro 𝕂 _ e h
    obtain ⟨h1, h2⟩ := h
    have hsv : ∀ n,
        singularValue (directedDoubleSine (submodule (e := e) U)
          (submodule (e := e) V)) n = singularValue (directedDoubleSine U V) n := by
      intro n
      rw [directedDoubleSine_pmap (e := e) U V]
      exact approximationNumber_clm (e := e) (directedDoubleSine U V) n
    have hres : ∀ n,
        singularValue (clm (e := e) D.residual) n = singularValue D.residual n :=
      fun n => approximationNumber_clm (e := e) D.residual n
    have hev := N.eval_congr hsv
    have hevR := N.eval_congr hres
    refine ⟨?_, ?_⟩
    · show N.eval (directedDoubleSine U V) ≠ ⊤
      rw [← hev]; exact h1
    · show δ * (N.eval (directedDoubleSine U V)).toReal ≤
        2 * (N.eval D.residual).toReal
      rw [← hev, ← hevR]; exact h2
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
  · set e := TauCeti.RCLikeIso.real (𝕜 := 𝕜) hI with he
    refine key (𝕂 := ℝ) e (sinTwoTheta_directed_proof_real N
      ((isSelfAdjoint_pmap_iff (e := e)).mpr hA) ((reduces_pmap_iff (e := e)).mpr hU) hδ
      (sylvesterGap_congr_right (submodule_orthogonal (e := e) U).symm
        (sylvesterGap_block_pmap (e := e) (hU := hU)
          (hU' := (reduces_pmap_iff (e := e)).mpr hU)
          (hUc' := (reduces_pmap_iff (e := e)).mpr hU.orthogonal) hgap))
      (BoundedTrialBlock.pmap (e := e) D)
      ((UINorm.finite_clm_iff (e := e) N D.residual).mpr hRmem))
  · set e := TauCeti.RCLikeIso.complex (𝕜 := 𝕜) hI with he
    refine key (𝕂 := ℂ) e (sinTwoTheta_directed_proof_complex N
      ((isSelfAdjoint_pmap_iff (e := e)).mpr hA) ((reduces_pmap_iff (e := e)).mpr hU) hδ
      (sylvesterGap_congr_right (submodule_orthogonal (e := e) U).symm
        (sylvesterGap_block_pmap (e := e) (hU := hU)
          (hU' := (reduces_pmap_iff (e := e)).mpr hU)
          (hUc' := (reduces_pmap_iff (e := e)).mpr hU.orthogonal) hgap))
      (BoundedTrialBlock.pmap (e := e) D)
      ((UINorm.finite_clm_iff (e := e) N D.residual).mpr hRmem))

/-! ## 13. The four theorems

The seven printed clauses, assembled into the Challenge's four statements. -/

section FourTheorems

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- **Davis--Kahan 1970, Section 2, the `sin Θ` theorem.** -/
theorem sinTheta_solution (N : UINorm)
    {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {Λ₁ : G →ₗ.[𝕜] G}
    {E₀ : F →L[𝕜] E} {F₀ : K →L[𝕜] E} {F₁ : G →L[𝕜] E} {R : F →L[𝕜] E}
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (hres : IsTrialResidual A A₀ E₀ R) (hdec : IsExactDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SylvesterGap A₀ Λ₁ δ) (hR : N.Finite R) :
    N.Finite (directedSine E₀ F₀) ∧
      δ * N.norm (directedSine E₀ F₀) ≤ N.norm R :=
  sinTheta_proof N hA hA₀ hΛ₁ hres hdec hδ hgap hR

-- `hA` is the source's own hypothesis that the ambient operator is self-adjoint.
-- Neither clause proof consumes it -- the directed clause gets what it needs from
-- the Ritz data and the reducing complement -- but it is a printed hypothesis and
-- the statement keeps it.
set_option linter.unusedVariables false in
/-- **Davis--Kahan 1970, Section 2, the `tan Θ` theorem**, both printed
conclusions. -/
theorem tanTheta_solution (N : UINorm)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    {α δ : ℝ} (hδ : 0 < δ)
    (hunwanted : SemiboundedBelow (block A Vᗮ hV.orthogonal) (α + δ)) :
    TanThetaResult N A V α δ where
  directed := fun {_U} _ D hupper hR =>
    tanTheta_directed_proof N hV hδ
      (fun y hyV hy => hunwanted ⟨⟨y, hyV⟩, hy⟩) D hupper hR
  ambient := fun {_U} _ D hupper H hH hres h35 hHmem =>
    tanTheta_ambient_proof N hV hδ
      (fun y hyV hy => hunwanted ⟨⟨y, hyV⟩, hy⟩) D hupper H hH hres h35 hHmem

/-- **Davis--Kahan 1970, Section 2, the `sin 2Θ` theorem**, both printed
conclusions. -/
theorem sinTwoTheta_solution (N : UINorm)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SylvesterGap (block A U hU) (block A Uᗮ hU.orthogonal) δ) :
    SinTwoThetaResult N A U δ where
  directed := fun {_V} _ D hR => sinTwoTheta_directed_proof N hA hU hδ hgap D hR
  ambient := fun H hH {_V} _ hV hHmem =>
    sinTwoTheta_ambient_proof N hA hU hδ hgap H hH hV hHmem

/-- **Davis--Kahan 1970, Section 2, the `tan 2Θ` theorem**, both printed
conclusions. -/
theorem tanTwoTheta_solution (N : UINorm)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[𝕜] E) (hH : IsSelfAdjoint H)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : SemiboundedAbove (block A U hU) α)
    (hhigh : SemiboundedBelow (block A Uᗮ hU.orthogonal) (α + δ)) :
    TanTwoThetaResult N A U H δ where
  directed := fun {_V} _ hV hRmem =>
    tanTwoTheta_directed_proof N hA hU H hoffdiag₀ hoffdiag₁ hδ
      (formBound_upper_of_semiboundedAbove hU hlow)
      (formBound_lower_of_semiboundedBelow hU hhigh) hV hRmem
  ambient := fun {_V} _ hV hHmem =>
    tanTwoTheta_ambient_proof N hA hU H hH hoffdiag₀ hoffdiag₁ hδ
      (formBound_upper_of_semiboundedAbove hU hlow)
      (formBound_lower_of_semiboundedBelow hU hhigh) hV hHmem

end FourTheorems

/-! ## 14. The two capability classes, at every `RCLike` field -/

section Capabilities

/-- The min--max lower bound, at an arbitrary `RCLike` field. -/
example (𝕜 : Type u) [RCLike 𝕜] :
    ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜 := inferInstance

/-- The unbounded Sylvester Ky Fan estimate, likewise. -/
example (𝕜 : Type u) [RCLike 𝕜] : HasUnboundedSylvesterKyFan.{u, v} 𝕜 := inferInstance

end Capabilities

/-! ## 15. Status

All seven printed Section 2 inequality clauses are proved here, at an arbitrary
`[RCLike 𝕜]`, and assembled into the Challenge's four theorems.  None carries a
capability binder, a field-dispatch hypothesis, a finite-dimensionality
hypothesis, or a spectral selection of the trial subspace; each depends on
`propext`, `Classical.choice`, `Quot.sound` and nothing else.

| printed clause | proof |
| --- | --- |
| `sin Θ` | `sinTheta_proof` |
| `tan Θ` directed | `tanTheta_directed_proof` |
| `tan Θ` ambient | `tanTheta_ambient_proof` |
| `sin 2Θ` directed | `sinTwoTheta_directed_proof` |
| `sin 2Θ` ambient | `sinTwoTheta_ambient_proof` |
| `tan 2Θ` directed | `tanTwoTheta_directed_proof` |
| `tan 2Θ` ambient | `tanTwoTheta_ambient_proof` |

Two things this file establishes beyond the inequalities.

**The Challenge's vocabulary is not an approximation of the development's; it is
the development's.**  The norm -- the object most at risk of being quietly
weakened in a compact restatement -- corresponds by `rfl`; the separation
corresponds constructor by constructor including both half-infinite branches; the
trial data corresponds field for field with the compression still a partial map;
and the off-diagonal condition corresponds to the development's `IsOddFor`.

**The scalar field is closed by transport, not by genericity of the machinery.**
`gramOperator`, `cfc` and the double-angle functional calculus are complex.  What
is generic is the *observable*: every quantity a clause mentions is a function of
one operator's singular-value sequence, and `TauCeti.ScalarTransport` renames the
field without touching the vectors, the additive group, the topology, the norm,
the operators, or that sequence.  `RCLike.I_eq_zero_or_im_I_eq_one` supplies the
case split, and the real branch of each tangent clause is itself proved by
complexification, so the analysis happens once. -/

end


/-! ## The four theorems

The Challenge's four statements, at the Challenge's own types, proved. -/

section Advertised

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- **The `sin Θ` theorem.**  If the trial block `A₀` and the complementary exact
block `Λ₁` are separated by a gap `δ`, then `δ ‖sin Θ₀‖ ≤ ‖R‖` in every unitarily
invariant norm.  The ambient operator may be unbounded, the trial block may be
unbounded, the space may have any dimension, and the separating interval may be
half-infinite.  This is the one Section 2 theorem with a single conclusion. -/

theorem sinTheta (N : UINorm)
    {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {Λ₁ : G →ₗ.[𝕜] G}
    {E₀ : F →L[𝕜] E} {F₀ : K →L[𝕜] E} {F₁ : G →L[𝕜] E} {R : F →L[𝕜] E}
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (hres : IsTrialResidual A A₀ E₀ R) (hdec : IsExactDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SylvesterGap A₀ Λ₁ δ) (hR : N.Finite R) :
    N.Finite (directedSine E₀ F₀) ∧
      δ * N.norm (directedSine E₀ F₀) ≤ N.norm R :=
  sinTheta_proof N hA hA₀ hΛ₁ hres hdec hδ hgap hR

-- `hA` is the source's own hypothesis that the ambient operator is self-adjoint.
-- Neither clause proof consumes it -- the directed clause gets what it needs from
-- the Ritz data and the reducing complement -- but it is a printed hypothesis and
-- the statement keeps it.
set_option linter.unusedVariables false in
/-- **The `tan Θ` theorem**, both printed conclusions.

The separation is *ordered* -- the trial block at or below `α`, the unwanted
exact block at or above `α + δ` -- and the perturbation has vanishing trial
diagonal block, the Rayleigh--Ritz condition `H₀ = 0` carried by `RitzData` and
by `D.residual = P_{Uᗮ} H|_U`.  Then `δ ‖tan Θ₀‖ ≤ ‖R‖` and `δ ‖tan Θ‖ ≤ ‖H‖`,
with the sharp factor one.  `V` is any subspace reducing `A`. -/

theorem tanTheta (N : UINorm)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    {α δ : ℝ} (hδ : 0 < δ)
    (hunwanted : SemiboundedBelow (block A Vᗮ hV.orthogonal) (α + δ)) :
    TanThetaResult N A V α δ where
  directed := fun {_U} _ D hupper hR =>
    tanTheta_directed_proof N hV hδ
      (fun y hyV hy => hunwanted ⟨⟨y, hyV⟩, hy⟩) D hupper hR
  ambient := fun {_U} _ D hupper H hH hres h35 hHmem =>
    tanTheta_ambient_proof N hV hδ
      (fun y hyV hy => hunwanted ⟨⟨y, hyV⟩, hy⟩) D hupper H hH hres h35 hHmem

/-- **The `sin 2Θ` theorem**, both printed conclusions.  The separating interval
may be half-infinite, the ambient operator may be unbounded, and `U` is any
subspace reducing `A` whose two blocks the separation puts a gap `δ` between. -/

theorem sinTwoTheta (N : UINorm)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SylvesterGap (block A U hU) (block A Uᗮ hU.orthogonal) δ) :
    SinTwoThetaResult N A U δ where
  directed := fun {_V} _ D hR => sinTwoTheta_directed_proof N hA hU hδ hgap D hR
  ambient := fun H hH {_V} _ hV hHmem =>
    sinTwoTheta_ambient_proof N hA hU hδ hgap H hH hV hHmem

/-- **The `tan 2Θ` theorem**, both printed conclusions.  The separation is
ordered on the two blocks of `A` and the perturbation is *off-diagonal* for the
splitting -- `H₀ = H₁ = 0`.  Then `δ ‖tan 2Θ₀‖ ≤ 2 ‖R‖` and
`δ ‖tan 2Θ‖ ≤ 2 ‖H‖`. -/

theorem tanTwoTheta (N : UINorm)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[𝕜] E) (hH : IsSelfAdjoint H)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : SemiboundedAbove (block A U hU) α)
    (hhigh : SemiboundedBelow (block A Uᗮ hU.orthogonal) (α + δ)) :
    TanTwoThetaResult N A U H δ where
  directed := fun {_V} _ hV hRmem =>
    tanTwoTheta_directed_proof N hA hU H hoffdiag₀ hoffdiag₁ hδ
      (formBound_upper_of_semiboundedAbove hU hlow)
      (formBound_lower_of_semiboundedBelow hU hhigh) hV hRmem
  ambient := fun {_V} _ hV hHmem =>
    tanTwoTheta_ambient_proof N hA hU H hH hoffdiag₀ hoffdiag₁ hδ
      (formBound_upper_of_semiboundedAbove hU hlow)
      (formBound_lower_of_semiboundedBelow hU hhigh) hV hHmem

end Advertised

end RotationOfEigenvectors
