/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import Mathlib

/-!
# Davis--Kahan 1970: the four Section 2 theorems

The namespace is `RotationOfEigenvectors`, after the paper's title.  Everything
below is ordinary Mathlib vocabulary; the only non-Mathlib names are the source
objects defined here.

Two conventions, stated once.  There is no functional calculus anywhere: a
unitarily invariant norm sees only the singular-value sequence, so every angle
quantity is either an explicit block of orthogonal projections or a sequence of
trigonometric functions of singular values.  And `‖tan Θ‖` is evaluated on the
tangent *sequence*, with each tangent theorem *concluding* that the tangent has
no pole rather than assuming it away.
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
      δ * N.norm (directedSine E₀ F₀) ≤ N.norm R := by
  sorry

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
    TanThetaResult N A V α δ := by
  sorry

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

/-- **The `sin 2Θ` theorem**, both printed conclusions.  The separating interval
may be half-infinite, the ambient operator may be unbounded, and `U` is any
subspace reducing `A` whose two blocks the separation puts a gap `δ` between. -/
theorem sinTwoTheta (N : UINorm)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SylvesterGap (block A U hU) (block A Uᗮ hU.orthogonal) δ) :
    SinTwoThetaResult N A U δ := by
  sorry

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
    TanTwoThetaResult N A U H δ := by
  sorry

end Theorems

end RotationOfEigenvectors
