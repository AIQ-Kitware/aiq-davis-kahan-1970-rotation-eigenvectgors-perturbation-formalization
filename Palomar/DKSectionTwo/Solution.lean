/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
import DavisKahan.Sources.DavisKahan1970.SectionTwo

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
structure SymmetricNormingFunction where
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
noncomputable def SymmetricNormingFunction.evalSeq (N : SymmetricNormingFunction) (s : ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal
    ((N.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ)
      (fun i => s (i : ℕ)))

/-- The sequence lies in the norm's ideal. -/
def SymmetricNormingFunction.SeqFinite (N : SymmetricNormingFunction) (s : ℕ → ℝ) : Prop := N.evalSeq s ≠ ⊤

/-- The real-valued norm of a sequence, meaningful on the ideal. -/
noncomputable def SymmetricNormingFunction.seqNorm (N : SymmetricNormingFunction) (s : ℕ → ℝ) : ℝ :=
  (N.evalSeq s).toReal

section NormEval

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The norm's extended value on an operator: its value on the singular-value
sequence, and `⊤` exactly off the norm's ideal. -/
noncomputable def SymmetricNormingFunction.eval (N : SymmetricNormingFunction) (T : E →L[𝕜] F) : ℝ≥0∞ :=
  N.evalSeq (fun n => singularValue T n)

/-- The operator lies in the norm's ideal. -/
def SymmetricNormingFunction.Finite (N : SymmetricNormingFunction) (T : E →L[𝕜] F) : Prop := N.eval T ≠ ⊤

/-- The real-valued norm, meaningful on the ideal. -/
noncomputable def SymmetricNormingFunction.norm (N : SymmetricNormingFunction) (T : E →L[𝕜] F) : ℝ := (N.eval T).toReal

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


end Angles


/-! ## 7. Bridge to the compiled Davis--Kahan development

The Challenge intentionally uses Mathlib-only vocabulary.  The Solution keeps
that public vocabulary unchanged and translates it once into the production
Section 2 API.  In particular, the tangent proofs use the scalar-generic
`RCLike` endpoints directly; there is no local real/complex proof split.
-/

open TauCeti
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.Sylvester
open TauCeti.ApproximationNumber
open scoped InnerProductSpace TauCeti.CompleteSubspace

section NormBridge

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Challenge's singular values are the development's approximation numbers. -/
theorem singularValue_eq_approximationNumber (T : E →L[𝕜] F) (n : ℕ) :
    singularValue T n = T.approximationNumber n := rfl

/-- Convert the Mathlib-only finite-dimensional UI seminorm to the production
rectangular UI-seminorm structure. -/
noncomputable def UISeminorm.toTauCeti {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] (N : UISeminorm G) :
    TauCeti.UnitarilyInvariantSeminorm ℂ G G where
  toSeminorm := Seminorm.of N.toFun N.add_le N.smul
  unitary_invariant' :=
    TauCeti.UnitarilyInvariantSeminorm.unitary_invariant_of_isometry N.invariant

omit [CompleteSpace E] [CompleteSpace F] in
/-- The diagonal operators used by the two finite gauges coincide. -/
theorem diagOp_eq {n : ℕ} {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
    (b : OrthonormalBasis (Fin n) ℂ G) (x : Fin n → ℝ) :
    diagOp b x = TauCeti.diagOp b x := rfl

/-- Hence the finite gauges coincide. -/
theorem UISeminorm.gauge_eq {n : ℕ} {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] (N : UISeminorm G)
    (b : OrthonormalBasis (Fin n) ℂ G) (x : Fin n → ℝ) :
    N.gauge b x = N.toTauCeti.gauge b x := rfl

/-- The Challenge symmetric norming function as the production source norm. -/
noncomputable def SymmetricNormingFunction.toSourceNorm (N : SymmetricNormingFunction) :
    TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction where
  finiteNorm n := (N.finiteNorm n).toTauCeti
  normalized := by
    change (N.finiteNorm 1).toTauCeti.gauge
      (EuclideanSpace.basisFun (Fin 1) ℂ) (fun _ => 1) = 1
    rw [← UISeminorm.gauge_eq]
    exact N.normalized
  zero_pad := by
    intro n x
    change (N.finiteNorm (n + 1)).toTauCeti.gauge
        (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
        (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) =
      (N.finiteNorm n).toTauCeti.gauge
        (EuclideanSpace.basisFun (Fin n) ℂ) x
    rw [← UISeminorm.gauge_eq, ← UISeminorm.gauge_eq]
    exact N.zero_pad x

/-- A sequence represented as the approximation-number sequence of an operator
has the same extended norm in the Challenge and production vocabularies. -/
theorem SymmetricNormingFunction.evalSeq_eq_of_approximationNumber
    (N : SymmetricNormingFunction) (s : ℕ → ℝ) (T : E →L[𝕜] F)
    (h : ∀ n, T.approximationNumber n = s n) :
    N.evalSeq s = N.toSourceNorm.extendedGauge T := by
  unfold SymmetricNormingFunction.evalSeq
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge
  refine iSup_congr fun n => ?_
  congr 1
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix
  change
    (N.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) (fun i => s (i : ℕ)) =
      (N.finiteNorm n).toTauCeti.gauge (EuclideanSpace.basisFun (Fin n) ℂ)
        (fun i => approximationSingularValue (i : ℕ) T)
  rw [← UISeminorm.gauge_eq]
  congr 1
  funext i
  change s (i : ℕ) = T.approximationNumber (i : ℕ)
  exact (h (i : ℕ)).symm

/-- Operator evaluation agrees with production evaluation. -/
theorem SymmetricNormingFunction.eval_eq
    (N : SymmetricNormingFunction) (T : E →L[𝕜] F) :
    N.eval T = N.toSourceNorm.extendedGauge T := by
  unfold SymmetricNormingFunction.eval
  exact N.evalSeq_eq_of_approximationNumber _ T
    (fun n => (singularValue_eq_approximationNumber T n).symm)

/-- Ideal membership is the same proposition on both sides of the bridge. -/
theorem SymmetricNormingFunction.finite_iff
    (N : SymmetricNormingFunction) (T : E →L[𝕜] F) :
    N.Finite T ↔ N.toSourceNorm.Mem T := by
  unfold SymmetricNormingFunction.Finite
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem
  rw [N.eval_eq T]

/-- The real-valued operator norms agree. -/
theorem SymmetricNormingFunction.norm_eq
    (N : SymmetricNormingFunction) (T : E →L[𝕜] F) :
    N.norm T = N.toSourceNorm.gauge T := by
  unfold SymmetricNormingFunction.norm
  unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge
  rw [N.eval_eq T]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Pole exclusion from the approximation-number bound. -/
theorem tangentDefined_of_approximationNumber_lt_one (S : E →L[𝕜] F)
    (h : ∀ n, S.approximationNumber n < 1) : TangentDefined S := by
  intro n
  rw [Real.cos_arcsin]
  have h0 : 0 ≤ singularValue S n := S.approximationNumber_nonneg n
  have h1 : singularValue S n < 1 := h n
  exact ne_of_gt (Real.sqrt_pos.mpr (by nlinarith))

end NormBridge

section VocabularyBridge

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

omit [CompleteSpace E] [CompleteSpace F] in
theorem isTrialResidual_iff (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F)
    (E₀ R : F →L[𝕜] E) :
    IsTrialResidual A A₀ E₀ R ↔
      _root_.TauCeti.DavisKahan1970.IsTrialResidual A A₀ E₀ R := by
  constructor
  · exact fun h => ⟨h.isometry, h.mapsDomain, h.residualEquation⟩
  · exact fun h => ⟨h.isometry, h.mapsDomain, h.residualEquation⟩

theorem isExactDecomposition_iff (A : E →ₗ.[𝕜] E) (Λ₁ : G →ₗ.[𝕜] G)
    (F₀ : K →L[𝕜] E) (F₁ : G →L[𝕜] E) :
    IsExactDecomposition A Λ₁ F₀ F₁ ↔
      _root_.TauCeti.DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ := by
  constructor
  · exact fun h => ⟨h.desiredIsometry, h.complementIsometry, h.orthogonal, h.complete,
      h.mapsDomain, h.intertwines⟩
  · exact fun h => ⟨h.desiredIsometry, h.complementIsometry, h.orthogonal, h.complete,
      h.mapsDomain, h.intertwines⟩

omit [CompleteSpace E] in
theorem realResolventSet_eq (A : E →ₗ.[𝕜] E) :
    realResolventSet A = TauCeti.LinearPMap.realResolventSet A := by
  ext lam
  rw [TauCeti.LinearPMap.mem_realResolventSet_iff]
  rfl

omit [CompleteSpace E] in
theorem realSpectrum_eq (A : E →ₗ.[𝕜] E) :
    realSpectrum A = TauCeti.LinearPMap.realSpectrum A := by
  ext lam
  rw [TauCeti.LinearPMap.mem_realSpectrum_iff, realSpectrum, Set.mem_compl_iff,
    realResolventSet_eq]

omit [CompleteSpace E] in
theorem semiboundedBelow_iff (A : E →ₗ.[𝕜] E) (c : ℝ) :
    SemiboundedBelow A c ↔ TauCeti.LinearPMap.SemiboundedBelow A c := by
  rw [TauCeti.LinearPMap.semiboundedBelow_iff]
  exact Iff.rfl

omit [CompleteSpace E] in
theorem semiboundedAbove_iff (A : E →ₗ.[𝕜] E) (c : ℝ) :
    SemiboundedAbove A c ↔ TauCeti.LinearPMap.SemiboundedAbove A c := by
  rw [TauCeti.LinearPMap.semiboundedAbove_iff]
  exact Iff.rfl

omit [CompleteSpace E] [CompleteSpace F] in
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

section ReducingBridge

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem reduces_iff (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    Reduces A U ↔ TauCeti.LinearPMap.ReducesSubspace A U := by
  constructor
  · exact fun h => TauCeti.LinearPMap.ReducesSubspace.of_components
      h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact fun h => ⟨h.projection_mem_domain, h.orthogonalProjection_mem_domain,
      h.invariant, h.orthogonal_invariant⟩

omit [CompleteSpace E] in
theorem block_eq (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (h : Reduces A U) :
    block A U h =
      TauCeti.LinearPMap.reducingRestriction A U ((reduces_iff A U).1 h) := by
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
theorem addBounded_eq (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    addBounded A V = TauCeti.LinearPMap.addBounded A V := by
  refine LinearPMap.ext ?_ ?_
  · rw [TauCeti.LinearPMap.addBounded_domain]
    rfl
  · intro x hf hg
    rw [TauCeti.LinearPMap.addBounded_apply]
    rfl

/-- A Challenge Ritz bundle as the production unbounded Ritz pair. -/
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

omit [CompleteSpace E] in
/-- A reducing subspace of the bounded perturbation supplies the reflection
intertwining data used by the ambient double-angle theorem. -/
theorem reflectionIntertwines_of_reduces {A : E →ₗ.[𝕜] E} {H : E →L[𝕜] E}
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V) :
    TauCeti.DavisKahan.ReflectionIntertwines A H V :=
  TauCeti.DavisKahan.ReflectionIntertwines.ofReducesSubspace
    (by rw [← addBounded_eq]; exact (reduces_iff _ _).1 hV)

omit [CompleteSpace E] in
theorem formBound_upper_of_semiboundedAbove {A : E →ₗ.[𝕜] E}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) {α : ℝ}
    (hupper : SemiboundedAbove (block A U hU) α) :
    ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ α * ‖(x : E)‖ ^ 2 :=
  fun x hxU => hupper ⟨⟨(x : E), hxU⟩, x.2⟩

omit [CompleteSpace E] in
theorem formBound_lower_of_semiboundedBelow {A : E →ₗ.[𝕜] E}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) {c : ℝ}
    (hlower : SemiboundedBelow (block A Uᗮ hU.orthogonal) c) :
    ∀ x : A.domain, (x : E) ∈ Uᗮ →
      c * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜 :=
  fun x hxU => hlower ⟨⟨(x : E), hxU⟩, x.2⟩

omit [CompleteSpace E] in
theorem directedDoubleSine_eq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedDoubleSine U V = TauCeti.DavisKahan.sinTwoThetaIdealBlock U V := rfl

end ReducingBridge


/-! ## 8. The four theorem families of Section 2

The Palomar surface contains five ordinary theorem declarations.  The two
whole-space tangent bounds are consequences in the source proof and are not
repeated here; the two `sin 2Θ` clauses remain separate.
-/

section Theorems

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G K : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- **The `sin Θ` theorem.** -/
theorem sinTheta (N : SymmetricNormingFunction)
    {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {Λ₁ : G →ₗ.[𝕜] G}
    {E₀ : F →L[𝕜] E} {F₀ : K →L[𝕜] E} {F₁ : G →L[𝕜] E} {R : F →L[𝕜] E}
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (hres : IsTrialResidual A A₀ E₀ R) (hdec : IsExactDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SylvesterGap A₀ Λ₁ δ) (hR : N.Finite R) :
    N.Finite (directedSine E₀ F₀) ∧
      δ * N.norm (directedSine E₀ F₀) ≤ N.norm R := by
  have hsrc :=
    _root_.TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_rclike
      N.toSourceNorm A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁
      ((isTrialResidual_iff A A₀ E₀ R).1 hres)
      ((isExactDecomposition_iff A Λ₁ F₀ F₁).1 hdec)
      hδ ((sylvesterGap_iff A₀ Λ₁ δ).1 hgap) ((N.finite_iff R).1 hR)
  refine ⟨(N.finite_iff _).2 hsrc.1, ?_⟩
  rw [N.norm_eq, N.norm_eq]
  exact hsrc.2

/-- **The `tan Θ` theorem, in its stronger residual form.** -/
theorem tanTheta (N : SymmetricNormingFunction)
    {A : E →ₗ.[𝕜] E} (_hA : IsSelfAdjoint A)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    {α δ : ℝ} (hδ : 0 < δ)
    (hunwanted : SemiboundedBelow (block A Vᗮ hV.orthogonal) (α + δ))
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (D : RitzData A U) (hupper : SemiboundedAbove D.compression α)
    (hR : N.Finite D.residual) :
    TangentDefined (directedSineBlock U V) ∧
      N.SeqFinite (tanSeq (directedSineBlock U V)) ∧
      δ * N.seqNorm (tanSeq (directedSineBlock U V)) ≤ N.norm D.residual := by
  let hVc : TauCeti.DavisKahan.ReducingComplement A V :=
    TauCeti.DavisKahan.ReducingComplement.ofReducesSubspace ((reduces_iff A V).1 hV)
  have hupper' : TauCeti.LinearPMap.SemiboundedAbove
      D.toUnboundedRitzPair.trial.compression α :=
    (semiboundedAbove_iff D.compression α).1 hupper
  have hunwanted' : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_𝕜 :=
    fun y hy hyA => formBound_lower_of_semiboundedBelow hV hunwanted ⟨y, hyA⟩ hy
  obtain ⟨hlt, tanTheta0, htan, hmem, hbound⟩ :=
    _root_.TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_exists_rclike
      N.toSourceNorm D.toUnboundedRitzPair hVc hδ hupper' hunwanted'
      ((N.finite_iff D.residual).1 hR)
  have hseq : ∀ n, tanTheta0.approximationNumber n =
      tanSeq (directedSineBlock U V) n := by
    intro n
    change tanTheta0.approximationNumber n =
      Real.tan (Real.arcsin ((TauCeti.DavisKahan.TanTheta.directedSineBlock U V).approximationNumber n))
    exact htan n
  have heval : N.evalSeq (tanSeq (directedSineBlock U V)) =
      N.toSourceNorm.extendedGauge tanTheta0 :=
    N.evalSeq_eq_of_approximationNumber _ tanTheta0 hseq
  refine ⟨tangentDefined_of_approximationNumber_lt_one _ ?_, ?_, ?_⟩
  · intro n
    change (TauCeti.DavisKahan.TanTheta.directedSineBlock U V).approximationNumber n < 1
    exact hlt n
  · show N.evalSeq (tanSeq (directedSineBlock U V)) ≠ ⊤
    rw [heval]
    exact hmem
  · show δ * (N.evalSeq (tanSeq (directedSineBlock U V))).toReal ≤ N.norm D.residual
    rw [heval, N.norm_eq]
    exact hbound

/-- **The residual clause of the `sin 2Θ` theorem.** -/
theorem sinTwoTheta_directed (N : SymmetricNormingFunction)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SylvesterGap (block A U hU) (block A Uᗮ hU.orthogonal) δ)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (D : BoundedTrialBlock A V) (hR : N.Finite D.residual) :
    N.Finite (directedDoubleSine U V) ∧
      δ * N.norm (directedDoubleSine U V) ≤ 2 * N.norm D.residual := by
  have hUred : TauCeti.LinearPMap.ReducesSubspace A U := (reduces_iff A U).1 hU
  have hgap' : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hUred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hUred.orthogonal) δ := by
    rw [block_eq A U hU, block_eq A Uᗮ hU.orthogonal] at hgap
    exact (sylvesterGap_iff _ _ _).1 hgap
  have hres : ∀ v : V, A ⟨(v : E), D.mem_domain v⟩ =
      D.residual v + ((D.compression v : V) : E) :=
    fun v => (D.action_eq v).trans (add_comm _ _)
  have hsrc :=
    _root_.TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_symmetricNorming_rclike
      N.toSourceNorm hA hUred D.mem_domain hres hδ hgap'
      ((N.finite_iff D.residual).1 hR)
  rw [directedDoubleSine_eq]
  refine ⟨(N.finite_iff _).2 hsrc.1, ?_⟩
  rw [N.norm_eq, N.norm_eq]
  exact hsrc.2

/-- **The whole-space clause of the `sin 2Θ` theorem, with the printed
operator roles.** -/
theorem sinTwoTheta_ambient (N : SymmetricNormingFunction)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[𝕜] E) (hH : IsSelfAdjoint H)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SylvesterGap
      (block (addBounded A H) V hV)
      (block (addBounded A H) Vᗮ hV.orthogonal) δ)
    (hHmem : N.Finite H) :
    N.Finite (ambientDoubleSine U V) ∧
      δ * N.norm (ambientDoubleSine U V) ≤ 2 * N.norm H := by
  have hUred : TauCeti.LinearPMap.ReducesSubspace A U := (reduces_iff A U).1 hU
  have hVredLocal : TauCeti.LinearPMap.ReducesSubspace (addBounded A H) V :=
    (reduces_iff (addBounded A H) V).1 hV
  have hVred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A H) V := by
    simpa only [addBounded_eq] using hVredLocal
  have hgapLocal : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction (addBounded A H) V hVredLocal)
      (TauCeti.LinearPMap.reducingRestriction
        (addBounded A H) Vᗮ hVredLocal.orthogonal) δ := by
    rw [← block_eq (addBounded A H) V hV,
      ← block_eq (addBounded A H) Vᗮ hV.orthogonal]
    exact (sylvesterGap_iff _ _ _).1 hgap
  have hgap' : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A H) V hVred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A H) Vᗮ hVred.orthogonal) δ := by
    simpa only [addBounded_eq] using hgapLocal
  have hHsym : H.IsSymmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH
  have hsrc :=
    _root_.TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_rclike
      N.toSourceNorm hA H hHsym hUred hVred hδ hgap'
      ((N.finite_iff H).1 hHmem)
  have hsame :=
    _root_.TauCeti.DavisKahan.Angle.sinTwoAngleOperator_hasSameApproximationNumbers
      (𝕜 := 𝕜) U V
  obtain ⟨hiff, hgauge⟩ :=
    SameApproximationSingularSequence.normingMem_iff_and_gauge_eq N.toSourceNorm hsame
  refine ⟨(N.finite_iff _).2 (hiff.mp hsrc.1), ?_⟩
  rw [N.norm_eq, N.norm_eq]
  change δ * N.toSourceNorm.gauge
      ((U.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection - U.starProjection) ≤
    2 * N.toSourceNorm.gauge H
  rw [← hgauge]
  exact hsrc.2

/-- **The `tan 2Θ` theorem, in its stronger residual form.** -/
theorem tanTwoTheta (N : SymmetricNormingFunction)
    {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (H : E →L[𝕜] E) (_hH : IsSelfAdjoint H)
    (hoffdiag₀ : U.starProjection ∘L H ∘L U.starProjection = 0)
    (hoffdiag₁ : Uᗮ.starProjection ∘L H ∘L Uᗮ.starProjection = 0)
    {α δ : ℝ} (hδ : 0 < δ)
    (hlow : SemiboundedAbove (block A U hU) α)
    (hhigh : SemiboundedBelow (block A Uᗮ hU.orthogonal) (α + δ))
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces (addBounded A H) V)
    (hRmem : N.Finite (Uᗮ.starProjection ∘L H ∘L U.starProjection)) :
    TangentDefined (directedDoubleSine U V) ∧
      N.SeqFinite (tanSeq (directedDoubleSine U V)) ∧
      δ * N.seqNorm (tanSeq (directedDoubleSine U V)) ≤
        2 * N.norm (Uᗮ.starProjection ∘L H ∘L U.starProjection) := by
  have hUred : TauCeti.LinearPMap.ReducesSubspace A U := (reduces_iff A U).1 hU
  have hVred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A H) V := by
    rw [← addBounded_eq]
    exact (reduces_iff _ _).1 hV
  have hUa := formBound_upper_of_semiboundedAbove hU hlow
  have hUb := formBound_lower_of_semiboundedBelow hU hhigh
  have hblk : TauCeti.DavisKahan.ExactSinTheta.projectionBlock Uᗮ U H =
      Uᗮ.starProjection ∘L H ∘L U.starProjection := rfl
  have hext : N.toSourceNorm.extendedGauge
      (TauCeti.DavisKahan.ExactSinTheta.projectionBlock Uᗮ U H) =
      N.toSourceNorm.extendedGauge
        (TauCeti.DavisKahan.ExactSinTheta.blockCompression Uᗮ U H) :=
    N.toSourceNorm.extendedGauge_eq_of_hasSameApproximationNumbers
      (TauCeti.DavisKahan.ExactSinTheta.projectionBlock_same_compression Uᗮ U H)
  have hRproj : N.toSourceNorm.Mem
      (TauCeti.DavisKahan.ExactSinTheta.projectionBlock Uᗮ U H) := by
    rw [hblk]
    exact (N.finite_iff _).1 hRmem
  have hRblock : N.toSourceNorm.Mem
      (TauCeti.DavisKahan.ExactSinTheta.blockCompression Uᗮ U H) := by
    unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem at hRproj ⊢
    rwa [← hext]
  obtain ⟨hlt, T, htan, hmem, hbound⟩ :=
    _root_.TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_rclike
      N.toSourceNorm V hA hUred (isOddFor_of_offDiagonal hoffdiag₀ hoffdiag₁)
      hVred hUa hUb (by linarith) hRblock
  have hseq : ∀ n, T.approximationNumber n = tanSeq (directedDoubleSine U V) n := by
    intro n
    change T.approximationNumber n =
      Real.tan (Real.arcsin
        ((TauCeti.DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n))
    exact htan n
  have heval : N.evalSeq (tanSeq (directedDoubleSine U V)) =
      N.toSourceNorm.extendedGauge T :=
    N.evalSeq_eq_of_approximationNumber _ T hseq
  have hgauge : N.toSourceNorm.gauge
      (TauCeti.DavisKahan.ExactSinTheta.projectionBlock Uᗮ U H) =
      N.toSourceNorm.gauge
        (TauCeti.DavisKahan.ExactSinTheta.blockCompression Uᗮ U H) := by
    unfold TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge
    rw [hext]
  have hδeq : α + δ - α = δ := by ring
  rw [hδeq] at hbound
  refine ⟨tangentDefined_of_approximationNumber_lt_one _ ?_, ?_, ?_⟩
  · intro n
    change (TauCeti.DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n < 1
    exact hlt n
  · show N.evalSeq (tanSeq (directedDoubleSine U V)) ≠ ⊤
    rw [heval]
    exact hmem
  · show δ * (N.evalSeq (tanSeq (directedDoubleSine U V))).toReal ≤
      2 * N.norm (Uᗮ.starProjection ∘L H ∘L U.starProjection)
    rw [heval, N.norm_eq]
    change δ * N.toSourceNorm.gauge T ≤
      2 * N.toSourceNorm.gauge (Uᗮ.starProjection ∘L H ∘L U.starProjection)
    calc
      δ * N.toSourceNorm.gauge T ≤
          2 * N.toSourceNorm.gauge
            (TauCeti.DavisKahan.ExactSinTheta.blockCompression Uᗮ U H) := hbound
      _ = 2 * N.toSourceNorm.gauge
            (TauCeti.DavisKahan.ExactSinTheta.projectionBlock Uᗮ U H) := by
          rw [hgauge]
      _ = 2 * N.toSourceNorm.gauge
            (Uᗮ.starProjection ∘L H ∘L U.starProjection) := by rw [hblk]

end Theorems

end RotationOfEigenvectors
