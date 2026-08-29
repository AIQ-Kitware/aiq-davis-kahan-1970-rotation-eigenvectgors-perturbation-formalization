/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5

Staged for Tau Ceti, roadmap topic T05.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`UnitarilyInvariantSeminorm.lean`).

Formalized by Claude Fable 5 (claude-fable-5[1m]).

Unitarily invariant (semi)norms on the square operators over a
finite-dimensional inner product space, the operator SVD factorization
`A = U ∘ diag(σ(A)) ∘ V`, the symmetric-gauge representation `N A = Φ_N(σ(A))`,
and the **Fan dominance principle**: Ky Fan domination
`∀ k, kyFanSum k A ≤ kyFanSum k B` implies `N A ≤ N B` for every unitarily
invariant norm `N`.  The engine is the Hardy–Littlewood–Pólya transfer descent of
`ForTauCeti.Analysis.Convex.Majorization`, applied to the gauge through
`UnitarilyInvariantSeminorm.finiteSymmetricGauge`: no weak-majorization completion and no
Birkhoff decomposition, each transform step costing one triangle inequality, one
homogeneity, and one swap-permutation invariance of the gauge.
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.KyFan
public import ForTauCeti.Analysis.Convex.Majorization
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection


/-! # Unitarily invariant norms and the Fan dominance principle

For a finite-dimensional inner product space `E` over `𝕜 = ℝ, ℂ`:

* `TauCeti.diagOp b x`: the operator with (real) diagonal `x` in the
  orthonormal basis `b`, with its algebra (`diagOp_add`, `diagOp_real_smul`,
  `diagOp_comp`, symmetry) and its singular values
  (`singularValues_diagOp`: for antitone nonnegative `x` they are `x` itself);
* `TauCeti.exists_unitary_diagOp_factorization` — the **operator SVD**:
  every `A : E →ₗ[𝕜] E` factors as `U ∘ₗ diagOp b σ(A) ∘ₗ V` with `U, V`
  unitary, relative to *any* fixed orthonormal basis `b`;
* `TauCeti.UnitarilyInvariantSeminorm`: subadditive, absolutely homogeneous,
  and invariant under composition with unitaries on both sides (seminorm
  axioms — positivity is never needed for Davis–Kahan);
* `TauCeti.UnitarilyInvariantSeminorm.apply_eq_gauge` — the **symmetric-gauge
  representation** `N A = Φ_N(σ(A))` where `Φ_N x := N (diagOp b x)`;
* `TauCeti.UnitarilyInvariantSeminorm.finiteSymmetricGauge` — the gauge as a
  `TauCeti.FiniteSymmetricGauge`, which is what makes the majorization theory apply;
* `TauCeti.UnitarilyInvariantSeminorm.gauge_le_gauge_of_prefix_sums_le` — the
  **T-transform descent**: for `z` antitone nonnegative and `y` nonnegative,
  prefix-sum domination `∀ m, ∑_{i<m} z ≤ ∑_{i<m} y` forces `Φ z ≤ Φ y`;
* `TauCeti.UnitarilyInvariantSeminorm.apply_le_of_kyFanSum_le` — the
  **Fan dominance principle**;
* `TauCeti.UnitarilyInvariantSeminorm.apply_adjoint` — `N (A⋆) = N A`.

The descent replaces the classical majorization pipeline (weak-majorization completion +
the Hardy–Littlewood–Pólya *characterization* by doubly stochastic matrices + Birkhoff) by
its transfer lemma alone: given a violation `y l < z l` pick the least such `l`; prefix
domination produces `j < l` with `z j < y j`; averaging `y` with its `(j l)`-swap by
`c₂ = δ/(y j − y l)`, `δ = min (y j − z j) (z l − y l)`, moves `y j ↦ y j − δ` and
`y l ↦ y l + δ`, kills a disagreement, preserves nonnegativity and prefix domination, and
does not increase the gauge.  That argument now lives once, for a general symmetric-convex
set, in `ForTauCeti.Analysis.Convex.Majorization`.

## References

* R. Bhatia, *Matrix Analysis*, Chapter IV (symmetric gauge functions, Ky Fan
  dominance, Theorem IV.2.2).
* L. Mirsky, *Symmetric gauge functions and unitarily invariant norms*,
  Quart. J. Math. Oxford 11 (1960), 50–59.
-/

public section

namespace TauCeti

open scoped InnerProductSpace
open LinearMap
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {n : ℕ}

/-! ### The diagonal operator of a real vector in an orthonormal basis -/

/-- The operator with (real) diagonal `x` in the orthonormal basis `b`:
`diagOp b x (b i) = x i • b i`. -/
noncomputable def diagOp (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
    E →ₗ[𝕜] E :=
  ∑ i, ((x i : ℝ) : 𝕜) • (InnerProductSpace.rankOne 𝕜 (b i) (b i)).toLinearMap

omit [FiniteDimensional 𝕜 E] in
/-- The defining formula: `diagOp b x` expands `v` in the basis and scales the `i`-th coefficient
by `x i`. -/
@[simp]
theorem diagOp_apply (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) (v : E) :
    diagOp b x v = ∑ i, ((x i : ℝ) : 𝕜) • ⟪b i, v⟫_𝕜 • b i := by
  unfold diagOp
  rw [LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by
    simp [InnerProductSpace.rankOne_apply]

omit [FiniteDimensional 𝕜 E] in
/-- A diagonal operator scales each basis vector by its own entry.  This is the form used to
compare two diagonal operators, since equality on a basis suffices. -/
theorem diagOp_apply_basis (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ)
    (j : Fin n) : diagOp b x (b j) = ((x j : ℝ) : 𝕜) • b j := by
  rw [diagOp_apply]
  have hterm : ∀ i ∈ Finset.univ, ((x i : ℝ) : 𝕜) • ⟪b i, b j⟫_𝕜 • b i
      = if i = j then ((x i : ℝ) : 𝕜) • b i else 0 := fun i _ => by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [orthonormal_iff_ite.mp b.orthonormal i j, hij]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq' Finset.univ j fun i => ((x i : ℝ) : 𝕜) • b i]
  simp

omit [FiniteDimensional 𝕜 E] in
/-- `diagOp b` is additive in the diagonal. -/
theorem diagOp_add (b : OrthonormalBasis (Fin n) 𝕜 E) (x y : Fin n → ℝ) :
    diagOp b (x + y) = diagOp b x + diagOp b y := by
  unfold diagOp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, RCLike.ofReal_add, add_smul]

omit [FiniteDimensional 𝕜 E] in
/-- `diagOp b` is homogeneous in the diagonal, with the real scalar cast into `𝕜`. -/
theorem diagOp_real_smul (b : OrthonormalBasis (Fin n) 𝕜 E) (c : ℝ)
    (x : Fin n → ℝ) : diagOp b (c • x) = ((c : ℝ) : 𝕜) • diagOp b x := by
  unfold diagOp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, RCLike.ofReal_mul, smul_smul]

omit [FiniteDimensional 𝕜 E] in
/-- A constant real diagonal is a scalar multiple of the identity.  This is
the bridge between the functional-calculus form `r • id` and the diagonal
form the singular-value lemmas are stated in. -/
theorem diagOp_const (b : OrthonormalBasis (Fin n) 𝕜 E) (r : ℝ) :
    diagOp b (fun _ => r) = (((r : ℝ) : 𝕜) • LinearMap.id) := by
  refine b.toBasis.ext fun j => ?_
  rw [OrthonormalBasis.coe_toBasis, diagOp_apply_basis]
  simp

omit [FiniteDimensional 𝕜 E] in
/-- The two-entry constant diagonal, in the `![r, r]` shape the planar
singular-value lemmas use. -/
theorem diagOp_const_pair (b : OrthonormalBasis (Fin 2) 𝕜 E) (r : ℝ) :
    diagOp b ![r, r] = (((r : ℝ) : 𝕜) • LinearMap.id) := by
  refine b.toBasis.ext fun j => ?_
  rw [OrthonormalBasis.coe_toBasis, diagOp_apply_basis]
  fin_cases j <;> simp

omit [FiniteDimensional 𝕜 E] in
/-- A real diagonal operator is symmetric. -/
theorem isSymmetric_diagOp (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
    (diagOp b x).IsSymmetric := by
  intro u v
  rw [diagOp_apply, diagOp_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [inner_smul_left, inner_smul_right, RCLike.conj_ofReal,
    inner_conj_symm]
  ring

/-- A real diagonal operator is self-adjoint.  This is why a unitarily invariant norm applied to
`diagOp` yields a *symmetric* gauge on vectors. -/
theorem adjoint_diagOp (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
    (diagOp b x).adjoint = diagOp b x :=
  (isSymmetric_diagOp b x).adjoint_eq

omit [FiniteDimensional 𝕜 E] in
/-- Diagonal operators in the same basis multiply diagonally. -/
theorem diagOp_comp (b : OrthonormalBasis (Fin n) 𝕜 E) (x y : Fin n → ℝ) :
    diagOp b x ∘ₗ diagOp b y = diagOp b (x * y) := by
  refine b.toBasis.ext fun j => ?_
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, diagOp_apply_basis,
    map_smul, smul_smul, Pi.mul_apply, RCLike.ofReal_mul, mul_comm]

/-- The singular values of a diagonal operator with *antitone nonnegative*
diagonal are the diagonal itself. -/
theorem singularValues_diagOp (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) {x : Fin n → ℝ}
    (hx_anti : Antitone x) (hx0 : ∀ i, 0 ≤ x i) (i : Fin n) :
    (diagOp b x).singularValues (i : ℕ) = x i := by
  have hgram : (diagOp b x).adjoint ∘ₗ diagOp b x = diagOp b (x * x) := by
    rw [adjoint_diagOp, diagOp_comp]
  have hsq_anti : Antitone fun i => x i ^ 2 := fun i j hij =>
    pow_le_pow_left₀ (hx0 j) (hx_anti hij) 2
  have heig : (diagOp b x).isSymmetric_adjoint_comp_self.eigenvalues hn
      = fun i => x i ^ 2 :=
    (eigenvalues_congr hgram (diagOp b x).isSymmetric_adjoint_comp_self
      (isSymmetric_diagOp b (x * x)) hn).trans
      (LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis _ hn b hsq_anti fun i => by
        rw [diagOp_apply_basis]
        congr 1
        rw [Pi.mul_apply]
        push_cast
        ring)
  rw [(diagOp b x).singularValues_fin hn i, congrFun heig i,
    Real.sqrt_sq (hx0 i)]

/-! ### The operator SVD factorization -/

omit [FiniteDimensional 𝕜 E] in
@[simp]
private theorem coe_toLinearMap_apply (U : E ≃ₗᵢ[𝕜] E) (v : E) :
    U.toLinearMap v = U v := (rfl)

/-- **Operator SVD**: relative to *any* fixed orthonormal basis `b`, every
square operator factors as `A = U ∘ diag(σ(A)) ∘ V` with `U, V` unitary. -/
theorem exists_unitary_diagOp_factorization (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (A : E →ₗ[𝕜] E) :
    ∃ U V : E ≃ₗᵢ[𝕜] E,
      A = U.toLinearMap ∘ₗ diagOp b (fun i => A.singularValues (i : ℕ))
        ∘ₗ V.toLinearMap := by
  subst hn
  set w := A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl with hw
  set K := b.equiv w (Equiv.refl _) with hK
  have hKb : ∀ i, K (b i) = w i := fun i => by
    rw [hK, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply]
  have hKsymm : ∀ i, K.symm (w i) = b i := fun i => by
    rw [← hKb i, LinearIsometryEquiv.symm_apply_apply]
  have habs_w : ∀ i, operatorAbs A (w i)
      = ((A.singularValues (i : ℕ) : ℝ) : 𝕜) • w i := by
    intro i
    rw [show operatorAbs A = (LinearMap.isPositive_adjoint_comp_self A).sqrt from rfl,
      (LinearMap.isPositive_adjoint_comp_self A).sqrt_apply_eigenvectorBasis i,
      ← A.singularValues_fin rfl i]
  have habs : operatorAbs A
      = K.toLinearMap ∘ₗ diagOp b (fun i => A.singularValues (i : ℕ))
        ∘ₗ K.symm.toLinearMap := by
    refine w.toBasis.ext fun i => ?_
    simp only [OrthonormalBasis.coe_toBasis, habs_w i, LinearMap.comp_apply,
      coe_toLinearMap_apply, hKsymm i, diagOp_apply_basis, map_smul, hKb i]
  refine ⟨K.trans (choosePolarUnitary A), K.symm, ?_⟩
  ext v
  have hpolar := LinearMap.congr_fun (polar_decomposition_choosePolarUnitary A) v
  rw [LinearMap.comp_apply] at hpolar
  have habsv := LinearMap.congr_fun habs v
  rw [LinearMap.comp_apply, LinearMap.comp_apply, coe_toLinearMap_apply,
    coe_toLinearMap_apply] at habsv
  simp only [hpolar, LinearMap.comp_apply, coe_toLinearMap_apply, habsv,
    LinearIsometryEquiv.trans_apply]
  rfl

/-! ### Unitarily invariant norms -/

/-- A **unitarily invariant (semi)norm** on the square operators over a
finite-dimensional inner product space: subadditive, absolutely homogeneous,
and invariant under composition with unitaries on both sides.

Positivity (`N A = 0 → A = 0`) is deliberately *not* required — the
Davis–Kahan pipeline never uses it, and every consequence below (gauge
representation, Fan dominance) holds at the seminorm level. -/
structure UnitarilyInvariantSeminorm (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    where
  /-- The underlying function on square operators. -/
  toFun : (E →ₗ[𝕜] E) → ℝ
  /-- Subadditivity. -/
  add_le' : ∀ A B : E →ₗ[𝕜] E, toFun (A + B) ≤ toFun A + toFun B
  /-- Absolute homogeneity. -/
  smul' : ∀ (a : 𝕜) (A : E →ₗ[𝕜] E), toFun (a • A) = ‖a‖ * toFun A
  /-- Two-sided unitary invariance. -/
  invariant' : ∀ (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E),
    toFun (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) = toFun A

namespace UnitarilyInvariantSeminorm

/-- Apply a unitarily invariant norm directly to an operator, writing `N A` for `N.toFun A`. -/
instance : CoeFun (UnitarilyInvariantSeminorm 𝕜 E) fun _ => (E →ₗ[𝕜] E) → ℝ :=
  ⟨UnitarilyInvariantSeminorm.toFun⟩

variable (N : UnitarilyInvariantSeminorm 𝕜 E)

/-- Subadditivity of a unitarily invariant norm. -/
theorem add_le (A B : E →ₗ[𝕜] E) : N (A + B) ≤ N A + N B := N.add_le' A B

/-- Absolute homogeneity of a unitarily invariant norm. -/
theorem smul_eq (a : 𝕜) (A : E →ₗ[𝕜] E) : N (a • A) = ‖a‖ * N A := N.smul' a A

/-- Two-sided unitary invariance -- the defining property, restated for direct use.  See
`invariant_left` and `invariant_right` for the one-sided specializations. -/
theorem invariant (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E) :
    N (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) = N A := N.invariant' U V A

/-- Left unitary invariance. -/
theorem invariant_left (U : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E) :
    N (U.toLinearMap ∘ₗ A) = N A := by
  have h := N.invariant' U (LinearIsometryEquiv.refl 𝕜 E) A
  have hid : A ∘ₗ (LinearIsometryEquiv.refl 𝕜 E).toLinearMap = A := by
    ext v; rfl
  rwa [hid] at h

/-- Right unitary invariance. -/
theorem invariant_right (V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E) :
    N (A ∘ₗ V.toLinearMap) = N A := by
  have h := N.invariant' (LinearIsometryEquiv.refl 𝕜 E) V A
  have hid : (LinearIsometryEquiv.refl 𝕜 E).toLinearMap
      ∘ₗ (A ∘ₗ V.toLinearMap) = A ∘ₗ V.toLinearMap := by
    ext v; rfl
  rwa [hid] at h

/-- A unitarily invariant norm vanishes at zero.  Note this follows from homogeneity alone;
definiteness is deliberately not bundled, so the converse does not hold. -/
theorem apply_zero : N (0 : E →ₗ[𝕜] E) = 0 := by
  have h := N.smul' (0 : 𝕜) 0
  rwa [zero_smul, norm_zero, zero_mul] at h

/-- A unitarily invariant norm is unchanged by negation. -/
theorem apply_neg (A : E →ₗ[𝕜] E) : N (-A) = N A := by
  have h := N.smul' (-1 : 𝕜) A
  rwa [neg_one_smul, norm_neg, norm_one, one_mul] at h

/-- A unitarily invariant norm is nonnegative -- from subadditivity applied to `A` and `-A`, not
assumed as a field. -/
theorem nonneg (A : E →ₗ[𝕜] E) : 0 ≤ N A := by
  have h := N.add_le' A (-A)
  rw [add_neg_cancel, N.apply_zero, N.apply_neg] at h
  linarith

/-! ### The symmetric gauge -/

/-- The **symmetric gauge** of a unitarily invariant norm relative to an
orthonormal basis `b`: the norm of the diagonal operator with diagonal `x`.
Defined on *all* real vectors, not only sorted nonnegative ones — the
T-transform descent exploits its subadditivity, homogeneity, permutation
invariance, and single-coordinate sign invariance on arbitrary vectors. -/
noncomputable def gauge (N : UnitarilyInvariantSeminorm 𝕜 E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : ℝ :=
  N (diagOp b x)

/-- The induced vector gauge is subadditive, inherited from the norm through `diagOp_add`. -/
theorem gauge_add_le (b : OrthonormalBasis (Fin n) 𝕜 E) (x y : Fin n → ℝ) :
    N.gauge b (x + y) ≤ N.gauge b x + N.gauge b y := by
  rw [gauge, diagOp_add]
  exact N.add_le' _ _

/-- The induced vector gauge is absolutely homogeneous over `ℝ`. -/
theorem gauge_real_smul (b : OrthonormalBasis (Fin n) 𝕜 E) (c : ℝ)
    (x : Fin n → ℝ) : N.gauge b (c • x) = |c| * N.gauge b x := by
  rw [gauge, diagOp_real_smul, N.smul', RCLike.norm_ofReal]
  rfl

/-- Permutation invariance of the gauge: conjugating the diagonal operator by
the basis-permutation unitary permutes the diagonal. -/
theorem gauge_perm (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) : N.gauge b (x ∘ π) = N.gauge b x := by
  have hconj : diagOp b (x ∘ π)
      = (b.equiv b π).symm.toLinearMap ∘ₗ diagOp b x
        ∘ₗ (b.equiv b π).toLinearMap := by
    refine b.toBasis.ext fun j => ?_
    simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
      coe_toLinearMap_apply, OrthonormalBasis.equiv_apply_basis, diagOp_apply_basis,
      map_smul, Function.comp_apply]
    congr 1
    rw [← OrthonormalBasis.equiv_apply_basis b b π j,
      LinearIsometryEquiv.symm_apply_apply]
  rw [gauge, hconj, N.invariant']
  rfl

/-- Single-coordinate sign flip invariance of the gauge: flipping the sign of
the `j`-th diagonal entry composes the diagonal operator with the reflection
through `(𝕜 ∙ b j)ᗮ`, a unitary. -/
theorem gauge_neg_single (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ)
    (j : Fin n) :
    N.gauge b (Function.update x j (-(x j))) = N.gauge b x := by
  have hcomp : diagOp b (Function.update x j (-(x j)))
      = diagOp b x ∘ₗ ((𝕜 ∙ b j)ᗮ).reflection.toLinearMap := by
    refine b.toBasis.ext fun i => ?_
    rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
      coe_toLinearMap_apply]
    rcases eq_or_ne i j with rfl | hij
    · simp only [Submodule.reflection_orthogonalComplement_singleton_eq_neg,
        map_neg, diagOp_apply_basis, Function.update_self, neg_smul]
    · have hmem : b i ∈ (𝕜 ∙ b j)ᗮ :=
        Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
          (b.orthonormal.2 (Ne.symm hij))
      rw [Submodule.reflection_mem_subspace_eq_self hmem, diagOp_apply_basis,
        diagOp_apply_basis, Function.update_of_ne hij]
  rw [gauge, hcomp, N.invariant_right]
  rfl

/-- **The gauge representation**: a unitarily invariant norm is the gauge of
the singular values, via the operator SVD. -/
theorem apply_eq_gauge (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (A : E →ₗ[𝕜] E) :
    N A = N.gauge b fun i => A.singularValues (i : ℕ) := by
  obtain ⟨U, V, hUV⟩ := exists_unitary_diagOp_factorization hn b A
  conv_lhs => rw [hUV]
  exact N.invariant' U V _

/-- A unitarily invariant norm is determined by the singular-value sequence.

Immediate from the gauge representation: both sides are the same gauge applied
to the same sequence. -/
theorem eq_of_same_singularValues {A B : E →ₗ[𝕜] E}
    (h : A.singularValues = B.singularValues) : N A = N B := by
  rw [N.apply_eq_gauge rfl (stdOrthonormalBasis 𝕜 E) A,
    N.apply_eq_gauge rfl (stdOrthonormalBasis 𝕜 E) B, h]

/-! ### Monotonicity of the gauge -/

/-- The gauge of a unitarily invariant norm, packaged as a `FiniteSymmetricGauge`.  Its four
fields are exactly `gauge_add_le`, `gauge_real_smul`, `gauge_perm` and `gauge_neg_single`,
which is what makes the Hardy--Littlewood--Pólya transfer theory
(`ForTauCeti.Analysis.Convex.Majorization`) apply verbatim: everything below is that theory
read through this packaging, not a second proof of it. -/
noncomputable def finiteSymmetricGauge (N : UnitarilyInvariantSeminorm 𝕜 E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) : FiniteSymmetricGauge n where
  toFun := N.gauge b
  add_le' := N.gauge_add_le b
  real_smul' := N.gauge_real_smul b
  perm' := N.gauge_perm b
  neg_single' := N.gauge_neg_single b

/-- The induced finite symmetric gauge, unfolded. -/
@[simp] theorem finiteSymmetricGauge_apply (b : OrthonormalBasis (Fin n) 𝕜 E)
    (x : Fin n → ℝ) : N.finiteSymmetricGauge b x = N.gauge b x := (rfl)

/-- Shrinking one coordinate of `y` (in absolute value) does not increase the
gauge: `update y j t` with `|t| ≤ y j` is a convex combination of `y` and its
`j`-th sign flip. -/
theorem gauge_update_le (b : OrthonormalBasis (Fin n) 𝕜 E) {y : Fin n → ℝ}
    {j : Fin n} {t : ℝ} (ht : |t| ≤ y j) :
    N.gauge b (Function.update y j t) ≤ N.gauge b y :=
  (N.finiteSymmetricGauge b).update_le ht

/-- **Coordinatewise monotonicity of the gauge** on nonnegative vectors. -/
theorem gauge_mono (b : OrthonormalBasis (Fin n) 𝕜 E) {x y : Fin n → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    N.gauge b x ≤ N.gauge b y :=
  (N.finiteSymmetricGauge b).mono hx0 hxy

/-! ### The T-transform descent -/

/-- **The T-transform descent on the gauge** — the engine of Fan dominance.
If `z` is antitone and nonnegative, `y` is nonnegative, and every prefix sum
of `z` is dominated by the corresponding prefix sum of `y`, then
`Φ_N(z) ≤ Φ_N(y)`.

No total-sum equality is assumed, no majorization completion and no
separation theorem is used: this is
`TauCeti.FiniteSymmetricGauge.le_of_prefixSum_le`, whose descent averages `y` with a
transposition of itself, at a cost of one triangle inequality, one homogeneity, and one
swap invariance of the gauge per step. -/
theorem gauge_le_gauge_of_prefix_sums_le (b : OrthonormalBasis (Fin n) 𝕜 E)
    {z y : Fin n → ℝ} (hz_anti : Antitone z) (hz0 : ∀ i, 0 ≤ z i)
    (hy0 : ∀ i, 0 ≤ y i)
    (hpre : ∀ m : ℕ,
      ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, z i
        ≤ ∑ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < m, y i) :
    N.gauge b z ≤ N.gauge b y :=
  (N.finiteSymmetricGauge b).le_of_prefixSum_le hz_anti hz0 hy0 hpre

/-! ### The Fan dominance principle -/

/-- **The Fan dominance principle** (Ky Fan; Bhatia IV.2.2): if every Ky Fan
sum of `A` is dominated by the corresponding Ky Fan sum of `B`, then
`N A ≤ N B` for *every* unitarily invariant norm `N`. -/
theorem apply_le_of_kyFanSum_le {A B : E →ₗ[𝕜] E}
    (h : ∀ k, kyFanSum k A ≤ kyFanSum k B) : N A ≤ N B := by
  have hanti : Antitone fun i : Fin (finrank 𝕜 E) => A.singularValues (i : ℕ) :=
    fun i j hij => A.singularValues_antitone (Fin.le_def.mp hij)
  rw [N.apply_eq_gauge rfl (stdOrthonormalBasis 𝕜 E) A,
    N.apply_eq_gauge rfl (stdOrthonormalBasis 𝕜 E) B]
  refine N.gauge_le_gauge_of_prefix_sums_le (stdOrthonormalBasis 𝕜 E) hanti
    (fun i => A.singularValues_nonneg _) (fun i => B.singularValues_nonneg _)
    fun m => ?_
  rcases le_or_gt m (finrank 𝕜 E) with hm | hm
  · rw [sum_filter_lt_eq_sum_fin hm fun k => A.singularValues k,
      sum_filter_lt_eq_sum_fin hm fun k => B.singularValues k,
      ← kyFanSum_eq_sum_fin, ← kyFanSum_eq_sum_fin]
    exact h m
  · have huniv : (Finset.univ.filter
        fun i : Fin (finrank 𝕜 E) => (i : ℕ) < m) = Finset.univ :=
      Finset.filter_true_of_mem fun i _ => lt_trans i.isLt hm
    rw [huniv, ← kyFanSum_eq_sum_fin, ← kyFanSum_eq_sum_fin]
    exact h _

/-- Unitarily invariant norms are `star`-invariant: `N (A⋆) = N A`.  Via the
gauge representation and `σ(A⋆) = σ(A)`. -/
theorem apply_adjoint (A : E →ₗ[𝕜] E) : N A.adjoint = N A := by
  rw [N.apply_eq_gauge rfl (stdOrthonormalBasis 𝕜 E) A.adjoint,
    N.apply_eq_gauge rfl (stdOrthonormalBasis 𝕜 E) A]
  simp only [singularValues_adjoint]

/-! ### The operator-ideal property -/

/-- **The ideal property (left factor).**  If `‖C y‖ ≤ c ‖y‖` for `0 ≤ c`, then
`N (C ∘ₗ X) ≤ c * N X` for every unitarily invariant norm.  From Fan dominance
applied to the singular-value domination `σᵢ(C ∘ X) ≤ c σᵢ(X)`. -/
theorem apply_comp_le {C X : E →ₗ[𝕜] E} {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ y, ‖C y‖ ≤ c * ‖y‖) : N (C ∘ₗ X) ≤ c * N X :=
  calc N (C ∘ₗ X)
      ≤ N (((c : 𝕜)) • X) :=
        N.apply_le_of_kyFanSum_le fun k =>
          kyFanSum_le_of_singularValues_le (fun i => by
            rw [singularValues_real_smul X hc i]
            exact singularValues_comp_le hc hC X i) k
    _ = c * N X := by rw [N.smul_eq, RCLike.norm_ofReal, abs_of_nonneg hc]

/-- **The ideal property (right factor).**  If `‖C y‖ ≤ c ‖y‖` for `0 ≤ c`, then
`N (X ∘ₗ C) ≤ N X * c`. -/
theorem apply_comp_le' {X C : E →ₗ[𝕜] E} {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ y, ‖C y‖ ≤ c * ‖y‖) : N (X ∘ₗ C) ≤ N X * c :=
  calc N (X ∘ₗ C)
      ≤ N (((c : 𝕜)) • X) :=
        N.apply_le_of_kyFanSum_le fun k =>
          kyFanSum_le_of_singularValues_le (fun i => by
            rw [singularValues_real_smul X hc i]
            exact singularValues_comp_le' hc hC i) k
    _ = N X * c := by rw [N.smul_eq, RCLike.norm_ofReal, abs_of_nonneg hc, mul_comm]

/-! ### The Frobenius (Hilbert–Schmidt) unitarily invariant norm

`‖A‖_F = √(∑ᵢ ‖A bᵢ‖²)` over any orthonormal basis is a unitarily invariant
norm: subadditivity is the Minkowski inequality on `EuclideanSpace`, absolute
homogeneity is pointwise, and two-sided unitary invariance is
`sum_sq_norm_apply_unitary_comp` on the right and `LinearIsometryEquiv.norm_map`
on the left.  This is the norm the paper's `…_hilbertSchmidt` bounds use, and it
instantiates the every-UI-norm Davis–Kahan theorems to the Frobenius vocabulary
(plan step OP2).

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.UnitarilyInvariantNorm`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `7481732`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Fable 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

/-- `√(∑ (fᵢ + gᵢ)²) ≤ √(∑ fᵢ²) + √(∑ gᵢ²)` for nonnegative real vectors: the
Minkowski inequality, obtained from `EuclideanSpace`'s triangle inequality by
transporting `f, g` across `WithLp.equiv`.

Public rather than `private` since 2026-07-30: the rectangular instances file
had a character-for-character copy of this proof under the name
`sqrt_sum_add_sq_le_rect`, which is what being `private` invites.  The
namespace is not ideal — this is a fact about `Fin m → ℝ` and has nothing to do
with unitarily invariant norms — but it is where the proof already lived, and
moving it is a placement decision rather than a de-duplication. -/
theorem sqrt_sum_add_sq_le {m : ℕ} (f g : Fin m → ℝ) :
    Real.sqrt (∑ i, (f i + g i) ^ 2)
      ≤ Real.sqrt (∑ i, f i ^ 2) + Real.sqrt (∑ i, g i ^ 2) := by
  let x : EuclideanSpace ℝ (Fin m) := (WithLp.equiv 2 (Fin m → ℝ)).symm f
  let y : EuclideanSpace ℝ (Fin m) := (WithLp.equiv 2 (Fin m → ℝ)).symm g
  have hnx : ‖x‖ = Real.sqrt (∑ i, f i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by
      rw [show x i = f i from rfl, Real.norm_eq_abs, sq_abs])
  have hny : ‖y‖ = Real.sqrt (∑ i, g i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by
      rw [show y i = g i from rfl, Real.norm_eq_abs, sq_abs])
  have hnxy : ‖x + y‖ = Real.sqrt (∑ i, (f i + g i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by
      rw [PiLp.add_apply, show x i = f i from rfl, show y i = g i from rfl,
        Real.norm_eq_abs, sq_abs])
  rw [← hnx, ← hny, ← hnxy]
  exact norm_add_le x y

/-- **The Frobenius (Hilbert–Schmidt) norm as a unitarily invariant norm.**
`A ↦ √(∑ᵢ ‖A bᵢ‖²)` over the standard orthonormal basis. -/
@[expose]
noncomputable def frobenius (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : UnitarilyInvariantSeminorm 𝕜 E where
  toFun A := Real.sqrt (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)
  add_le' A B := by
    have hmono : Real.sqrt (∑ i, ‖(A + B) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)
        ≤ Real.sqrt (∑ i, (‖A (stdOrthonormalBasis 𝕜 E i)‖
            + ‖B (stdOrthonormalBasis 𝕜 E i)‖) ^ 2) := by
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      rw [LinearMap.add_apply]; exact norm_add_le _ _
    exact hmono.trans (sqrt_sum_add_sq_le _ _)
  smul' a A := by
    have h : ∀ i, ‖(a • A) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2
        = ‖a‖ ^ 2 * ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 := fun i => by
      rw [LinearMap.smul_apply, norm_smul, mul_pow]
    rw [show (∑ i, ‖(a • A) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)
        = ‖a‖ ^ 2 * ∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => h i,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg a)]
  invariant' U V A := by
    have key : ∀ i, ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2
        = ‖A (V (stdOrthonormalBasis 𝕜 E i))‖ ^ 2 := fun i => by
      rw [show (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) (stdOrthonormalBasis 𝕜 E i)
          = U (A (V (stdOrthonormalBasis 𝕜 E i))) from rfl, U.norm_map]
    rw [show (∑ i, ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)
        = ∑ i, ‖A (V (stdOrthonormalBasis 𝕜 E i))‖ ^ 2 from
        Finset.sum_congr rfl fun i _ => key i,
      sum_sq_norm_apply_unitary_comp A V rfl (stdOrthonormalBasis 𝕜 E)]

variable (𝕜 E) in
/-- **Basis independence of the Frobenius norm.**  `‖A‖_F = √(∑ₖ ‖A bₖ‖²)` for
*any* orthonormal basis `b`, not just the standard one — both sides equal
`√(∑ σₖ²)` by `sum_sq_singularValues`. -/
@[simp]
theorem frobenius_apply (A : E →ₗ[𝕜] E) (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) :
    frobenius 𝕜 E A = Real.sqrt (∑ k, ‖A (b k)‖ ^ 2) := by
  subst hn
  -- names the application so the norm bound applies to it directly.
  change Real.sqrt (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) = _
  rw [← sum_sq_singularValues A rfl (stdOrthonormalBasis 𝕜 E),
    ← sum_sq_singularValues A rfl b]

variable (𝕜 E) in
/-- The squared Frobenius norm as a column-norm sum — the `‖A‖²_F` vocabulary of
the paper's Hilbert–Schmidt bounds. -/
theorem frobenius_sq (A : E →ₗ[𝕜] E) (hn : finrank 𝕜 E = n)
    (b : OrthonormalBasis (Fin n) 𝕜 E) :
    frobenius 𝕜 E A ^ 2 = ∑ k, ‖A (b k)‖ ^ 2 := by
  rw [frobenius_apply 𝕜 E A hn b,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]

end UnitarilyInvariantSeminorm

end TauCeti
