/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CourantFischer
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Gap

/-!
# Finite-dimensional spectral subspaces

Restricted spectra, reducing subspaces, canonical spectral projectors, and the
quadratic-form bridges used by finite Davis--Kahan theorems.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Core/SpectralSubspace.lean`
before the dependency-closed base of the sin-Θ core moved into the staging
layer.  Statements, proofs, signatures and namespaces are
unchanged; the declarations already lived in `TauCeti.DavisKahan*`, so the move
was a path change and an import repoint and nothing else.

The move became possible only once Y3(b2) took the `ForMathlib`
inner-product-space component into `ForTauCeti`: before that this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
/-- A subspace is **invariant** under an operator when the operator maps it into
itself.

Named for what it says.  It was called `Reduces`, which collided with
`ContinuousLinearMap.Reduces` — a genuinely *stronger* predicate requiring
`Uᗮ` to be invariant too — so one name meant two things in one library and a
reader meeting `IsInvariant A U` in a docstring could not tell which.  For a
symmetric operator the two coincide, and `isInvariant_orthogonal_of_isSymmetric`
is what supplies that; but the implication is one-directional in general, which
is exactly why the names had to be separated. -/
@[expose]
def IsInvariant (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  ∀ x ∈ U, A x ∈ U

omit [FiniteDimensional 𝕜 E] in
/-- `LinearMap.coe_restrict_apply`, restated for a hypothesis in `IsInvariant` form.

Mathlib's lemma is stated for `LinearMap.restrict`'s own hypothesis shape, and `IsInvariant A U`
is only *definitionally* that shape.  `simp` and `rw` match at `instances` transparency, so
neither will bridge the gap and the Mathlib lemma silently never fires on an `IsInvariant`
restriction.  Every `A.restrict hU` in this development carries an `IsInvariant`, so this is
the spelling that actually gets used. -/
@[simp] theorem coe_restrict_apply_of_isInvariant {A : E →ₗ[𝕜] E} {U : Submodule 𝕜 E}
    (hU : IsInvariant A U) (x : U) :
    ((A.restrict hU x : U) : E) = A (x : E) := rfl

/-- The finite-dimensional point spectrum of `A` carried by `U`.

For symmetric operators this is the spectrum of the restriction to `U` once
`U` reduces `A`.  The definition avoids exposing a choice of restricted
coordinate space in theorem statements.

Eigenvectors are Mathlib's `Module.End.HasEigenvector` rather than a local predicate; the
only thing a local one added was to fix the eigenvalue as real, which is a property of the
`lam : ℝ` binder here and not of the notion of eigenvector. -/
def restrictedSpectrum (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) : Set ℝ :=
  {lam | ∃ x, x ∈ U ∧ Module.End.HasEigenvector A (lam : 𝕜) x}

omit [FiniteDimensional 𝕜 E] in
/-- **The membership characterization**, in the eigenvalue-equation form that consumers
want.

`restrictedSpectrum` is stated through `Module.End.HasEigenvector` so that Mathlib's
eigenspace API applies to it, but almost every proof needs the equation `A x = lam • x`
rather than membership in an eigenspace.  This lemma is the only place the two are
converted, so a proof never destructures the definition and the internal shape of
`HasEigenvector` -- which orders its conjuncts `(mem_eigenspace, ne_zero)` -- stops being
part of this definition's public interface. -/
theorem mem_restrictedSpectrum_iff {A : E →ₗ[𝕜] E} {U : Submodule 𝕜 E} {lam : ℝ} :
    lam ∈ restrictedSpectrum A U ↔ ∃ x ∈ U, x ≠ 0 ∧ A x = (lam : 𝕜) • x :=
  ⟨fun ⟨x, hxU, hxEig, hx0⟩ => ⟨x, hxU, hx0, Module.End.mem_eigenspace_iff.mp hxEig⟩,
    fun ⟨x, hxU, hx0, hxEig⟩ => ⟨x, hxU, Module.End.mem_eigenspace_iff.mpr hxEig, hx0⟩⟩

omit [FiniteDimensional 𝕜 E] in
/-- The introduction rule: a nonzero eigenvector in `U` witnesses its eigenvalue. -/
theorem mem_restrictedSpectrum {A : E →ₗ[𝕜] E} {U : Submodule 𝕜 E} {lam : ℝ} {x : E}
    (hxU : x ∈ U) (hx0 : x ≠ 0) (hxEig : A x = (lam : 𝕜) • x) :
    lam ∈ restrictedSpectrum A U :=
  mem_restrictedSpectrum_iff.mpr ⟨x, hxU, hx0, hxEig⟩

/-- Every eigenvalue of `A` carried by `U` lies in `Ω`. -/
@[expose]
def SpectrumIn (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (Ω : Set ℝ) : Prop :=
  restrictedSpectrum A U ⊆ Ω

/-- Canonical finite-dimensional spectral subspace selected by a real set. -/
@[expose]
noncomputable def spectralSubspace (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 {x | ∃ lam ∈ Ω, Module.End.HasEigenvector A (lam : 𝕜) x}

/-- Canonical orthogonal spectral projector. -/
@[expose]
noncomputable def spectralProjection (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    E →ₗ[𝕜] E :=
  ((spectralSubspace A Ω).starProjection : E →L[𝕜] E)

/-- The orthogonal projector onto a finite-dimensional subspace, as a linear
map. -/
@[expose]
noncomputable def projection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    E →ₗ[𝕜] E :=
  ((U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)

/-- The complementary projector. -/
@[expose]
noncomputable def complementaryProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  projection Uᗮ

omit [FiniteDimensional 𝕜 E] in
/-- **The complementary projector is `1 - P`.**  The linear-map form of
`Submodule.starProjection_add_starProjection_orthogonal`, which is what turns a
two-projection identity into ordinary algebra in the endomorphism ring. -/
theorem complementaryProjection_eq_id_sub (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    complementaryProjection U = LinearMap.id - projection U := by
  ext x
  have h := U.starProjection_add_starProjection_orthogonal x
  simp only [LinearMap.sub_apply, LinearMap.id_apply]
  exact eq_sub_of_add_eq' h

omit [FiniteDimensional 𝕜 E] in
/-- An orthogonal projector is symmetric. -/
theorem projection_isSymmetric (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : (projection U).IsSymmetric :=
  U.starProjection_isSymmetric

/-- An orthogonal projector is its own adjoint. -/
@[simp] theorem projection_adjoint (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    (projection U).adjoint = projection U :=
  (projection_isSymmetric U).adjoint_eq

omit [FiniteDimensional 𝕜 E] in
/-- A symmetric operator leaves the orthogonal complement of an invariant
subspace invariant.
-/
theorem isInvariant_orthogonal_of_isSymmetric {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) {U : Submodule 𝕜 E} (hU : IsInvariant A U) :
    IsInvariant A Uᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← hA u x]
  exact Submodule.inner_right_of_mem_orthogonal (hU u hu) hx

omit [FiniteDimensional 𝕜 E] in
/-- The canonical spectral subspace reduces its operator.  Symmetry is not
needed for this algebraic fact; it is needed later for orthogonal reduction and
for completeness of the real eigenvector decomposition.
-/
theorem isInvariant_spectralSubspace (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    IsInvariant A (spectralSubspace A Ω) := by
  intro x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨lam, hlam, hy⟩
    rw [Module.End.mem_eigenspace_iff.mp hy.1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨lam, hlam, hy⟩)
  · simp
  · intro x y _ _ hx hy
    simpa only [map_add] using (spectralSubspace A Ω).add_mem hx hy
  · intro c x _ hx
    simpa only [map_smul] using (spectralSubspace A Ω).smul_mem c hx

/-! ### Restriction to an invariant subspace and the restricted-spectrum bridge

These give the concrete restriction `A.restrict hU : U →ₗ[𝕜] U` of an operator to
an invariant subspace and identify its full point spectrum with the `U`-carried
point spectrum of `A`.  This is the bridge used to discharge the spectral
hypotheses of the residual/perturbation `sin Θ` theorems on the subtype. -/

omit [FiniteDimensional 𝕜 E] in
/-- The restriction of a symmetric operator to an invariant subspace is
symmetric (mathlib's `LinearMap.IsSymmetric.restrict_invariant`, restated for the
`IsInvariant` predicate). -/
theorem isSymmetric_restrict {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} (hU : IsInvariant A U) :
    (A.restrict hU).IsSymmetric :=
  hA.restrict_invariant hU

omit [FiniteDimensional 𝕜 E] in
/-- **The restricted-spectrum bridge.**  The point spectrum of the restriction
`A.restrict hU : U →ₗ[𝕜] U` (over the whole `⊤`) equals the `U`-carried point
spectrum of `A`.  Eigenvectors transport across the subtype coercion. -/
theorem restrictedSpectrum_restrict (A : E →ₗ[𝕜] E)
    {U : Submodule 𝕜 E} (hU : IsInvariant A U) :
    restrictedSpectrum (A.restrict hU) ⊤ = restrictedSpectrum A U := by
  ext lam
  constructor
  · intro hlam
    obtain ⟨x, -, hx0, hxEig⟩ := mem_restrictedSpectrum_iff.mp hlam
    refine mem_restrictedSpectrum x.2 (fun hx => hx0 (Subtype.ext hx)) ?_
    -- `LinearMap.coe_restrict_apply` and `Submodule.coe_smul` are both `rfl`, but `rw`
    -- cannot match them here: `hU : IsInvariant A U` is only definitionally the hypothesis
    -- `LinearMap.restrict` is stated with.  `exact` checks up to defeq.
    exact congrArg (Subtype.val) hxEig
  · intro hlam
    obtain ⟨x, hxU, hx0, hxEig⟩ := mem_restrictedSpectrum_iff.mp hlam
    refine mem_restrictedSpectrum (x := ⟨x, hxU⟩) Submodule.mem_top
      (fun hxu => hx0 (congrArg Subtype.val hxu)) ?_
    apply Subtype.ext
    exact hxEig

omit [FiniteDimensional 𝕜 E] in
/-- The containment form of the restricted-spectrum bridge: `A.restrict hU` has
spectrum in `s` iff `A` carries spectrum in `s` on `U`. -/
theorem spectrumIn_restrict_iff (A : E →ₗ[𝕜] E)
    {U : Submodule 𝕜 E} (hU : IsInvariant A U) (s : Set ℝ) :
    SpectrumIn (A.restrict hU) ⊤ s ↔ SpectrumIn A U s := by
  unfold SpectrumIn
  rw [restrictedSpectrum_restrict]

omit [FiniteDimensional 𝕜 E] in
/-- **A symmetric operator commutes with the projection onto a reducing
subspace.**  For `A` symmetric and `U` an `A`-invariant subspace (so `Uᗮ` is
invariant too), `P_U (A x) = A (P_U x)`. -/
theorem projection_apply_comm_of_isInvariant {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U) (x : E) :
    projection U (A x) = A (projection U x) := by
  have hUperp : IsInvariant A Uᗮ := isInvariant_orthogonal_of_isSymmetric hA hU
  have hpx : U.starProjection x ∈ U := U.starProjection_apply_mem x
  have hrest : x - U.starProjection x ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
  have hApx : A (U.starProjection x) ∈ U := hU _ hpx
  have hArest : A (x - U.starProjection x) ∈ Uᗮ := hUperp _ hrest
  have hsplit : A x = A (U.starProjection x) + A (x - U.starProjection x) := by
    rw [← map_add]; congr 1; abel
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change U.starProjection (A x) = A (U.starProjection x)
  rw [hsplit, map_add, U.starProjection_eq_self_iff.mpr hApx,
    (Submodule.starProjection_apply_eq_zero_iff U).mpr hArest, add_zero]

omit [FiniteDimensional 𝕜 E] in
/-- The complementary projection onto `Uᗮ` also commutes with `A` when `A` is
symmetric and `U` reduces `A`. -/
theorem complementaryProjection_apply_comm_of_isInvariant {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : IsInvariant A U) (x : E) :
    complementaryProjection U (A x) = A (complementaryProjection U x) :=
  projection_apply_comm_of_isInvariant hA (isInvariant_orthogonal_of_isSymmetric hA hU) x

/-! ### Spectral gap ⟹ quadratic-form coercivity bridge

These convert the abstract eigenvalue-set hypotheses (`SpectrumIn A U s`) into the
quadratic-form bounds `re ⟪A x, x⟫ ≤ c ‖x‖²` (or `≥`) that the dimension-free
operator-norm Sylvester/`sin Θ` machinery consumes.  This is the point where
finite-dimensional spectral decomposition (an eigenbasis of the restriction) is
genuinely used. -/

/-- If every eigenvalue of a symmetric `T` is `≤ c`, the quadratic form is
bounded above by `c ‖·‖²` (diagonalization: `∑ λᵢ ‖repr xᵢ‖² ≤ c ∑ ‖repr xᵢ‖²`). -/
theorem re_inner_le_of_forall_eigenvalue_le {n : ℕ} {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {c : ℝ}
    (hc : ∀ i, hT.eigenvalues hn i ≤ c) (x : E) :
    RCLike.re ⟪T x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  refine LinearMap.IsSymmetric.re_inner_apply_self_le_of_mem_spanIndices hT hn (s := Set.univ)
    (fun i _ => hc i) ?_
  have htop : (hT.eigenvectorBasis hn).spanIndices (Set.univ : Set (Fin n)) = ⊤ := by
    rw [OrthonormalBasis.spanIndices, eq_top_iff,
      ← (hT.eigenvectorBasis hn).toBasis.span_eq]
    exact Submodule.span_mono (by rintro y ⟨i, rfl⟩; exact ⟨i, trivial, rfl⟩)
  rw [htop]; exact Submodule.mem_top

/-- Dual: if every eigenvalue of a symmetric `T` is `≥ c`, the quadratic form is
bounded below by `c ‖·‖²`. -/
theorem le_re_inner_of_forall_le_eigenvalue {n : ℕ} {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {c : ℝ}
    (hc : ∀ i, c ≤ hT.eigenvalues hn i) (x : E) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  refine LinearMap.IsSymmetric.le_re_inner_apply_self_of_mem_spanIndices hT hn (s := Set.univ)
    (fun i _ => hc i) ?_
  have htop : (hT.eigenvectorBasis hn).spanIndices (Set.univ : Set (Fin n)) = ⊤ := by
    rw [OrthonormalBasis.spanIndices, eq_top_iff,
      ← (hT.eigenvectorBasis hn).toBasis.span_eq]
    exact Submodule.span_mono (by rintro y ⟨i, rfl⟩; exact ⟨i, trivial, rfl⟩)
  rw [htop]; exact Submodule.mem_top

/-- **The spectral-gap coercivity bridge (upper).**  If `A` is symmetric, `U`
reduces `A`, and the `U`-carried spectrum lies in `Set.Iic c`, then the quadratic
form of `A` is bounded above by `c ‖·‖²` on `U`. -/
theorem re_inner_le_of_spectrumIn {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} (hU : IsInvariant A U) {c : ℝ}
    (hspec : SpectrumIn A U (Set.Iic c)) {x : E} (hx : x ∈ U) :
    RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  have hA'sym : (A.restrict hU).IsSymmetric := isSymmetric_restrict hA hU
  have hev : ∀ i, hA'sym.eigenvalues rfl i ≤ c := fun i => by
    have hmem : hA'sym.eigenvalues rfl i ∈ restrictedSpectrum (A.restrict hU) ⊤ :=
      mem_restrictedSpectrum Submodule.mem_top
        ((hA'sym.eigenvectorBasis rfl).orthonormal.ne_zero i)
        (hA'sym.apply_eigenvectorBasis rfl i)
    rw [restrictedSpectrum_restrict] at hmem
    exact hspec hmem
  have hquad := re_inner_le_of_forall_eigenvalue_le hA'sym rfl hev ⟨x, hx⟩
  exact hquad

/-- **The spectral-gap coercivity bridge (lower).**  If `A` is symmetric, `U`
reduces `A`, and the `U`-carried spectrum lies in `Set.Ici c`, then the quadratic
form of `A` is bounded below by `c ‖·‖²` on `U`. -/
theorem le_re_inner_of_spectrumIn {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} (hU : IsInvariant A U) {c : ℝ}
    (hspec : SpectrumIn A U (Set.Ici c)) {x : E} (hx : x ∈ U) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜 := by
  have hA'sym : (A.restrict hU).IsSymmetric := isSymmetric_restrict hA hU
  have hev : ∀ i, c ≤ hA'sym.eigenvalues rfl i := fun i => by
    have hmem : hA'sym.eigenvalues rfl i ∈ restrictedSpectrum (A.restrict hU) ⊤ :=
      mem_restrictedSpectrum Submodule.mem_top
        ((hA'sym.eigenvectorBasis rfl).orthonormal.ne_zero i)
        (hA'sym.apply_eigenvectorBasis rfl i)
    rw [restrictedSpectrum_restrict] at hmem
    exact hspec hmem
  have hquad := le_re_inner_of_forall_le_eigenvalue hA'sym rfl hev ⟨x, hx⟩
  exact hquad

/-- The canonical projector has the expected range.
-/
theorem range_spectralProjection (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    LinearMap.range (spectralProjection A Ω) = spectralSubspace A Ω := by
  exact Submodule.range_starProjection (spectralSubspace A Ω)

omit [FiniteDimensional 𝕜 E] in
/-- Spectral selection is independent of the chosen eigenbasis.
-/
theorem spectralSubspace_eq_span_eigenvectors (A : E →ₗ[𝕜] E)
    (Ω : Set ℝ) :
    spectralSubspace A Ω =
      Submodule.span 𝕜 {x | ∃ lam ∈ Ω, Module.End.HasEigenvector A (lam : 𝕜) x} :=
  rfl

omit [FiniteDimensional 𝕜 E] in
/-- **The spectral subspace selected by `Ω` carries only spectrum in `Ω`.**

`spectralSubspace A Ω` is *defined* as a span of eigenvectors whose eigenvalues lie in
`Ω`, but that does not immediately say the span contains no *other* eigenvector: a sum of
eigenvectors could a priori be an eigenvector for a fresh eigenvalue.  It cannot, and this
is the theorem saying so.

The proof is eigenspace independence, not symmetry or finite dimension: the span sits
inside `⨆ μ ∈ Ω, eigenspace A μ`, and an eigenvector for `lam ∉ Ω` would lie in the
intersection of `eigenspace A lam` with the supremum of the *others*, which
`Module.End.eigenspaces_iSupIndep` makes trivial.  So `A` needs no hypotheses at all.

**This was a hypothesis, not a theorem.**  Production perturbation statements carried it as
`hAselected : SpectrumIn A (spectralSubspace A (Set.Icc a b)) (Set.Icc a b)`, which is
exactly this conclusion at `Ω = Set.Icc a b`; a caller had to discharge, by hand, a fact
that holds unconditionally. -/
theorem spectrumIn_spectralSubspace (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    SpectrumIn A (spectralSubspace A Ω) Ω := by
  intro lam hlam
  obtain ⟨x, hxU, hx0, hxeq⟩ := mem_restrictedSpectrum_iff.mp hlam
  by_contra hlamΩ
  -- The span of the selected eigenvectors sits inside the supremum of their eigenspaces.
  have hspan : spectralSubspace A Ω ≤
      ⨆ μ ∈ ((↑) '' Ω : Set 𝕜), Module.End.eigenspace A μ := by
    rw [spectralSubspace, Submodule.span_le]
    rintro y ⟨lam', hlam'Ω, hy⟩
    exact Submodule.mem_iSup_of_mem _
      (Submodule.mem_iSup_of_mem ⟨lam', hlam'Ω, rfl⟩ hy.1)
  -- Every eigenvalue that supremum ranges over is different from `lam`.
  have hle : (⨆ μ ∈ ((↑) '' Ω : Set 𝕜), Module.End.eigenspace A μ) ≤
      ⨆ μ, ⨆ _ : μ ≠ (lam : 𝕜), Module.End.eigenspace A μ := by
    refine iSup_le fun μ => iSup_le fun hμ => ?_
    obtain ⟨r, hrΩ, hr⟩ := hμ
    refine le_iSup_of_le μ (le_iSup_of_le (fun hcon => hlamΩ ?_) le_rfl)
    exact (RCLike.ofReal_inj.mp (hr.trans hcon)) ▸ hrΩ
  -- Independence of eigenspaces then forces `x = 0`.
  have hdisj := (iSupIndep_def.mp (Module.End.eigenspaces_iSupIndep A)) (lam : 𝕜)
  exact hx0 (Submodule.mem_bot 𝕜 |>.mp
    (hdisj.le_bot ⟨Module.End.mem_eigenspace_iff.mpr hxeq, hle (hspan hxU)⟩))


end TauCeti
