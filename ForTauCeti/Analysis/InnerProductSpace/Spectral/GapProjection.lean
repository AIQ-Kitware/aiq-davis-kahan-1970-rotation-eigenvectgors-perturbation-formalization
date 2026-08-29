/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SeparatedIntertwiner
public import ForTauCeti.Analysis.InnerProductSpace.SpectralOrder.Complex
public import ForTauCeti.Analysis.InnerProductSpace.SpectralOrder.Real
public import ForTauCeti.Analysis.InnerProductSpace.RealContinuousFunctionalCalculus

/-!
# The gap step function of a block-diagonal self-adjoint operator is its projection

Let `A` be a bounded self-adjoint operator, let `U` reduce it, and write `A₀`, `A₁` for the
two restrictions.  If the two block spectra are separated by a gap,

```
spectrum A₀ ⊆ (-∞, α],      spectrum A₁ ⊆ [α + δ, ∞),      δ > 0,
```

then *every* real function `f` with `f = 1` below the gap and `f = 0` above it satisfies

```
f(A) = P_U.
```

That is, the functional calculus at a step function cutting the gap returns the orthogonal
projection onto the low block — which is what makes a reducing projection a *spectral*
projection.

## What has to be proved, and what does not

Nothing here needs a projection-valued measure, and nothing needs `f` to be continuous
anywhere except on the spectrum, where the gap makes it automatic.  Two facts carry the whole
statement.

**The gap in the block spectra is a gap in the spectrum**
(`spectrum_subset_union_of_blockGap`).  This is the only analytic step.  For `λ` strictly
inside `(α, α + δ)` the operator `λ − A` is bounded below by `min (λ − α) (α + δ − λ)`: it is
bounded below on `U` because the quadratic form of `A` is `≤ α` there, bounded below on `Uᗮ`
because that form is `≥ α + δ`, and the two estimates add in quadrature because `λ − A`
preserves both blocks.  A bounded-below *self-adjoint* operator is invertible, and the route
taken here is to invert `(λ − A)²` — which is positive, so Mathlib's
`isUnit_of_forall_le_norm_inner_map` applies verbatim — and then descend, since an element
whose square is a unit and which commutes with that square's inverse is itself a unit.

Note the estimates on the two blocks have *opposite signs*: `λ − A` is `≥ λ − α > 0` on `U`
and `≤ λ − α − δ < 0` on `Uᗮ`.  So `λ − A` is not semidefinite and no positivity argument
applies to it directly; that is exactly why the proof goes through its square.

**Everything else is the intertwining law.**  `U.subtypeL` intertwines `A₀` with `A`, so
`TauCeti.LinearPMap.cfc_intertwines_selfAdjoint` gives `f(A) ∘ ι_U = ι_U ∘ f(A₀)`, and `f = 1` on
`spectrum A₀` makes `f(A₀) = 1`; hence `f(A)` is the identity on `U`.  The same law on `Uᗮ`
with `f = 0` there makes `f(A)` vanish on `Uᗮ`.  An operator that is the identity on `U` and
zero on `Uᗮ` is `P_U`.

## Real and complex scalars

Davis and Kahan work on a real *or* complex Hilbert space, so both are provided.  The two
branches are separate statements rather than one over an abstract `RCLike` field, and the
reason is the functional calculus rather than the mathematics: the theorem applies `cfc` on
`E`, on `↥U` and on `↥Uᗮ`, and for an abstract scalar field none of those three
`ContinuousFunctionalCalculus ℝ (· →L[𝕜] ·) IsSelfAdjoint` instances can be synthesised, so a
generic statement would have to carry three instance blocks for a caller to discharge.  At `ℂ`
they come from Mathlib and at `ℝ` from
`ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint`, so each branch reads
cleanly.  The proofs differ only in which spectral-order bridge turns the block spectra into
quadratic-form bounds.

## Source

This is the content Davis and Kahan use in Question 10.4 of *The rotation of eigenvectors by
a perturbation. III* (SIAM J. Numer. Anal. **7** (1970) 1--46), where they take
`f(ξ) = 1` for `ξ ≤ α` and `f(ξ) = 0` for `α + δ ≤ ξ` and assert `f(A) = P`, `f(A+H) = Q`,
`f(A₀) = 1` under the `tan 2θ` hypotheses.  Their `f` is a genuine step function, undefined
between `α` and `α + δ`; the theorem below is stated for an arbitrary such `f` precisely
because the value on the gap is immaterial — no spectrum is there.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and `ForTauCeti`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti
namespace SpectralGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

section BoundedBelow

variable {A : E →L[ℂ] E} {U : Submodule ℂ E} [U.HasOrthogonalProjection]

omit [CompleteSpace E] in
/-- A quadratic-form lower bound on a *fixed* vector gives a norm lower bound on it.

The one-vector form is what the block estimate needs: neither block bound holds on all of
`E`, only on its own summand. -/
private theorem norm_lower_of_re_inner_le (T : E →L[ℂ] E) {c : ℝ} {x : E}
    (h : c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_ℂ) : c * ‖x‖ ≤ ‖T x‖ := by
  rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
  · have hx0 : x = 0 := norm_eq_zero.mp hx.symm
    simp [hx0]
  · have hcs : RCLike.re ⟪T x, x⟫_ℂ ≤ ‖T x‖ * ‖x‖ :=
      le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
    have hmul : c * ‖x‖ * ‖x‖ ≤ ‖T x‖ * ‖x‖ := by nlinarith
    exact le_of_mul_le_mul_right hmul hx

omit [CompleteSpace E] in
/-- The quadratic form of a real scalar multiple. -/
private theorem re_inner_real_smul (r : ℝ) (x : E) :
    RCLike.re ⟪r • x, x⟫_ℂ = r * ‖x‖ ^ 2 := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, RCLike.conj_ofReal,
    RCLike.re_ofReal_mul, inner_self_eq_norm_sq]

/-- An element whose square is a unit, in a monoid, is a unit: it inherits a right inverse
from the square's inverse, and a left one because it commutes with that inverse. -/
private theorem isUnit_of_isUnit_mul_self {M : Type*} [Monoid M] {a : M}
    (h : IsUnit (a * a)) : IsUnit a := by
  obtain ⟨v, hv⟩ := h
  have hcomm : Commute a ((v⁻¹ : Mˣ) : M) :=
    (hv ▸ (Commute.refl a).mul_right (Commute.refl a) : Commute a ((v : Mˣ) : M)).units_inv_right
  have hright : a * (a * ((v⁻¹ : Mˣ) : M)) = 1 := by
    rw [← mul_assoc, ← hv, v.mul_inv]
  have hleft : (a * ((v⁻¹ : Mˣ) : M)) * a = 1 := by
    rw [hcomm.eq, mul_assoc, ← hv, v.inv_mul]
  exact ⟨⟨a, a * ((v⁻¹ : Mˣ) : M), hright, hleft⟩, rfl⟩

end BoundedBelow

section Gap

variable {A : E →L[ℂ] E} {U : Submodule ℂ E} [U.HasOrthogonalProjection]
  {α δ : ℝ}

/-- **The gap between the two block spectra is a gap in the spectrum.**

If the quadratic form of the self-adjoint `A` is at most `α` on the reducing subspace `U` and
at least `α + δ` on `Uᗮ`, then no real spectral value of `A` lies strictly between.

Stated with quadratic-form hypotheses rather than block spectra because that is the form the
proof consumes; `spectrum_subset_union_of_blockGap` below packages the spectral version. -/
theorem spectrum_subset_union_of_formGap (hA : IsSelfAdjoint A)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAUperp : ∀ x ∈ Uᗮ, A x ∈ Uᗮ)
    (hlow : ∀ x ∈ U, RCLike.re ⟪A x, x⟫_ℂ ≤ α * ‖x‖ ^ 2)
    (hhigh : ∀ x ∈ Uᗮ, (α + δ) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ) :
    spectrum ℝ A ⊆ Set.Iic α ∪ Set.Ici (α + δ) := by
  intro lam hlam
  by_contra hmem
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, not_or, not_le] at hmem
  obtain ⟨hlt, hgt⟩ := hmem
  set T : E →L[ℂ] E := algebraMap ℝ (E →L[ℂ] E) lam - A with hT
  have hTapply : ∀ x : E, T x = lam • x - A x := by
    intro x
    simp [hT, Algebra.algebraMap_eq_smul_one]
  have hTsa : IsSelfAdjoint T := by
    refine IsSelfAdjoint.sub ?_ hA
    exact cfc_predicate_algebraMap lam
  have hTinner : ∀ x : E, RCLike.re ⟪T x, x⟫_ℂ = lam * ‖x‖ ^ 2 - RCLike.re ⟪A x, x⟫_ℂ := by
    intro x
    rw [hTapply, inner_sub_left, map_sub, re_inner_real_smul]
  -- `T` preserves both blocks
  have hTU : ∀ x ∈ U, T x ∈ U := by
    intro x hx
    rw [hTapply]
    exact U.sub_mem (U.smul_mem _ hx) (hAU x hx)
  have hTUperp : ∀ x ∈ Uᗮ, T x ∈ Uᗮ := by
    intro x hx
    rw [hTapply]
    exact Uᗮ.sub_mem (Uᗮ.smul_mem _ hx) (hAUperp x hx)
  -- the two one-sided estimates
  set c : ℝ := min (lam - α) (α + δ - lam) with hc
  have hcpos : 0 < c := lt_min (by linarith) (by linarith)
  have hboundU : ∀ x ∈ U, c * ‖x‖ ≤ ‖T x‖ := by
    intro x hx
    refine norm_lower_of_re_inner_le T ?_
    rw [hTinner]
    have := hlow x hx
    have hcle : c ≤ lam - α := min_le_left _ _
    nlinarith [sq_nonneg ‖x‖]
  have hboundUperp : ∀ x ∈ Uᗮ, c * ‖x‖ ≤ ‖T x‖ := by
    intro x hx
    have hneg : c * ‖x‖ ^ 2 ≤ RCLike.re ⟪(-T) x, x⟫_ℂ := by
      have hTx : RCLike.re ⟪(-T) x, x⟫_ℂ = -RCLike.re ⟪T x, x⟫_ℂ := by
        simp [inner_neg_left]
      rw [hTx, hTinner]
      have := hhigh x hx
      have hcle : c ≤ α + δ - lam := min_le_right _ _
      nlinarith [sq_nonneg ‖x‖]
    simpa using norm_lower_of_re_inner_le (-T) hneg
  -- add the two estimates in quadrature
  have hbound : ∀ x : E, c ^ 2 * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
    intro x
    obtain ⟨u, huU, w, hwU, rfl⟩ : ∃ u ∈ U, ∃ w ∈ (Uᗮ : Submodule ℂ E), x = u + w :=
      ⟨U.starProjection x, U.starProjection_apply_mem x, x - U.starProjection x,
        U.sub_starProjection_mem_orthogonal x, by abel⟩
    have horth : ⟪u, w⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp hwU u huU
    have hnormx : ‖u + w‖ ^ 2 = ‖u‖ ^ 2 + ‖w‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := ℂ), horth]
      simp
    have hTx : T (u + w) = T u + T w := map_add _ _ _
    have horthT : ⟪T u, T w⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal _ _).mp (hTUperp w hwU) (T u) (hTU u huU)
    have hnormT : ‖T (u + w)‖ ^ 2 = ‖T u‖ ^ 2 + ‖T w‖ ^ 2 := by
      rw [hTx, norm_add_sq (𝕜 := ℂ), horthT]
      simp
    have h1 := hboundU u huU
    have h2 := hboundUperp w hwU
    rw [hnormT, hnormx]
    have h1' : c ^ 2 * ‖u‖ ^ 2 ≤ ‖T u‖ ^ 2 := by
      have := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ c * ‖u‖) h1
      nlinarith
    have h2' : c ^ 2 * ‖w‖ ^ 2 ≤ ‖T w‖ ^ 2 := by
      have := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ c * ‖w‖) h2
      nlinarith
    nlinarith
  -- `T * T` is invertible, hence so is `T`
  have hTsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hTsa
  have hTTunit : IsUnit (T * T) := by
    refine ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map (𝕜 := ℂ) (T * T)
      (c := Real.toNNReal (c ^ 2)) (Real.toNNReal_pos.mpr (by positivity)) fun x => ?_
    have hinner : ⟪(T * T) x, x⟫_ℂ = ⟪T x, T x⟫_ℂ := hTsym (T x) x
    rw [hinner, inner_self_eq_norm_sq_to_K, Real.coe_toNNReal _ (by positivity)]
    refine le_trans (le_of_eq (by ring)) (le_trans (hbound x) (le_of_eq ?_))
    simp
  have hTunit : IsUnit T := isUnit_of_isUnit_mul_self hTTunit
  exact hlam hTunit

end Gap

section StepFunction

-- The continuous functional calculus of an operator on `↥U` is reached only after
-- synthesising `CStarAlgebra (↥U →L[ℂ] ↥U)`, which itself needs `CompleteSpace ↥U`; that is
-- one nesting level more than the default budget allows.  The same search succeeds unaided
-- for `E →L[ℂ] E`, where no subtype intervenes.
set_option maxSynthPendingDepth 3

variable {A : E →L[ℂ] E} {U : Submodule ℂ E} [U.HasOrthogonalProjection]

omit [CompleteSpace E] [U.HasOrthogonalProjection] in
/-- Reading an intertwining relation `ι_U ∘ A₀ = A ∘ ι_U` pointwise: `A₀` is the restriction. -/
private theorem coe_block_apply {A₀ : U →L[ℂ] U}
    (h : U.subtypeL ∘L A₀ = A ∘L U.subtypeL) (x : U) : ((A₀ x : U) : E) = A (x : E) := by
  have := ContinuousLinearMap.ext_iff.mp h x
  simpa using this

omit [U.HasOrthogonalProjection] in
/-- A block of a self-adjoint operator is self-adjoint. -/
private theorem isSelfAdjoint_block [CompleteSpace U] {A₀ : U →L[ℂ] U}
    (hA : IsSelfAdjoint A) (h : U.subtypeL ∘L A₀ = A ∘L U.subtypeL) :
    IsSelfAdjoint A₀ := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_
  have hx : ((A₀ x : U) : E) = A (x : E) := coe_block_apply h x
  have hy : ((A₀ y : U) : E) = A (y : E) := coe_block_apply h y
  have := hsym (x : E) (y : E)
  simpa [Submodule.coe_inner, hx, hy] using this

/-- **The continuous ramp cutting the gap.**  Any `f` that is `1` below `α` and `0` above
`α + δ` agrees with this on the complement of the open gap, so it inherits continuity there
without being continuous anywhere else. -/
private noncomputable def gapRamp (α δ t : ℝ) : ℝ := min 1 (max 0 ((α + δ - t) / δ))

private theorem continuous_gapRamp (α δ : ℝ) : Continuous (gapRamp α δ) := by
  unfold gapRamp
  fun_prop

private theorem eqOn_gapRamp {α δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℝ}
    (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    Set.EqOn f (gapRamp α δ) (Set.Iic α ∪ Set.Ici (α + δ)) := by
  rintro t (ht | ht)
  · rw [hf1 t ht]
    have h1 : 1 ≤ (α + δ - t) / δ := by
      rw [le_div_iff₀ hδ]
      simp only [Set.mem_Iic] at ht
      linarith
    simp only [gapRamp]
    rw [max_eq_right (by linarith), min_eq_left h1]
  · rw [hf0 t ht]
    have h0 : (α + δ - t) / δ ≤ 0 := by
      rw [div_le_iff₀ hδ]
      simp only [Set.mem_Ici] at ht
      linarith
    simp only [gapRamp]
    rw [max_eq_left h0, min_eq_right zero_le_one]

/-- **Davis--Kahan 1970, the functional-calculus identity behind Question 10.4.**

Let `A` be bounded self-adjoint, let `U` reduce it with blocks `A₀` on `U` and `A₁` on `Uᗮ`
presented by their intertwining relations, and let the two block spectra be separated:
`spectrum A₀ ⊆ (-∞, α]` and `spectrum A₁ ⊆ [α + δ, ∞)` with `δ > 0`.  Then for **every**
real function `f` that is `1` at or below `α` and `0` at or above `α + δ`,

`f(A) = P_U`.

`f` is otherwise arbitrary — in particular Davis and Kahan's discontinuous step function
qualifies.  Nothing constrains it on the open gap `(α, α + δ)` because the gap carries no
spectrum (`spectrum_subset_union_of_formGap`), which is also what makes `f` continuous where
the functional calculus reads it. -/
theorem cfc_eq_starProjection_of_blockGap [CompleteSpace U]
    [CompleteSpace (Uᗮ : Submodule ℂ E)]
    (hA : IsSelfAdjoint A)
    {A₀ : U →L[ℂ] U} {A₁ : (Uᗮ : Submodule ℂ E) →L[ℂ] (Uᗮ : Submodule ℂ E)}
    (hA₀ : U.subtypeL ∘L A₀ = A ∘L U.subtypeL)
    (hA₁ : Uᗮ.subtypeL ∘L A₁ = A ∘L Uᗮ.subtypeL)
    {α δ : ℝ} (hδ : 0 < δ)
    (hσ₀ : spectrum ℝ A₀ ⊆ Set.Iic α)
    (hσ₁ : spectrum ℝ A₁ ⊆ Set.Ici (α + δ))
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    cfc f A = U.starProjection := by
  have hA₀sa : IsSelfAdjoint A₀ := isSelfAdjoint_block hA hA₀
  have hA₁sa : IsSelfAdjoint A₁ := isSelfAdjoint_block hA hA₁
  -- the blocks are invariant subspaces
  have hAU : ∀ x ∈ U, A x ∈ U := by
    intro x hx
    rw [← coe_block_apply hA₀ ⟨x, hx⟩]
    exact (A₀ ⟨x, hx⟩).2
  have hAUperp : ∀ x ∈ Uᗮ, A x ∈ Uᗮ := by
    intro x hx
    rw [← coe_block_apply hA₁ ⟨x, hx⟩]
    exact (A₁ ⟨x, hx⟩).2
  -- the block spectra become quadratic-form bounds
  have hlow : ∀ x ∈ U, RCLike.re ⟪A x, x⟫_ℂ ≤ α * ‖x‖ ^ 2 := by
    intro x hx
    have h := TauCeti.SpectralOrder.Complex.re_inner_le_of_spectrum_subset_Iic A₀ hA₀sa hσ₀
      ⟨x, hx⟩
    simpa [Submodule.coe_norm, Submodule.coe_inner, coe_block_apply hA₀ ⟨x, hx⟩] using h
  have hhigh : ∀ x ∈ Uᗮ, (α + δ) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ := by
    intro x hx
    have h := TauCeti.SpectralOrder.Complex.le_re_inner_of_spectrum_subset_Ici A₁ hA₁sa hσ₁
      ⟨x, hx⟩
    simpa [Submodule.coe_norm, Submodule.coe_inner, coe_block_apply hA₁ ⟨x, hx⟩] using h
  -- the gap is free of spectrum, so `f` is continuous where the calculus reads it
  have hspec : spectrum ℝ A ⊆ Set.Iic α ∪ Set.Ici (α + δ) :=
    spectrum_subset_union_of_formGap hA hAU hAUperp hlow hhigh
  have hcont : ContinuousOn f (Set.Iic α ∪ Set.Ici (α + δ)) :=
    ((continuous_gapRamp α δ).continuousOn).congr (eqOn_gapRamp hδ hf1 hf0)
  have hσ₁' : spectrum ℝ A₁ ⊆ Set.Iic α ∪ Set.Ici (α + δ) := fun t ht =>
    Or.inr (hσ₁ ht)
  have hσ₀' : spectrum ℝ A₀ ⊆ Set.Iic α ∪ Set.Ici (α + δ) := fun t ht =>
    Or.inl (hσ₀ ht)
  -- the two block values of the calculus
  have hblock₀ : cfc f A₀ = 1 := by
    rw [cfc_congr (g := fun _ : ℝ => (1 : ℝ)) (a := A₀) fun t ht => hf1 t (hσ₀ ht)]
    exact cfc_one ℝ A₀
  have hblock₁ : cfc f A₁ = 0 := by
    rw [cfc_congr (g := fun _ : ℝ => (0 : ℝ)) (a := A₁) fun t ht => hf0 t (hσ₁ ht)]
    exact cfc_zero ℝ A₁
  -- transport them along the two inclusions
  have hint₀ : U.subtypeL ∘L cfc f A₀ = cfc f A ∘L U.subtypeL :=
    TauCeti.LinearPMap.cfc_intertwines_selfAdjoint hA hA₀sa hA₀
      (hcont.mono (Set.union_subset hspec hσ₀'))
  have hint₁ : Uᗮ.subtypeL ∘L cfc f A₁ = cfc f A ∘L Uᗮ.subtypeL :=
    TauCeti.LinearPMap.cfc_intertwines_selfAdjoint hA hA₁sa hA₁
      (hcont.mono (Set.union_subset hspec hσ₁'))
  have hfixU : ∀ x ∈ U, cfc f A x = x := by
    intro x hx
    have := ContinuousLinearMap.ext_iff.mp hint₀ ⟨x, hx⟩
    simpa [hblock₀] using this.symm
  have hkillUperp : ∀ x ∈ Uᗮ, cfc f A x = 0 := by
    intro x hx
    have := ContinuousLinearMap.ext_iff.mp hint₁ ⟨x, hx⟩
    simpa [hblock₁] using this.symm
  -- an operator that fixes `U` and kills `Uᗮ` is the projection onto `U`
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨u, huU, w, hwU, rfl⟩ : ∃ u ∈ U, ∃ w ∈ (Uᗮ : Submodule ℂ E), x = u + w :=
    ⟨U.starProjection x, U.starProjection_apply_mem x, x - U.starProjection x,
      U.sub_starProjection_mem_orthogonal x, by abel⟩
  have hPu : U.starProjection u = u := Submodule.starProjection_eq_self_iff.mpr huU
  have hPw : U.starProjection w = 0 :=
    Submodule.eq_starProjection_of_mem_orthogonal' U.zero_mem hwU (by simp)
  rw [map_add, hfixU u huU, hkillUperp w hwU, add_zero, map_add, hPu, hPw, add_zero]

end StepFunction

/-! ## The real branch

The same two theorems over a real Hilbert space.  Only the spectral-order bridge changes:
`TauCeti.SpectralOrder.Real.upperFormBoundOn_top_of_spectrum_subset_Iic` and its lower twin
replace the complex `re_inner_le_of_spectrum_subset_Iic` / `le_re_inner_of_spectrum_subset_Ici`.
Everything else — the lower bound on `λ − A`, the descent from `(λ − A)²`, the ramp that makes
`f` continuous on the spectrum, and the intertwining law — is the same argument. -/

section RealScalars

set_option maxSynthPendingDepth 3

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Real twin of `norm_lower_of_re_inner_le`. -/
private theorem norm_lower_of_re_inner_le_real (T : F →L[ℝ] F) {c : ℝ} {x : F}
    (h : c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_ℝ) : c * ‖x‖ ≤ ‖T x‖ := by
  rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
  · have hx0 : x = 0 := norm_eq_zero.mp hx.symm
    simp [hx0]
  · have hcs : RCLike.re ⟪T x, x⟫_ℝ ≤ ‖T x‖ * ‖x‖ :=
      le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
    have hmul : c * ‖x‖ * ‖x‖ ≤ ‖T x‖ * ‖x‖ := by nlinarith
    exact le_of_mul_le_mul_right hmul hx

omit [CompleteSpace F] in
/-- Real twin of `re_inner_real_smul`. -/
private theorem re_inner_real_smul_real (r : ℝ) (x : F) :
    RCLike.re ⟪r • x, x⟫_ℝ = r * ‖x‖ ^ 2 := by
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp

omit [CompleteSpace F] in
/-- Real twin of `coe_block_apply`. -/
private theorem coe_block_apply_real {A : F →L[ℝ] F} {U : Submodule ℝ F}
    {A₀ : U →L[ℝ] U} (h : U.subtypeL ∘L A₀ = A ∘L U.subtypeL) (x : U) :
    ((A₀ x : U) : F) = A (x : F) := by
  have := ContinuousLinearMap.ext_iff.mp h x
  simpa using this

/-- Real twin of `isSelfAdjoint_block`. -/
private theorem isSelfAdjoint_block_real {A : F →L[ℝ] F} {U : Submodule ℝ F}
    [CompleteSpace U] {A₀ : U →L[ℝ] U} (hA : IsSelfAdjoint A)
    (h : U.subtypeL ∘L A₀ = A ∘L U.subtypeL) : IsSelfAdjoint A₀ := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_
  have hx : ((A₀ x : U) : F) = A (x : F) := coe_block_apply_real h x
  have hy : ((A₀ y : U) : F) = A (y : F) := coe_block_apply_real h y
  have := hsym (x : F) (y : F)
  simpa [Submodule.coe_inner, hx, hy] using this

/-- **The real twin of `spectrum_subset_union_of_formGap`.** -/
theorem spectrum_subset_union_of_formGap_real {A : F →L[ℝ] F} {U : Submodule ℝ F}
    [U.HasOrthogonalProjection] {α δ : ℝ} (hA : IsSelfAdjoint A)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAUperp : ∀ x ∈ Uᗮ, A x ∈ Uᗮ)
    (hlow : ∀ x ∈ U, RCLike.re ⟪A x, x⟫_ℝ ≤ α * ‖x‖ ^ 2)
    (hhigh : ∀ x ∈ Uᗮ, (α + δ) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℝ) :
    spectrum ℝ A ⊆ Set.Iic α ∪ Set.Ici (α + δ) := by
  intro lam hlam
  by_contra hmem
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, not_or, not_le] at hmem
  obtain ⟨hlt, hgt⟩ := hmem
  set T : F →L[ℝ] F := algebraMap ℝ (F →L[ℝ] F) lam - A with hT
  have hTapply : ∀ x : F, T x = lam • x - A x := by
    intro x
    simp [hT, Algebra.algebraMap_eq_smul_one]
  have hTsa : IsSelfAdjoint T :=
    (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all lam)).sub hA
  have hTinner : ∀ x : F, RCLike.re ⟪T x, x⟫_ℝ = lam * ‖x‖ ^ 2 - RCLike.re ⟪A x, x⟫_ℝ := by
    intro x
    rw [hTapply, inner_sub_left, map_sub, re_inner_real_smul_real]
  have hTU : ∀ x ∈ U, T x ∈ U := by
    intro x hx
    rw [hTapply]
    exact U.sub_mem (U.smul_mem _ hx) (hAU x hx)
  have hTUperp : ∀ x ∈ Uᗮ, T x ∈ Uᗮ := by
    intro x hx
    rw [hTapply]
    exact Uᗮ.sub_mem (Uᗮ.smul_mem _ hx) (hAUperp x hx)
  set c : ℝ := min (lam - α) (α + δ - lam) with hc
  have hcpos : 0 < c := lt_min (by linarith) (by linarith)
  have hboundU : ∀ x ∈ U, c * ‖x‖ ≤ ‖T x‖ := by
    intro x hx
    refine norm_lower_of_re_inner_le_real T ?_
    rw [hTinner]
    have := hlow x hx
    have hcle : c ≤ lam - α := min_le_left _ _
    nlinarith [sq_nonneg ‖x‖]
  have hboundUperp : ∀ x ∈ Uᗮ, c * ‖x‖ ≤ ‖T x‖ := by
    intro x hx
    have hneg : c * ‖x‖ ^ 2 ≤ RCLike.re ⟪(-T) x, x⟫_ℝ := by
      have hTx : RCLike.re ⟪(-T) x, x⟫_ℝ = -RCLike.re ⟪T x, x⟫_ℝ := by
        simp [inner_neg_left]
      rw [hTx, hTinner]
      have := hhigh x hx
      have hcle : c ≤ α + δ - lam := min_le_right _ _
      nlinarith [sq_nonneg ‖x‖]
    simpa using norm_lower_of_re_inner_le_real (-T) hneg
  have hbound : ∀ x : F, c ^ 2 * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
    intro x
    obtain ⟨u, huU, w, hwU, rfl⟩ : ∃ u ∈ U, ∃ w ∈ (Uᗮ : Submodule ℝ F), x = u + w :=
      ⟨U.starProjection x, U.starProjection_apply_mem x, x - U.starProjection x,
        U.sub_starProjection_mem_orthogonal x, by abel⟩
    have horth : ⟪u, w⟫_ℝ = 0 := (Submodule.mem_orthogonal _ _).mp hwU u huU
    have hnormx : ‖u + w‖ ^ 2 = ‖u‖ ^ 2 + ‖w‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := ℝ), horth]
      simp
    have hTx : T (u + w) = T u + T w := map_add _ _ _
    have horthT : ⟪T u, T w⟫_ℝ = 0 :=
      (Submodule.mem_orthogonal _ _).mp (hTUperp w hwU) (T u) (hTU u huU)
    have hnormT : ‖T (u + w)‖ ^ 2 = ‖T u‖ ^ 2 + ‖T w‖ ^ 2 := by
      rw [hTx, norm_add_sq (𝕜 := ℝ), horthT]
      simp
    have h1 := hboundU u huU
    have h2 := hboundUperp w hwU
    rw [hnormT, hnormx]
    have h1' : c ^ 2 * ‖u‖ ^ 2 ≤ ‖T u‖ ^ 2 := by
      have := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ c * ‖u‖) h1
      nlinarith
    have h2' : c ^ 2 * ‖w‖ ^ 2 ≤ ‖T w‖ ^ 2 := by
      have := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ c * ‖w‖) h2
      nlinarith
    nlinarith
  have hTsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hTsa
  have hTTunit : IsUnit (T * T) := by
    refine ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map (𝕜 := ℝ) (T * T)
      (c := Real.toNNReal (c ^ 2)) (Real.toNNReal_pos.mpr (by positivity)) fun x => ?_
    have hinner : ⟪(T * T) x, x⟫_ℝ = ⟪T x, T x⟫_ℝ := hTsym (T x) x
    rw [hinner, inner_self_eq_norm_sq_to_K, Real.coe_toNNReal _ (by positivity)]
    refine le_trans (le_of_eq (by ring)) (le_trans (hbound x) (le_of_eq ?_))
    simp
  exact hlam (isUnit_of_isUnit_mul_self hTTunit)

/-- **The real twin of `cfc_eq_starProjection_of_blockGap`.** -/
theorem cfc_eq_starProjection_of_blockGap_real {A : F →L[ℝ] F} {U : Submodule ℝ F}
    [U.HasOrthogonalProjection] [CompleteSpace U] [CompleteSpace (Uᗮ : Submodule ℝ F)]
    (hA : IsSelfAdjoint A)
    {A₀ : U →L[ℝ] U} {A₁ : (Uᗮ : Submodule ℝ F) →L[ℝ] (Uᗮ : Submodule ℝ F)}
    (hA₀ : U.subtypeL ∘L A₀ = A ∘L U.subtypeL)
    (hA₁ : Uᗮ.subtypeL ∘L A₁ = A ∘L Uᗮ.subtypeL)
    {α δ : ℝ} (hδ : 0 < δ)
    (hσ₀ : spectrum ℝ A₀ ⊆ Set.Iic α)
    (hσ₁ : spectrum ℝ A₁ ⊆ Set.Ici (α + δ))
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    cfc f A = U.starProjection := by
  have hA₀sa : IsSelfAdjoint A₀ := isSelfAdjoint_block_real hA hA₀
  have hA₁sa : IsSelfAdjoint A₁ := isSelfAdjoint_block_real hA hA₁
  have hAU : ∀ x ∈ U, A x ∈ U := by
    intro x hx
    rw [← coe_block_apply_real hA₀ ⟨x, hx⟩]
    exact (A₀ ⟨x, hx⟩).2
  have hAUperp : ∀ x ∈ Uᗮ, A x ∈ Uᗮ := by
    intro x hx
    rw [← coe_block_apply_real hA₁ ⟨x, hx⟩]
    exact (A₁ ⟨x, hx⟩).2
  have hlow : ∀ x ∈ U, RCLike.re ⟪A x, x⟫_ℝ ≤ α * ‖x‖ ^ 2 := by
    intro x hx
    have h := TauCeti.SpectralOrder.Real.upperFormBoundOn_top_of_spectrum_subset_Iic A₀
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA₀sa) hσ₀ ⟨x, hx⟩
      Submodule.mem_top
    simpa [Submodule.coe_norm, Submodule.coe_inner, coe_block_apply_real hA₀ ⟨x, hx⟩] using h
  have hhigh : ∀ x ∈ Uᗮ, (α + δ) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℝ := by
    intro x hx
    have h := TauCeti.SpectralOrder.Real.lowerFormBoundOn_top_of_spectrum_subset_Ici A₁
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA₁sa) hσ₁ ⟨x, hx⟩
      Submodule.mem_top
    simpa [Submodule.coe_norm, Submodule.coe_inner, coe_block_apply_real hA₁ ⟨x, hx⟩] using h
  have hspec : spectrum ℝ A ⊆ Set.Iic α ∪ Set.Ici (α + δ) :=
    spectrum_subset_union_of_formGap_real hA hAU hAUperp hlow hhigh
  have hcont : ContinuousOn f (Set.Iic α ∪ Set.Ici (α + δ)) :=
    ((continuous_gapRamp α δ).continuousOn).congr (eqOn_gapRamp hδ hf1 hf0)
  have hσ₀' : spectrum ℝ A₀ ⊆ Set.Iic α ∪ Set.Ici (α + δ) := fun t ht => Or.inl (hσ₀ ht)
  have hσ₁' : spectrum ℝ A₁ ⊆ Set.Iic α ∪ Set.Ici (α + δ) := fun t ht => Or.inr (hσ₁ ht)
  have hblock₀ : cfc f A₀ = 1 := by
    rw [cfc_congr (g := fun _ : ℝ => (1 : ℝ)) (a := A₀) fun t ht => hf1 t (hσ₀ ht)]
    exact cfc_one ℝ A₀
  have hblock₁ : cfc f A₁ = 0 := by
    rw [cfc_congr (g := fun _ : ℝ => (0 : ℝ)) (a := A₁) fun t ht => hf0 t (hσ₁ ht)]
    exact cfc_zero ℝ A₁
  have hint₀ : U.subtypeL ∘L cfc f A₀ = cfc f A ∘L U.subtypeL :=
    TauCeti.LinearPMap.cfc_intertwines_selfAdjoint hA hA₀sa hA₀
      (hcont.mono (Set.union_subset hspec hσ₀'))
  have hint₁ : Uᗮ.subtypeL ∘L cfc f A₁ = cfc f A ∘L Uᗮ.subtypeL :=
    TauCeti.LinearPMap.cfc_intertwines_selfAdjoint hA hA₁sa hA₁
      (hcont.mono (Set.union_subset hspec hσ₁'))
  have hfixU : ∀ x ∈ U, cfc f A x = x := by
    intro x hx
    have := ContinuousLinearMap.ext_iff.mp hint₀ ⟨x, hx⟩
    simpa [hblock₀] using this.symm
  have hkillUperp : ∀ x ∈ Uᗮ, cfc f A x = 0 := by
    intro x hx
    have := ContinuousLinearMap.ext_iff.mp hint₁ ⟨x, hx⟩
    simpa [hblock₁] using this.symm
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨u, huU, w, hwU, rfl⟩ : ∃ u ∈ U, ∃ w ∈ (Uᗮ : Submodule ℝ F), x = u + w :=
    ⟨U.starProjection x, U.starProjection_apply_mem x, x - U.starProjection x,
      U.sub_starProjection_mem_orthogonal x, by abel⟩
  have hPu : U.starProjection u = u := Submodule.starProjection_eq_self_iff.mpr huU
  have hPw : U.starProjection w = 0 :=
    Submodule.eq_starProjection_of_mem_orthogonal' U.zero_mem hwU (by simp)
  rw [map_add, hfixU u huU, hkillUperp w hwU, add_zero, map_add, hPu, hPw, add_zero]

end RealScalars

end SpectralGap
end TauCeti
