/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointResolvent

/-!
# A self-adjoint operator bounded below at a real point

If `A` is self-adjoint, `z` is real, and `c ‖x‖ ≤ ‖A x - z x‖` on the domain,
then `z` lies in the resolvent set.

`SelfAdjointResolvent.lean` proves the *non-real* case, where the lower bound
comes for free as `|Im z|`.  Its three steps — injectivity, closed range, dense
range — use only the bound, so they generalise; what does not generalise is the
bound's source.  At a real point there is none, so it becomes a hypothesis that
the caller earns.

That is the shape a spectral-gap argument wants: prove an estimate, obtain a
resolvent point, and let `diag_eq_zero_of_subset_resolventSet` turn resolvent
points into a statement about *every* vector's diagonal measure at once.

Realness is used in exactly one place, the dense-range step.  For non-real `z`
the argument is "a self-adjoint operator has no non-real eigenvalue".  Here
`conj z = z`, so a vector orthogonal to the range is an honest eigenvector at
`z`, and the lower bound kills it directly.

## Sources

*Follows nothing in particular*: the real-point case of a resolvent criterion, factored
so that the caller supplies the lower bound the non-real case gets for free.

## Provenance

*New.*  The closed-range argument follows `isClosed_range_shiftMap`, with the
lower bound abstracted out of it.
-/

public section

open scoped InnerProductSpace

namespace TauCeti
namespace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {A : E →ₗ.[ℂ] E} {z : ℂ} {c : ℝ}

omit [CompleteSpace E] in
/-- A lower bound makes `A - z` injective. -/
theorem injective_shiftMap_of_lower_bound (hc : 0 < c)
    (hbd : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x - z • (x : E)‖) :
    Function.Injective (shiftMap A z) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have h := hbd x
  rw [show A x - z • (x : E) = shiftMap A z x from rfl, hx, norm_zero] at h
  have hx0 : ‖(x : E)‖ = 0 :=
    le_antisymm (by nlinarith [norm_nonneg ((x : E))]) (norm_nonneg _)
  exact Subtype.ext (by simpa using hx0)

/-! `isClosed_range_shiftMap_of_lower_bound` moved to
`LinearPMap/SelfAdjointResolvent.lean` on 2026-07-30: that module proves the
`z.im ≠ 0` case of the same statement and could not cite this one, since this
file is the one that does the importing.  Same namespace, so no consumer
changed.

(The previous wording began a line with the word "import", which
`check_dependency_layers.py` reads as an import statement — it reported this
module as importing a package called `runs`.  Prose inside a Lean file is
scanned too.) -/

/-- **Dense range, at a real point.**  A vector orthogonal to the range of
`A - z` is an eigenvector at `z` — this is where `conj z = z` is used — and the
lower bound kills it. -/
theorem eq_zero_of_orthogonal_shiftRange_of_real (hA : IsSelfAdjoint A)
    (hzre : (starRingEnd ℂ) z = z) (hc : 0 < c)
    (hbd : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x - z • (x : E)‖)
    {y : E} (hy : ∀ x : A.domain, ⟪y, A x - z • (x : E)⟫_ℂ = 0) : y = 0 := by
  have hdense : Dense (A.domain : Set E) := hA.dense_domain
  have hEq : ∀ x : A.domain, ⟪(starRingEnd ℂ) z • y, (x : E)⟫_ℂ = ⟪y, A x⟫_ℂ :=
    inner_conj_smul_eq_of_orthogonal_shiftRange hy
  have hmem : y ∈ (_root_.LinearPMap.adjoint A).domain :=
    _root_.LinearPMap.mem_adjoint_domain_of_exists _ ⟨(starRingEnd ℂ) z • y, hEq⟩
  have hmemA : y ∈ A.domain := by
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at hmem
  have hadj : _root_.LinearPMap.adjoint A ⟨y, hmem⟩ = (starRingEnd ℂ) z • y :=
    _root_.LinearPMap.adjoint_apply_eq hdense ⟨y, hmem⟩ hEq
  have hAy : A ⟨y, hmemA⟩ = z • y := by
    have htrans := (_root_.LinearPMap.ext_iff.mp
      (_root_.LinearPMap.isSelfAdjoint_def.mp hA)).2 (x := y) (hf := hmem) (hg := hmemA)
    rw [← htrans, hadj, hzre]
  have h := hbd ⟨y, hmemA⟩
  rw [hAy, sub_self, norm_zero] at h
  have hy0 : ‖y‖ = 0 := le_antisymm (by nlinarith [norm_nonneg y]) (norm_nonneg _)
  simpa using hy0

/-- **A real point with a lower bound is a resolvent point.** -/
theorem mem_resolventSet_of_lower_bound (hA : IsSelfAdjoint A)
    (hzre : (starRingEnd ℂ) z = z) (hc : 0 < c)
    (hbd : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x - z • (x : E)‖) :
    z ∈ resolventSet A := by
  have hinj := injective_shiftMap_of_lower_bound hc hbd
  have hclosed := isClosed_range_shiftMap_of_lower_bound hA hc hbd
  set K : Submodule ℂ E := LinearMap.range (shiftMap A z) with hK
  have hKclosed : IsClosed (K : Set E) := hclosed
  have hproj : K.HasOrthogonalProjection :=
    haveI : CompleteSpace K := hKclosed.completeSpace_coe
    inferInstance
  have hperp : Kᗮ = ⊥ :=
    orthogonal_range_shiftMap_eq_bot fun _ hy =>
      eq_zero_of_orthogonal_shiftRange_of_real hA hzre hc hbd hy
  have hKtop : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hperp
  have hsurj : Function.Surjective (shiftMap A z) := by
    intro y
    have hyK : y ∈ K := hKtop ▸ Submodule.mem_top
    exact hyK
  -- the algebraic inverse, made bounded by the same estimate.  The canonical resolvent
  -- inverts `z • I - A`, which is `-(shiftMap A z)`; negation preserves bijectivity.
  set sm : A.domain →ₗ[ℂ] E := -(shiftMap A z) with hsm
  have hsmapp : ∀ x : A.domain, sm x = z • (x : E) - A x := by
    intro x
    rw [hsm]
    simp only [LinearMap.neg_apply, shiftMap_apply]
    module
  have hinj' : Function.Injective sm :=
    fun a b hab => hinj (neg_injective (by simpa [hsm] using hab))
  have hsurj' : Function.Surjective sm := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (-y)
    exact ⟨x, by rw [hsm]; simp [hx]⟩
  set e : A.domain ≃ₗ[ℂ] E := LinearEquiv.ofBijective sm ⟨hinj', hsurj'⟩ with he
  have heapp : ∀ x : A.domain, e x = z • (x : E) - A x := hsmapp
  -- Stated in exactly the shape `LinearMap.mkContinuous` expects below.  The `Subtype.val`
  -- form is only definitionally that shape, and the resulting `mkContinuous` term is then
  -- not type-correct at `implicit` transparency, which stops `simp` from firing on it.
  have hinvbd : ∀ φ : E,
      ‖(A.domain.subtype.comp (e.symm : E →ₗ[ℂ] A.domain)) φ‖ ≤ c⁻¹ * ‖φ‖ := by
    intro φ
    change ‖((e.symm φ : A.domain) : E)‖ ≤ c⁻¹ * ‖φ‖
    have h := hbd (e.symm φ)
    have hflip : A (e.symm φ) - z • ((e.symm φ : A.domain) : E) = -φ := by
      have h0 := e.apply_symm_apply φ
      rw [heapp] at h0
      linear_combination (norm := module) -h0
    rw [hflip, norm_neg] at h
    rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact h
  refine mem_resolventSet_iff.mpr ⟨LinearMap.mkContinuous
    ((A.domain.subtype).comp (e.symm : E →ₗ[ℂ] A.domain)) c⁻¹ hinvbd,
    fun φ => (e.symm φ).2, ?_, ?_⟩
  · intro φ
    have h := e.apply_symm_apply φ
    rw [heapp] at h
    exact h
  · intro ψ
    have hsym : e ψ = z • (ψ : E) - A ψ := heapp ψ
    simp only [LinearMap.mkContinuous_apply, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype]
    rw [← hsym]
    exact congrArg Subtype.val (e.symm_apply_apply ψ)

end LinearPMap
end TauCeti
