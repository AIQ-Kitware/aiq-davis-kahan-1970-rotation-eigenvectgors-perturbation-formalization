/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.InfiniteDimensional.Sylvester.Basic
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
import DavisKahan.SpectralTheory.AbstractSpectrum
import DavisKahan.SinTheta.SpectralBridge

/-!
# Current-API restriction layer for the infinite-dimensional sine theorems

This module replaces two interfaces removed during the Mathlib update:

* codomain restriction of a bounded map to a proved containing subspace;
* restriction of a reducing bounded operator to the orthogonal summand.

It also records the rectangular block equations and spectral transport lemmas
used by `SinTheta/General.lean`.  The definitions are explicit, so later source
modules do not depend on stale convenience constructors.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace
open TauCeti.DavisKahan.ExactSinTheta

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- Restrict the codomain of a bounded map when every value lies in the target
subspace. -/
noncomputable def codRestrictTo
    (T : E →L[𝕜] F) (M : Submodule 𝕜 F)
    (hT : ∀ x, T x ∈ M) : E →L[𝕜] M :=
  T.codRestrict M hT

omit [CompleteSpace E] [CompleteSpace F] in
/-- Corestricting the codomain leaves the value unchanged on underlying vectors. -/
@[simp]
theorem coe_codRestrictTo_apply
    (T : E →L[𝕜] F) (M : Submodule 𝕜 F)
    (hT : ∀ x, T x ∈ M) (x : E) :
    ((codRestrictTo T M hT x : M) : F) = T x :=
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- Codomain restriction to a subspace containing the range preserves the
operator norm.  Completeness of the domain is not used, so the lemma also
applies when the domain is a bare subspace carrier. -/
theorem norm_codRestrictTo_eq
    (T : E →L[𝕜] F) (M : Submodule 𝕜 F)
    (hT : ∀ x, T x ∈ M) :
    ‖codRestrictTo T M hT‖ = ‖T‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) ?_
    intro x
    simpa [codRestrictTo] using T.le_opNorm x
  · refine ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (codRestrictTo T M hT)) ?_
    intro x
    have hx := (codRestrictTo T M hT).le_opNorm x
    simpa [codRestrictTo] using hx

/-- The actual bounded restriction to the selected summand of a reducing
subspace. -/
noncomputable def restrictToReducingSubspace
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (hU : Reduces A U) : U →L[𝕜] U :=
  A.restrict hU.1

omit [CompleteSpace E] in
/-- The restriction to a reducing subspace agrees with `A` on underlying vectors. -/
@[simp]
theorem restrictToReducingSubspace_apply
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (hU : Reduces A U) (x : U) :
    ((restrictToReducingSubspace A U hU x : U) : E) = A (x : E) :=
  rfl

omit [CompleteSpace E] in
/-- Symmetry descends to the selected reducing restriction. -/
theorem _root_.TauCeti.DavisKahan.IsSelfAdjointOperator.restrictToReducingSubspace
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    (U : Submodule 𝕜 E) (hU : Reduces A U) :
    IsSelfAdjointOperator (restrictToReducingSubspace A U hU) :=
  LinearMap.IsSymmetric.restrict_invariant hA hU.1

omit [CompleteSpace E] in
/-- The theorem-facing restricted spectrum of the selected summand is the real
spectrum of the explicit restriction. -/
theorem restrictedSpectrum_eq_realSpectrum_restrictToReducingSubspace
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (hU : Reduces A U) :
    restrictedSpectrum A U =
      realSpectrum (restrictToReducingSubspace A U hU) := by
  rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_eq_restrictionSpectrum
    A U hU.1]
  rfl

/-- The actual bounded restriction to the orthogonal summand of a reducing
subspace. -/
noncomputable def restrictToOrthogonal
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (hU : Reduces A U) : Uᗮ →L[𝕜] Uᗮ :=
  A.restrict hU.2

omit [CompleteSpace E] in
/-- The restriction to the orthogonal complement agrees with `A` on underlying vectors. -/
@[simp]
theorem restrictToOrthogonal_apply
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (hU : Reduces A U) (x : Uᗮ) :
    ((restrictToOrthogonal A U hU x : Uᗮ) : E) = A (x : E) :=
  rfl

omit [CompleteSpace E] in
/-- Symmetry descends to the orthogonal reducing restriction. -/
theorem _root_.TauCeti.DavisKahan.IsSelfAdjointOperator.restrictToOrthogonal
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    (U : Submodule 𝕜 E) (hU : Reduces A U) :
    IsSelfAdjointOperator (restrictToOrthogonal A U hU) :=
  LinearMap.IsSymmetric.restrict_invariant hA hU.2

omit [CompleteSpace E] in
/-- The theorem-facing restricted spectrum of the orthogonal summand is the
real spectrum of the explicit restriction. -/
theorem restrictedSpectrum_orthogonal_eq
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (hU : Reduces A U) :
    restrictedSpectrum A Uᗮ = realSpectrum (restrictToOrthogonal A U hU) := by
  rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_eq_restrictionSpectrum
    A Uᗮ hU.2]
  rfl

omit [CompleteSpace E] in
/-- The restriction to the full space carries the original real spectrum.  This
is the `RCLike`-general companion of the `ℂ`-only lemma of the same name in
`OrderedSemigroup`; it is proved here by conjugating the top-restriction through
`Submodule.topContEquiv` and invoking spectral invariance of an algebra
equivalence.  Completeness of the ambient space is not required, so the lemma
also applies to the restricted operators living on non-`CompleteSpace`
subspace carriers. -/
theorem restrictedSpectrum_top_eq_realSpectrum_general (A : E →L[𝕜] E) :
    TauCeti.DavisKahan.Foundation.restrictedSpectrum A
        (⊤ : Submodule 𝕜 E) =
      TauCeti.DavisKahan.Foundation.realSpectrum A := by
  have hInv :
      TauCeti.DavisKahan.Foundation.InvariantFor A (⊤ : Submodule 𝕜 E) :=
    fun x _ => Submodule.mem_top
  have hbridge :=
    TauCeti.DavisKahan.Foundation.restrictedSpectrum_eq_restrictionSpectrum
      A ⊤ hInv
  have hconj :
      (Submodule.topContEquiv : (⊤ : Submodule 𝕜 E) ≃L[𝕜] E).conjContinuousAlgEquiv
        (A.restrict hInv) = A := by
    ext x
    rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
    show ((A.restrict hInv) ((Submodule.topContEquiv :
      (⊤ : Submodule 𝕜 E) ≃L[𝕜] E).symm x) : E) = A x
    rw [ContinuousLinearMap.coe_restrict_apply]
    rfl
  have hspec : spectrum 𝕜 (A.restrict hInv) = spectrum 𝕜 A := by
    conv_rhs => rw [← hconj]
    exact (AlgEquiv.spectrum_eq
      ((Submodule.topContEquiv : (⊤ : Submodule 𝕜 E) ≃L[𝕜] E).conjContinuousAlgEquiv)
      (A.restrict hInv)).symm
  rw [hbridge]
  ext r
  simp only [TauCeti.DavisKahan.Foundation.realSpectrum,
    Set.mem_ofPred_eq, hspec]

omit [CompleteSpace E] in
/-- The closed-operator real resolvent set of a bounded operator's full-domain
realization is exactly the invertibility locus of `X - lam` in the bounded
operator algebra. -/
theorem mem_realResolventSet_ofBounded_iff (X : E →L[𝕜] E) (lam : ℝ) :
    lam ∈ TauCeti.LinearPMap.realResolventSet
        ((X.toLinearMap.toPMap ⊤)) ↔
      IsUnit (X - (lam : 𝕜) • (1 : E →L[𝕜] E)) := by
  constructor
  · rintro ⟨R, hleft, hright⟩
    refine ⟨⟨X - (lam : 𝕜) • (1 : E →L[𝕜] E), R, ?_, ?_⟩, rfl⟩
    · apply ContinuousLinearMap.ext
      intro y
      obtain ⟨h, hy⟩ := hright y
      have hy' : X (R y) - (lam : 𝕜) • R y = y := hy
      simpa [mul_apply_eq_comp, sub_apply,
        smul_apply, one_apply_eq_self] using hy'
    · apply ContinuousLinearMap.ext
      intro x
      have hx' : R (X x - (lam : 𝕜) • x) = x := hleft ⟨x, Submodule.mem_top⟩
      simpa [mul_apply_eq_comp, sub_apply,
        smul_apply, one_apply_eq_self] using hx'
  · rintro ⟨u, hu⟩
    have hval : (↑u : E →L[𝕜] E) = X - (lam : 𝕜) • (1 : E →L[𝕜] E) := hu
    refine ⟨↑u⁻¹, ?_, ?_⟩
    · intro x
      show (↑u⁻¹ : E →L[𝕜] E) (X (x : E) - (lam : 𝕜) • (x : E)) = (x : E)
      have hinv : (↑u⁻¹ : E →L[𝕜] E) * (X - (lam : 𝕜) • (1 : E →L[𝕜] E)) = 1 := by
        rw [← hval]; exact u.inv_mul
      have hpt := ContinuousLinearMap.ext_iff.mp hinv (x : E)
      simpa [mul_apply_eq_comp, sub_apply,
        smul_apply, one_apply_eq_self] using hpt
    · intro y
      refine ⟨Submodule.mem_top, ?_⟩
      show X ((↑u⁻¹ : E →L[𝕜] E) y) - (lam : 𝕜) • ((↑u⁻¹ : E →L[𝕜] E) y) = y
      have hinv : (X - (lam : 𝕜) • (1 : E →L[𝕜] E)) * (↑u⁻¹ : E →L[𝕜] E) = 1 := by
        rw [← hval]; exact u.mul_inv
      have hpt := ContinuousLinearMap.ext_iff.mp hinv y
      simpa [mul_apply_eq_comp, sub_apply,
        smul_apply, one_apply_eq_self] using hpt

omit [CompleteSpace E] in
/-- The bounded-realization real spectrum used by the `sin Θ` interval/exterior
bridge coincides with the Banach-algebra real spectrum used by the abstract
separation predicates. -/
theorem boundedRealSpectrum_eq_realSpectrum (X : E →L[𝕜] E) :
    TauCeti.DavisKahan.ExactSinTheta.boundedRealSpectrum X =
      TauCeti.DavisKahan.Foundation.realSpectrum X := by
  ext lam
  show lam ∈ (TauCeti.LinearPMap.realResolventSet
      ((X.toLinearMap.toPMap ⊤)))ᶜ ↔
    (lam : 𝕜) ∈ spectrum 𝕜 X
  rw [Set.mem_compl_iff, mem_realResolventSet_ofBounded_iff, spectrum.mem_iff,
    Algebra.algebraMap_eq_smul_one, ← IsUnit.neg_iff, neg_sub]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Orthogonal projection on the left is contractive in operator norm. -/
theorem projection_comp_opNorm_le
    (U : Submodule 𝕜 F) [U.HasOrthogonalProjection]
    (T : E →L[𝕜] F) :
    ‖U.starProjection ∘L T‖ ≤ ‖T‖ := by
  calc
    ‖U.starProjection ∘L T‖ ≤ ‖U.starProjection‖ * ‖T‖ :=
      U.starProjection.opNorm_comp_le T
    _ ≤ 1 * ‖T‖ := by
      gcongr
      exact U.starProjection_norm_le
    _ = ‖T‖ := one_mul _

omit [CompleteSpace E] [CompleteSpace F] in
/-- The rectangular projection--operator--inclusion block is contractive. -/
theorem restricted_projection_sandwich_norm_le
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (V : Submodule 𝕜 F) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] F) :
    ‖codRestrictTo
        (Vᗮ.starProjection ∘L T ∘L U.subtypeL) Vᗮ
        (fun _x => Vᗮ.starProjection_apply_mem _)‖ ≤ ‖T‖ := by
  -- Explicit arguments: with the operator left as a metavariable, `rw` cannot solve it from
  -- the membership proof, whose type is only definitionally the expected one.
  rw [norm_codRestrictTo_eq (Vᗮ.starProjection ∘L T ∘L U.subtypeL) Vᗮ
    (fun x => Vᗮ.starProjection_apply_mem _)]
  calc
    ‖Vᗮ.starProjection ∘L T ∘L U.subtypeL‖
        ≤ ‖Vᗮ.starProjection‖ * ‖T‖ * ‖U.subtypeL‖ := by
          refine (Vᗮ.starProjection.opNorm_comp_le (T ∘L U.subtypeL)).trans ?_
          rw [mul_assoc]
          gcongr
          exact T.opNorm_comp_le U.subtypeL
    _ ≤ 1 * ‖T‖ * 1 := by
      gcongr
      · exact Vᗮ.starProjection_norm_le
      · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
        intro x
        simp
    _ = ‖T‖ := by ring

omit [CompleteSpace E] in
/-- The directed projection gap is the norm of the rectangular cross block. -/
theorem directedGap_eq_restrictedBlock_norm
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖codRestrictTo
        (Vᗮ.starProjection ∘L U.subtypeL) Vᗮ
        (fun _x => Vᗮ.starProjection_apply_mem _)‖ = directedGap U V := by
  let T : U →L[𝕜] Vᗮ :=
    codRestrictTo (Vᗮ.starProjection ∘L U.subtypeL) Vᗮ
      (fun x => Vᗮ.starProjection_apply_mem _)
  have hle1 : ‖T‖ ≤ ‖Vᗮ.starProjection ∘L U.starProjection‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (Vᗮ.starProjection ∘L U.starProjection)) ?_
    intro x
    have hPx : U.starProjection (x : E) = (x : E) :=
      Submodule.starProjection_eq_self_iff.mpr x.property
    have h := (Vᗮ.starProjection ∘L U.starProjection).le_opNorm (x : E)
    -- `codRestrictTo` is deliberately *not* unfolded: unfolded, the `codRestrict` coercion no
    -- longer reduces, whereas this file's own `coe_codRestrictTo_apply` still fires.
    -- Keeping `codRestrictTo` bundled avoids exposing the `codRestrict` coercion.  The step is
    -- definitional, so `change` states it directly and the estimate then matches `h`.
    change ‖Vᗮ.starProjection (x : E)‖ ≤
      ‖Vᗮ.starProjection ∘L U.starProjection‖ * ‖(x : E)‖
    simpa [hPx] using h
  have hle2 : ‖Vᗮ.starProjection ∘L U.starProjection‖ ≤ ‖T‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) ?_
    intro x
    let ux : U := ⟨U.starProjection x, U.starProjection_apply_mem x⟩
    have hTx := T.le_opNorm ux
    have hproj : ‖U.starProjection x‖ ≤ ‖x‖ :=
      U.norm_starProjection_apply_le x
    calc
      ‖(Vᗮ.starProjection ∘L U.starProjection) x‖ = ‖T ux‖ := by rfl
      _ ≤ ‖T‖ * ‖ux‖ := hTx
      _ ≤ ‖T‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left hproj (norm_nonneg T)
  change ‖T‖ = ‖Vᗮ.starProjection ∘L U.starProjection‖
  exact le_antisymm hle1 hle2

omit [CompleteSpace E] [CompleteSpace F] in
/-- The directed residual block satisfies the restricted Sylvester equation. -/
theorem directedResidual_sylvesterEquation
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U)
    {X : F →L[𝕜] E} {M : F →L[𝕜] F} :
    sylvesterOperator (restrictToOrthogonal A U hU) M
      (codRestrictTo (Uᗮ.starProjection ∘L X) Uᗮ
        (fun _x => Uᗮ.starProjection_apply_mem _)) =
      codRestrictTo (Uᗮ.starProjection ∘L DavisKahan.residual A X M) Uᗮ
        (fun _x => Uᗮ.starProjection_apply_mem _) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  simp only [sylvesterOperator, DavisKahan.residual, sub_apply,
    ContinuousLinearMap.comp_apply,
    coe_codRestrictTo_apply]
  have hUperp : Reduces A Uᗮ := reduces_orthogonalComplement hA hU.2
  have hcomm := projection_apply_comm_of_isInvariant A Uᗮ hUperp (X x)
  change A (Uᗮ.starProjection (X x)) - Uᗮ.starProjection (X (M x)) =
    Uᗮ.starProjection (A (X x) - X (M x))
  rw [map_sub, hcomm]

omit [CompleteSpace E] in
/-- The directed perturbation block satisfies its restricted Sylvester
equation. -/
theorem directedPerturbation_sylvesterEquation
    {A B : E →L[𝕜] E}
    (_hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V) :
    sylvesterOperator (restrictToOrthogonal B V hV)
      (restrictToReducingSubspace A U hU)
      (codRestrictTo (Vᗮ.starProjection ∘L U.subtypeL) Vᗮ
        (fun _x => Vᗮ.starProjection_apply_mem _)) =
      codRestrictTo
        (Vᗮ.starProjection ∘L (B - A) ∘L U.subtypeL) Vᗮ
        (fun _x => Vᗮ.starProjection_apply_mem _) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  simp only [sylvesterOperator, sub_apply, ContinuousLinearMap.comp_apply]
  have hVperp : Reduces B Vᗮ := reduces_orthogonalComplement hB hV.2
  have hcomm := projection_apply_comm_of_isInvariant B Vᗮ hVperp (x : E)
  change B (Vᗮ.starProjection (x : E)) - Vᗮ.starProjection (A (x : E)) =
    Vᗮ.starProjection (B (x : E) - A (x : E))
  rw [map_sub, hcomm]

omit [CompleteSpace E] in
/-- Hybrid separation transports to the two actual restricted operators. -/
theorem hybridGap_restrictions
    {A B : E →L[𝕜] E}
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (_hA : IsSelfAdjointOperator A) (_hB : IsSelfAdjointOperator B)
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hgap : HybridGap A B U V d) :
    SpectraSeparated (restrictToOrthogonal B V hV) ⊤
      (restrictToReducingSubspace A U hU) ⊤ d := by
  refine ⟨by intro x hx; trivial, by intro x hx; trivial, ?_⟩
  intro b hb a ha
  have hb' : b ∈ restrictedSpectrum B Vᗮ := by
    rw [restrictedSpectrum_orthogonal_eq B V hV]
    rw [restrictedSpectrum_top_eq_realSpectrum_general] at hb
    exact hb
  have ha' : a ∈ restrictedSpectrum A U := by
    rw [restrictedSpectrum_eq_realSpectrum_restrictToReducingSubspace A U hU]
    rw [restrictedSpectrum_top_eq_realSpectrum_general] at ha
    exact ha
  simpa [abs_sub_comm] using hgap.2.2 a ha' b hb'

omit [CompleteSpace E] in
/-- Interval/exterior data transports to the restriction-level gap used by the
rectangular ideal theorem. -/
theorem intervalExteriorSeparated_restrictions
    {A B : E →L[𝕜] E}
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (_hA : IsSelfAdjointOperator A) (_hB : IsSelfAdjointOperator B)
    (hU : Reduces A U) (hV : Reduces B V)
    {left right d : ℝ}
    (hgap : IntervalExteriorSeparated A U B Vᗮ left right d) :
    TauCeti.DavisKahan.ExactSinTheta.IntervalExteriorGap
      (restrictToOrthogonal B V hV) (restrictToReducingSubspace A U hU)
      left right d := by
  right
  constructor
  · intro a ha
    have ha' : a ∈ restrictedSpectrum A U := by
      rw [restrictedSpectrum_eq_realSpectrum_restrictToReducingSubspace A U hU]
      rw [boundedRealSpectrum_eq_realSpectrum] at ha
      exact ha
    exact hgap.1.2 ha'
  · intro b hb
    have hb' : b ∈ restrictedSpectrum B Vᗮ := by
      rw [restrictedSpectrum_orthogonal_eq B V hV]
      rw [boundedRealSpectrum_eq_realSpectrum] at hb
      exact hb
    exact hgap.2.2 hb'

end
end DavisKahanExt
end TauCeti