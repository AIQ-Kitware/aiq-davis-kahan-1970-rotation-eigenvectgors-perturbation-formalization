/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.OperatorIdeal.UnitarilyInvariant.FamilyCore
import DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtBasis
import DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtTensor
import ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Conjugation
import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Group
import ForTauCeti.Analysis.InnerProductSpace.Sylvester.SpectralGap
import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Generator

/-!
# The complex rectangular Hilbert--Schmidt ideal family

The paper square norm is already defined through approximation singular values
and is identified with the norm of the canonical Hilbert tensor.  This file
uses that tensor model to supply the algebraic operations, triangle inequality,
operator-norm domination, and completeness that
`SymmetricOperatorIdealFamily.Core` asks for.

The construction is rectangular and basis-free.  Its only scalar restriction
is complex scalars, inherited from the current Hilbert tensor implementation.
The real family is intended to be obtained by exact complexification transport.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open Filter
open TauCeti.HilbertSchmidt

noncomputable section

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Addition preserves the paper Hilbert--Schmidt class. -/
theorem isPaperHilbertSchmidt_add
    {A B : E →L[ℂ] F}
    (hA : IsPaperHilbertSchmidt A)
    (hB : IsPaperHilbertSchmidt B) :
    IsPaperHilbertSchmidt (A + B) := by
  let zA := paperHilbertSchmidtTensor A hA
  let zB := paperHilbertSchmidtTensor B hB
  have hrepr : ofLp (paperHSBasis _) (zA + zB) = A + B := by
    rw [ofLp_add]
    rw [toOperator_paperHilbertSchmidtTensor,
      toOperator_paperHilbertSchmidtTensor]
  rw [← hrepr]
  exact isPaperHilbertSchmidt_toOperator (zA + zB)

/-- The canonical tensor of a sum is the sum of the canonical tensors. -/
theorem paperHilbertSchmidtTensor_add
    {A B : E →L[ℂ] F}
    (hA : IsPaperHilbertSchmidt A)
    (hB : IsPaperHilbertSchmidt B) :
    paperHilbertSchmidtTensor (A + B)
        (isPaperHilbertSchmidt_add hA hB) =
      paperHilbertSchmidtTensor A hA +
        paperHilbertSchmidtTensor B hB := by
  apply ofLp_injective (paperHSBasis _)
  rw [toOperator_paperHilbertSchmidtTensor,
    ofLp_add,
    toOperator_paperHilbertSchmidtTensor,
    toOperator_paperHilbertSchmidtTensor]

/-- The paper Hilbert--Schmidt norm satisfies the triangle inequality. -/
theorem paperHilbertSchmidtNorm_add_le
    {A B : E →L[ℂ] F}
    (hA : IsPaperHilbertSchmidt A)
    (hB : IsPaperHilbertSchmidt B) :
    paperHilbertSchmidtNorm (A + B) ≤
      paperHilbertSchmidtNorm A + paperHilbertSchmidtNorm B := by
  let hAB := isPaperHilbertSchmidt_add hA hB
  rw [← norm_paperHilbertSchmidtTensor (A + B) hAB,
    paperHilbertSchmidtTensor_add hA hB,
    ← norm_paperHilbertSchmidtTensor A hA,
    ← norm_paperHilbertSchmidtTensor B hB]
  exact norm_add_le _ _

/-- A zero paper Hilbert--Schmidt norm forces the represented operator to
vanish. -/
theorem paperHilbertSchmidtNorm_eq_zero
    {A : E →L[ℂ] F} (hA : IsPaperHilbertSchmidt A)
    (hzero : paperHilbertSchmidtNorm A = 0) : A = 0 := by
  let z := paperHilbertSchmidtTensor A hA
  have hzNorm : ‖z‖ = 0 := by
    rw [norm_paperHilbertSchmidtTensor]
    exact hzero
  have hz : paperHilbertSchmidtTensor A hA = 0 := norm_eq_zero.mp hzNorm
  have hrepr := toOperator_paperHilbertSchmidtTensor A hA
  rw [hz, ofLp_zero] at hrepr
  exact hrepr.symm

/-- Subtraction preserves the paper Hilbert--Schmidt class. -/
theorem isPaperHilbertSchmidt_sub
    {A B : E →L[ℂ] F}
    (hA : IsPaperHilbertSchmidt A)
    (hB : IsPaperHilbertSchmidt B) :
    IsPaperHilbertSchmidt (A - B) := by
  rw [sub_eq_add_neg]
  exact isPaperHilbertSchmidt_add hA ((isPaperHilbertSchmidt_neg_iff B).2 hB)

/-- The canonical tensor respects subtraction. -/
theorem paperHilbertSchmidtTensor_sub
    {A B : E →L[ℂ] F}
    (hA : IsPaperHilbertSchmidt A)
    (hB : IsPaperHilbertSchmidt B) :
    paperHilbertSchmidtTensor (A - B) (isPaperHilbertSchmidt_sub hA hB) =
      paperHilbertSchmidtTensor A hA -
        paperHilbertSchmidtTensor B hB := by
  apply ofLp_injective (paperHSBasis _)
  rw [toOperator_paperHilbertSchmidtTensor,
    ofLp_sub,
    toOperator_paperHilbertSchmidtTensor,
    toOperator_paperHilbertSchmidtTensor]

/-- A sequence Cauchy in the paper square norm converges to a paper
Hilbert--Schmidt operator in that norm. -/
theorem paperHilbertSchmidt_complete
    (A : ℕ → E →L[ℂ] F)
    (hA : ∀ n, IsPaperHilbertSchmidt (A n))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n,
      N ≤ m → N ≤ n →
        paperHilbertSchmidtNorm (A m - A n) < ε) :
    ∃ L : E →L[ℂ] F, IsPaperHilbertSchmidt L ∧
      ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
        paperHilbertSchmidtNorm (A n - L) < ε := by
  let z : ℕ → lp (fun _ : PaperHSIndex E => F) 2 :=
    fun n => paperHilbertSchmidtTensor (A n) (hA n)
  have hzCauchy : CauchySeq z := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hsub : IsPaperHilbertSchmidt (A m - A n) :=
      isPaperHilbertSchmidt_sub (hA m) (hA n)
    have hcanon : paperHilbertSchmidtTensor (A m - A n) hsub = z m - z n := by
      apply ofLp_injective (paperHSBasis _)
      rw [toOperator_paperHilbertSchmidtTensor,
        ofLp_sub,
        toOperator_paperHilbertSchmidtTensor,
        toOperator_paperHilbertSchmidtTensor]
    have hnorm : ‖z m - z n‖ =
        paperHilbertSchmidtNorm (A m - A n) := by
      rw [← hcanon, norm_paperHilbertSchmidtTensor]
    simpa only [dist_eq_norm, hnorm] using hN m n hm hn
  obtain ⟨zlim, hzlim⟩ := cauchySeq_tendsto_of_complete hzCauchy
  let L : E →L[ℂ] F := ofLp (paperHSBasis _) zlim
  have hL : IsPaperHilbertSchmidt L :=
    isPaperHilbertSchmidt_toOperator zlim
  refine ⟨L, hL, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hzlim) ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have hsub : IsPaperHilbertSchmidt (A n - L) :=
    isPaperHilbertSchmidt_sub (hA n) hL
  have hcanon : paperHilbertSchmidtTensor (A n - L) hsub = z n - zlim := by
    apply ofLp_injective (paperHSBasis _)
    rw [toOperator_paperHilbertSchmidtTensor,
      ofLp_sub,
      toOperator_paperHilbertSchmidtTensor]
  have hnorm : paperHilbertSchmidtNorm (A n - L) = ‖z n - zlim‖ := by
    rw [← norm_paperHilbertSchmidtTensor (A n - L) hsub, hcanon]
  rw [hnorm, ← dist_eq_norm]
  exact hN n hn

/-- The coherent complex rectangular Hilbert--Schmidt ideal family. -/
noncomputable def hilbertSchmidtComplex :
    SymmetricOperatorIdealFamily (𝕜 := ℂ) :=
  SymmetricOperatorIdealFamily.ofCore <| by
  classical
  refine
    { Mem := fun T => IsPaperHilbertSchmidt T
      gauge := fun T => paperHilbertSchmidtNorm T
      zero_mem := by
        intro E F _ _ _ _ _ _
        unfold IsPaperHilbertSchmidt
        rw [paperHilbertSchmidtEnergy_zero]
        exact ENNReal.zero_ne_top
      add_mem := by
        intro E F _ _ _ _ _ _ A B hA hB
        exact isPaperHilbertSchmidt_add hA hB
      smul_mem := by
        intro E F _ _ _ _ _ _ c A hA
        by_cases hc : c = 0
        · subst c
          simpa using (show IsPaperHilbertSchmidt (0 : E →L[ℂ] F) from by
            unfold IsPaperHilbertSchmidt
            rw [paperHilbertSchmidtEnergy_zero]
            exact ENNReal.zero_ne_top)
        · exact (isPaperHilbertSchmidt_smul_iff c hc A).2 hA
      adjoint_mem := by
        intro E F _ _ _ _ _ _ A hA
        exact (isPaperHilbertSchmidt_adjoint_iff A).2 hA
      comp_mem := by
        intro E F G H _ _ _ _ _ _ _ _ _ _ _ _ L A R hA
        exact hA.comp L R
      gauge_nonneg := by
        intro E F _ _ _ _ _ _ A hA
        exact paperHilbertSchmidtNorm_nonneg A
      gauge_zero := by
        intro E F _ _ _ _ _ _
        exact paperHilbertSchmidtNorm_zero
      gauge_add_le := by
        intro E F _ _ _ _ _ _ A B hA hB
        exact paperHilbertSchmidtNorm_add_le hA hB
      gauge_smul := by
        intro E F _ _ _ _ _ _ c A hA
        exact paperHilbertSchmidtNorm_smul c A hA
      gauge_adjoint := by
        intro E F _ _ _ _ _ _ A hA
        exact paperHilbertSchmidtNorm_adjoint A
      gauge_comp_le := by
        intro E F G H _ _ _ _ _ _ _ _ _ _ _ _ L A R hA
        exact paperHilbertSchmidtNorm_comp_le L hA R
      opNorm_le_gauge := by
        intro E F _ _ _ _ _ _ A hA
        exact opNorm_le_paperHilbertSchmidtNorm hA
      gauge_complete := by
        intro E F _ _ _ _ _ _ A hA hcauchy
        exact paperHilbertSchmidt_complete A hA hcauchy }

end

end ExactSinTheta
end DavisKahan
end TauCeti