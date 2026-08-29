/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtComplexFamily
import DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtFiniteRank
import DavisKahan.SpectralTheory.PartialMap.Complexification

/-!
# Real rectangular Hilbert--Schmidt family by complexification

This module supplies the real-scalar Hilbert--Schmidt family used by the
Davis--Kahan source formalization.

The complex family is already represented isometrically by the Hilbert tensor
space.  A Cauchy sequence of complexified real operators therefore has a
complex Hilbert--Schmidt limit.  Operator-norm domination shows that the limit
maps the real copy into the real copy.  Restricting that limit to real vectors
and taking real coordinates produces the required real operator, whose
complexification is exactly the complex limit.

The construction is the real counterpart of `HilbertSchmidtComplexFamily`: the
complex Hilbert--Schmidt completion is descended through the canonical real copy.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open Filter Topology
open TauCeti.RealComplexification
open PartialMapComplexification

noncomputable section

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local notation "Eℂ" => RealComplexification E
local notation "Fℂ" => RealComplexification F

/-- A complex operator maps the distinguished real copy into the real copy. -/
def MapsRealCopy (T : Eℂ →L[ℂ] Fℂ) : Prop :=
  ∀ x : E, im (T (ofReal x)) = 0

omit [CompleteSpace E] [CompleteSpace F] in
/-- Every coordinatewise complexification maps real vectors to real vectors. -/
theorem mapsRealCopy_complexify (T : E →L[ℝ] F) :
    MapsRealCopy (complexify T) := by
  intro x
  simp

omit [CompleteSpace F] in
/-- A vector with zero imaginary coordinate is its real-coordinate embedding. -/
theorem eq_ofReal_re_of_im_eq_zero
    (z : Fℂ) (hz : im z = 0) : ofReal (re z) = z := by
  apply RealComplexification.ext
  · simp
  · simp [hz]

omit [CompleteSpace E] [CompleteSpace F] in
/-- A complex-linear operator that preserves the real copy is exactly the
complexification of its real restriction. -/
theorem complexify_realPartOperator_eq
    (T : Eℂ →L[ℂ] Fℂ) (hT : MapsRealCopy T) :
    complexify (realPartOperator T) = T := by
  apply ContinuousLinearMap.ext
  intro z
  have hz : z = ofReal (re z) + Complex.I • ofReal (im z) := by
    apply RealComplexification.ext <;> simp
  have hreal : ∀ x : E,
      ofReal (realPartOperator T x) = T (ofReal x) := by
    intro x
    exact eq_ofReal_re_of_im_eq_zero (T (ofReal x)) (hT x)
  rw [hz]
  simp only [map_add, map_smul, complexify_ofReal, hreal]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Convergence in operator norm preserves the property of mapping the real
copy into itself. -/
theorem mapsRealCopy_of_tendsto
    (T : ℕ → Eℂ →L[ℂ] Fℂ) (L : Eℂ →L[ℂ] Fℂ)
    (hT : ∀ n, MapsRealCopy (T n))
    (hlim : Tendsto T atTop (𝓝 L)) :
    MapsRealCopy L := by
  intro x
  let ev : (Eℂ →L[ℂ] Fℂ) →L[ℂ] Fℂ :=
    ContinuousLinearMap.apply ℂ Fℂ (ofReal x)
  have happly : Tendsto (fun n => T n (ofReal x)) atTop
      (𝓝 (L (ofReal x))) :=
    ev.continuous.continuousAt.tendsto.comp hlim
  have him : Tendsto (fun n => im (T n (ofReal x))) atTop
      (𝓝 (im (L (ofReal x)))) :=
    continuous_im.continuousAt.tendsto.comp happly
  have hzero : Tendsto (fun _ : ℕ => (0 : F)) atTop (𝓝 0) :=
    tendsto_const_nhds
  have hseq : (fun n => im (T n (ofReal x))) = fun _ : ℕ => (0 : F) := by
    funext n
    exact hT n x
  have himzero : Tendsto (fun n => im (T n (ofReal x))) atTop (𝓝 0) := by
    rw [hseq]
    exact hzero
  exact tendsto_nhds_unique him himzero

/-- Hilbert--Schmidt convergence implies operator-norm convergence. -/
theorem tendsto_opNorm_of_paperHilbertSchmidt
    (T : ℕ → Eℂ →L[ℂ] Fℂ) (L : Eℂ →L[ℂ] Fℂ)
    (hT : ∀ n, IsPaperHilbertSchmidt (T n))
    (hL : IsPaperHilbertSchmidt L)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
      paperHilbertSchmidtNorm (T n - L) < ε) :
    Tendsto T atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hconv ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have hsub : IsPaperHilbertSchmidt (T n - L) :=
    isPaperHilbertSchmidt_sub (hT n) hL
  have hop : ‖T n - L‖ ≤ paperHilbertSchmidtNorm (T n - L) :=
    opNorm_le_paperHilbertSchmidtNorm hsub
  simpa only [dist_eq_norm] using lt_of_le_of_lt hop (hN n hn)

/-- The real paper Hilbert--Schmidt class is complete.  The proof descends the
complex tensor-space limit through the closed real-copy condition. -/
theorem paperHilbertSchmidt_complete_real
    (A : ℕ → E →L[ℝ] F)
    (hA : ∀ n, IsPaperHilbertSchmidt (A n))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n,
      N ≤ m → N ≤ n →
        paperHilbertSchmidtNorm (A m - A n) < ε) :
    ∃ L : E →L[ℝ] F, IsPaperHilbertSchmidt L ∧
      ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
        paperHilbertSchmidtNorm (A n - L) < ε := by
  let Ac : ℕ → Eℂ →L[ℂ] Fℂ := fun n => complexify (A n)
  have hAc : ∀ n, IsPaperHilbertSchmidt (Ac n) := by
    intro n
    exact (isPaperHilbertSchmidt_complexify_iff (A n)).2 (hA n)
  have hcauchyC : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n,
      N ≤ m → N ≤ n →
        paperHilbertSchmidtNorm (Ac m - Ac n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, ?_⟩
    intro m n hm hn
    rw [show Ac m - Ac n = complexify (A m - A n) by
      simp [Ac, complexify_sub]]
    rw [paperHilbertSchmidtNorm_complexify]
    exact hN m n hm hn
  obtain ⟨Lc, hLc, hconvC⟩ :=
    paperHilbertSchmidt_complete Ac hAc hcauchyC
  have hOp : Tendsto Ac atTop (𝓝 Lc) :=
    tendsto_opNorm_of_paperHilbertSchmidt Ac Lc hAc hLc hconvC
  have hreal : MapsRealCopy Lc :=
    mapsRealCopy_of_tendsto Ac Lc
      (fun n => mapsRealCopy_complexify (A n)) hOp
  let L : E →L[ℝ] F := realPartOperator Lc
  have hLc_eq : complexify L = Lc := by
    simpa [L] using complexify_realPartOperator_eq Lc hreal
  have hL : IsPaperHilbertSchmidt L := by
    rw [← isPaperHilbertSchmidt_complexify_iff L, hLc_eq]
    exact hLc
  refine ⟨L, hL, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := hconvC ε hε
  refine ⟨N, ?_⟩
  intro n hn
  calc
    paperHilbertSchmidtNorm (A n - L) =
        paperHilbertSchmidtNorm (complexify (A n - L)) := by
          rw [paperHilbertSchmidtNorm_complexify]
    _ = paperHilbertSchmidtNorm (Ac n - Lc) := by
          rw [complexify_sub, hLc_eq]
    _ < ε := hN n hn

/-- Addition closure of the real paper Hilbert--Schmidt class, transported from
its complex tensor representation. -/
theorem isPaperHilbertSchmidt_add_real
    {A B : E →L[ℝ] F}
    (hA : IsPaperHilbertSchmidt A)
    (hB : IsPaperHilbertSchmidt B) :
    IsPaperHilbertSchmidt (A + B) := by
  rw [← isPaperHilbertSchmidt_complexify_iff]
  rw [complexify_add]
  exact isPaperHilbertSchmidt_add
    ((isPaperHilbertSchmidt_complexify_iff A).2 hA)
    ((isPaperHilbertSchmidt_complexify_iff B).2 hB)

/-- Triangle inequality for the real paper Hilbert--Schmidt norm. -/
theorem paperHilbertSchmidtNorm_add_le_real
    {A B : E →L[ℝ] F}
    (hA : IsPaperHilbertSchmidt A)
    (hB : IsPaperHilbertSchmidt B) :
    paperHilbertSchmidtNorm (A + B) ≤
      paperHilbertSchmidtNorm A + paperHilbertSchmidtNorm B := by
  calc
    paperHilbertSchmidtNorm (A + B) =
        paperHilbertSchmidtNorm (complexify (A + B)) := by
          rw [paperHilbertSchmidtNorm_complexify]
    _ = paperHilbertSchmidtNorm (complexify A + complexify B) := by
          rw [complexify_add]
    _ ≤ paperHilbertSchmidtNorm (complexify A) +
          paperHilbertSchmidtNorm (complexify B) :=
      paperHilbertSchmidtNorm_add_le
        ((isPaperHilbertSchmidt_complexify_iff A).2 hA)
        ((isPaperHilbertSchmidt_complexify_iff B).2 hB)
    _ = paperHilbertSchmidtNorm A + paperHilbertSchmidtNorm B := by
          rw [paperHilbertSchmidtNorm_complexify,
            paperHilbertSchmidtNorm_complexify]

/-- The complete rectangular Hilbert--Schmidt family over real Hilbert spaces. -/
noncomputable def hilbertSchmidtReal :
    SymmetricOperatorIdealFamily (𝕜 := ℝ) :=
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
        exact isPaperHilbertSchmidt_add_real hA hB
      smul_mem := by
        intro E F _ _ _ _ _ _ c A hA
        by_cases hc : c = 0
        · subst c
          simpa using (show IsPaperHilbertSchmidt (0 : E →L[ℝ] F) from by
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
        exact paperHilbertSchmidtNorm_add_le_real hA hB
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
        exact paperHilbertSchmidt_complete_real A hA hcauchy }

end

end ExactSinTheta
end DavisKahan
end TauCeti