/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.InfiniteDimensional.Ideals.Symmetric
import DavisKahan.InfiniteDimensional.Ideals.CompactIntegral
import DavisKahan.InfiniteDimensional.Sylvester.FourierSemigroup
import DavisKahan.InfiniteDimensional.Sylvester.OrderedSemigroup
import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Bound
import ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm
import DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Infinite-dimensional bounded Sylvester equations

There are two distinct inverse estimates.

* Ordered spectra give the sharp constant one by a decaying semigroup.
* Arbitrarily separated spectra give the universal `pi/2` estimate through the
  Haagerup--Zsido reciprocal Fourier kernel.

The oscillatory construction is stated over complex Hilbert spaces.  A same-space
formula `exp(i t A)` is not available over real scalars; real consequences must be
transported through complexification.
-/

namespace TauCeti

open TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators

noncomputable section

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Sylvester operator `X |-> A X - X B`. -/
def sylvesterOperator (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (X : E →L[𝕜] F) : E →L[𝕜] F :=
  A ∘L X - X ∘L B

/-- The Sylvester operator sends `0` to `0`. -/
@[simp] theorem sylvesterOperator_zero
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) :
    sylvesterOperator A B (0 : E →L[𝕜] F) = 0 := by
  simp [sylvesterOperator]

/-- The Sylvester operator is additive. -/
theorem sylvesterOperator_add
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) (X Y : E →L[𝕜] F) :
    sylvesterOperator A B (X + Y) =
      sylvesterOperator A B X + sylvesterOperator A B Y := by
  simp only [sylvesterOperator, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.add_comp]
  abel

/-- The Sylvester operator commutes with subtraction. -/
theorem sylvesterOperator_sub
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) (X Y : E →L[𝕜] F) :
    sylvesterOperator A B (X - Y) =
      sylvesterOperator A B X - sylvesterOperator A B Y := by
  simp only [sylvesterOperator, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.sub_comp]
  abel

/-- The Sylvester operator is homogeneous. -/
theorem sylvesterOperator_smul
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) (c : 𝕜) (X : E →L[𝕜] F) :
    sylvesterOperator A B (c • X) = c • sylvesterOperator A B X := by
  ext x
  simp [sylvesterOperator, smul_sub]

/-- Elementary operator-norm bound. -/
theorem norm_sylvesterOperator_le
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) (X : E →L[𝕜] F) :
    ‖sylvesterOperator A B X‖ ≤ (‖A‖ + ‖B‖) * ‖X‖ := by
  calc
    ‖sylvesterOperator A B X‖ ≤ ‖A ∘L X‖ + ‖X ∘L B‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖X‖ + ‖X‖ * ‖B‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le A X)
        (ContinuousLinearMap.opNorm_comp_le X B)
    _ = (‖A‖ + ‖B‖) * ‖X‖ := by ring

/-- The sharp coercive form of the ordered Sylvester estimate. -/
theorem norm_sylvester_le_of_coercive
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {c g : ℝ} (hg : 0 < g)
    (hAc : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hEq : sylvesterOperator A B X = C) :
    ‖X‖ ≤ ‖C‖ / g :=
  TauCeti.ContinuousLinearMap.opNorm_le_div_of_comp_sub_comp_eq hA hB hg hAc hBc hEq


section OrderedComplex

variable {Ec : Type u} [NormedAddCommGroup Ec] [InnerProductSpace ℂ Ec]
  [CompleteSpace Ec]
variable {Fc : Type v} [NormedAddCommGroup Fc] [InnerProductSpace ℂ Fc]
  [CompleteSpace Fc]

/-- Sharp constant-one estimate for ordered bounded self-adjoint spectra. -/
theorem norm_sylvester_le_of_orderedSeparation
    {A : Fc →L[ℂ] Fc} {B : Ec →L[ℂ] Ec} {X C : Ec →L[ℂ] Fc}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (hEq : sylvesterOperator A B X = C) :
    d * ‖X‖ ≤ ‖C‖ := by
  have hrep := orderedSylvester_reconstruction hA hB hd hsep hEq
  have hgint : Integrable (Set.indicator (Set.Ici 0)
      (fun t => ‖C‖ * Real.exp (-d * t))) := by
    have hexp : IntegrableOn (fun t : ℝ => ‖C‖ * Real.exp (-d * t))
        (Set.Ici 0) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact (exp_neg_integrableOn_Ioi 0 hd).const_mul ‖C‖
    exact hexp.integrable_indicator measurableSet_Ici
  have hbound : ∀ t : ℝ, ‖Set.indicator (Set.Ici 0)
      (fun t => semigroup (-A) t ∘L C ∘L semigroup B t) t‖ ≤
      Set.indicator (Set.Ici 0) (fun t => ‖C‖ * Real.exp (-d * t)) t := by
    intro t
    by_cases ht : t ∈ Set.Ici 0
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, mul_comm]
      exact orderedSemigroup_integrand_bound hA hB hd hsep C t ht
    · simp [Set.indicator_of_notMem ht]
  have hXle : ‖X‖ ≤ ∫ t, Set.indicator (Set.Ici 0)
      (fun t => ‖C‖ * Real.exp (-d * t)) t := by
    rw [hrep]
    exact norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hbound)
  have hexp_val : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-d * t)) = d⁻¹ := by
    have h := integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) 0 hd
    simp only [mul_zero, integral_exp_neg_Ioi, neg_zero, Real.exp_zero,
      smul_eq_mul, mul_one] at h
    simp only [neg_mul]
    exact h
  have hval : (∫ t, Set.indicator (Set.Ici 0)
      (fun t => ‖C‖ * Real.exp (-d * t)) t) = ‖C‖ / d := by
    rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_const_mul, hexp_val, div_eq_mul_inv]
  have hfin : ‖X‖ ≤ ‖C‖ / d := by
    rw [← hval]
    exact hXle
  rw [mul_comm]
  exact (le_div_iff₀ hd).mp hfin

end OrderedComplex

section Complex

variable {Ec : Type u} [NormedAddCommGroup Ec] [InnerProductSpace ℂ Ec]
  [CompleteSpace Ec]
variable {Fc : Type v} [NormedAddCommGroup Fc] [InnerProductSpace ℂ Fc]
  [CompleteSpace Fc]

/-- Fourier-integral solution selected under a supplied positive gap. -/
noncomputable def separatedSylvesterSolution
    (A : Fc →L[ℂ] Fc) (B : Ec →L[ℂ] Ec)
    (d : ℝ) (hd : 0 < d) (C : Ec →L[ℂ] Fc) : Ec →L[ℂ] Fc :=
  ∫ t : ℝ, separatedSylvesterMultiplier d hd t •
    (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))

/-- Exact reconstruction of any solution by the reciprocal Fourier kernel. -/
theorem separatedSylvester_reconstruction
    {A : Fc →L[ℂ] Fc} {B : Ec →L[ℂ] Ec}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (X C : Ec →L[ℂ] Fc)
    (hEq : sylvesterOperator A B X = C) :
    X = separatedSylvesterSolution A B d hd C := by
  unfold separatedSylvesterSolution
  exact separatedSylvester_reconstruction_complex hA hB hd hsep X C hEq

/-- The selected Fourier integral is Bochner integrable. -/
theorem separatedSylvester_integrable
    {A : Fc →L[ℂ] Fc} {B : Ec →L[ℂ] Ec}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d) (C : Ec →L[ℂ] Fc) :
    Integrable fun t : ℝ => separatedSylvesterMultiplier d hd t •
      (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)) :=
  separatedSylvester_integrable_complex hA hB hd C

/-- The Fourier integral solves the Sylvester equation. -/
theorem sylvester_solve
    {A : Fc →L[ℂ] Fc} {B : Ec →L[ℂ] Ec}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (C : Ec →L[ℂ] Fc) :
    sylvesterOperator A B (separatedSylvesterSolution A B d hd C) = C := by
  unfold sylvesterOperator separatedSylvesterSolution
  exact spectral_step_integral_right_inverse hA hB hd hsep C

/-- Universal Bhatia--Davis--McIntosh bound. -/
theorem norm_sylvester_le_of_generalSeparation
    {A : Fc →L[ℂ] Fc} {B : Ec →L[ℂ] Ec}
    {X C : Ec →L[ℂ] Fc}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : sylvesterOperator A B X = C) :
    d * ‖X‖ ≤ (Real.pi / 2) * ‖C‖ := by
  rw [separatedSylvester_reconstruction hA hB hd hsep X C hEq]
  have hint := separatedSylvester_integrable hA hB hd C
  calc
    d * ‖separatedSylvesterSolution A B d hd C‖
        ≤ d * (∫ t : ℝ, ‖separatedSylvesterMultiplier d hd t‖ * ‖C‖) := by
      gcongr
      unfold separatedSylvesterSolution
      calc
        ‖∫ t : ℝ, separatedSylvesterMultiplier d hd t •
            (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))‖
            ≤ ∫ t : ℝ, ‖separatedSylvesterMultiplier d hd t •
              (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))‖ :=
                norm_integral_le_integral_norm _
        _ = ∫ t : ℝ, ‖separatedSylvesterMultiplier d hd t‖ * ‖C‖ := by
          apply integral_congr_ae
          filter_upwards [] with t
          rw [norm_smul, norm_unitary_left_right A hA B hB t C]
    _ = d * ((∫ t : ℝ, ‖separatedSylvesterMultiplier d hd t‖) * ‖C‖) := by
      rw [integral_mul_const]
    _ = (Real.pi / 2) * ‖C‖ := by
      rw [l1_norm_separatedSylvesterMultiplier d hd]
      field_simp [ne_of_gt hd]

/-- Uniqueness under separated spectra. -/
theorem sylvester_unique
    {A : Fc →L[ℂ] Fc} {B : Ec →L[ℂ] Ec}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    {X Y : Ec →L[ℂ] Fc}
    (hX : sylvesterOperator A B X = sylvesterOperator A B Y) :
    X = Y := by
  have hzero : sylvesterOperator A B (X - Y) = 0 := by
    rw [sylvesterOperator_sub, hX, sub_self]
  have hle := norm_sylvester_le_of_generalSeparation hA hB hd hsep hzero
  rw [norm_zero, mul_zero] at hle
  have hnorm : ‖X - Y‖ = 0 := by
    have hd0 : 0 < d := hd
    nlinarith [norm_nonneg (X - Y), Real.pi_pos]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Compact right-hand sides give compact separated solutions.

The first ideal argument is retained for the existing call sites.  The theorem
is specifically about the concrete compact/operator-norm ideal; the local
abbreviation used by those consumers unfolds to that ideal. -/
theorem compact_mem_of_separatedSylvester_solution
    (_I : SymmetricNormIdeal (𝕜 := ℂ) (E := Ec))
    {A : Fc →L[ℂ] Fc} {B : Ec →L[ℂ] Ec}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    {X C : Ec →L[ℂ] Fc}
    (hEq : sylvesterOperator A B X = C)
    (hC : IsCompactOperator C) :
    IsCompactOperator X := by
  have hrep := separatedSylvester_reconstruction_complex hA hB hd hsep X C hEq
  have hint := separatedSylvester_integrable_complex hA hB hd C
  rw [hrep]
  refine isCompactOperator_integral hint (Filter.Eventually.of_forall fun t => ?_)
  have h1 : IsCompactOperator (⇑C ∘ ⇑(unitaryGroup B (-t))) :=
    hC.comp_clm (unitaryGroup B (-t))
  have h2 : IsCompactOperator
      (⇑(unitaryGroup A t) ∘ (⇑C ∘ ⇑(unitaryGroup B (-t)))) :=
    h1.continuous_comp (unitaryGroup A t).continuous
  exact h2.smul (separatedSylvesterMultiplier d hd t)

end Complex

end

end DavisKahanExt
end TauCeti