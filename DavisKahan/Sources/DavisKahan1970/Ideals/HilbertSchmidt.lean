/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SingularValueTransport
import DavisKahan.OperatorIdeal.ApproximationNumbers.OperatorModulus
import DavisKahan.OperatorIdeal.ComplexificationApproximation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Inv

/-!
# The source square or Hilbert--Schmidt norm

The second generalized sine theorem is specifically a square-norm theorem.  It
cannot be represented by the arbitrary-norm ideal family unless an actual
Hilbert--Schmidt instance has been constructed.  This module gives a scalar-
generic, rectangular definition directly from the complete approximation-
number sequence.

The extended energy is `sum_n a_n(A)^2`.  Membership means this extended sum is
finite, and the norm is its square root.  This is basis free and immediately
compatible with every singular-value transport theorem in the repository.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators ENNReal
open TauCeti.RealComplexification


noncomputable section

universe u vE vF vG vH vE1 vF1 vE2 vF2

/-- Extended Hilbert--Schmidt energy, defined by the squared approximation
singular-value sequence. -/
def paperHilbertSchmidtEnergy
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) : ENNReal :=
  ∑' n : ℕ, ENNReal.ofReal ((approximationSingularValue n A) ^ 2)

/-- Canonical Hilbert--Schmidt membership. -/
def IsPaperHilbertSchmidt
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) : Prop :=
  paperHilbertSchmidtEnergy A ≠ ⊤

/-- Basis-free rectangular Hilbert--Schmidt norm. -/
def paperHilbertSchmidtNorm
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) : ℝ :=
  Real.sqrt (paperHilbertSchmidtEnergy A).toReal

/-- The zero operator has zero Hilbert--Schmidt energy. -/
@[simp]
theorem paperHilbertSchmidtEnergy_zero
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] :
    paperHilbertSchmidtEnergy (0 : E →L[𝕜] F) = 0 := by
  unfold paperHilbertSchmidtEnergy
  simp

/-- The zero operator has zero Hilbert--Schmidt norm. -/
@[simp]
theorem paperHilbertSchmidtNorm_zero
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] :
    paperHilbertSchmidtNorm (0 : E →L[𝕜] F) = 0 := by
  simp [paperHilbertSchmidtNorm]

/-- The square norm is nonnegative. -/
theorem paperHilbertSchmidtNorm_nonneg
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    0 ≤ paperHilbertSchmidtNorm A :=
  Real.sqrt_nonneg _

/-- Complete singular-value equality preserves Hilbert--Schmidt energy. -/
theorem SameApproximationSingularSequence.paperHilbertSchmidtEnergy_eq
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ : Type vE1} {F₁ : Type vF1}
    {E₂ : Type vE2} {F₂ : Type vF2}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [CompleteSpace F₂]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) :
    paperHilbertSchmidtEnergy A = paperHilbertSchmidtEnergy B := by
  unfold paperHilbertSchmidtEnergy
  congr 1
  funext n
  exact congrArg (fun x : ℝ => ENNReal.ofReal (x ^ 2)) (h n)

/-- Complete singular-value equality preserves Hilbert--Schmidt membership. -/
theorem SameApproximationSingularSequence.isPaperHilbertSchmidt_iff
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ : Type vE1} {F₁ : Type vF1}
    {E₂ : Type vE2} {F₂ : Type vF2}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [CompleteSpace F₂]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) :
    IsPaperHilbertSchmidt A ↔ IsPaperHilbertSchmidt B := by
  unfold IsPaperHilbertSchmidt
  rw [h.paperHilbertSchmidtEnergy_eq]

/-- Complete singular-value equality preserves the square norm. -/
theorem SameApproximationSingularSequence.paperHilbertSchmidtNorm_eq
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ : Type vE1} {F₁ : Type vF1}
    {E₂ : Type vE2} {F₂ : Type vF2}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [CompleteSpace F₂]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) :
    paperHilbertSchmidtNorm A = paperHilbertSchmidtNorm B := by
  unfold paperHilbertSchmidtNorm
  rw [h.paperHilbertSchmidtEnergy_eq]


/-- Adjoint invariance of Hilbert--Schmidt membership. -/
theorem isPaperHilbertSchmidt_adjoint_iff
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    IsPaperHilbertSchmidt A.adjoint ↔ IsPaperHilbertSchmidt A := by
  apply SameApproximationSingularSequence.isPaperHilbertSchmidt_iff
  intro n
  exact approximationSingularValue_adjoint n A

/-- Adjoint invariance of the square norm. -/
theorem paperHilbertSchmidtNorm_adjoint
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    paperHilbertSchmidtNorm A.adjoint = paperHilbertSchmidtNorm A := by
  apply SameApproximationSingularSequence.paperHilbertSchmidtNorm_eq
  intro n
  exact approximationSingularValue_adjoint n A

/-- The modulus has the same square norm as the original rectangular map. -/
theorem paperHilbertSchmidtNorm_operatorModulus
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) :
    paperHilbertSchmidtNorm (ContinuousLinearMap.modulus A) =
      paperHilbertSchmidtNorm A :=
  SameApproximationSingularSequence.paperHilbertSchmidtNorm_eq
    (modulus_hasSameApproximationNumbers A)


/-- Real complexification preserves Hilbert--Schmidt energy exactly. -/
theorem paperHilbertSchmidtEnergy_complexify
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) :
    paperHilbertSchmidtEnergy (RealComplexification.complexify A) =
      paperHilbertSchmidtEnergy A := by
  unfold paperHilbertSchmidtEnergy
  congr 1
  funext n
  rw [ComplexificationApproximation.approximationSingularValue_complexify]

/-- Real complexification preserves square-norm membership. -/
theorem isPaperHilbertSchmidt_complexify_iff
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) :
    IsPaperHilbertSchmidt (RealComplexification.complexify A) ↔
      IsPaperHilbertSchmidt A := by
  unfold IsPaperHilbertSchmidt
  rw [paperHilbertSchmidtEnergy_complexify]

/-- Real complexification preserves the square norm. -/
theorem paperHilbertSchmidtNorm_complexify
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) :
    paperHilbertSchmidtNorm (RealComplexification.complexify A) =
      paperHilbertSchmidtNorm A := by
  unfold paperHilbertSchmidtNorm
  rw [paperHilbertSchmidtEnergy_complexify]

/-- Scaling law for Hilbert--Schmidt energy. -/
theorem paperHilbertSchmidtEnergy_smul
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (c : 𝕜) (A : E →L[𝕜] F) :
    paperHilbertSchmidtEnergy (c • A) =
      ENNReal.ofReal (‖c‖ ^ 2) * paperHilbertSchmidtEnergy A := by
  unfold paperHilbertSchmidtEnergy
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext n
  rw [approximationSingularValue_smul, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _)]

/-- Absolute homogeneity of the square norm on finite-energy operators. -/
theorem paperHilbertSchmidtNorm_smul
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (c : 𝕜) (A : E →L[𝕜] F)
    (_hA : IsPaperHilbertSchmidt A) :
    paperHilbertSchmidtNorm (c • A) = ‖c‖ * paperHilbertSchmidtNorm A := by
  simp only [paperHilbertSchmidtNorm, paperHilbertSchmidtEnergy_smul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
    Real.sqrt_mul (sq_nonneg ‖c‖), Real.sqrt_sq (norm_nonneg c),
    paperHilbertSchmidtNorm]


/-- Nonzero scalar multiplication preserves Hilbert--Schmidt membership. -/
theorem isPaperHilbertSchmidt_smul_iff
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (c : 𝕜) (hc : c ≠ 0) (A : E →L[𝕜] F) :
    IsPaperHilbertSchmidt (c • A) ↔ IsPaperHilbertSchmidt A := by
  unfold IsPaperHilbertSchmidt
  rw [paperHilbertSchmidtEnergy_smul]
  constructor
  · intro h
    by_contra hA
    have htop : paperHilbertSchmidtEnergy A = ⊤ := by simpa using hA
    rw [htop, ENNReal.mul_top] at h
    · exact h rfl
    · simp [hc]
  · intro hA
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA

/-- Negation preserves Hilbert--Schmidt membership. -/
@[simp]
theorem isPaperHilbertSchmidt_neg_iff
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    IsPaperHilbertSchmidt (-A) ↔ IsPaperHilbertSchmidt A := by
  have h := isPaperHilbertSchmidt_smul_iff (-1 : 𝕜) (by simp) A
  rwa [neg_one_smul] at h


/-- Negation preserves the square norm. -/
@[simp]
theorem paperHilbertSchmidtNorm_neg
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    paperHilbertSchmidtNorm (-A) = paperHilbertSchmidtNorm A := by
  apply SameApproximationSingularSequence.paperHilbertSchmidtNorm_eq
  intro n
  rw [← neg_one_smul 𝕜 A, ContinuousLinearMap.approximationNumber_smul]
  simp


/-- Two-sided ideal control of the extended Hilbert--Schmidt energy. -/
theorem paperHilbertSchmidtEnergy_comp_le
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    {G : Type vG} {H : Type vH}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : H →L[𝕜] E) :
    paperHilbertSchmidtEnergy (L ∘L A ∘L R) ≤
      ENNReal.ofReal ((‖L‖ * ‖R‖) ^ 2) *
        paperHilbertSchmidtEnergy A := by
  unfold paperHilbertSchmidtEnergy
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  have hsing := approximationSingularValue_comp_le n L A R
  have hnonneg : 0 ≤ approximationSingularValue n (L ∘L A ∘L R) :=
    approximationSingularValue_nonneg _ _
  have hbound :
      approximationSingularValue n (L ∘L A ∘L R) ^ 2 ≤
        (‖L‖ * ‖R‖) ^ 2 * approximationSingularValue n A ^ 2 := by
    calc
      approximationSingularValue n (L ∘L A ∘L R) ^ 2
          ≤ (‖L‖ * approximationSingularValue n A * ‖R‖) ^ 2 :=
        pow_le_pow_left₀ hnonneg hsing 2
      _ = (‖L‖ * ‖R‖) ^ 2 * approximationSingularValue n A ^ 2 := by ring
  rw [← ENNReal.ofReal_mul (sq_nonneg (‖L‖ * ‖R‖))]
  exact ENNReal.ofReal_le_ofReal hbound

/-- The two-sided ideal property for canonical Hilbert--Schmidt membership. -/
theorem IsPaperHilbertSchmidt.comp
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    {G : Type vG} {H : Type vH}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {A : E →L[𝕜] F} (hA : IsPaperHilbertSchmidt A)
    (L : F →L[𝕜] G) (R : H →L[𝕜] E) :
    IsPaperHilbertSchmidt (L ∘L A ∘L R) := by
  unfold IsPaperHilbertSchmidt at hA ⊢
  refine ne_top_of_le_ne_top ?_ (paperHilbertSchmidtEnergy_comp_le L A R)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA

/-- Sharp two-sided ideal norm estimate. -/
theorem paperHilbertSchmidtNorm_comp_le
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    {G : Type vG} {H : Type vH}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : F →L[𝕜] G) {A : E →L[𝕜] F} (hA : IsPaperHilbertSchmidt A)
    (R : H →L[𝕜] E) :
    paperHilbertSchmidtNorm (L ∘L A ∘L R) ≤
      ‖L‖ * paperHilbertSchmidtNorm A * ‖R‖ := by
  have henergy := paperHilbertSchmidtEnergy_comp_le L A R
  have hfinite :
      paperHilbertSchmidtEnergy (L ∘L A ∘L R) ≠ ⊤ :=
    hA.comp L R
  rw [paperHilbertSchmidtNorm, paperHilbertSchmidtNorm]
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA) henergy
  calc
    Real.sqrt (paperHilbertSchmidtEnergy (L ∘L A ∘L R)).toReal
        ≤ Real.sqrt
            ((ENNReal.ofReal ((‖L‖ * ‖R‖) ^ 2) *
              paperHilbertSchmidtEnergy A).toReal) :=
      Real.sqrt_le_sqrt hreal
    _ = ‖L‖ * Real.sqrt (paperHilbertSchmidtEnergy A).toReal * ‖R‖ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
        Real.sqrt_mul (sq_nonneg (‖L‖ * ‖R‖)),
        Real.sqrt_sq (mul_nonneg (norm_nonneg L) (norm_nonneg R))]
      ring

/-- Inclusion and orthogonal projection contractions do not enlarge the
square norm. -/
theorem paperHilbertSchmidtNorm_comp_isometries_le
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    {G : Type vG} {H : Type vH}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : F →L[𝕜] G) {A : E →L[𝕜] F} (hA : IsPaperHilbertSchmidt A)
    (R : H →L[𝕜] E) (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    paperHilbertSchmidtNorm (L ∘L A ∘L R) ≤
      paperHilbertSchmidtNorm A := by
  calc
    paperHilbertSchmidtNorm (L ∘L A ∘L R)
        ≤ ‖L‖ * paperHilbertSchmidtNorm A * ‖R‖ :=
      paperHilbertSchmidtNorm_comp_le L hA R
    _ ≤ 1 * paperHilbertSchmidtNorm A * 1 := by
      gcongr <;>
        simpa using paperHilbertSchmidtNorm_nonneg A
    _ = paperHilbertSchmidtNorm A := by ring

/-- Squared norm identity on the canonical ideal. -/
theorem sq_paperHilbertSchmidtNorm
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A : E →L[𝕜] F} (_hA : IsPaperHilbertSchmidt A) :
    paperHilbertSchmidtNorm A ^ 2 =
      (paperHilbertSchmidtEnergy A).toReal := by
  unfold paperHilbertSchmidtNorm
  rw [Real.sq_sqrt]
  exact ENNReal.toReal_nonneg

end

end ExactSinTheta
end DavisKahan
end TauCeti