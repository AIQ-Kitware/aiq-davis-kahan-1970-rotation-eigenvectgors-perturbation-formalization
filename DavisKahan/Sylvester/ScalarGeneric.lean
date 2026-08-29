/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Anthropic Claude Opus 5
-/
import DavisKahan.Sylvester.RealUnbounded

/-!
# The unbounded Sylvester Ky Fan estimate as a property of the scalar field

The manuscript Section 5 Sylvester theorem exists here twice and only twice.
`davisKahan1970_sylvester_complex` is proved over `ℂ`, through the vendored
Spectra spectral cutoffs and the ordered engine; `real_unbounded_sylvester_kyFan`
is proved over `ℝ`, by complexifying and descending through exact invariance of
the approximation numbers.  Neither is `RCLike`-generic, and neither can be made
so by a case split: `RCLike` carries no discriminator separating its two intended
models, so "it holds for `ℝ` and it holds for `ℂ`" is not by itself a proof of
anything about a general `RCLike` field.

This module does for that estimate exactly what
`ContinuousLinearMap.HasMinMaxLowerBoundEverywhere` already does one layer down
for the min--max lower bound: it names the estimate as a property *of the scalar
field*, quantified over every pair of Hilbert spaces at once, and supplies the
two instances.  A statement over `[RCLike 𝕜]` may then take the class as an
instance binder; at `ℝ` and at `ℂ` instance search discharges it, so no
hypothesis is added to any statement that was previously written out over a
fixed field.

Only the finite Ky Fan gauges appear.  That is the weakest form that still
generates the rest: wherever a `KyFanDominantIdealFamily` is in hand, Fan
dominance recovers the arbitrary-ideal conclusion, which is how both
`davisKahan1970_sylvester_real` and the source-facing `PaperUnitaryInvariantNorm`
statements are already built.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe u v

/-- **The unbounded Sylvester Ky Fan estimate, as a property of the scalar field
alone.**

The field-specific theorems are statements about one pair of Hilbert spaces at a
time.  A statement that is generic in `𝕜` cannot invoke either of them, so it
needs the estimate quantified uniformly over every pair of spaces.  This class is
that quantification and nothing more.

Both fields are instances: `hasUnboundedSylvesterKyFan_complex` from the Section 5
theorem itself, `hasUnboundedSylvesterKyFan_real` from the complexification
descent.  Note what the class does *not* assume: no ideal family, no Fan
dominance, and no membership hypothesis -- the finite Ky Fan gauges are
everywhere finite, so the estimate needs none. -/
class HasUnboundedSylvesterKyFan (𝕜 : Type u) [RCLike 𝕜] : Prop where
  /-- Every domain-aware Sylvester equation between closed self-adjoint operators
  separated by `δ` obeys the sharp majorization at every finite Ky Fan gauge. -/
  out : ∀ {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A : E →ₗ.[𝕜] E}
    {B : F →ₗ.[𝕜] F},
    IsSelfAdjoint A → IsSelfAdjoint B →
      ∀ {X C : F →L[𝕜] E} {δ : ℝ}, 0 < δ →
        FormBoundedSylvesterGap A B δ →
        TauCeti.LinearPMap.SylvesterEquation A B X C →
        ∀ k : ℕ,
          δ * kyFanApproximationGauge k X ≤ kyFanApproximationGauge k C

section

variable {𝕜 : Type u} [RCLike 𝕜] [HasUnboundedSylvesterKyFan.{u, v} 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Scalar-generic finite Ky Fan majorization for a domain-aware Sylvester
equation.  This is the applied form; the class field is the quantified one. -/
theorem unbounded_sylvester_kyFan
    {A : E →ₗ.[𝕜] E}
    {B : F →ₗ.[𝕜] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X C : F →L[𝕜] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (k : ℕ) :
    δ * kyFanApproximationGauge k X ≤ kyFanApproximationGauge k C :=
  HasUnboundedSylvesterKyFan.out hA hB hδ hgap hEq k

end

/-- `ℂ` satisfies the estimate: it is the Section 5 theorem, read at the fixed
finite Ky Fan family for each positive index. -/
instance hasUnboundedSylvesterKyFan_complex :
    HasUnboundedSylvesterKyFan.{0, v} ℂ where
  out := by
    intro E F _ _ _ _ _ _ A B hA hB X C δ hδ hgap hEq k
    by_cases hk : k = 0
    · subst k
      simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hraw := davisKahan1970_sylvester_complex
        (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hkpos) hA hB hδ hgap hEq
        (KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℂ) k hkpos C)
      simpa only [KyFanDominantIdealFamily.kyFan_gauge] using hraw.2

/-- `ℝ` satisfies the estimate, by the complexification descent. -/
instance hasUnboundedSylvesterKyFan_real :
    HasUnboundedSylvesterKyFan.{0, v} ℝ where
  out := by
    intro E F _ _ _ _ _ _ A B hA hB X C δ hδ hgap hEq k
    exact real_unbounded_sylvester_kyFan hA hB hδ hgap hEq k

end

end ExactSinTheta
end DavisKahan
end TauCeti
