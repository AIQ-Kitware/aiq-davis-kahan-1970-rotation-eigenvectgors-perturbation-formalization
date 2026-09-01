/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/

import DavisKahan.Geometry.Halmos.Realization
import ForTauCeti.Analysis.InnerProductSpace.RealContinuousFunctionalCalculus

/-!
# Davis--Kahan 1970, Theorem 3.1, the realization half

The classification half of Theorem 3.1 -- `twoProjection_operator_classification`
in `Section3Classification.lean` -- says that the angle datum determines the
pair.  The paper's sentence (ii) is the converse of the *existence* kind: every
admissible angle datum is attained.  This module states that sentence, in two
shapes: from a packaged `HalmosAngleDatum`, and from the printed data -- two
Hermitian operators `Θ₀`, `Θ₁` confined to `[0, π/2]` and an intertwining
partial isometry `J`.

The construction is owned upstream by `Geometry/Halmos/Realization.lean`; every
statement here is grounded on it by `:=`, so there is a single source of truth
and no geometry is redone.

Everything is `RCLike`-generic, so the real case is an instantiation rather than
a second theorem; it is recorded at the end as an `example`, which adds no
declaration but fails loudly if the `𝕜 = ℝ` hypothesis block ever stops being
inhabited.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan

universe u v

section Realization

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Davis--Kahan 1970, Theorem 3.1, the realization half — the paper's sentence
(ii).**

The classification half (`twoProjection_operator_classification`, and
`TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification_complex` in the paper's
multiplicity phrasing) says that the angle datum determines the pair.  This says the converse of the *existence* kind: every
admissible angle datum is *attained*.  Given `cos Θ₀, sin Θ₀` on `E`,
`cos Θ₁, sin Θ₁` on `F` and the intertwiner `J₀` that matches their spectral
multiplicities away from the angle `0`, the two subspaces

`U = E`-factor,  `V = W₀ E` with `W₀ x = (cos Θ₀ x, J₀ sin Θ₀ x)`

of `E ⊕₂ F` satisfy, in order:

1. the compression of `P_V` to `U` is `cos² Θ₀`;
2. the compression of `P_Vᗮ` to `Uᗮ` is `cos² Θ₁`;
3. `U ⊓ V` is the angle-`0` eigenspace on the `P`-side;
4. `Uᗮ ⊓ Vᗮ` is the angle-`0` eigenspace on the `Pᗮ`-side;
5. `U ⊓ Vᗮ` is the angle-`π/2` eigenspace on the `P`-side;
6. `Uᗮ ⊓ V` is the angle-`π/2` eigenspace on the `Pᗮ`-side;
7. the two crossed defects are isometric.

Items 3--7 are the mathematical content of the theorem's hypothesis: the
`π/2` multiplicities are *forced* to agree, because `J₀` restricts to a linear
isometric equivalence between them, while the `0` multiplicities are the two
kernels of `sin Θ₀` and `sin Θ₁`, which `J₀` never sees.  That the latter are
genuinely unconstrained is witnessed by
`theorem3_1_realization_zeroAngle_unconstrained`.

Grounded by `:=` on `Geometry/Halmos/Realization.lean`, so there is a single
source of truth.  The block matrix behind item 1 and item 2 is
`starProjection_targetSubspace_apply`, which reproduces equation (3.7) of the
source, both off-diagonal entries positive. -/
theorem theorem3_1_realization (d : HalmosAngleDatum 𝕜 E F) :
    (∀ x : E, (sourceSubspace 𝕜 E F).starProjection
        (d.targetSubspace.starProjection (modelInl 𝕜 E F x)) =
          modelInl 𝕜 E F (d.cos₀ (d.cos₀ x))) ∧
      (∀ y : F, (sourceSubspace 𝕜 E F)ᗮ.starProjection
        ((d.targetSubspace)ᗮ.starProjection (modelInr 𝕜 E F y)) =
          modelInr 𝕜 E F (d.cos₁ (d.cos₁ y))) ∧
      halmosCommonPart (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.sin₀ : E →ₗ[𝕜] E)) ∧
      halmosExteriorPart (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.sin₁ : F →ₗ[𝕜] F)) ∧
      halmosSourceDefect (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.cos₀ : E →ₗ[𝕜] E)) ∧
      halmosTargetDefect (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.cos₁ : F →ₗ[𝕜] F)) ∧
      Nonempty (↥(halmosSourceDefect (sourceSubspace 𝕜 E F) d.targetSubspace) ≃ₗᵢ[𝕜]
        ↥(halmosTargetDefect (sourceSubspace 𝕜 E F) d.targetSubspace)) :=
  ⟨d.compress_source_eq, d.compress_sourceOrthogonal_eq, d.halmosCommonPart_eq,
    d.halmosExteriorPart_eq, d.halmosSourceDefect_eq, d.halmosTargetDefect_eq,
    d.nonempty_halmosSourceDefect_equiv_targetDefect⟩
section OfAngles

variable [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]
  [Algebra ℝ (F →L[𝕜] F)] [IsScalarTower ℝ 𝕜 (F →L[𝕜] F)]
  [ContinuousFunctionalCalculus ℝ (F →L[𝕜] F) IsSelfAdjoint]

/-- **Davis--Kahan 1970, Theorem 3.1, sentence (ii), in the printed shape: stated
from the angle operators rather than from a packaged datum.**

`theorem3_1_realization` consumes a `HalmosAngleDatum`, which carries
`cos Θ₀, sin Θ₀, cos Θ₁, sin Θ₁` and the intertwiner as five independent fields.
The paper does not.  It says "given such `Θⱼ` acting on spaces `Hⱼ`", where
"such" refers to the theorem's own sentence "these are arbitrary Hermitian
operators satisfying the following conditions: `0 ≤ Θⱼ ≤ π/2`; ... and the
spectral multiplicity functions of the `Θⱼ` are the same except for a possible
difference in the multiplicity of `{0}`", and then extracts from that last
condition "some isometry `J₀` of `closure (ran Θ₀)` onto `closure (ran Θ₁)` such
that `J₀ Θ₀ J₀⁻¹` agrees on its domain with `Θ₁`".  So the printed data are two
Hermitian operators and one intertwining partial isometry — and that is this
statement's hypothesis list.  The datum is built inside the proof by
`HalmosAngleDatum.ofIntertwinedAngles`, and each
`cos Θⱼ`, `sin Θⱼ` in the conclusion is the continuous functional calculus of
`Θⱼ` rather than an opaque field, so the seven conjuncts of
`theorem3_1_realization` are read here directly off `Θ₀`, `Θ₁` and `J`.

**The two partial-isometry hypotheses are the paper's, not an artifact.**
`hisom` and `hcoisom` say that `J` is isometric on `ran sin Θ₀` and co-isometric
onto `ran sin Θ₁`; that is the content of the printed `J₀`, and it is a
multiplicity statement, invisible to a functional calculus of one operator at a
time.  Everything else the datum needs is derived.

**On the spectral confinement.**  `_hspec₀` and `_hspec₁` are the printed
`0 ≤ Θⱼ ≤ π/2`.  They are taken as hypotheses here and are deliberately unused in
the proof, hence the underscores.  They belong here rather than on the
constructor: `HalmosAngleDatum` records no nonnegativity, and none of the ten
fields `ofIntertwinedAngles` derives needs one — `cos² + sin² = 1` and
`J f(Θ₀) = f(Θ₁) J` hold over all of `ℝ` — so assuming confinement there would
narrow the constructor for nothing.  What confinement buys is that the statement
*reads* as the printed sentence: on `[0, π/2]` one has `sin t = 0 ↔ t = 0` and
`cos t = 0 ↔ t = π/2`, so conjuncts 3--4 exhibit the two angle-`0` spaces and
conjuncts 5--6 the two angle-`π/2` spaces, which is what Davis and Kahan mean by
calling the `Θⱼ` angle operators.  Dropping the two hypotheses would leave the
same theorem with the same proof and a weaker reading; keeping them costs
nothing, so they are kept.

`RCLike`-generic.  The real case is therefore an instantiation and not a second
theorem: `theorem3_1_realization_ofAngles_real`. -/
theorem theorem3_1_realization_ofAngles
    {Θ₀ : E →L[𝕜] E} {Θ₁ : F →L[𝕜] F}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (_hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (_hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (J : E →L[𝕜] F) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
    (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
    (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁) :
    (∀ x : E, (sourceSubspace 𝕜 E F).starProjection
        ((HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace.starProjection (modelInl 𝕜 E F x)) =
          modelInl 𝕜 E F (cfc Real.cos Θ₀ (cfc Real.cos Θ₀ x))) ∧
      (∀ y : F, (sourceSubspace 𝕜 E F)ᗮ.starProjection
        (((HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace)ᗮ.starProjection (modelInr 𝕜 E F y)) =
          modelInr 𝕜 E F (cfc Real.cos Θ₁ (cfc Real.cos Θ₁ y))) ∧
      halmosCommonPart (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.sin Θ₀ : E →L[𝕜] E) : E →ₗ[𝕜] E)) ∧
      halmosExteriorPart (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.sin Θ₁ : F →L[𝕜] F) : F →ₗ[𝕜] F)) ∧
      halmosSourceDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.cos Θ₀ : E →L[𝕜] E) : E →ₗ[𝕜] E)) ∧
      halmosTargetDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.cos Θ₁ : F →L[𝕜] F) : F →ₗ[𝕜] F)) ∧
      Nonempty (↥(halmosSourceDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace) ≃ₗᵢ[𝕜]
        ↥(halmosTargetDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace)) :=
  theorem3_1_realization (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom)

end OfAngles
/-- **The multiplicity at angle `0` is genuinely unconstrained.**

The all-`0` datum over an arbitrary pair `(E, F)` of Hilbert spaces
realizes `U = V`, whose angle-`0` spaces are the whole of `E` on the `P`-side and
the whole of `F` on the `Pᗮ`-side.  `E` and `F` are unrelated, so no admissibility
condition at angle `0` can be imposed — in contrast to the angle `π/2`, where
item 7 of `theorem3_1_realization` forces the two multiplicities to agree.
Together the two statements are why Davis and Kahan's hypothesis is asymmetric
between `0` and `π/2`. -/
theorem theorem3_1_realization_zeroAngle_unconstrained
    (𝕜 : Type*) [RCLike 𝕜]
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (F : Type v) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] :
    halmosCommonPart (sourceSubspace 𝕜 E F) (trivialHalmosAngleDatum 𝕜 E F).targetSubspace =
        sourceSubspace 𝕜 E F ∧
      halmosExteriorPart (sourceSubspace 𝕜 E F)
          (trivialHalmosAngleDatum 𝕜 E F).targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F)) ⊤ :=
  ⟨trivial_halmosCommonPart_eq 𝕜 E F, trivial_halmosExteriorPart_eq 𝕜 E F⟩
end Realization

/-! ## Theorem 3.1, sentence (ii), over a real Hilbert space

`theorem3_1_realization_ofAngles` is `RCLike`-generic, so its real form is an
instantiation and not a theorem.  It is recorded as an `example` rather than by
name deliberately: it adds no declaration, and it fails loudly if the `𝕜 = ℝ`
hypothesis block ever stops being inhabited.  That block is the only thing that
could have made the real case cost something -- the wrapper needs
`ContinuousFunctionalCalculus ℝ (Hⱼ →L[ℝ] Hⱼ) IsSelfAdjoint` on *both* spaces to
form `cos Θⱼ` and `sin Θⱼ`, and instance search supplies it from
`ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint`, in
unrestricted dimension.  Two of the seven conjuncts are read off below: the
angle-`π/2` space on the `P`-side, and the isometry between the two crossed
defects that forces the two `π/2` multiplicities to agree. -/

section RealScalars

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
  [CompleteSpace H₂]

example {Θ₀ : H₁ →L[ℝ] H₁} {Θ₁ : H₂ →L[ℝ] H₂}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (J : H₁ →L[ℝ] H₂) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
    (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
    (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁) :
    halmosSourceDefect (sourceSubspace ℝ H₁ H₂)
        (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
      Submodule.map (modelInl ℝ H₁ H₂ : H₁ →ₗ[ℝ] WithLp 2 (H₁ × H₂))
        (LinearMap.ker ((cfc Real.cos Θ₀ : H₁ →L[ℝ] H₁) : H₁ →ₗ[ℝ] H₁)) ∧
    Nonempty (↥(halmosSourceDefect (sourceSubspace ℝ H₁ H₂)
        (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
          hcoisom).targetSubspace) ≃ₗᵢ[ℝ]
      ↥(halmosTargetDefect (sourceSubspace ℝ H₁ H₂)
        (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
          hcoisom).targetSubspace)) :=
  ⟨(theorem3_1_realization_ofAngles hΘ₀ hΘ₁ hspec₀ hspec₁ J hJ hisom hcoisom).2.2.2.2.1,
    (theorem3_1_realization_ofAngles hΘ₀ hΘ₁ hspec₀ hspec₁ J hJ hisom hcoisom).2.2.2.2.2.2⟩
end RealScalars

end DavisKahan1970
end TauCeti
