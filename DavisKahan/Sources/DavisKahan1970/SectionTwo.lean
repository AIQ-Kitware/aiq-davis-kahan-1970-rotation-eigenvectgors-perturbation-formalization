/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.PaperSurface
import DavisKahan.Sources.DavisKahan1970.TanThetaUnboundedAmbient
import DavisKahan.Sources.DavisKahan1970.TanThetaUnboundedAmbientReal
import DavisKahan.Sources.DavisKahan1970.SinTwoTheta
import DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedAmbientExact
import DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedExactReal

/-!
# The four Section 2 theorems, in one place

Davis--Kahan 1970 opens with four unnumbered theorems -- `sin Θ`, `tan Θ`,
`sin 2Θ`, `tan 2Θ` -- and the rest of the paper is their proof, their sharpness,
and their consequences.  **This module is the public inventory of those four, over
both scalar fields, and is the module to cite.**

```
TauCeti.DavisKahan1970.SectionTwo.sinTheta       sinTheta_real
TauCeti.DavisKahan1970.SectionTwo.tanTheta       tanTheta_real
TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta    sinTwoTheta_real
TauCeti.DavisKahan1970.SectionTwo.tanTwoTheta    tanTwoTheta_real
```

Every one of the eight is at the accepted full source scope, and its *own* type
says so: an unbounded self-adjoint `LinearPMap` ambient operator, a Hilbert space
of arbitrary dimension, a `PaperUnitaryInvariantNorm` -- the paper's symmetric
gauge, not the operator norm -- and both printed conclusions, the ideal membership
and the inequality.  No capability class, no finite-dimensionality hypothesis, no
proof-vehicle operator in the conclusion, and no branch or pole certificate
demanded of the caller.  Nothing has to be assembled from a finite-dimensional
"headline" plus a companion plus an audit note.

The declarations here are `alias`es, so each has exactly the type of the theorem
it names; the proofs and the supporting theory stay in the modules where they
belong.  The implementations they select are, in order:

| result | complex | real |
| --- | --- | --- |
| `sin Θ` | `DavisKahan1970.sinTheta_complex` | `DavisKahan1970.sinTheta_real` |
| `tan Θ` | `tanTheta_unbounded_ambient_ritz_paperUINorm` | `…_real` |
| `sin 2Θ` | `sinTwoTheta_addBounded_paperUINorm_angleOperator` | `…_real_angleOperator` |
| `tan 2Θ` | `tanTwoTheta_unbounded_ambient_paperAngle_paperUINorm` | `…_real` |

## What the four ask for, and what they do not

Each takes ordinary mathematical data: the operator, the subspace or spectral
selection, the gap, the bounded residual or perturbation, the norm, and the ideal
membership of the perturbation.  Structural facts that are properties of those
objects rather than hypotheses of the theorem are carried by objects with
constructors from the generic vocabulary --
`DavisKahan.UnboundedRitzPair` (`.ofTrialBlock`),
`DavisKahan.ReducingComplement` (`.ofReducesSubspace`), and
`DavisKahan.ReflectionIntertwines` (`.ofReducesSubspace`) -- so a caller who holds
a `TauCeti.LinearPMap.ReducesSubspace` never meets a competing reduction
vocabulary.

The proof vehicles do not appear: not `HasUnboundedSylvesterKyFan`, not
`ContinuousLinearMap.HasMinMaxLowerBoundEverywhere`, not `sinTwoThetaIdealBlock`,
not `unboundedReflectionTangent`, and not a caller-built spectral reflection.

## Angle conventions in the conclusions

* `sin Θ` concludes on the paper's own `(I - F₀F₀⋆) E₀`, which is what the printed
  theorem displays.
* `tan Θ` concludes on the *ambient* `paperTanAngleOperatorC` / `…R`.
* `sin 2Θ` concludes on the *directed* double-angle sine `2 sin Θ cos Θ`.  Directed
  and ambient differ in multiplicity -- an ambient angle object carries each
  principal angle twice where the one-sided block carries it once -- and the
  directed operator is the block's partner, so it is the faithful target here.
* `tan 2Θ` concludes on the *ambient* branch-free `|tan 2Θ|`.  Its block is
  two-sided, so here the ambient object is the partner.  A unitarily invariant
  norm cannot distinguish `tan 2Θ` from `|tan 2Θ|`, and only the latter is defined
  without a quarter-acute branch hypothesis.

Getting that directed/ambient distinction backwards once cost this development a
false claim that the `tan 2Θ` transport could not exist; the census records the
retraction.

## What is deliberately *not* here

Everything else in the development remains available and is unaffected: the
scalar-generic presentation forms, the directed and whole-space variants, the
finite-dimensional specializations, the operator-norm statements, the Ky Fan
families, and the bundled-problem entry points such as
`TauCeti.DavisKahan1970.sinTheta`.  Those are useful and are kept; they are simply
not the theorem inventory a reader should have to assemble.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. 7 (1970), 1--46: the four unnumbered Section 2 theorems,
  the Section 6 ambient assembly, and the Appendix to Section 6.
-/

namespace TauCeti
namespace DavisKahan1970
namespace SectionTwo

/-! ## `sin Θ` -/

/-- **Davis--Kahan 1970, the `sin Θ` theorem, over `ℂ`.**

`δ · N(sin Θ₀) ≤ N(R)` with `sin Θ₀ = (I - F₀F₀⋆) E₀`, together with membership of
`sin Θ₀` in the norm's ideal.  Unbounded self-adjoint ambient operator, arbitrary
Hilbert dimension, the whole `FormBoundedSylvesterGap` rather than one of its
branches, and an arbitrary source unitarily invariant norm.

`DavisKahan1970.sinTheta_complex_of_intervalExterior` states the same theorem with
the gap written out as the printed interval/exterior separation. -/
alias sinTheta := _root_.DavisKahan1970.sinTheta_complex

/-- **Davis--Kahan 1970, the `sin Θ` theorem, over `ℝ`.**

The real sibling of `sinTheta`, with the same argument list, the same full gap
scope and the same two conclusions.  The descent from the complex case happens
inside the proof and is not visible in the statement. -/
alias sinTheta_real := _root_.DavisKahan1970.sinTheta_real

/-! ## `tan Θ` -/

/-- **Davis--Kahan 1970, the `tan Θ` theorem, over `ℂ`.**

`δ · N(tan Θ) ≤ N(H)` on the ambient tangent `paperTanAngleOperatorC U V`, with
ideal membership, for an unbounded self-adjoint `A`, its unbounded Ritz pair on
the trial subspace `U`, and a subspace `V` whose complement reduces `A`.

The caller supplies the mathematics -- semiboundedness of the compression above
`α`, coercivity `α + δ` on the unwanted subspace, the standing crossed-defect
condition (3.5) of Section 3, and the Rayleigh--Ritz residual identity -- and
nothing else: the structural facts live in `DavisKahan.UnboundedRitzPair` and
`DavisKahan.ReducingComplement`. -/
alias tanTheta := tanTheta_unbounded_ambient_ritz_paperUINorm

/-- **Davis--Kahan 1970, the `tan Θ` theorem, over `ℝ`.**

The real sibling of `tanTheta`, on the real ambient tangent
`paperTanAngleOperatorR U V`.  Space, operator, subspaces, perturbation, angle and
gauge are all real; only the Appendix Ky Fan passage is proved by
complexification, at the level where approximation numbers are preserved
exactly. -/
alias tanTheta_real := tanTheta_unbounded_ambient_ritz_paperUINorm_real

/-! ## `sin 2Θ` -/

/-- **Davis--Kahan 1970, the `sin 2Θ` theorem, over `ℂ`.**

`δ · N(sin 2Θ) ≤ 2 N(E)`, with the paper's sharp factor two, for the spectral
subspaces selected by `B` from an unbounded self-adjoint `A` and by `S` from the
bounded perturbation `A + E`, under the printed spectrum gap.  The conclusion is
on the directed double-angle sine `2 sin Θ cos Θ`, not on the proof's overlap
block. -/
alias sinTwoTheta := sinTwoTheta_addBounded_paperUINorm_angleOperator

/-- **Davis--Kahan 1970, the `sin 2Θ` theorem, over `ℝ`.**

The real sibling of `sinTwoTheta`, reaching the ideal layer through
`FormBoundedSylvesterGap` -- which is the hypothesis shape the real proof actually
has -- and concluding on the directed double-angle sine of the real pair, read in
the canonical complexification where this development keeps the real double-angle
operators. -/
alias sinTwoTheta_real := sinTwoTheta_addBounded_paperUINorm_real_angleOperator

/-! ## `tan 2Θ` -/

/-- **Davis--Kahan 1970, the `tan 2Θ` theorem, over `ℂ`.**

`(b - a) · N(|tan 2Θ|) ≤ 2 N(B)` on the paper's ambient branch-free double-angle
tangent, with ideal membership, for an unbounded self-adjoint `A`, a bounded
self-adjoint perturbation `B` odd for the selected spectral subspace, and a
subspace `V` whose reflection intertwines `A + B`
(`DavisKahan.ReflectionIntertwines`, built from a `ReducesSubspace` by
`.ofReducesSubspace`).

No pole certificate is asked for: the ordered gap forces the reflection's diagonal
block to be a unit, and that unit excludes the quarter-turn poles. -/
alias tanTwoTheta := tanTwoTheta_unbounded_ambient_paperAngle_paperUINorm

/-- **Davis--Kahan 1970, the `tan 2Θ` theorem, over `ℝ`.**

The real sibling of `tanTwoTheta`, on the real ambient `|tan 2Θ|`.  The real
statement is transported from the complex one through the complexification, with
no loss of constant or norm class and no second analytic proof. -/
alias tanTwoTheta_real := tanTwoTheta_unbounded_ambient_paperAngle_paperUINorm_real

end SectionTwo
end DavisKahan1970
end TauCeti
