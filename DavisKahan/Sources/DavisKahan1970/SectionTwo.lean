/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.PaperSurface
import DavisKahan.Sources.DavisKahan1970.TanThetaUnboundedAmbient
import DavisKahan.Sources.DavisKahan1970.TanThetaUnboundedAmbientReal
import DavisKahan.Sources.DavisKahan1970.SinTwoTheta
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbientUnbounded
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaUnboundedDirectedResidual
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaUnboundedDirectedResidualReal
import DavisKahan.Sources.DavisKahan1970.TanThetaDirectedUnbounded
import DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedAmbientExact
import DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedExactReal

/-!
# The four Section 2 theorems, in one place

Davis--Kahan 1970 opens with four unnumbered theorems -- `sin Θ`, `tan Θ`,
`sin 2Θ`, `tan 2Θ` -- and the rest of the paper is their proof, their sharpness,
and their consequences.  **This module is the public inventory of those four, over
both scalar fields, and is the module to cite.**

```
TauCeti.DavisKahan1970.SectionTwo.sinTheta_complex       sinTheta_real
TauCeti.DavisKahan1970.SectionTwo.tanTheta_complex       tanTheta_real
TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta_complex    sinTwoTheta_real
TauCeti.DavisKahan1970.SectionTwo.tanTwoTheta_complex    tanTwoTheta_real
```

## `sinTheta` is bound; the other three short names are reserved

`SectionTwo.sinTheta` names the scalar-generic endpoint
`DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike`: the printed
statement, over an arbitrary `RCLike` field, at the printed scope.

`SectionTwo.tanTheta`, `.sinTwoTheta` and `.tanTwoTheta` name nothing.  They are
reserved for the same thing -- generic over `RCLike 𝕜` **and** at the printed
source scope -- and no such declaration exists for those three.  Binding a short
name to the complex statement is what previously made `SectionTwo.sinTheta` read
as the canonical theorem when it was the complex one, so the three stay empty.

The gap is measured against the *paper*, not against the strongest form the
library happens to hold.  The distributable source specification fixes the scope:
the four results are stated "for infinite as well as finite dimensional separable
Hilbert spaces", the spectral intervals in the gap hypotheses "may be
half-infinite", and the norm is an arbitrary unitary-invariant norm.  Against
that, every axis on which the closest scalar-generic declaration differs from the
fixed-field endpoint it should match:

| axis | `tan Θ` | `sin 2Θ` | `tan 2Θ` |
| --- | --- | --- | --- |
| closest `RCLike` declaration | `tanTheta_directed_finiteDimensional_paperUINorm_rclike` | `sinTwoTheta_directed_finiteDimensional_paperUINorm_rclike` | `tanTwoTheta_branchFree_bounded_finiteSubspace_paperUINorm_rclike` |
| ambient dimension | finite `E`, `F` | finite `E`, `F` | arbitrary ✓ |
| ambient operator | bounded `E →ₗ[𝕜] E` | bounded | bounded `E →L[𝕜] E` |
| trial subspace | -- | -- | `[FiniteDimensional 𝕜 U]` |
| Ritz scope | bounded compression | -- | -- |
| angle in the conclusion | directed tangent supplied as a parameter with a `singularValues` characterization | `sinTwoThetaEmbedding U X`, the trial-coordinate `2S|C|` | an arbitrary representative whose approximation numbers rearrange the branch-free scalars |
| endpoint's angle | ambient `paperTanAngleOperator` | directed double-angle sine of the spectral pair | ambient `paperAbsTanTwoAngleOperator` |
| norm | `PaperUnitaryInvariantNorm` ✓ | ✓ | ✓ |
| gap | interval/exterior, against the endpoint's `FormBoundedSylvesterGap` | same | ordered form `a < b` |

The `sin Θ` bridge that produced the binding above was a repackaging: the
component theorem already proved the paper-norm statement by applying the
full-gap ideal-family theorem one Ky Fan index at a time, so taking `hgap`
directly cost nothing.

### Two obstacles, and they are different

For the other three, a scalar-generic statement meets **a definitional obstacle
first and a field-specific analytic layer behind it.**  Both are real; neither
alone is the whole story, and an earlier version of this file claimed only the
first.

*Definitional.*  The objects the three conclusions name exist only as fixed-field
pairs: `...C` is defined natively and `...R` by transport --
`paperTanAngleOperatorR U V = realPartOperator (paperTanAngleOperatorC
(complexifySubmodule U) (complexifySubmodule V))`, and likewise for `sin 2Θ`,
`tan 2Θ` and `|tan 2Θ|`.  There is no `paperTanAngleOperator` over `𝕜`, so a
scalar-generic statement cannot presently be *written*.

*Availability.*  Writing one is not a matter of copying the `ℂ` definition under a
`[RCLike 𝕜]` binder.  `sinAngleOperatorC` is `ContinuousLinearMap.modulus (P_U -
P_V)`, and `ContinuousLinearMap.modulus` carries
`[ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]` as a hypothesis --
Mathlib declines to register that as an instance precisely because it is not
available outside `ℂ`.  So the arcsin/tan layers built on it are not "essentially
available for arbitrary `RCLike` operator algebras"; they are available where that
functional calculus is.

*Analytic.*  Behind both sits a genuine field-specific proof layer.  The `tan Θ`
route runs through `UnboundedCompressionTrialData.all_kyFan_core`, which lives in
the `ℂ`-pinned half of `TanTheta/Theorem63UnboundedCompression.lean` -- the file
splits a scalar-generic algebra layer from a truncation layer fixed to
`[InnerProductSpace ℂ H]` because the latter uses the projection-valued spectral
measure -- and `TanThetaUnboundedAmbientReal.lean` says in its own header that the
real route complexifies the data and reuses that complex Appendix cutoff/Ky-Fan
argument.  A generic definition would also owe a theorem that its `ℝ` instance
agrees with the transport-defined `...R`, or every existing real theorem stops
applying to it.

None of this says the mathematics resists generalization; it says the work is
operator-theoretic infrastructure, not a rename.
`tanTwoTheta_branchFree_bounded_paperUINorm_complex` is evidence on the other
side: it is the arbitrary-trial-subspace form over `ℂ`, so the finite-subspace
restriction is already known to be removable at one field.

## Three of the four printed theorems have TWO clauses

`sin Θ` prints one conclusion.  `tan Θ`, `sin 2Θ` and `tan 2Θ` each print two:

```text
directed:  δ N(tan Θ₀)   ≤ N(R)      -- on the trial residual
ambient:   δ N(tan Θ)    ≤ N(H)      -- on the whole-space perturbation
```

They are different quantities with different right-hand sides, and **no single
alias below is the whole printed theorem for those three.**  Each result
therefore has an explicit `_directed_` and `_ambient_` alias at each scalar
field, and the older unqualified `tanTheta_complex`-style names are retained as
the ambient clause, which is what they always were.

The maintained per-clause witness table is generated from
`dev/davis-kahan-1970-formalization-result-inventory.json` into the reviewer
packet; it, not this comment, is where a reviewer checks which theorem
discharges which clause.

## What each fixed-field alias says, and what has been reviewed

Each has a type that displays an unbounded self-adjoint `LinearPMap` ambient
operator, a Hilbert space of arbitrary dimension, a `PaperUnitaryInvariantNorm`
-- the paper's symmetric gauge, not the operator norm -- and the two halves of
its own printed clause: ideal membership and the inequality.  No capability
class, no finite-dimensionality hypothesis, no proof-vehicle operator in the
conclusion, and no branch or pole certificate demanded of the caller.

That is what the *types* say.  Whether each matches the printed result is a
separate, reviewed question, and the answer lives in the maintained result
inventory rather than here -- including its one standing qualification, that
`S2-tan-theta` is accepted under a nonlocal source interpretation because its
printed statement is not locally self-contained.  Do not read the paragraph above
as that review's verdict.

Both `sin 2Θ` endpoints now take `FormBoundedSylvesterGap`, so the printed
half-infinite gap scope is covered over both fields;
`sinTwoTheta_directed_unbounded_addBounded_spectrumGap_paperUINorm_complex` is the
earlier complex route, at a bounded separating interval only, and is kept as an
alternative rather than as this result's witness.  The `sin 2Θ` *ambient* clause
is covered at the same scope by
`sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_complex` and its real
sibling; the bounded ambient endpoints are their specializations.

The declarations here are `alias`es, so each has exactly the type of the theorem
it names; the proofs and the supporting theory stay in the modules where they
belong.  The implementations they select are, in order:

| result | clause | complex | real |
| --- | --- | --- | --- |
| `sin Θ` | directed (only) | `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_complex` | `…_real` |
| `tan Θ` | directed | `tanTheta_directed_unboundedTrial_paperUINorm_complex` | `…_real` |
| `tan Θ` | ambient | `tanTheta_ambient_unboundedRitz_paperUINorm_complex` | `…_real` |
| `sin 2Θ` | directed | `sinTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_complex` | `…_real` |
| `sin 2Θ` | ambient | `sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_complex` | `…_real` |
| `tan 2Θ` | directed | `tanTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_complex` | `…_real` |
| `tan 2Θ` | ambient | `tanTwoTheta_ambient_unbounded_paperUINorm_complex` | `…_real` |

The unqualified `tanTheta_complex`, `sinTwoTheta_complex` and `tanTwoTheta_complex`
(and their real siblings) each name **one** clause -- the ambient one for the two
tangent theorems, the directed one for `sin 2Θ` -- and their docstrings say which.
They are retained because they are the names downstream code already uses; a reader
looking for the whole printed result should use the `_directed_`/`_ambient_` pair,
or, for `sin 2Θ`, the `sinTwoTheta_source_*` certificate that states both.

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
`TauCeti.DavisKahan1970.sinTheta_bundled_complex`.  Those are useful and are kept; they are simply
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

/-- **Davis--Kahan 1970, the `sin Θ` theorem, over an arbitrary `RCLike` field.**

The scalar-generic endpoint at the printed source scope: unbounded self-adjoint
ambient `LinearPMap`, arbitrary Hilbert dimension, the whole
`FormBoundedSylvesterGap`, an arbitrary `PaperUnitaryInvariantNorm`, and both
printed conclusions.  `sinTheta_complex` and `sinTheta_real` below are the same
statement at the two fields Davis and Kahan write about, and they are the ones to
cite when a fixed field is in hand: this one additionally carries the two
`RCLike` capability classes, which are theorems for `ℝ` and `ℂ` but appear in the
signature because `RCLike` is an open class. -/
alias sinTheta := _root_.DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike

/-- **Davis--Kahan 1970, the `sin Θ` theorem, over `ℂ`.**

`δ · N(sin Θ₀) ≤ N(R)` with `sin Θ₀ = (I - F₀F₀⋆) E₀`, together with membership of
`sin Θ₀` in the norm's ideal.  Unbounded self-adjoint ambient operator, arbitrary
Hilbert dimension, the whole `FormBoundedSylvesterGap` rather than one of its
branches, and an arbitrary source unitarily invariant norm.

`DavisKahan1970.sinTheta_unbounded_intervalExterior_paperUINorm_complex` states the same theorem with
the gap written out as the printed interval/exterior separation. -/
alias sinTheta_complex := _root_.DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_complex

/-- **Davis--Kahan 1970, the `sin Θ` theorem, over `ℝ`.**

The real sibling of `sinTheta`, with the same argument list, the same full gap
scope and the same two conclusions.  The descent from the complex case happens
inside the proof and is not visible in the statement. -/
alias sinTheta_real := _root_.DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_real

/-! ## `tan Θ` -/

/-- **Davis--Kahan 1970, the `tan Θ` theorem, over `ℂ` -- the AMBIENT clause.**

The printed `tan Θ` theorem has two boxed conclusions.  This name is the second,
`δ N(tan Θ) ≤ N(H)`; the first, `δ N(tan Θ₀) ≤ N(R)`, is `tanTheta_directed_complex`.
The pair is the whole result; neither alone is.

`δ · N(tan Θ) ≤ N(H)` on the ambient tangent `paperTanAngleOperatorC U V`, with
ideal membership, for an unbounded self-adjoint `A`, its unbounded Ritz pair on
the trial subspace `U`, and a subspace `V` whose complement reduces `A`.

The caller supplies the mathematics -- semiboundedness of the compression above
`α`, coercivity `α + δ` on the unwanted subspace, the standing crossed-defect
condition (3.5) of Section 3, and the Rayleigh--Ritz residual identity -- and
nothing else: the structural facts live in `DavisKahan.UnboundedRitzPair` and
`DavisKahan.ReducingComplement`. -/
alias tanTheta_complex := tanTheta_ambient_unboundedRitz_paperUINorm_complex

/-- **Davis--Kahan 1970, the `tan Θ` theorem, over `ℝ` -- the AMBIENT clause.**

Its directed partner is `tanTheta_directed_real`.

The real sibling of `tanTheta_ambient_complex`, on the real ambient tangent
`paperTanAngleOperatorR U V`.  Space, operator, subspaces, perturbation, angle and
gauge are all real; only the Appendix Ky Fan passage is proved by
complexification, at the level where approximation numbers are preserved
exactly. -/
alias tanTheta_real := tanTheta_ambient_unboundedRitz_paperUINorm_real

/-! ## `sin 2Θ` -/

/-- **Davis--Kahan 1970, the `sin 2Θ` theorem, over `ℂ` -- the DIRECTED clause.**

The printed `sin 2Θ` theorem has two boxed conclusions.  This name is the first,
`δ N(sin 2Θ₀) ≤ 2 N(R)` in its bounded-perturbation form; the ambient one,
`δ N(sin 2Θ) ≤ 2 N(H)`, is `sinTwoTheta_ambient_complex`.  `sinTwoTheta_source_complex`
below states both together.

`δ · N(sin 2Θ) ≤ 2 N(E)`, with the paper's sharp factor two, for the spectral
subspaces selected by `B` from an unbounded self-adjoint `A` and by `S` from the
bounded perturbation `A + E`, under the whole `FormBoundedSylvesterGap` -- so the
separating interval may be half-infinite, as the source permits.  The conclusion
is on the directed double-angle sine `2 sin Θ cos Θ`, not on the proof's overlap
block.

`sinTwoTheta_directed_unbounded_addBounded_spectrumGap_paperUINorm_complex` is the
earlier route, which reads the separation as a bounded interval `[β, α]` whose
enlargement the complementary restriction's spectrum avoids. -/
alias sinTwoTheta_complex := sinTwoTheta_directed_unbounded_addBounded_paperUINorm_complex

/-- **Davis--Kahan 1970, the `sin 2Θ` theorem, over `ℝ` -- the DIRECTED clause.**

Its ambient partner is `sinTwoTheta_ambient_real`, and `sinTwoTheta_source_real`
states both together.

The real sibling of `sinTwoTheta_complex`, reaching the ideal layer through
`FormBoundedSylvesterGap` -- which is the hypothesis shape the real proof actually
has -- and concluding on the directed double-angle sine of the real pair, read in
the canonical complexification where this development keeps the real double-angle
operators. -/
alias sinTwoTheta_real := sinTwoTheta_directed_unbounded_addBounded_paperUINorm_real

/-! ## The two printed clauses, named

`tanTheta_complex`, `sinTwoTheta_complex` and `tanTwoTheta_complex` (and their
real siblings) are the AMBIENT clause of their theorem.  The directed clause is a
different statement -- a different angle object and the trial residual rather than
the ambient perturbation on the right -- so it gets its own name rather than
being folded into the ambient one with irrelevant hypotheses. -/

/-- **`tan Θ`, ambient clause, over `ℂ`**: `δ N(tan Θ) ≤ N(H)`. -/
alias tanTheta_ambient_complex := tanTheta_ambient_unboundedRitz_paperUINorm_complex

/-- **`tan Θ`, ambient clause, over `ℝ`**. -/
alias tanTheta_ambient_real := tanTheta_ambient_unboundedRitz_paperUINorm_real

/-- **`tan Θ`, directed clause, over `ℂ`**: `δ N(tan Θ₀) ≤ N(R)`, with the trial
residual on the right and the representative characterized by its approximation
numbers. -/
alias tanTheta_directed_complex := tanTheta_directed_unboundedTrial_paperUINorm_complex

/-- **`tan Θ`, directed clause, over `ℝ`**. -/
alias tanTheta_directed_real := tanTheta_directed_unboundedTrial_paperUINorm_real

/-- **`sin 2Θ`, directed clause, over `ℂ`**: `δ N(sin 2Θ₀) ≤ 2 N(R)`. -/
alias sinTwoTheta_directed_complex :=
  sinTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_complex

/-- **`sin 2Θ`, directed clause, over `ℝ`**. -/
alias sinTwoTheta_directed_real :=
  sinTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_real

/-- **`tan 2Θ`, directed clause, over `ℂ`**: `(b − a) N(tan 2Θ₀) ≤ 2 N(R)`. -/
alias tanTwoTheta_directed_complex :=
  tanTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_complex

/-- **`tan 2Θ`, directed clause, over `ℝ`**. -/
alias tanTwoTheta_directed_real :=
  tanTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_real

/-- **`tan 2Θ`, ambient clause, over `ℂ`**: `(b − a) N(|tan 2Θ|) ≤ 2 N(B)`. -/
alias tanTwoTheta_ambient_complex := tanTwoTheta_ambient_unbounded_paperUINorm_complex

/-- **`tan 2Θ`, ambient clause, over `ℝ`**. -/
alias tanTwoTheta_ambient_real := tanTwoTheta_ambient_unbounded_paperUINorm_real

/-- **`sin 2Θ`, ambient clause, over `ℂ`**: `δ N(sin 2Θ) ≤ 2 N(H)` on the paper's
*ambient* double-angle sine `paperSinTwoAngleOperatorC`, at this result's unbounded
scope.

This alias was deliberately absent until 2026-08-31, because the only paper-norm
ambient endpoint was `sinTwoTheta_ambient_bounded_paperUINorm_complex`, whose
ambient operator is bounded.  It now names the theorem at the printed scope; the
bounded statement is retained as an alternative proof of its own specialization. -/
alias sinTwoTheta_ambient_complex :=
  sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_complex

/-- **`sin 2Θ`, ambient clause, over `ℝ`**. -/
alias sinTwoTheta_ambient_real :=
  sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_real

/-! ## `tan 2Θ` -/

/-- **Davis--Kahan 1970, the `tan 2Θ` theorem, over `ℂ` -- the AMBIENT clause.**

The printed `tan 2Θ` theorem has two boxed conclusions.  This name is the second,
`(b − a) N(|tan 2Θ|) ≤ 2 N(B)`; the directed one is `tanTwoTheta_directed_complex`.

`(b - a) · N(|tan 2Θ|) ≤ 2 N(B)` on the paper's ambient branch-free double-angle
tangent, with ideal membership, for an unbounded self-adjoint `A`, a bounded
self-adjoint perturbation `B` odd for the selected spectral subspace, and a
subspace `V` whose reflection intertwines `A + B`
(`DavisKahan.ReflectionIntertwines`, built from a `ReducesSubspace` by
`.ofReducesSubspace`).

No pole certificate is asked for: the ordered gap forces the reflection's diagonal
block to be a unit, and that unit excludes the quarter-turn poles. -/
alias tanTwoTheta_complex := tanTwoTheta_ambient_unbounded_paperUINorm_complex

/-- **Davis--Kahan 1970, the `tan 2Θ` theorem, over `ℝ` -- the AMBIENT clause.**

Its directed partner is `tanTwoTheta_directed_real`.

The real sibling of `tanTwoTheta_ambient_complex`, on the real ambient `|tan 2Θ|`.  The real
statement is transported from the complex one through the complexification, with
no loss of constant or norm class and no second analytic proof. -/
alias tanTwoTheta_real := tanTwoTheta_ambient_unbounded_paperUINorm_real

/-! ## The whole printed `sin 2Θ` theorem, in one declaration

Davis and Kahan print two boxed conclusions under one set of separation
hypotheses.  The two clause aliases above are those two conclusions; the two
declarations here are the *result*, so a reviewer has one name to point at.

Both clauses take the same operator, the same measurable selection of its
spectrum and the same `FormBoundedSylvesterGap`, so that data is shared.  What is
not shared stays inside its own conjunct: the directed clause quantifies over the
trial subspace and its residual, the ambient clause over the bounded perturbation
and the selection it makes from the perturbed operator.  Forcing either one's data
into the other's telescope would change the printed statement, so it is not done.

`tan Θ` and `tan 2Θ` have no such certificate: their two clauses share almost no
data -- an unbounded Ritz pair against a trial block, a reflection intertwiner
against an involution -- so a conjunction would be two disjoint theorems written
next to each other, which is what the clause aliases already are. -/

section SinTwoThetaSource

open TauCeti.DavisKahan TauCeti.DavisKahan.ExactSinTheta TauCeti.DavisKahanExt

universe v

/-- A subspace admitting an orthogonal projection inside a complete ambient space
is itself complete.  `local instance` does not propagate through imports, so it is
reinstalled here for the trial subspaces the directed clause quantifies over. -/
local instance instCompleteSpaceCoeSectionTwoSource
    {𝕜 : Type*} [RCLike 𝕜] {G : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (W : Submodule 𝕜 G) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

/-- **Davis--Kahan 1970, the `sin 2Θ` theorem over `ℂ`, both printed conclusions.**

Under one separation hypothesis: `δ N(sin 2Θ₀) ≤ 2 N(R)` for every trial subspace
inside `dom A` with residual `R`, and `δ N(sin 2Θ) ≤ 2 N(H)` for every bounded
self-adjoint perturbation `H` and every measurable selection from the perturbed
operator's spectrum.  Unbounded self-adjoint ambient operator, arbitrary Hilbert
dimension, arbitrary source unitarily invariant norm, the whole gap. -/
theorem sinTwoTheta_source_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    (N : PaperUnitaryInvariantNorm)
    (A : Hc →ₗ.[ℂ] Hc) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (selfAdjointSpectralRestriction A hA B hB)
      (selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ) :
    (∀ {V : Submodule ℂ Hc} [V.HasOrthogonalProjection]
        {M : V →L[ℂ] V} {R : V →L[ℂ] Hc}
        (hVdom : ∀ v : V, ((v : V) : Hc) ∈ A.domain),
        (∀ v : V, A ⟨((v : V) : Hc), hVdom v⟩ = R v + ((M v : V) : Hc)) →
        N.Mem R →
          N.Mem (sinTwoThetaIdealBlock (selfAdjointSpectralSubspace A hA B hB) V) ∧
            δ * N.gauge (sinTwoThetaIdealBlock
                (selfAdjointSpectralSubspace A hA B hB) V) ≤ 2 * N.gauge R) ∧
      (∀ (Eop : Hc →L[ℂ] Hc) (hEop : IsSelfAdjointOperator Eop)
        (S : Set ℝ) (hS : MeasurableSet S), N.Mem Eop →
          N.Mem (paperSinTwoAngleOperatorC (selfAdjointSpectralSubspace A hA B hB)
              (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
                (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
            δ * N.gauge (paperSinTwoAngleOperatorC
                (selfAdjointSpectralSubspace A hA B hB)
                (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
                  (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤ 2 * N.gauge Eop) :=
  ⟨fun hVdom hres hR =>
      sinTwoTheta_directed_complex N hA B hB hVdom hres hδ hgap hR,
    fun Eop hEop S hS hEmem =>
      sinTwoTheta_ambient_complex N A hA Eop hEop B S hB hS hδ hgap hEmem⟩

/-- **Davis--Kahan 1970, the `sin 2Θ` theorem over `ℝ`, both printed
conclusions.**  The real sibling of `sinTwoTheta_source_complex`, at the same
strength. -/
theorem sinTwoTheta_source_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    (N : PaperUnitaryInvariantNorm)
    (A : Er →ₗ.[ℝ] Er) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA B hB)
      (RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ) :
    (∀ {V : Submodule ℝ Er} [V.HasOrthogonalProjection]
        {M : V →L[ℝ] V} {R : V →L[ℝ] Er}
        (hVdom : ∀ v : V, ((v : V) : Er) ∈ A.domain),
        (∀ v : V, A ⟨((v : V) : Er), hVdom v⟩ = R v + ((M v : V) : Er)) →
        N.Mem R →
          N.Mem (sinTwoThetaIdealBlock
              (RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB) V) ∧
            δ * N.gauge (sinTwoThetaIdealBlock
                (RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB) V) ≤
              2 * N.gauge R) ∧
      (∀ (Eop : Er →L[ℝ] Er) (hEop : IsSelfAdjointOperator Eop)
        (S : Set ℝ) (hS : MeasurableSet S), N.Mem Eop →
          N.Mem (paperSinTwoAngleOperatorR
              (RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB)
              (RealSpectralRestriction.realSelfAdjointSpectralSubspace
                (TauCeti.LinearPMap.addBounded A Eop)
                (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
            δ * N.gauge (paperSinTwoAngleOperatorR
                (RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB)
                (RealSpectralRestriction.realSelfAdjointSpectralSubspace
                  (TauCeti.LinearPMap.addBounded A Eop)
                  (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤ 2 * N.gauge Eop) :=
  ⟨fun hVdom hres hR =>
      sinTwoTheta_directed_real N hA B hB hVdom hres hδ hgap hR,
    fun Eop hEop S hS hEmem =>
      sinTwoTheta_ambient_real N A hA Eop hEop B S hB hS hδ hgap hEmem⟩

end SinTwoThetaSource

end SectionTwo
end DavisKahan1970
end TauCeti
