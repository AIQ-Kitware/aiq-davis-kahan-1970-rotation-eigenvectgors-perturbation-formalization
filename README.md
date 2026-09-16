# Davis–Kahan 1970 Section 2 theorems — Lean 4 / Palomar submission

This repository is a self-contained Palomar submission extraction for the four
headline theorem families from Section 2 of Chandler Davis and W. M. Kahan,
*The rotation of eigenvectors by a perturbation. III*, SIAM Journal on Numerical
Analysis 7(1), 1970, 1–46, DOI 10.1137/0707001.

This repository follows Palomar's ordinary single-project layout. The submission
surface is the conventional root `Challenge.lean`, `Solution.lean`,
`comparator.json`, and `formalization.yaml`. Comparator compares five ordinary
theorem declarations in `Challenge.lean` against matching proofs in
`Solution.lean`:

* `RotationOfEigenvectors.sinTheta`
* `RotationOfEigenvectors.tanTheta`
* `RotationOfEigenvectors.sinTwoTheta_directed`
* `RotationOfEigenvectors.sinTwoTheta_ambient`
* `RotationOfEigenvectors.tanTwoTheta`

There is one submission surface and one Comparator configuration. No project or
metadata path override is needed on the Palomar submission form.

## What the result says

Davis and Kahan study how much invariant subspaces can rotate under a Hermitian
perturbation.  Their four Section 2 theorem families bound trigonometric
functions of the principal angles between the original and perturbed subspaces
in terms of a spectral gap and either a trial residual or the perturbation
itself.

The Palomar entry exposes the following selected source-facing clauses:

* **sin Θ:** `δ · N(sin Θ₀) ≤ N(R)`, at the source's where-defined norm boundary;
* **tan Θ:** `δ · N(tan Θ₀) ≤ N(R)`, together with the theorem's pole exclusion;
* **sin 2Θ, residual:** `δ · N(sin 2Θ₀) ≤ 2 N(R)`, for self-adjoint `A` and perturbed `T` on a common domain, with only the residual extension required bounded and with the printed oriented `Λ₀`/`Λ₁` gap;
* **sin 2Θ, whole-space:** `δ · N(sin 2Θ) ≤ 2 N(H)`, with the printed oriented spectral gap on the two perturbed `A + H` blocks relative to the reducing subspace `V` (the source's `Λ₀, Λ₁`);
* **tan 2Θ:** `δ · N(tan 2Θ₀) ≤ 2 N(R)`, again with pole exclusion.

The three sine declarations state the numerical inequality where both displayed
norms are finite.  This mirrors the source-facing partial-norm API and avoids
turning the stronger membership-transfer facts proved by the implementation into
part of the advertised Davis--Kahan statement.  The directed `sin 2Θ` clause
uses the common-domain formulation: the trial restriction itself need not be
bounded and there is no globally bounded perturbation assumption in that clause.

The paper also displays whole-space tan Θ and tan 2Θ inequalities.  They are not
separate Comparator declarations here because the source proofs derive them
after the residual estimates from the common block geometry; the included
`DavisKahan` library contains the ambient endpoints as well.  By contrast both
sin 2Θ conclusions are retained because they are genuinely distinct public
consequences.  In particular, the whole-space `sin 2Θ` declaration uses the
printed operator roles: its gap is on the two `A + H` blocks relative to `V`,
not on the unperturbed `A` blocks relative to `U`.  The ordinary one-gap sin Θ theorem has no corresponding ambient
unitarily-invariant-norm conclusion: Davis and Kahan explicitly give a
counterexample and then state a separate symmetric sin Θ result under a second
gap.

## Why it matters

These are foundational spectral-subspace perturbation estimates.  They turn
spectral separation plus a perturbation or residual bound into quantitative
control of invariant-subspace error.  That mechanism underlies eigenvector and
eigenspace perturbation theory in numerical linear algebra, operator theory,
and many later statistical and data-analysis variants of Davis–Kahan.

The formalization permits finite- and infinite-dimensional separable Hilbert
spaces, matching the paper's standing ambient-space convention, and supports the
unbounded self-adjoint/partial-map setting represented in the paper and its
Appendix.  The Palomar statements are scalar-generic over Mathlib's `RCLike`
abstraction, so the same declarations cover the real and complex cases.

At the level of the *relative dimensions of the compared subspaces*, the Lean
statements are deliberately more general than the standing Section 1 setup: the
projection/angle representatives do not impose the matching-dimension equations
used there to construct a whole-space direct rotation.  The paper later says the
`sin 2Θ` theorem can be extended to `dim X(E₀) < dim X(F₀)`, while explicitly
noting that no corresponding `tan 2Θ` extension was known.  This dimension-free
scope is therefore recorded as a formal strengthening/adaptation, not described
as literally printed scope.

## The norm quantifier

The paper quantifies over arbitrary normalized unitarily invariant norms.  The
Mathlib-only Challenge represents that quantifier by a dimension-coherent
`SymmetricNormingFunction` built from finite-dimensional two-sided unitarily
invariant seminorms and extended through approximation singular values.

That Lean type is **not literally the entire infinite-dimensional UIN class**.
For example, the included development discusses Fan-dominant UIN norms that are
not generated by a symmetric gauge.  What makes the Challenge presentation
source-faithful at the level of these inequalities is a formalized Fan-dominance
bridge: simultaneous bounds for all symmetric norming functions are equivalent
to the corresponding Ky Fan majorization statements, which imply the estimates
for the source-facing where-defined UIN abstraction.  The relevant development
includes `symmetricNorming_iff_kyFanDominant` and source-facing
`NormalizedUnitaryInvariantNorm` / where-defined endpoints.

This distinction is recorded explicitly in
`formalization.yaml`.  The Challenge does not claim that
`SymmetricNormingFunction` and the full UIN class are definitionally the same
object.

## Fidelity and scope

The five compared declarations are a compact Palomar presentation of the four
headline Section 2 theorem families, not a claim that this Comparator entry
covers every proposition in the 1970 paper.  They retain the paper's standing
separability convention.  In particular, the directed `sin 2Θ` declaration is
the accepted common-domain form from the parent source audit rather than the
older bounded-trial specialization.  Both `sin 2Θ` declarations use a dedicated
`SinTwoThetaGap` at the Challenge boundary: `Λ₀` is the inside block and `Λ₁`
the exterior block, with only the lower half-line extension printed after the
Section 2 statements.  The broader symmetric `SylvesterGap` remains an internal
proof tool and the public gap for the printed `sin Θ` alternatives.  The included
`DavisKahan` library
contains the wider development, including source-facing UIN endpoints, ambient
tangent forms, direct-rotation results, later sections, sharpness results, and a
machine-checked counterexample to printed Proposition 4.4 together with its
repair.  Those are outside this Comparator entry.

The Challenge is intentionally self-contained against Mathlib rather than
importing the local proof library into the statement surface.  Every local
notion used by a compared theorem has a mathematical docstring there.  The
Solution adapts those local definitions to the corresponding declarations in
the extracted proof libraries.

## Provenance

The development and audit history are maintained in
[`AIQ-Kitware/aiq-dkps-formalization`](https://github.com/AIQ-Kitware/aiq-dkps-formalization).
This repository is a submission extraction: it commits the `ForTauCeti` and
`DavisKahan` proof source needed by the Solution and builds that source directly,
so it is not merely a Comparator shim around an external checkout.  The parent
repository remains the maintenance origin; fixes should be made there and then
refreshed into this extraction.

The accepted common-domain `sin 2Θ` source module and the source-facing Section
Two inventory were refreshed from parent commit
`9fe59f6b02482111e5be6a2b812edd011990fda5`.  The standalone repository commits
the extracted proof source it builds; Palomar-specific Challenge, Solution,
metadata, and verification files are maintained here.

## Repository layout

The submission-facing files use the ordinary Palomar template layout:

```text
Challenge.lean                       small Mathlib-only statement surface
Solution.lean                        matching proofs from the libraries below
comparator.json                      Comparator declaration list
formalization.yaml                   Palomar/formalization.yaml metadata
Palomar/DKSectionTwo/SolutionPrelude.lean
                                      Solution-only Mathlib prelude used to keep
                                      Comparator helper constants identical
ForTauCeti/                           reusable supporting mathematics
DavisKahan/                           Davis–Kahan formalization
DavisKahan.lean
ForTauCeti.lean
lakefile.toml
lake-manifest.json
lean-toolchain
LICENSE
scripts/check_palomar_readiness.py
scripts/build_verification_tools.sh
scripts/verify_palomar.sh
```

`SolutionPrelude.lean` is not a second submission surface and is never imported
by `Challenge.lean`; it exists only because Comparator compares non-target helper
constants definitionally across the Challenge and Solution environments.

## Local verification

The intended local preflight is:

```bash
lake build
python3 scripts/check_palomar_readiness.py
scripts/verify_palomar.sh --static-only
```

Because the root `Challenge` and `Solution` libraries are default Lake targets,
plain `lake build` checks the proof development and the submission surface.

The static-only verifier confirms repository shape and kernel builds but, as it
prints, is **not** a Comparator pass.  Build the pinned Comparator, `lean4export`,
NanoDa, and Landrun bundle once with:

```bash
scripts/build_verification_tools.sh
```

The builder keeps the reproducible dated bundle (currently
`~/.cache/palomar-tools-20260916`) and, only after all four tools build
successfully, updates `~/.cache/palomar-tools-latest` to point at it.  Here
`latest` means the most recently installed **pinned Palomar bundle**, not an
unpinned upstream release.  `scripts/verify_palomar.sh` automatically discovers
that stable pointer and also recognizes older dated bundles if the pointer has
not been created yet.  An explicit caller `PATH` still takes precedence;
`PALOMAR_TOOLS_BIN` can name another tool directory, and
`PALOMAR_TOOLS_CACHE_PARENT` can move the cache root.  No shell-profile edit is
required.

Before submission, run the full mechanical reproduction:

```bash
scripts/verify_palomar.sh
```

The submission form can use Palomar's defaults:

```text
project directory:          repository root / leave blank
Comparator configuration:  comparator.json
formalization metadata:     formalization.yaml / leave override blank
```

A Palomar submission must pin the final public Git commit by its full
40-character SHA.  Local verification is not Palomar verification, acceptance,
or registration.
