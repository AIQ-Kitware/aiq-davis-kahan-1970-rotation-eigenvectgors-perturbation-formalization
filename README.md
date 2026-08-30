# Davis–Kahan 1970: the operator-norm sin-Θ theorem, in Lean 4

A machine-checked proof of the operator-norm sin-Θ theorem of Chandler Davis and
W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*, SIAM Journal on
Numerical Analysis 7(1), 1970, 1–46, <https://doi.org/10.1137/0707001>.

## The result

Let `T` and `S` be symmetric operators on a finite-dimensional inner product space
over `ℝ` or `ℂ`. Let `U` be `T`-invariant with the quadratic form of `T` at or
above `c + g` on it, and `V` be `S`-invariant with the form of `S` at or below `c`
on it — so `U` and `V` sit on opposite sides of a spectral gap of width `g > 0`. If
`‖S − T‖ ≤ ε`, then

  `‖P_V ∘ P_U‖ ≤ ε / g`

for the orthogonal projections `P_U`, `P_V`. The left side is `‖sin Θ‖`, the
largest sine of a principal angle between the two subspaces.

## Why it matters

This is the estimate that makes computed invariant subspaces trustworthy: it turns
a bound on an operator *residual* into a bound on a subspace *angle*, which is what
an eigenvalue computation actually needs. It is standard equipment in numerical
linear algebra and operator theory, and its statistical descendants — most directly
the Yu–Wang–Samworth variant — are cited across spectral methods.

Three features are worth naming. The bound is dimension-free: only `ε` and `g`
appear on the right. The separation hypothesis is one-sided and stated by quadratic
forms, which is how the theorem is used — one needs no access to the spectra
themselves. And `U` and `V` need not be spectral subspaces of any particular
eigenvalue set; invariance plus the form separation suffices.

## Fidelity

This entry formalizes the operator-norm form with no added hypothesis and no
weakened conclusion.

It is deliberately narrower than the paper. Davis and Kahan state their results for
a separable Hilbert space, unbounded self-adjoint operators, and arbitrary
unitarily invariant norms, and the `DavisKahan` library included here formalizes them at that
scope. That general statement cannot be written in a Palomar Challenge today: it
needs a unitarily invariant norm class and a spectral-subspace API that Mathlib does
not have, and importing the local ones would put the whole development inside the
trusted statement surface, which is exactly what a Challenge is supposed to avoid.

The general theorems are easy to find in the included library. Davis and Kahan open
with four unnumbered theorems, and
`DavisKahan/Sources/DavisKahan1970/SectionTwo.lean` is the inventory of all four
over both scalar fields:

```
TauCeti.DavisKahan1970.SectionTwo.sinTheta       sinTheta_real
TauCeti.DavisKahan1970.SectionTwo.tanTheta       tanTheta_real
TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta    sinTwoTheta_real
TauCeti.DavisKahan1970.SectionTwo.tanTwoTheta    tanTwoTheta_real
```

Each states its result at that full scope in its own type — unbounded self-adjoint
`LinearPMap` ambient operator, arbitrary Hilbert dimension, an arbitrary source
unitarily invariant norm, and both printed conclusions. `SectionTwoUsage.lean`
beside it calls each from ordinary operator-theory hypotheses. Read those to see
what the paper actually claims; the entry compared here is the one corner of it
that Mathlib's vocabulary can state.

Two disclosures about the wider formalization, neither part of this entry: printed
Proposition 4.4 of the paper is false, and the `DavisKahan` library carries a
machine-checked counterexample satisfying its printed hypotheses together with the
natural Q-norm repair; and the Section 2 ambient tan-Θ theorem is not locally
self-contained, since its printed statement omits a crossed-defect condition the
paper introduces later and then treats as standing.

## Where this comes from

This repository is an **extraction**, not a fork with a life of its own.
[`AIQ-Kitware/aiq-dkps-formalization`](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
is authoritative: mathematics is developed, reviewed and audited there, and this
repository is a snapshot of the `ForTauCeti` and `DavisKahan` packages taken from it, without the surrounding history and
without the packages that are not needed here. It exists so the entry can be read,
built and checked on its own, and so a reader is not asked to clone a much larger
multi-paper development to see one theorem's proof.

The practical consequence: **send changes upstream.** A fix made here and not made
there is lost at the next extraction. When the upstream packages move, this snapshot
is refreshed from them.

What is deliberately *not* extracted: the source-order census, the distilled source
specification, the semantic-audit apparatus and the gate scripts. Those track coverage
of the whole 1970 paper and are maintenance machinery for the authoritative repository;
duplicating them here would create a second copy to keep honest. Accordingly **this
repository makes no completion claim about the paper** -- it presents a proved theorem
and the development it lives in.

The extraction is a copy of the package directories, so every module keeps its
upstream path, namespace and provenance header. The libraries build against a pinned
Mathlib and a pinned Tau Ceti, recorded in `lakefile.toml` and `lake-manifest.json`.

## Layout

```
Challenge.lean      the Palomar statement, against Mathlib alone, with a
                    deliberate statement-side hole
Solution.lean       the same declaration, supplied from the libraries below
comparator.json     what Comparator compares, and the permitted axioms
formalization.yaml  registry metadata
ForTauCeti/         reusable mathematics, in its final `TauCeti.*` namespaces
DavisKahan/         the Davis--Kahan development, whose four Section 2 theorems
                    are inventoried in
                    DavisKahan/Sources/DavisKahan1970/SectionTwo.lean
```

`lake build` builds the entry. `lake build ForTauCeti` and `lake build DavisKahan` build the libraries.

## Status

Preparation. Nothing here claims registration, acceptance, or peer review by the
Palomar Registry.

