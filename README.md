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

Two disclosures about the wider formalization, neither part of *this* entry:
printed Proposition 4.4 of the paper is false, and the `DavisKahan` library carries
a machine-checked counterexample satisfying its printed hypotheses together with the
natural Q-norm repair; and the Section 2 ambient tan-Θ theorem is not locally
self-contained, since its printed statement omits a crossed-defect condition the
paper introduces later and then treats as standing.  The second of those **is** part
of the Section 2 entry below, where it is set out in full.

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

## Two entries

| entry | what is compared |
| --- | --- |
| root (`comparator.json`) | the operator-norm sin-Θ bound described above: one theorem, finite dimensions, one norm |
| `registry/dk-section-two/` | **the four unnumbered theorems Davis and Kahan open Section 2 with**, at the printed scope — arbitrary dimension, an unbounded self-adjoint ambient operator, an arbitrary unitarily invariant norm, half-infinite separating intervals, and a reducing rather than spectrally selected trial subspace |

The Section 2 entry is the paper's headline package: seven printed inequality
clauses in all — `sin Θ`, and a directed and an ambient clause each for `tan Θ`,
`sin 2Θ` and `tan 2Θ` — with the printed residual on the right and the printed
constants one and two. The two tangent families additionally *conclude*, rather
than assume, that no principal angle sits at the tangent's pole: Lean's
`Real.tan` is total, so a pole would otherwise be silently valued at zero.

Three qualifications in that entry are stated here, and again in its
`formalization.yaml`, rather than left for a reader to find.

* **The ambient `tan Θ` clause carries one hypothesis the Section 2 display does
  not print**: `CrossedDefectsEquivalent U V`, the constructive form of the
  paper's condition (3.5).  (3.5) is introduced in Section 3, made standing there
  for the rest of the paper, and used by the Section 6 proof of that clause, so
  the hypothesis is imported from the paper's later scope rather than read off the
  local statement.  It is not decoration: the inequality and the no-pole
  conclusion are both proved from it, and without it there is an
  infinite-dimensional configuration — nested half-spaces, of the kind the
  Proposition 3.2 remark exhibits — in which every printed hypothesis holds, `‖H‖`
  is finite, and the ambient tangent is unbounded.  The formalization reads the
  printed theorem under the paper's own global semantics, in which Section 1
  declares such results vacuous when a displayed norm fails to exist; under the
  competing literal reading the printed clause would be false as transcribed and
  the Lean statement would be its repair.  Either way the hypothesis is not in the
  display, and this repository says so rather than claiming otherwise.  The other
  six clauses state exactly the printed hypotheses.
* The `sin 2Θ` directed clause takes a **bounded** trial compression. That is
  what the Appendix to Section 6 supports: it relaxes the sine family to allow
  *one* of the two exact blocks to be unbounded, reserves "both may be unbounded"
  for the tangent theorem, and names no double-angle result at all.
* A **doubled angle is presented by its own sine**, never by doubling the single
  angle. `t ↦ sin 2t` is not monotone on `[0, π/2]`, so no indexwise map carries
  the ordered singular values of `sin Θ` to those of `sin 2Θ`; principal angles
  `75°` and `30°` already order the two sequences oppositely.

## Layout

```
Challenge.lean      the root Palomar statement, against Mathlib alone, with a
                    deliberate statement-side hole
Solution.lean       the same declaration, supplied from the libraries below
comparator.json     what Comparator compares there, and the permitted axioms
formalization.yaml  registry metadata for the root entry
Palomar/            one directory per additional entry:
  DKSectionTwo/     Challenge.lean and Solution.lean for the Section 2 entry
registry/           one directory per additional entry, with its comparator.json
                    and its formalization.yaml
ForTauCeti/         reusable mathematics, in its final `TauCeti.*` namespaces
DavisKahan/         the Davis--Kahan development, whose four Section 2 theorems
                    are inventoried in
                    DavisKahan/Sources/DavisKahan1970/SectionTwo.lean
```

`lake build` builds the root entry. `lake build ForTauCeti`, `lake build DavisKahan`
and `lake build Palomar` build the libraries.

## Verifying locally

```bash
python3 scripts/check_palomar_readiness.py        # static preflight, seconds
scripts/verify_palomar.sh                         # + build + Comparator + NanoDa
scripts/verify_palomar.sh --fake-landrun          # if landrun is unavailable
```

The preflight checks what can be checked without Lean: no submodules, no LFS
pointers, no committed build artifacts, one root licence, every dependency pinned
to a credential-free GitHub URL at a full SHA, the metadata shape, the Comparator
configuration keys, and — the one that matters — that the Challenge's *transitive*
import closure reaches no module in this repository. `verify_palomar.sh` then
builds every declared library, including the `Challenge` library that the default
build deliberately excludes because it carries statement-side holes, and runs the
real Comparator with the independent NanoDa kernel.

Both scripts live here rather than upstream because they ask whether *this*
repository verifies. That is not a question the development repository can answer
about itself.

That is local verification only. It is not Palomar verification, not acceptance,
and not registration.

## Status

Preparation. Nothing here claims registration, acceptance, or peer review by the
Palomar Registry.

