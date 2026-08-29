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
unitarily invariant norms, and the substantive repository formalizes them at that
scope. That general statement cannot be written in a Palomar Challenge today: it
needs a unitarily invariant norm class and a spectral-subspace API that Mathlib does
not have, and importing the local ones would put the whole development inside the
trusted statement surface, which is exactly what a Challenge is supposed to avoid.

Two disclosures about the wider formalization, neither part of this entry: printed
Proposition 4.4 of the paper is false, and the substantive repository carries a
machine-checked counterexample satisfying its printed hypotheses together with the
natural Q-norm repair; and the Section 2 ambient tan-Θ theorem is not locally
self-contained, since its printed statement omits a crossed-defect condition the
paper introduces later and then treats as standing.

## Structure

`Challenge.lean` states the theorem against Mathlib alone, with a deliberate
statement-side hole. `Solution.lean` supplies the same declaration from the
substantive development, pinned as a Lake dependency. Comparator checks that the
two agree and that the proof uses only `propext`, `Quot.sound` and
`Classical.choice`.

The proof extends `T` and `S` to globally coercive and globally bounded operators
using the invariance of `U`, `V` and their orthogonal complements, derives a
Sylvester relation for `P_U ∘ P_V`, and applies a Sylvester norm bound. It stays in
the substantive repository rather than being copied here.
