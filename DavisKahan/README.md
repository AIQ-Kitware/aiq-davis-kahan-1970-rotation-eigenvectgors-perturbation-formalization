# DavisKahan

This is the canonical Davis--Kahan library root.

## Headline finding: Proposition 4.4 of the published paper is false

**Davis--Kahan (1970), Proposition 4.4 is not a theorem, and this library
machine-checks the refutation.** The claim, as transcribed, is:

> over a real space, if every principal angle is at most `π/3`, then the direct
> rotation minimizes every unitarily invariant norm of the full displacement
> `I - W` over unitaries `W` carrying `U` onto `V`.

It fails already for the trace norm in `ℝ⁴`.

**The witness is explicit and small.** Take `U = span{e₀, e₁}` and the
orthogonal competitor `W = ½·H` with

```
H = !![ 1,-1,-1,-1;  1, 1, 1,-1; -1,-1, 1,-1;  1,-1, 1, 1]
```

and `V = W(U)`. Both principal angles are `π/4 ≤ π/3` and the pair is acute, so
the hypothesis holds. `W` restricted to `M = span{(e₀+e₂)/√2, (e₁+e₃)/√2}` is a
rotation by `π/2` fixing `Mᗮ` pointwise, so `σ(I-W) = (√2, √2, 0, 0)` and the
trace norm is `2√2` — strictly smaller than the direct rotation's. The
conclusion therefore fails under the stated hypothesis.

| what | where |
|---|---|
| the configuration and the refutation | [`FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean`](FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean) |
| the source claim, stated as written | `DavisKahanProposition4_4_Finite` |
| the refutation | `not_davisKahanProposition4_4_Finite` |
| the norm-agnostic form | `shortRotation_fullDisplacement_refuted` |

**On universes, because the statement is polymorphic.** Lean cannot quantify
over universes, so `¬ P.{0}` is the strongest available refutation of a
universe-polymorphic `P` — and it suffices: a polymorphic `P` holds only if it
holds at every universe, so refuting it at universe `0` refutes it outright. The
witness `EuclideanSpace ℝ (Fin 4)` lives there.

**What replaces it.** Two nearby statements *are* true and are the endpoints to
reach for instead:

- `uiNorm_restrictedDisplacement_le` — the **restricted** displacement, with no
  angle hypothesis at all;
- `directRotation_displacementSquare_uiNorm` — the displacement **square**.

The failure is specific: it is the *full* displacement under a *largest-angle*
hypothesis that does not hold, not the direct rotation's optimality in general.

### Why this is first class, and why abandoned internal work is not

**jon, 2026-07-30.** A refuted claim in a *published paper* is a contribution:
it is a correction to the literature, it is what a reader most needs to know
before trusting the source, and it is why the counterexample, the explanation of
the failure, and the corrected endpoints all live in the production library
rather than in a footnote.

That is the opposite of an approach *we* tried and abandoned. Those are
sequestered into `FailedAttempts` precisely because they
teach a reader nothing about the mathematics — only about our route to it.

**This material is deliberately not `ForTauCeti`-bound.** It is paper-specific
refutation, not reusable general mathematics, so it stays here. `AGENTS.md`
carries the general rule — *a source claim shown false is completed by a
machine-checked counterexample, an explanation of the failure, and a corrected
theorem when one is justified* — and this is its flagship instance. **Do not
restore Proposition 4.4 as a theorem.**

## Project mission

The default target is the full Hilbert-space theory of Davis--Kahan (1970), not
only a bounded or finite-dimensional specialization.  The canonical
source-facing single-angle theorem must include the paper's unbounded
self-adjoint scope with explicit domains and bounded residuals, together with
arbitrary supported unitary-invariant norms.  Bounded Hermitian operators are a
major specialization and proof seam, not the final API boundary.

The finite branch is a valuable proof-complete specialization with weaker
foundational requirements and a richer currently implemented UI-norm API. It
must not be presented as completion of the paper unless the claim is explicitly
qualified as finite-dimensional.

- `BoundedOperator/` contains supported arbitrary-Hilbert-space bounded
  specializations and reusable geometric foundations. It is not the owner of
  the unqualified source-facing theorem names.
- `FiniteDimensional/Core/` contains finite spectral-subspace, gap, angle, and
  block-operator vocabulary.
- `FiniteDimensional/Residual/` contains Ritz, trial-map, and angle-embedding
  residual interfaces.
- `FiniteDimensional/Sylvester/` contains finite-dimensional Sylvester
  estimates and their internal reciprocal-multiplier machinery.
- `FiniteDimensional/SinTheta/`, `TanTheta/`, and `DoubleAngle/` contain the
  stable finite theorem families.
- `FiniteDimensional/DirectRotation/` contains the proved canonical rotation
  construction and its basic intertwining surface.
- `Sources/` contains publication-facing theorem surfaces and source-specific
  wrappers. `Sources/DavisKahan1970/README.md` and the generated source census
  record the current proved/conditional boundary across the 1970 paper.
- `Specialized/` contains distinct useful secondary endpoints.
- `Alternative/` contains proof-complete duplicate or lower-dependency proofs
  and noncanonical wrapper APIs retained for explicit reuse and cherry-picking.

The dependency direction is deliberate: canonical bounded and finite modules
must not import `Sources`, `Specialized`, or `Alternative`.
Those branches are leaves built on the canonical library.

`import DavisKahan` exposes the supported bounded-operator and
finite-dimensional theory together with the production source aggregate in
`DavisKahan.Sources.All`. That import surface is a convenience and stability
boundary, not a blanket claim that every source obligation is discharged.
Specialized endpoints, alternative proofs, and experiments require explicit
imports.

`import DavisKahan.All` exposes every proof-finished source, specialized, and
alternative module, while still excluding `Experimental`.

The maintained completion standard is documented in
[`docs/planning/davis-kahan-full-paper-goal.md`](../docs/planning/davis-kahan-full-paper-goal.md).
The completed single-angle source map is
[`docs/planning/davis-kahan-general-sin-theta-roadmap.md`](../docs/planning/davis-kahan-general-sin-theta-roadmap.md).
