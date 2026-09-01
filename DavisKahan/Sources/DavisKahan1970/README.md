# Davis--Kahan 1970 source coverage

This directory is the publication-facing layer for Chandler Davis and W. M. Kahan,
*The Rotation of Eigenvectors by a Perturbation. III*, SIAM Journal on Numerical
Analysis 7 (1970), 1--46.

## What is authoritative

Do not infer completion from this README or from the presence of one facade file.
The maintained theorem-by-theorem authority is
`dev/davis-kahan-1970-full-source-census.json`, with the generated readable view in
`dev/davis-kahan-1970-full-source-census.md`, and the completion denominator is
`dev/davis-kahan-1970-formalization-result-inventory.json` with its generated
view `dev/davis-kahan-1970-formalization-result-inventory.md`.

Run the checker for the current source-obligation summary:

```bash
python3 scripts/check_davis_kahan_1970_source_census.py
```

When Lean is available, use the compile-backed census/probe tooling for declaration
reachability rather than copying a current count into this document.

## The four Section 2 theorems

`SectionTwo.lean` is the public inventory of the paper's four unnumbered headline
theorems, over both scalar fields:

```
TauCeti.DavisKahan1970.SectionTwo.sinTheta_complex       sinTheta_real
TauCeti.DavisKahan1970.SectionTwo.tanTheta_complex       tanTheta_real
TauCeti.DavisKahan1970.SectionTwo.sinTwoTheta_complex    sinTwoTheta_real
TauCeti.DavisKahan1970.SectionTwo.tanTwoTheta_complex    tanTwoTheta_real
```

Each *type* displays an unbounded self-adjoint `LinearPMap` ambient operator,
arbitrary Hilbert dimension, a `PaperUnitaryInvariantNorm`, and both printed
conclusions. `SectionTwoUsage.lean` shows each being called from ordinary
operator-theory hypotheses.

Whether each matches the printed result is a separate, reviewed question, and
`dev/davis-kahan-1970-formalization-result-inventory.json` owns the answer --
including its standing qualification for `S2-tan-theta`. Do not read the sentence
above as that review's verdict; it describes the signatures, not the audit.

The scalar-generic presentation forms, directed and whole-space variants, finite
specializations, operator-norm statements and bundled-problem entry points remain
where they are and are unaffected; they are simply not the inventory a reader
should have to assemble.

## Production source aggregate

`DavisKahan/Sources/DavisKahan1970/All.lean` is the stable aggregate for the
production source development. It includes the maintained Section 8 and Section 9
packages as well as the sine-theta, Sylvester, double-angle, tangent, direct-
rotation, and Part III source surfaces.

The census is deliberately more precise than a blanket "paper complete" claim. It
records proved, conditional, refuted, scope-qualified, and non-proof-debt source
items separately. Consult it for the exact status and declaration names instead
of maintaining a second hand-written status table here.

## Completion standard

The durable scope/completion rules are summarized in
[`docs/planning/davis-kahan-full-paper-goal.md`](../../../docs/planning/davis-kahan-full-paper-goal.md).
Current repository policy is in [`AGENTS.md`](../../../AGENTS.md).
