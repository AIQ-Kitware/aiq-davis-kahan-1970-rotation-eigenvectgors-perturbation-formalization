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
