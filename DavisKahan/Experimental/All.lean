/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.All

/-! # Experimental Davis--Kahan theory

## Why there is no `Experimental.Sources.All`

`DavisKahan/Experimental/Sources/**` held the Davis--Kahan 1970 Section 8
package while its import closure still went through modules that did not
compile.  That closure became admission-free and buildable, so the package
moved to `DavisKahan/Sources/DavisKahan1970/Section8/` — exactly the promotion
its own aggregate docstring asked for — and the two `Experimental` aggregates
that existed only to reach it were deleted rather than left as empty shells.
`DavisKahan.All`, imported above, reaches Section 8 now.

**`Experimental/InfiniteDimensional/` is deleted (2026-08-27).**  Seventeen files
and about 4700 lines of an older ambient route, audited declaration by
declaration before removal: every module was either an explicitly labelled
"open obligations" interface whose proved part had already moved to
`SpectralTheory/PartialMap/**`, `Sylvester/**` or `ForTauCeti/.../LinearPMap/**`,
an unimplemented "construction plan", or a "legacy" engine the canonical one
never imported.  None of the seventeen elaborated any more -- each failed on
namespaces and identifiers (`DavisKahan.Experimental.Foundation`,
`IsUnitaryOperator`, `IntervalExteriorSeparated`) that no longer exist -- so
none of it was available for promotion without a rewrite, and nothing was
checking that, because the whole subtree was excluded from the coverage gate.
The census had already recorded the sharpest case: `ideal_sinTheta` and
`ideal_sinTwoTheta` there read exactly like the missing real-scalar `sin 2Theta`
endpoint and are **not** coverage, because their proofs are incomplete; the endpoint
was closed elsewhere.

The live development is `DavisKahan.All` together with `Geometry.Angle.*`,
`TanTwoTheta.All` and `DoubleAngle.{Unbounded,UnboundedIdeal}`, all of which
`DavisKahan.All` reaches.

## Why there is no `Experimental.Frontier.All`

That aggregate existed to build `DavisKahan/Experimental/Frontier/**`, which was
promoted long ago; by the end it imported six production modules and nothing
else, every one of them already reachable from the `DavisKahan.All` above.  It
is deleted rather than kept as an empty shell, for the same reason its
`Experimental.Sources` siblings were.
-/
