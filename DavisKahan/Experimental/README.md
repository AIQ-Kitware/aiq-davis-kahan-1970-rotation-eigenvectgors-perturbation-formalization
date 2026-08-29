# Experimental Davis--Kahan development

This tree is what is left of a staging area that has now been drained. Stable
modules must not import it; it may import them.

Everything it once held has been promoted or deleted. The Davis--Kahan 1970
source-facing statements live under `DavisKahan/Sources/DavisKahan1970/`, the
reusable mathematics under `DavisKahan/Geometry/`, `DavisKahan/SpectralTheory/`,
`DavisKahan/BoundedOperator/`, `DavisKahan/Sylvester/`,
`DavisKahan/InfiniteDimensional/` and `ForTauCeti/`, and the concrete
applications under `DavisKahan/Specialized/`.

What was removed, and why:

- `Frontier/` (2026-08-27) — the Section 3 classification spine, the Section 4
  propositions and the Section 9 analytic model were promoted long ago; the
  aggregate that remained imported six production modules and nothing else, all
  of them already reachable from `DavisKahan.All`. Its documentation described a
  repair order for a directory that no longer existed.
- `InfiniteDimensional/` (2026-08-27) — seventeen files of an older ambient
  route, audited declaration by declaration first. Every module was an
  explicitly labelled "open obligations" interface whose proved part had already
  moved to production, an unimplemented "construction plan", or a "legacy"
  engine the canonical one never imported; and none of the seventeen elaborated
  any more. See the `DavisKahan/Experimental/All.lean` docstring for the audit.
- `MathAhead/` (2026-08-27) — one abandoned route to the circle continuation
  contour, superseded by `SpectralTheory/CircleContour.lean` and
  `InfiniteDimensional/SinTheta/Continuation/CircleWitness.lean`.
- `Scratch/SharedFoundations/Ideal/` (2026-08-27) — two ideal-family
  experiments that had stopped compiling against the current ideal API.  Both
  carried mathematics worth keeping, so both were promoted rather than deleted:
  `ModulusTransport.lean` (a unitarily invariant gauge is absolute: `T` and
  `|T|` have the same one, by the two polar contraction factorizations) and
  `ReflectionTransport.lean` (reflections preserve ideal membership and gauge,
  so the directed mirror-angle block and the double-angle block agree).  Both
  now live under `DavisKahan/SharedFoundations/Ideal/`.

What remains: nothing.  The tree holds this file and an aggregate that imports
`DavisKahan.All`.  That is the correct steady state — a staging area is empty
between campaigns — and `scripts/check_experimental_coverage.py` now has an
empty exclusion list, which is the shape to keep it in.  A subtree exclusion
there is a standing bet that nobody is checking the modules inside it, and the
`InfiniteDimensional` deletion is what that bet cost.  Prefer promoting or
deleting to adding an exclusion.

Build the experimental development with:

```bash
lake build DavisKahan.Experimental
```
