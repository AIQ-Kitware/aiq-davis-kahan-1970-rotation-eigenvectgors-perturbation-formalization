/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm.Basic
public import ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm.Majorization
public import ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm.BlockSum
public import ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm.Instances

/-!
# Rectangular unitarily invariant norms

Aggregate entry point.  The development is split across the four modules imported
above so that each stays under Tau Ceti's file-length ceiling; importing this name
gives the whole theory, exactly as before the split.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm`,
  split out on 2026-07-28 because that file had grown to 2124 lines while Tau Ceti's
  `lean_lib` enforces a hard 1500-line ceiling, and 1000 for a newly added file.
* Extraction class: **split**.  No statement, proof or declaration name changed; only
  `exists_unitary_factorization_of_singularValues_eq` was promoted from `private` to
  public, because the split puts its users in a different module.
* Original authors / copyright: Jon Crall, Claude Fable 5;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section
