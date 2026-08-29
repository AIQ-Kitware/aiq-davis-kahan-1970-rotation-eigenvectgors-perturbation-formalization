/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Sources.DavisKahan1970.Section8.Smallness
import DavisKahan.Sources.DavisKahan1970.Section8.CompressionRepulsion
import DavisKahan.Sources.DavisKahan1970.Section8.SourceTheorem81
import DavisKahan.InfiniteDimensional.TanTheta.ContinuationWitnessAPriori

/-!
# Davis--Kahan 1970 Section 8 source surface

This leaf is the **low-level** Section 8 facade: it gives stable source-facing
names to the results that live upstream of the analytic layer.
`Section8/BranchRepulsion.lean` imports it, so it cannot itself import the
downstream Theorem 8.2 modules.

**The final facade is `Section8/PaperSurface.lean`,** downstream of
`Theorem81Approximation`, `Theorem81Majorization`, `Theorem81AngleForms`,
`Theorem82Branch` and the two `Theorem82Source` modules.  Its declarations land
in this same namespace, `TauCeti.DavisKahan1970.Section8`.  Read it, not this
file, for the claim-by-claim map of the printed section.

**Theorem 8.1 is promoted** (2026-08-07).  `SourceTheorem81.lean` proves it from
the printed hypotheses alone -- self-adjoint `A` reduced by `P`, the ordered
form gap, and a fully off-diagonal self-adjoint `H` -- with no contour, no
continuation witness, no smallness constant, and no caller-supplied orientation.
It delivers full spectral repulsion (continuous spectrum included), the
canonical branch as a genuine spectral subspace, the strict quarter-angle bound,
uniqueness of the branch under the printed *closed* condition, and the printed
`iff` between that condition and the spectral orientation.

**Parts (i)--(iii) and Theorem 8.2 are promoted too**, downstream.  Parts (i),
(ii) and (iii) are proved for *both* blocks at the canonical branch, part (iii)
for every symmetric gauge; Theorem 8.2's perturbation alternative is the printed
connectedness bootstrap and its residual alternative the printed Krein
reduction, both from the printed hypotheses with no half-gap bridge among them.
The earlier status note here, that (i)--(iii) were not fed the canonical branch
and that 8.2 still needed a common-contour witness and the Krein theorem, is
obsolete and has been removed.

The `..._of_rotatedBlockData` aliases below remain the *algebraic cores* -- they
take an abstract quadratic-data record and are internal infrastructure, not
evidence about the printed theorem.  `theorem8_1_selectedBranch_and_spectralRepulsion`
and `theorem8_2_perturbationHalfGap_selectedBranch` are likewise conditional
wrappers kept for Section 9's continuation layer; the source-facing statements
are the ones named in the downstream facade.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open Set
open scoped InnerProductSpace
open DavisKahanExt

universe v

section SourceAliases

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A V : H →L[ℂ] H} {s : Set ℝ}

/-- **Source-facing Theorem 8.1: existence of the canonical branch.**

Takes only the printed hypotheses.  Superseded name for
`theorem8_1_canonicalBranch`. -/
alias theorem8_1_source :=
  theorem8_1_canonicalBranch

/-- **Source-facing Theorem 8.1: the printed characterization.** -/
alias theorem8_1_source_characterization :=
  theorem8_1_maximalAngle_le_iff_spectrumIn

/-- **Source-facing Theorem 8.1: uniqueness of the branch.** -/
alias theorem8_1_source_uniqueness :=
  theorem8_1_eq_canonicalBranch_of_maximalAngle_le

/-! `theorem8_1_selectedBranch_and_spectralRepulsion` and
`theorem8_2_perturbationHalfGap_selectedBranch` used to be aliases here, for
`theorem81CoreConclusion` and `theorem82_branch_of_perturbationHalfGapBridge`
respectively.  Both aliases named a statement that takes the branch selection,
the contour smallness and the spectral orientation as *caller-supplied data*,
and both docstrings said so.  The theorems that actually carry those source
names -- proving the same conclusions from a circle datum, and adding the two
compression clauses -- are in `Section8/BranchRepulsion.lean`, in this same
namespace, so the aliases were competing with them for one source-numbered name
and are gone.  `theorem81CoreConclusion` and
`theorem82_branch_of_perturbationHalfGapBridge` keep their own names and their
consumers. -/


/-- Source-facing algebraic core of Theorem 8.1(i), before instantiating the
abstract quadratic data with the concrete direct-rotation sine/cosine blocks. -/
alias theorem8_1_upperCompressionRepulsion_of_rotatedBlockData :=
  upperCompressionRepulsion_of_data

/-- Lower-block companion of the source compression-repulsion inequality. -/
alias theorem8_1_lowerCompressionRepulsion_of_rotatedBlockData :=
  lowerCompressionRepulsion_of_data

/-- The continuation-selected endpoint has a unique contractive graph
coordinate.  This is the graph-theoretic form of selecting the side below the
quarter-turn pole. -/
alias theorem8_selectedEndpoint_existsUnique_contractiveAngularOperator :=
  SpectralContinuationWitness.existsUnique_selectedEndpointAngularOperator

/-- The selected branch satisfies the witness-level a priori tangent bound
once off-diagonality and the ordered form gap are supplied.  This is useful to
Section 9 after the canonical spectral branch has been identified. -/
alias theorem8_selectedBranch_tan_maximalAngle_le_div :=
  SpectralContinuationWitness.tan_maximalAngle_selectedSpectralSubspaces_le_div

end SourceAliases

end Section8
end DavisKahan1970
end TauCeti