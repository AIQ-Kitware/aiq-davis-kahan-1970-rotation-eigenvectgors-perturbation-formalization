/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Sources.DavisKahan1970.Section8.All

/-!
# Dependency audit for Davis--Kahan 1970 Section 8: internal infrastructure

**This is not the audit of the printed theorems.**  The declarations below are
the conditional bridges and abstract cores that Section 8's analytic layer and
Section 9's continuation layer consume: they take caller-supplied data records
-- a `SpectralContinuationWitness`, a half-gap bridge, an abstract quadratic
block record -- which the paper *proves* rather than assumes.  They are useful
and their trusted-dependency reports are clean, and that is all this
leaf certifies.

The audit of the actual Section 8 capstones is
`DavisKahan/Audits/Section8.lean`, which must live downstream of the analytic
layer because that is where Section 8's analytic content is.  It checks
Theorem 8.1's branch, characterization and uniqueness; parts (i), (ii) and (iii)
for both blocks including the every-symmetric-gauge forms; the eigenvalue/angle
source dictionary; and both Theorem 8.2 alternatives together with the printed
`Theta < pi/4`.

The trusted-dependency reports here should contain only the standard
classical/choice foundations inherited from the spectral calculus, and nothing
project-local.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

#check maximalAngle_selectedSpectralSubspaces_lt_pi_div_four
#check selectedBranchConclusion_of_contour_bound
#check orientedSpectralRepulsionConclusion
#check theorem81CoreConclusion
#check upperCompressionRepulsion_of_data
#check lowerCompressionRepulsion_of_data
#check theorem82_branch_of_perturbationHalfGapBridge
#check theorem82_branch_of_residualHalfGapBridge
#check theorem8_1_selectedBranch_and_spectralRepulsion
#check theorem8_2_perturbationHalfGap_selectedBranch
#check theorem8_selectedBranch_tan_maximalAngle_le_div

#print axioms maximalAngle_selectedSpectralSubspaces_lt_pi_div_four
#print axioms selectedBranchConclusion_of_contour_bound
#print axioms orientedSpectralRepulsionConclusion
#print axioms theorem81CoreConclusion
#print axioms upperCompressionRepulsion_of_data
#print axioms lowerCompressionRepulsion_of_data
#print axioms theorem82_branch_of_perturbationHalfGapBridge
#print axioms theorem82_branch_of_residualHalfGapBridge

end Section8
end DavisKahan1970
end TauCeti