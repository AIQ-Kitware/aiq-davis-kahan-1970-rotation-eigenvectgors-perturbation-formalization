/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.CommonCoreTheorems
import DavisKahan.Sources.DavisKahan1970.SineTheta.AngleIdentity

/-!
# Focused audit for the paper-correspondence mathematics-ahead layer

This file is intentionally excluded from normal imports.  Compile it directly
after the implementation leaves, then inspect the printed dependencies before
promoting the new source forms.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

#check PartialMap.IsGraphCore
#check CommonCoreResidualData.extends_to_domain
#check unboundedSinThetaDataOfCommonCore
#check CommonCoreTheorem61Data.result_every_unitarilyInvariantNorm_across
#check CommonCoreTheorem62Data.result_across
#check RealCommonCoreTheorem61Data.result_every_unitarilyInvariantNorm_across
#check RealCommonCoreTheorem62Data.result_across
#check spectrum_directedAngleBlockC_subset_Icc
#check sineDefinedDirectedAngleC_eq_directedAngleBlockC
#check sourceDirectedAngleC_eq_arcsin_sineModulus
#check sourceDirectedAngleR_eq_arcsin_sineModulus

#print axioms CommonCoreResidualData.extends_to_domain
#print axioms CommonCoreTheorem61Data.result_every_unitarilyInvariantNorm_across
#print axioms CommonCoreTheorem62Data.result_across
#print axioms sineDefinedDirectedAngleC_eq_directedAngleBlockC

end ExactSinTheta
end DavisKahan
end TauCeti
