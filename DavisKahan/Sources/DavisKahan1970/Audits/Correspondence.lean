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
#check PaperCommonCoreResidualData.extends_to_domain
#check unboundedSinThetaDataOfPaperCommonCore
#check PaperCommonCoreTheorem61Data.result_every_unitarilyInvariantNorm_across
#check PaperCommonCoreTheorem62Data.result_across
#check PaperRealCommonCoreTheorem61Data.result_every_unitarilyInvariantNorm_across
#check PaperRealCommonCoreTheorem62Data.result_across
#check spectrum_paperSourceDirectedAngleC_subset_Icc
#check paperSineDefinedDirectedAngleC_eq_source
#check paperSourceDirectedAngleC_eq_arcsin_sineModulus
#check paperSourceDirectedAngleR_eq_arcsin_sineModulus

#print axioms PaperCommonCoreResidualData.extends_to_domain
#print axioms PaperCommonCoreTheorem61Data.result_every_unitarilyInvariantNorm_across
#print axioms PaperCommonCoreTheorem62Data.result_across
#print axioms paperSineDefinedDirectedAngleC_eq_source

end ExactSinTheta
end DavisKahan
end TauCeti
