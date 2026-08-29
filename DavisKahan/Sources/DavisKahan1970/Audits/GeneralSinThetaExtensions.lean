/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.GeneralSinThetaExtensions

/-!
# Trusted-dependency audit for optional natural-input extensions

Compile this leaf only after every imported extension module builds from
source.  The established source endpoints are repeated here so a repair pass
cannot accidentally regress the theorem completed at the base commit.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

#check TauCeti.DavisKahan1970.sinTheta
#check TauCeti.DavisKahan1970.generalizedSinTheta
#check TauCeti.DavisKahan1970.sinTheta_real
#check TauCeti.DavisKahan1970.generalizedSinTheta_real
#check TauCeti.DavisKahan1970.sinTheta_real_spectralSubspace
#check TauCeti.DavisKahan1970.generalizedSinTheta_real_spectralSubspace
#check TauCeti.DavisKahan1970.generalizedSinTheta_spectralSubspace
#check TauCeti.DavisKahan1970.sinTheta_reducingSubspace_complex
#check TauCeti.DavisKahan1970.sinTheta_reducingSubspace_real
#check TauCeti.DavisKahan1970.generalizedSinTheta_reducingSubspace_complex
#check TauCeti.DavisKahan1970.generalizedSinTheta_reducingSubspace_real
#check TauCeti.DavisKahan1970.sinTheta_bounded_spectralSubspace
#check TauCeti.DavisKahan1970.generalizedSinTheta_bounded_spectralSubspace
#check TauCeti.DavisKahan1970.sinTheta_bounded_real_spectralSubspace
#check TauCeti.DavisKahan1970.generalizedSinTheta_bounded_real_spectralSubspace
#check mul_subspaceGap_le_of_two_directedGap_le
#check mul_subspaceGap_le_max_of_two_directedGap_le

#print axioms TauCeti.DavisKahan1970.sinTheta
#print axioms TauCeti.DavisKahan1970.generalizedSinTheta
#print axioms TauCeti.DavisKahan1970.sinTheta_real
#print axioms TauCeti.DavisKahan1970.generalizedSinTheta_real
#print axioms TauCeti.DavisKahan1970.sinTheta_real_spectralSubspace
#print axioms TauCeti.DavisKahan1970.generalizedSinTheta_real_spectralSubspace
#print axioms TauCeti.DavisKahan1970.generalizedSinTheta_spectralSubspace
#print axioms TauCeti.DavisKahan1970.sinTheta_reducingSubspace_complex
#print axioms TauCeti.DavisKahan1970.sinTheta_reducingSubspace_real
#print axioms TauCeti.DavisKahan1970.generalizedSinTheta_reducingSubspace_complex
#print axioms TauCeti.DavisKahan1970.generalizedSinTheta_reducingSubspace_real
#print axioms TauCeti.DavisKahan1970.sinTheta_bounded_spectralSubspace
#print axioms TauCeti.DavisKahan1970.generalizedSinTheta_bounded_spectralSubspace
#print axioms TauCeti.DavisKahan1970.sinTheta_bounded_real_spectralSubspace
#print axioms TauCeti.DavisKahan1970.generalizedSinTheta_bounded_real_spectralSubspace
#print axioms mul_subspaceGap_le_of_two_directedGap_le
#print axioms mul_subspaceGap_le_max_of_two_directedGap_le

end ExactSinTheta
end DavisKahan
end TauCeti
