/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.Ideals.UnitaryInvariantNormInstances
import DavisKahan.Sources.DavisKahan1970.Sylvester.HilbertSchmidtPairwise

/-!
# Audit surface for the literal square-norm Sylvester theorem

This module is intentionally excluded from ordinary aggregates. Compile it
directly after repairing the new infrastructure, then inspect the trusted
assumptions of every declaration below.

Updated 2026-07-29: the uniqueness half of the chain no longer runs through
Spectra's generator-intertwiner, so auditing
`generatorIntertwiner_eq_zero_of_disjoint_spectrum`,
`spectralProjection_intertwines_of_generator` and `GeneratorIntertwines.group`
was auditing constants the theorem no longer depends on.  They are replaced by
the single native endpoint
`TauCeti.LinearPMap.eq_zero_of_intertwines_of_disjoint_spectrum`.  The remaining
`Spectra.HilbertSchmidtTensor.*` entries are SR-D's, and are still load-bearing.

Also 2026-07-29: the direct `Spectra.QuantumMechanics.BornRule.Joint.ProjectivePVM`
import was dropped.  Nothing in this file referenced a declaration from it — the
Born-rule module was reached anyway, transitively, through
`Sylvester.HilbertSchmidtPairwise`, so the explicit import bought nothing and
made this file look like an independent Spectra consumer when it is not.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

#check paperNuclearNorm
#check paperUnitaryInvariantNorm_nonempty
#check TauCeti.HilbertSchmidt.ofLp
#check isPaperHilbertSchmidt_iff_existsUnique_tensor
#check paperHilbertSchmidtNorm_toOperator
#check TauCeti.HilbertSchmidt.sylvesterGroup
#check TauCeti.HilbertSchmidt.generator_sylvesterGroup_apply
#check TauCeti.OneParameterUnitaryGroup.isSelfAdjoint_generator
#check TauCeti.LinearPMap.generator_genToGroup
#check TauCeti.HilbertSchmidt.isSelfAdjoint_generator_sylvesterGroup
#check TauCeti.LinearPMap.apply_gapInverse
#check TauCeti.LinearPMap.eq_zero_of_intertwines_of_disjoint_spectrum
#check closedSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
#check TauCeti.HilbertSchmidt.hasVectorSpectralGap_sylvesterGroup
#check paperHilbertSchmidtTensor_hasVectorSpectralGap
#check paperHilbertSchmidt_sylvester_defectFirst
#check paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
#check paperHilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap_direct

#print axioms paperUnitaryInvariantNorm_nonempty
#print axioms isPaperHilbertSchmidt_iff_existsUnique_tensor
#print axioms paperHilbertSchmidtNorm_toOperator
#print axioms TauCeti.HilbertSchmidt.generator_sylvesterGroup_apply
#print axioms TauCeti.OneParameterUnitaryGroup.isSelfAdjoint_generator
#print axioms TauCeti.LinearPMap.generator_genToGroup
#print axioms TauCeti.HilbertSchmidt.isSelfAdjoint_generator_sylvesterGroup
#print axioms TauCeti.LinearPMap.apply_gapInverse
#print axioms TauCeti.LinearPMap.eq_zero_of_intertwines_of_disjoint_spectrum
#print axioms closedSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
#print axioms TauCeti.HilbertSchmidt.hasVectorSpectralGap_sylvesterGroup
#print axioms paperHilbertSchmidtTensor_hasVectorSpectralGap
#print axioms paperHilbertSchmidt_sylvester_defectFirst
#print axioms paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
#print axioms paperHilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap_direct

end ExactSinTheta
end DavisKahan
end TauCeti
