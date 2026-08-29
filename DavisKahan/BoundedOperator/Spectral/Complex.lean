/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8, GPT 5.6 High
-/
import DavisKahan.BoundedOperator.Compat
import ForTauCeti.Analysis.InnerProductSpace.SpectralOrder.Complex

/-!
# Complex spectral specialization of bounded Davis--Kahan theory

The supported perturbation theorem is scalar-generic and consumes form bounds.
This leaf module obtains those bounds from spectra of actual restricted
operators on complex Hilbert spaces.
-/

namespace TauCeti

open TauCeti
namespace DavisKahan
namespace Spectral
namespace Complex

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Sharp complex Davis--Kahan theorem from spectra of actual restrictions. -/
theorem opNorm_starProjection_sub_le_of_restriction_spectra
    {A B : H →L[ℂ] H} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric)
    {U W : Submodule ℂ H} [U.HasOrthogonalProjection]
    [W.HasOrthogonalProjection]
    (hU : Reduces A U) (hW : Reduces B W)
    {c g : ℝ} (hg : 0 < g)
    (hUhi : spectrum ℝ (A.restrict hU.1) ⊆ Set.Ici (c + g))
    (hUlo : spectrum ℝ (A.restrict hU.2) ⊆ Set.Iic c)
    (hWhi : spectrum ℝ (B.restrict hW.1) ⊆ Set.Ici (c + g))
    (hWlo : spectrum ℝ (B.restrict hW.2) ⊆ Set.Iic c) :
    ‖(U.starProjection - W.starProjection : H →L[ℂ] H)‖ ≤
      ‖B - A‖ / g := by
  apply opNorm_starProjection_sub_le_of_formBounds hA hB hU hW hg
  · exact SpectralOrder.Complex.lowerFormBoundOn_of_restriction_spectrum_subset_Ici
      hA hU.1 hUhi
  · exact SpectralOrder.Complex.upperFormBoundOn_of_restriction_spectrum_subset_Iic
      hA hU.2 hUlo
  · exact SpectralOrder.Complex.lowerFormBoundOn_of_restriction_spectrum_subset_Ici
      hB hW.1 hWhi
  · exact SpectralOrder.Complex.upperFormBoundOn_of_restriction_spectrum_subset_Iic
      hB hW.2 hWlo


end Complex
end Spectral
end DavisKahan
end TauCeti