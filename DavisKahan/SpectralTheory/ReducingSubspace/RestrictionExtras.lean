/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.ReducingSubspace.Restriction

/-!
# Convenience laws for reducing restrictions

This leaf keeps optional compatibility lemmas separate from the compiler-accepted
core restriction construction.  In particular, it records orthogonal-complement
closure and agreement with the ordinary bounded restriction.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

namespace PartialMap
namespace ReducesSubspace

omit [CompleteSpace E] in
/-- Orthogonal complementation preserves the reducing-subspace property. -/
theorem orthogonal
    {A : E →ₗ.[𝕜] E}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h : TauCeti.LinearPMap.ReducesSubspace A U) : TauCeti.LinearPMap.ReducesSubspace A Uᗮ :=
  TauCeti.LinearPMap.ReducesSubspace.orthogonal h

end ReducesSubspace

omit [CompleteSpace E] in
/-- A bounded reducing-subspace law induces the domain-aware law for the
full-domain closed operator. -/
theorem ofBounded_reducesSubspace
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.Reduces U) :
    TauCeti.LinearPMap.ReducesSubspace (A.toLinearMap.toPMap ⊤) U := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simp
  · intro x
    simp
  · intro x hx
    show A (x : E) ∈ U
    exact hred.1 (x : E) hx
  · intro x hx
    show A (x : E) ∈ Uᗮ
    exact hred.2 (x : E) hx

end PartialMap
end DavisKahanExt
end TauCeti
