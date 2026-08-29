/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
import ForTauCeti.Analysis.InnerProductSpace.SinTheta.OperatorNorm

/-!
# Solution: the Davis–Kahan operator-norm sin-Θ theorem

The compared declaration is `TauCeti.norm_starProjection_comp_starProjection_le`,
proved in `ForTauCeti/Analysis/InnerProductSpace/SinTheta/OperatorNorm.lean` of the
accompanying development and brought into scope by the import above.

The proof is not restated here. It builds the globally coercive extension
`T ∘ P_U + (c+g)(1 - P_U)` and the globally bounded `S ∘ P_V + c(1 - P_V)`, uses
the invariance of `U` and `V` and of their orthogonal complements to obtain the
Sylvester relation `A ∘ X - X ∘ B = P_U ∘ (T - S) ∘ P_V` for `X = P_U ∘ P_V`, and
concludes with a Sylvester norm bound; `‖P_V ∘ P_U‖ = ‖P_U ∘ P_V‖` because the
projections are self-adjoint. Duplicating that chain in a wrapper would create a
second copy to keep in step with the first.
-/
