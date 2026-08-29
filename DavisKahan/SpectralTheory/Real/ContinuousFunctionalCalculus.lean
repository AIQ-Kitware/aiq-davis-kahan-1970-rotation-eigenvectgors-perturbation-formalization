/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForTauCeti.Analysis.InnerProductSpace.SpectralOrder.Real

/-!
# Real operator continuous-functional-calculus roadmap

Mathlib's star-order bridge for Hilbert-space operators is parameterized by
`RCLike`, but the continuous functional calculus instance needed to register
the order is currently available only for complex operator algebras.  This
module reserves the alternative foundational route: construct the missing real
operator functional calculus and then obtain the real spectral bridge by the
same order argument as the complex specialization.

This module is intentionally excluded from the supported umbrella.
-/
