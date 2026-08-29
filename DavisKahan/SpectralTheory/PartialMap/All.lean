/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.PartialMap.Basic
import DavisKahan.SpectralTheory.PartialMap.BoundedRealization
import DavisKahan.SpectralTheory.PartialMap.Complexification
import DavisKahan.SpectralTheory.PartialMap.RealSpectrum
import DavisKahan.SpectralTheory.PartialMap.UnitaryConjugation

/-! # `DavisKahan/SpectralTheory/PartialMap`

The Davis--Kahan additions to Mathlib's `LinearPMap`: the real resolvent set and
spectrum, coordinatewise complexification, unitary conjugation, and bounded
realization.  Named `PartialMap` until 2026-08-28, after the bundled record
of that name. -/
