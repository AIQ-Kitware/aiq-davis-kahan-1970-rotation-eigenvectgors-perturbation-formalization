/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.All

/-!
# Admission-dependent Davis--Kahan API test bed

This explicit, nondefault root collects only modules that contain an admission
or depend transitively on one.  Claimed mathematics belongs under the normal
`DavisKahan` tree and is built by the ordinary `lake build` through
`DavisKahan.All`.
-/
