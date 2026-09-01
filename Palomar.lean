/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

/-!
# Palomar entries

Each entry is a `Challenge` module, stating its theorems against Mathlib alone
with deliberate statement-side holes, and a `Solution` module proving the same
declarations from the development.  The two are compared by the Comparator; this
root imports neither, so building it never builds a Challenge's holes.
-/
