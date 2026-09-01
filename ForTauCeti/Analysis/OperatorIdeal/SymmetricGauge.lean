/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.MeanInequalities
public import ForTauCeti.Analysis.Convex.Majorization
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Core
public import ForTauCeti.Analysis.OperatorIdeal.Family.Basic
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.DiagonalSequence
public import ForTauCeti.Analysis.OperatorIdeal.Family.KyFanDominance
public import ForTauCeti.Analysis.OperatorIdeal.Family.Schatten
public import ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm

/-!
# Symmetric norming functions on sequences

A **symmetric norming function** in the sense of Gohberg–Kreĭn: a subadditive,
positively homogeneous, permutation-invariant, monotone, normalized gauge on
finitely supported nonnegative sequences, together with its extension to
arbitrary `ℝ≥0∞`-valued sequences.

## Main definitions

* `TauCeti.TruncationGauge` — the structure.
* `TauCeti.TruncationGauge.extend` — the extension to `ℕ → ℝ≥0∞`, as a supremum
  over finitely supported truncations.

## Main results

* `TauCeti.TruncationGauge.single` — the gauge of a basis vector is its value;
  this is what `normalized'` and `symm'` buy together, and everything needing a
  scale goes through it.
* `TauCeti.TruncationGauge.extend_mono` and `extend_smul` — monotone in the
  sequence, and homogeneous under a nonnegative real scalar.
* `TauCeti.TruncationGauge.iSup_le_extend_le_tsum` — the two ends of the scale,
  `‖a‖_∞ ≤ Φ∞ a ≤ ∑ aₙ`, which is where `normalized` earns its place.

## Design

This is the `ℕ`-indexed, `ℝ≥0`-valued counterpart of
`TauCeti.FiniteSymmetricGauge` in `ForTauCeti/Analysis/Convex/Majorization.lean`,
and it mirrors that structure field for field where the two agree. The
differences are forced rather than chosen: values are `ℝ≥0`, so the finite
version's `real_smul'` with its `|c|` becomes plain multiplication and
`neg_single'` disappears; and `mono` and `normalized` are added, both of which
are vacuous or meaningless at a fixed finite index type.

**`extend` is a supremum, not a `tsum`.** The gauge has to be total and genuinely
`∞` off its ideal, and a supremum of an increasing net is total by construction,
where any route through summability reintroduces the side conditions this
interface exists to avoid. The same choice is what lets `schattenENorm` live at
`ℝ≥0∞` without side conditions.

**The supremum is over `Finset.range k` truncations rather than over all finitely
supported minorants.** Those give the same value — `mono` plus `symm` is exactly
what makes a truncation of the decreasing rearrangement extremal among minorants
of the same support size — but the `range k` form is a *monotone* net indexed by
`ℕ`, which is what a limit argument can use. Nothing in this file needs that
equivalence, and the family construction that does should prove it rather than
inherit it as a definition.

## A correction worth keeping

An earlier version of this docstring recorded `extend_smul` as blocked, saying
Mathlib "does not appear to state directly" that `min` commutes with
multiplication in `ℝ≥0∞`. **It does: `mul_min`.** The failing attempt had used
`ENNReal.mul_min_eq_min_mul`, which does not exist, and a single wrong guess at a
name became a recorded claim that the *fact* was absent. **Searching for a name
is not searching for a fact**, and the negative result sat in a
submission-library docstring where the next reader would have believed it.

## Not proved here, deliberately

`extend_coe_finsupp` — that `extend` restricted to a finitely supported sequence
is the gauge itself — is **not** in this file. It is true and it is the obvious
next lemma, but it needs the extremality of `range k` truncations noted above,
which is the same fact `symmetricGaugeFamily` needs. Proving it twice, or proving
it here and having the family slice restate it, is how one fact ends up with two
names. It belongs to the second slice of `{lane:FTC-SYMGAUGE}`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
  The signatures are
  `TauCetiRoadmap/OperatorTheory/OperatorIdeals/Suggested.lean`'s, which recorded
  them as Milestone B1 targets; this is their first implementation.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: none.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

/-- A **symmetric norming function** (Gohberg–Kreĭn): a monotone,
permutation-invariant, normalized gauge on finitely supported nonnegative
sequences.

`symm'` is stated against `Equiv.Perm ℕ` acting by precomposition, which is what
makes "symmetric" a property of `Φ` rather than a property of the sequences it is
applied to. -/
structure TruncationGauge where
  /-- The underlying gauge on finitely supported nonnegative sequences. -/
  toFun : (ℕ →₀ ℝ≥0) → ℝ≥0
  /-- Subadditivity. -/
  add_le' : ∀ a b : ℕ →₀ ℝ≥0, toFun (a + b) ≤ toFun a + toFun b
  /-- Positive homogeneity. -/
  smul' : ∀ (c : ℝ≥0) (a : ℕ →₀ ℝ≥0), toFun (c • a) = c * toFun a
  /-- Permutation invariance — the "symmetric" in symmetric norming function. -/
  symm' : ∀ (σ : Equiv.Perm ℕ) (a : ℕ →₀ ℝ≥0),
    toFun (Finsupp.equivMapDomain σ a) = toFun a
  /-- Monotonicity in the termwise order. -/
  mono' : ∀ ⦃a b : ℕ →₀ ℝ≥0⦄, a ≤ b → toFun a ≤ toFun b
  /-- Normalization: the first basis vector has gauge one.  This fixes the scale,
  and with it the two-sided bound `‖a‖_∞ ≤ Φ a ≤ ∑ aₙ`. -/
  normalized' : toFun (Finsupp.single 0 1) = 1

namespace TruncationGauge

/-- Apply a symmetric gauge directly, writing `Φ a` for `Φ.toFun a`. -/
instance : CoeFun TruncationGauge fun _ => (ℕ →₀ ℝ≥0) → ℝ≥0 :=
  ⟨TruncationGauge.toFun⟩

variable (Φ : TruncationGauge)

/-- Subadditivity, as a theorem rather than a structure field. -/
@[simp] theorem add_le (a b : ℕ →₀ ℝ≥0) : Φ (a + b) ≤ Φ a + Φ b := Φ.add_le' a b

/-- Positive homogeneity. -/
@[simp] theorem smul (c : ℝ≥0) (a : ℕ →₀ ℝ≥0) : Φ (c • a) = c * Φ a := Φ.smul' c a

/-- Permutation invariance. -/
@[simp] theorem symm (σ : Equiv.Perm ℕ) (a : ℕ →₀ ℝ≥0) :
    Φ (Finsupp.equivMapDomain σ a) = Φ a := Φ.symm' σ a

/-- Monotonicity in the termwise order. -/
theorem mono {a b : ℕ →₀ ℝ≥0} (h : a ≤ b) : Φ a ≤ Φ b := Φ.mono' h

/-- The first basis vector has gauge one. -/
@[simp] theorem normalized : Φ (Finsupp.single 0 1) = 1 := Φ.normalized'

/-- A gauge kills zero, by homogeneity at `c = 0`. -/
@[simp] theorem map_zero : Φ 0 = 0 := by
  have h := Φ.smul 0 0
  simpa using h

/-- **Every basis vector has gauge one, not just the first.**

This is the whole content of `normalized'` together with `symm'`: normalizing at
index `0` looks like an arbitrary choice, and permutation invariance is what makes
it not one.  Everything downstream that needs a scale — both ends of
`iSup_le_extend_le_tsum` — goes through this. -/
@[simp] theorem single_one (n : ℕ) : Φ (Finsupp.single n 1) = 1 := by
  have h : Finsupp.equivMapDomain (Equiv.swap 0 n) (Finsupp.single 0 1)
      = Finsupp.single n (1 : ℝ≥0) := by
    -- `equivMapDomain σ` reindexes by `σ⁻¹`; for a transposition `σ⁻¹ = σ`.
    ext j
    by_cases hj : j = n
    · subst hj; simp
    · rcases eq_or_ne j 0 with rfl | hj0
      · simp [Ne.symm hj]
      · rw [Finsupp.equivMapDomain_apply, Equiv.symm_swap,
          Equiv.swap_apply_of_ne_of_ne hj0 hj]
        simp [Ne.symm hj0, Ne.symm hj]
  calc Φ (Finsupp.single n 1) = Φ (Finsupp.equivMapDomain (Equiv.swap 0 n)
          (Finsupp.single 0 1)) := by rw [h]
    _ = Φ (Finsupp.single 0 1) := Φ.symm _ _
    _ = 1 := Φ.normalized

/-- The gauge of a single basis vector is its value. -/
@[simp] theorem single (n : ℕ) (c : ℝ≥0) : Φ (Finsupp.single n c) = c := by
  have hsm : c • Finsupp.single n (1 : ℝ≥0) = Finsupp.single n c := by
    ext j; by_cases hj : j = n <;> simp [hj]
  calc Φ (Finsupp.single n c) = Φ (c • Finsupp.single n (1 : ℝ≥0)) := by rw [hsm]
    _ = c * Φ (Finsupp.single n 1) := Φ.smul _ _
    _ = c := by rw [Φ.single_one n, mul_one]

/-- The `k`-term truncation of `a`, capped at `m`, as a finitely supported
`ℝ≥0`-valued sequence.

Built with `Finsupp.onFinset` rather than as a sum of `Finsupp.single`s so that
`truncate_apply` below is definitional: every fact about `extend` is a pointwise
fact about this function, and a sum of singles would put `Finset.sum_apply'`
between the two. -/
@[expose]
noncomputable def truncate (a : ℕ → ℝ≥0∞) (k : ℕ) (m : ℝ≥0) : ℕ →₀ ℝ≥0 :=
  Finsupp.onFinset (Finset.range k)
    (fun n => if n < k then (min (a n) (m : ℝ≥0∞)).toNNReal else 0)
    (fun n hn => by
      by_cases h : n < k
      · simpa using h
      · simp [h] at hn)

/-- The truncation, pointwise.  Definitional -- see `truncate`. -/
@[simp] theorem truncate_apply (a : ℕ → ℝ≥0∞) (k : ℕ) (m : ℝ≥0) (n : ℕ) :
    truncate a k m n = if n < k then (min (a n) (m : ℝ≥0∞)).toNNReal else 0 := rfl

/-- The extension of a symmetric gauge to arbitrary `ℝ≥0∞`-valued sequences: the
supremum of `Φ` over the truncations.

The supremum is over both the length `k` and a cap `m` on the values, and **the
cap is applied in `ℝ≥0∞`, before the conversion, not after**.  That is not a
stylistic choice: `ENNReal.toNNReal ∞ = 0`, so `min (a n).toNNReal m` reads an
infinite entry as *zero* and is not monotone in `a`.  Capping first sends `∞` to
`m`, and the supremum over `m` then recovers `∞` as the supremum of the finite
cuts, which is the value the gauge should take. -/
noncomputable def extend (Φ : TruncationGauge) (a : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ k : ℕ, ⨆ m : ℝ≥0, (Φ (truncate a k m) : ℝ≥0∞)

/-- Truncation is monotone in the sequence, at fixed length and cap. -/
theorem truncate_mono {a b : ℕ → ℝ≥0∞} (h : ∀ n, a n ≤ b n) (k : ℕ) (m : ℝ≥0) :
    truncate a k m ≤ truncate b k m := by
  refine Finsupp.le_def.2 fun n => ?_
  simp only [truncate_apply]
  split
  · refine ENNReal.toNNReal_mono ?_ (min_le_min (h n) le_rfl)
    exact ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := m)) (min_le_right _ _)
  · exact le_rfl

/-- The extension is monotone in the sequence. -/
theorem extend_mono {a b : ℕ → ℝ≥0∞} (h : ∀ n, a n ≤ b n) :
    Φ.extend a ≤ Φ.extend b :=
  iSup_mono fun k => iSup_mono fun m => by
    exact_mod_cast Φ.mono (truncate_mono h k m)

/-- **The low end of the scale**: every entry is bounded by the gauge.

This is the direction that needs `single_one`, hence `normalized'` and `symm'`
together: the truncation dominates the single basis vector at `n`, and that
vector's gauge is its value. -/
theorem le_extend (a : ℕ → ℝ≥0∞) (n : ℕ) : a n ≤ Φ.extend a := by
  refine ENNReal.le_of_forall_nnreal_lt fun c hc => ?_
  -- Capping at `c` leaves the `n`-th entry equal to `c`, because `c < a n`.
  have hmin : min (a n) ((c : ℝ≥0∞)) = (c : ℝ≥0∞) := min_eq_right hc.le
  have hsingle : Finsupp.single n c ≤ truncate a (n + 1) c := by
    refine Finsupp.le_def.2 fun j => ?_
    rcases eq_or_ne j n with rfl | hj
    · simp [hmin]
    · simp [Ne.symm hj]
  calc (c : ℝ≥0∞) = ((Φ (Finsupp.single n c) : ℝ≥0) : ℝ≥0∞) := by rw [Φ.single]
    _ ≤ ((Φ (truncate a (n + 1) c) : ℝ≥0) : ℝ≥0∞) := by
        exact_mod_cast Φ.mono hsingle
    _ ≤ Φ.extend a :=
        le_iSup_of_le (n + 1) (le_iSup (fun m : ℝ≥0 =>
          ((Φ (truncate a (n + 1) m) : ℝ≥0) : ℝ≥0∞)) c)

/-- **The low end, packaged**: `‖a‖_∞ ≤ Φ∞ a`. -/
theorem iSup_le_extend (a : ℕ → ℝ≥0∞) : (⨆ n, a n) ≤ Φ.extend a :=
  iSup_le (Φ.le_extend a)

/-- Subadditivity over a finitely supported sequence: `Φ f ≤ ∑ fₙ`.

Induction on the support, with `add_le'` at each step and `single` at the leaves.
This is the finite half of the high end of the scale. -/
theorem le_sum (f : ℕ →₀ ℝ≥0) : Φ f ≤ f.sum fun _ v => v := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add n b g hng hb ih =>
      rw [Finsupp.sum_add_index' (by simp) (by simp)]
      refine (Φ.add_le _ _).trans ?_
      gcongr
      simp [Finsupp.sum_single_index]

/-- **The high end of the scale**: `Φ∞ a ≤ ∑ aₙ`.

Every truncation is termwise below `a`, so its gauge is below the corresponding
partial sum, which is below the whole sum. -/
theorem extend_le_tsum (a : ℕ → ℝ≥0∞) : Φ.extend a ≤ ∑' n, a n := by
  refine iSup_le fun k => iSup_le fun m => ?_
  have hle : ((Φ (truncate a k m) : ℝ≥0) : ℝ≥0∞)
      ≤ ((truncate a k m).sum fun _ v => v : ℝ≥0) := by
    exact_mod_cast Φ.le_sum (truncate a k m)
  refine hle.trans ?_
  rw [Finsupp.sum, ENNReal.ofNNReal_finsetSum]
  refine (Finset.sum_le_sum fun n _ => ?_).trans (ENNReal.sum_le_tsum _)
  simp only [truncate_apply]
  split
  · exact (ENNReal.coe_toNNReal (ne_top_of_le_ne_top
      (ENNReal.coe_ne_top (r := m)) (min_le_right _ _))).le.trans (min_le_left _ _)
  · simp

/-- **Both ends of the scale**, and the reason the normalization is not a
restriction: `‖a‖_∞ ≤ Φ∞ a ≤ ∑ aₙ`. -/
theorem iSup_le_extend_le_tsum (a : ℕ → ℝ≥0∞) :
    (⨆ n, a n) ≤ Φ.extend a ∧ Φ.extend a ≤ ∑' n, a n :=
  ⟨Φ.iSup_le_extend a, Φ.extend_le_tsum a⟩

/-- The extension of the zero sequence is zero. -/
@[simp] theorem extend_zero : Φ.extend (fun _ => 0) = 0 := by
  simp [extend, show ∀ k m, truncate (fun _ : ℕ => (0 : ℝ≥0∞)) k m = 0 from
    fun k m => by ext n; simp]

/-- The extension of the everywhere-infinite sequence is `∞`.

Worth stating because it is the property `extend` was built as a supremum to
have: a definition routed through `tsum` would need the sequence summable before
it said anything, and would then say nothing here. -/
@[simp] theorem extend_top : Φ.extend (fun _ => ⊤) = ⊤ := by
  refine top_le_iff.1 ?_
  refine le_trans ?_ (Φ.iSup_le_extend (fun _ => ⊤))
  simp

/-- **`extend` is the supremum over ALL dominated finitely supported sequences.**

`extend` is defined as a supremum over the two-parameter family `truncate a k m`.  This
says the restriction to that family costs nothing: the same value is obtained by ranging
over every `b : ℕ →₀ ℝ≥0` dominated by `a`.

**Recorded because `ForTauCeti` currently contains a second `TruncationGauge` whose `extend`
is defined by the right-hand side here** (`Analysis/Normed/TruncationGauge.lean`), and
reconciling the two is a proof obligation, not a renaming — the two definitions are
different constructions that happen to agree.  This is that obligation, discharged on the
side that can state it.  See `{lane:FTC-SYMGAUGE-COLLIDE}`.

Both directions are short and neither needs more than `Φ.mono`: every truncation is
dominated, and conversely a dominated `b` has finite support, so it sits below the
truncation at any length past its support and any cap above its values. -/
theorem extend_eq_iSup_dominated (Φ : TruncationGauge) (a : ℕ → ℝ≥0∞) :
    Φ.extend a
      = ⨆ b : {b : ℕ →₀ ℝ≥0 // ∀ i, (b i : ℝ≥0∞) ≤ a i}, (Φ b.1 : ℝ≥0∞) := by
  refine le_antisymm (iSup_le fun k => iSup_le fun m => ?_) (iSup_le fun b => ?_)
  · refine le_iSup_of_le ⟨truncate a k m, fun i => ?_⟩ le_rfl
    simp only [truncate_apply]
    split
    · exact le_trans ENNReal.coe_toNNReal_le_self (min_le_left _ _)
    · simp
  · obtain ⟨k, hk⟩ : ∃ k, ∀ n ∈ b.1.support, n < k :=
      ⟨b.1.support.sup id + 1, fun n hn => Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
    refine le_iSup_of_le k (le_iSup_of_le (b.1.support.sup b.1) ?_)
    refine (ENNReal.coe_le_coe).2 (Φ.mono (Finsupp.le_def.2 fun n => ?_))
    simp only [truncate_apply]
    by_cases hn : n < k
    · simp only [hn, ite_true]
      have hb : (b.1 n : ℝ≥0∞) ≤ min (a n) ((b.1.support.sup b.1 : ℝ≥0) : ℝ≥0∞) := by
        refine le_min (b.2 n) ?_
        by_cases hmem : n ∈ b.1.support
        · exact_mod_cast Finset.le_sup (f := b.1) hmem
        · simp [Finsupp.notMem_support_iff.mp hmem]
      have hfin : min (a n) ((b.1.support.sup b.1 : ℝ≥0) : ℝ≥0∞) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.coe_ne_top) (min_le_right _ _)
      exact ENNReal.le_toNNReal_of_coe_le hb hfin
    · have : n ∉ b.1.support := fun hmem => hn (hk n hmem)
      simp [Finsupp.notMem_support_iff.mp this, hn]

/-- The truncation of a scaled sequence, at a scaled cap.

The cap has to scale with the sequence: `truncate` caps in `ℝ≥0∞` before
converting, so `c • truncate a k m` is the truncation of `c • a` at cap `c * m`,
not at `m`.  `mul_min` is what makes the two sides agree. -/
theorem smul_truncate (c : ℝ≥0) (a : ℕ → ℝ≥0∞) (k : ℕ) (m : ℝ≥0) :
    c • truncate a k m = truncate (fun n => (c : ℝ≥0∞) * a n) k (c * m) := by
  ext n
  simp only [truncate_apply, Finsupp.smul_apply, smul_eq_mul]
  split
  · rw [← ENNReal.toNNReal_coe (r := c), ← ENNReal.toNNReal_mul,
      ENNReal.toNNReal_coe, mul_min]
    congr 2
  · simp

/-- `extend` is homogeneous under a nonnegative real scalar.

One of the inputs `symmetricGaugeFamily.gauge_smul` needs.  Both directions are
the same computation read in opposite orders: the supremum over caps is what
absorbs the scaling, which is why `extend` had to range over `m` at all. -/
theorem extend_smul (c : ℝ≥0) (a : ℕ → ℝ≥0∞) :
    Φ.extend (fun n => (c : ℝ≥0∞) * a n) = (c : ℝ≥0∞) * Φ.extend a := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  refine le_antisymm ?_ ?_
  · refine iSup_le fun k => iSup_le fun m => ?_
    have hm : (c : ℝ≥0∞) * ((m / c : ℝ≥0) : ℝ≥0∞) = (m : ℝ≥0∞) := by
      rw [← ENNReal.coe_mul, mul_div_cancel₀ _ hc]
    calc ((Φ (truncate (fun n => (c : ℝ≥0∞) * a n) k m) : ℝ≥0) : ℝ≥0∞)
        = ((Φ (c • truncate a k (m / c)) : ℝ≥0) : ℝ≥0∞) := by
          rw [smul_truncate, mul_div_cancel₀ _ hc]
      _ = (c : ℝ≥0∞) * ((Φ (truncate a k (m / c)) : ℝ≥0) : ℝ≥0∞) := by
          rw [Φ.smul]; push_cast; ring
      _ ≤ (c : ℝ≥0∞) * Φ.extend a :=
          mul_le_mul' le_rfl (le_iSup_of_le k (le_iSup
            (fun m : ℝ≥0 => ((Φ (truncate a k m) : ℝ≥0) : ℝ≥0∞)) (m / c)))
  · rw [extend, ENNReal.mul_iSup]
    refine iSup_le fun k => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun m => ?_
    calc (c : ℝ≥0∞) * ((Φ (truncate a k m) : ℝ≥0) : ℝ≥0∞)
        = ((Φ (c • truncate a k m) : ℝ≥0) : ℝ≥0∞) := by
          rw [Φ.smul]; push_cast; ring
      _ = ((Φ (truncate (fun n => (c : ℝ≥0∞) * a n) k (c * m)) : ℝ≥0) : ℝ≥0∞) := by
          rw [smul_truncate]
      _ ≤ Φ.extend (fun n => (c : ℝ≥0∞) * a n) :=
          le_iSup_of_le k (le_iSup
            (fun m : ℝ≥0 => ((Φ (truncate (fun n => (c : ℝ≥0∞) * a n) k m) : ℝ≥0) : ℝ≥0∞))
            (c * m))

/-! ### The `ℓᵖ` symmetric norming function

`schattenGauge p` is the sequence-indexed counterpart of
`TauCeti.lpSymmetricGauge` in `ForTauCeti/Analysis/Normed/FiniteLpGauge.lean`,
which is the `Fin n` version.  Neither replaces the other; they are related by
`toFinite`.

**Why it is here rather than beside the finite one:** with it,
`symmetricGaugeFamily (schattenGauge p hp)` is the Schatten-`p` ideal and all
five ideal laws come free — which is the roadmap's own framing, that the Schatten
classes are *obtained* from Milestone B1 rather than constructed.
-/

/-- The `ℓᵖ` gauge of a finitely supported nonnegative sequence. -/
noncomputable def lpGaugeFinsupp (p : ℝ) (a : ℕ →₀ ℝ≥0) : ℝ≥0 :=
  (∑ n ∈ a.support, a n ^ p) ^ (1 / p)

/-- The sum defining `lpGaugeFinsupp` is unchanged by enlarging the index set:
outside the support the terms are `0 ^ p = 0`.

**This is the whole difference between a `Finsupp`-valued gauge and a `Fin n`
one**, and it is used at every field below — Minkowski and monotonicity both need
one common `Finset` for two or three different supports. -/
theorem sum_rpow_eq_of_support_subset {p : ℝ} (hp : 0 < p) (a : ℕ →₀ ℝ≥0)
    {s : Finset ℕ} (hs : a.support ⊆ s) :
    ∑ n ∈ s, a n ^ p = ∑ n ∈ a.support, a n ^ p := by
  refine (Finset.sum_subset hs fun n _ hn => ?_).symm
  have h0 : a n = 0 := by simpa using hn
  rw [h0, NNReal.zero_rpow hp.ne']

/-- Evaluate `lpGaugeFinsupp` over any finset containing the support. -/
theorem lpGaugeFinsupp_eq {p : ℝ} (hp : 0 < p) (a : ℕ →₀ ℝ≥0)
    {s : Finset ℕ} (hs : a.support ⊆ s) :
    lpGaugeFinsupp p a = (∑ n ∈ s, a n ^ p) ^ (1 / p) := by
  rw [lpGaugeFinsupp, sum_rpow_eq_of_support_subset hp a hs]

/-- **The `ℓᵖ` symmetric norming function**, `Φ_p a = (∑ aₙ ^ p) ^ (1/p)`.

Only `add_le'` has content — it is Minkowski, `NNReal.Lp_add_le`.  The other four
fields are sum manipulations, and each one needs
`sum_rpow_eq_of_support_subset` to put two different supports on one `Finset`. -/
@[expose]
noncomputable def schattenGauge (p : ℝ) (hp : 1 ≤ p) : TruncationGauge where
  toFun := lpGaugeFinsupp p
  add_le' a b := by
    have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le hp
    set s : Finset ℕ := (a + b).support ∪ a.support ∪ b.support with hsdef
    have hab : (a + b).support ⊆ s := by simp [hsdef, Finset.subset_union_left]
    have ha : a.support ⊆ s := by
      intro n hn
      simp only [hsdef, Finset.mem_union]
      exact Or.inl (Or.inr hn)
    have hb : b.support ⊆ s := by
      intro n hn
      simp only [hsdef, Finset.mem_union]
      exact Or.inr hn
    rw [lpGaugeFinsupp_eq hp0 _ hab, lpGaugeFinsupp_eq hp0 _ ha,
      lpGaugeFinsupp_eq hp0 _ hb]
    simpa using NNReal.Lp_add_le s (fun n => a n) (fun n => b n) hp
  smul' c a := by
    have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le hp
    have hsub : (c • a).support ⊆ a.support := Finsupp.support_smul
    rw [lpGaugeFinsupp_eq hp0 _ hsub, lpGaugeFinsupp]
    have : ∀ n ∈ a.support, ((c • a) n) ^ p = c ^ p * a n ^ p := by
      intro n _
      simp [NNReal.mul_rpow]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, NNReal.mul_rpow,
      ← NNReal.rpow_mul, mul_one_div_cancel hp0.ne', NNReal.rpow_one]
  symm' σ a := by
    have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le hp
    rw [lpGaugeFinsupp, lpGaugeFinsupp]
    congr 1
    refine Finset.sum_nbij' (fun n => σ.symm n) (fun n => σ n) ?_ ?_ ?_ ?_ ?_ <;>
      intro n hn <;> simp_all [Finsupp.equivMapDomain_apply]
  mono' a b hab := by
    have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le hp
    have hsub : a.support ⊆ a.support ∪ b.support := Finset.subset_union_left
    have hsub' : b.support ⊆ a.support ∪ b.support := Finset.subset_union_right
    rw [lpGaugeFinsupp_eq hp0 _ hsub, lpGaugeFinsupp_eq hp0 _ hsub']
    refine NNReal.rpow_le_rpow (Finset.sum_le_sum fun n _ => ?_) (by positivity)
    exact NNReal.rpow_le_rpow (Finsupp.le_def.1 hab n) hp0.le
  normalized' := by
    have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le hp
    rw [lpGaugeFinsupp]
    simp [NNReal.one_rpow, one_div]

/-- Every entry is below the gauge. -/
theorem le_lpGaugeFinsupp {p : ℝ} (hp : 0 < p) (a : ℕ →₀ ℝ≥0) (n : ℕ) :
    a n ≤ lpGaugeFinsupp p a := by
  classical
  by_cases hn : n ∈ a.support
  · have hterm : a n ^ p ≤ ∑ m ∈ a.support, a m ^ p :=
      Finset.single_le_sum (f := fun m => a m ^ p) (fun _ _ => zero_le) hn
    have := NNReal.rpow_le_rpow hterm (by positivity : (0:ℝ) ≤ 1 / p)
    rwa [← NNReal.rpow_mul, mul_one_div_cancel hp.ne', NNReal.rpow_one] at this
  · have h0 : a n = 0 := by simpa using hn
    rw [h0]
    exact zero_le

/-- **The `ℓᵖ` scale is antitone in `p`.**

Not available from Mathlib for the counting measure: `eLpNorm` comparison needs a
probability measure, which is the opposite normalisation.  The direct argument is
short — every entry is below `M = Φ_p a`, so `aₙ ^ q ≤ aₙ ^ p * M ^ (q - p)`, and
summing gives `Φ_q a ^ q ≤ M ^ q`. -/
theorem lpGaugeFinsupp_antitone {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (a : ℕ →₀ ℝ≥0) : lpGaugeFinsupp q a ≤ lpGaugeFinsupp p a := by
  classical
  have hq : (0 : ℝ) < q := hp.trans_le hpq
  set M : ℝ≥0 := lpGaugeFinsupp p a with hM
  -- Each term of the `q`-sum is bounded using `aₙ ≤ M`.
  have hterm : ∀ n ∈ a.support, a n ^ q ≤ a n ^ p * M ^ (q - p) := by
    intro n _
    have han : a n ≤ M := le_lpGaugeFinsupp hp a n
    calc a n ^ q = a n ^ p * a n ^ (q - p) := by
          rw [← NNReal.rpow_add' (by linarith)]
          ring_nf
      _ ≤ a n ^ p * M ^ (q - p) :=
          mul_le_mul' le_rfl (NNReal.rpow_le_rpow han (by linarith))
  have hsum : ∑ n ∈ a.support, a n ^ q ≤ M ^ q := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have hMp : (∑ n ∈ a.support, a n ^ p) = M ^ p := by
      rw [hM, lpGaugeFinsupp, ← NNReal.rpow_mul, one_div,
        inv_mul_cancel₀ hp.ne', NNReal.rpow_one]
    rw [hMp, ← NNReal.rpow_add' (by linarith)]
    ring_nf
    exact le_rfl
  calc lpGaugeFinsupp q a = (∑ n ∈ a.support, a n ^ q) ^ (1 / q) := rfl
    _ ≤ (M ^ q) ^ (1 / q) := NNReal.rpow_le_rpow hsum (by positivity)
    _ = M := by rw [← NNReal.rpow_mul, mul_one_div_cancel hq.ne', NNReal.rpow_one]

/-! ### Restriction to `Fin n`

The bridge to `TauCeti.FiniteSymmetricGauge`, which is what lets the finite
Hardy–Littlewood–Pólya transfer `FiniteSymmetricGauge.le_of_prefixSum_le` reach
sequences.  **The transfer itself is not reproved here** — it exists complete in
`ForTauCeti/Analysis/Convex/Majorization.lean`; only the restriction was missing,
and it is Milestone B2's blocker rather than the majorization argument.

**Absolute values are what reconcile the two structures**, and they are not a
convenience.  `FiniteSymmetricGauge` is `ℝ`-valued with a `neg_single'` field and
an `|c|` in its homogeneity; `TruncationGauge` is `ℝ≥0`-valued with neither.
Taking `|·|` on the way in is what discharges both, and it is why `add_le'` needs
`mono'` on top of `add_le'` rather than `add_le'` alone.
-/

/-- A real vector on `Fin n` as a finitely supported nonnegative sequence:
absolute values, extended by zero. -/
@[expose]
noncomputable def ofFin {n : ℕ} (x : Fin n → ℝ) : ℕ →₀ ℝ≥0 :=
  Finsupp.onFinset (Finset.range n)
    (fun i => if h : i < n then Real.nnabs (x ⟨i, h⟩) else 0)
    (fun i hi => by
      by_cases h : i < n
      · simpa using h
      · simp [h] at hi)

/-- `ofFin`, pointwise.  Definitional, as for `truncate_apply`. -/
@[simp] theorem ofFin_apply {n : ℕ} (x : Fin n → ℝ) (i : ℕ) :
    ofFin x i = if h : i < n then Real.nnabs (x ⟨i, h⟩) else 0 := rfl

/-- Restriction of a symmetric gauge to `Fin n`.

`perm'` is the field that needs work: a permutation of `Fin n` becomes one of `ℕ`
by `Equiv.Perm.extendDomain`, fixing everything from `n` on.  **The extension is
built from `π.symm`, not `π`** — `Finsupp.equivMapDomain` reindexes by the
*inverse*, so composing with `π` on the vector side corresponds to extending
`π.symm` on the index side.  Getting that backwards typechecks right up to the
final goal and then fails with `π` against `π.symm`. -/
noncomputable def toFinite (Φ : TruncationGauge) (n : ℕ) : FiniteSymmetricGauge n where
  toFun x := (Φ (ofFin x) : ℝ)
  add_le' x y := by
    have h : ofFin (x + y) ≤ ofFin x + ofFin y := by
      refine Finsupp.le_def.2 fun i => ?_
      by_cases hi : i < n
      · simp only [ofFin_apply, Finsupp.add_apply, dite_eq_left hi, Pi.add_apply]
        exact_mod_cast abs_add_le (x ⟨i, hi⟩) (y ⟨i, hi⟩)
      · simp [hi]
    exact_mod_cast (Φ.mono h).trans (Φ.add_le _ _)
  real_smul' c x := by
    have h : ofFin (c • x) = Real.nnabs c • ofFin x := by
      refine Finsupp.ext fun i => ?_
      by_cases hi : i < n
      · simp only [ofFin_apply, dite_eq_left hi, Finsupp.smul_apply, smul_eq_mul,
          Pi.smul_apply, smul_eq_mul]
        exact map_mul Real.nnabs c (x ⟨i, hi⟩)
      · simp [hi]
    rw [h, Φ.smul]
    push_cast
    ring
  perm' x π := by
    classical
    -- Extend `π` to `ℕ`, fixing everything from `n` on.
    -- built from `π.symm`, because `equivMapDomain` reindexes by the *inverse*
    set e : Equiv.Perm ℕ :=
      Equiv.Perm.extendDomain π.symm (Fin.equivSubtype (n := n)) with he
    have h : ofFin (x ∘ π) = Finsupp.equivMapDomain e (ofFin x) := by
      refine Finsupp.ext fun i => ?_
      by_cases hi : i < n
      · have : e.symm i = ((π ⟨i, hi⟩ : Fin n) : ℕ) := by
          rw [he, Equiv.Perm.extendDomain_symm, Equiv.symm_symm]
          simpa using Equiv.Perm.extendDomain_apply_image π
            (Fin.equivSubtype (n := n)) ⟨i, hi⟩
        simp [Finsupp.equivMapDomain_apply, this, hi, (π ⟨i, hi⟩).isLt]
      · have : e.symm i = i := by
          rw [he, Equiv.Perm.extendDomain_symm]
          exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hi
        simp [Finsupp.equivMapDomain_apply, this, hi]
    rw [h, Φ.symm]
  neg_single' x j := by
    have h : ofFin (Function.update x j (-x j)) = ofFin x := by
      refine Finsupp.ext fun i => ?_
      by_cases hi : i < n
      · by_cases hij : (⟨i, hi⟩ : Fin n) = j
        · subst hij; simp [hi, ← Real.toNNReal_abs, abs_neg]
        · simp [Function.update_of_ne hij, hi]
      · simp [hi]
    rw [h]

/-- The capped `k`-truncation of a nonnegative real sequence is pointwise below
the `ofFin` of its first `k` entries.

**The cap is never active on a real sequence** — `min (ofReal (a n)) m ≤ ofReal (a n)`
always — which is what lets the `ℝ≥0∞` gauge be compared with the finite one. -/
theorem truncate_le_ofFin {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (k : ℕ) (m : ℝ≥0) :
    truncate (fun n => ENNReal.ofReal (a n)) k m ≤ ofFin (fun i : Fin k => a i) := by
  refine Finsupp.le_def.2 fun i => ?_
  simp only [truncate_apply, ofFin_apply]
  split
  · rename_i hi
    have h1 : min (ENNReal.ofReal (a i)) ((m : ℝ≥0∞)) ≤ ENNReal.ofReal (a i) :=
      min_le_left _ _
    have h2 : (min (ENNReal.ofReal (a i)) ((m : ℝ≥0∞))).toNNReal ≤ (a i).toNNReal := by
      refine (ENNReal.toNNReal_mono (by simp) h1).trans ?_
      rw [← ENNReal.ofNNReal_toNNReal, ENNReal.toNNReal_coe]
    rwa [Real.nnabs_of_nonneg (ha i)]
  · simp

/-- The finite gauge of the first `k` entries is below the extended gauge.

**This is the lemma that makes `toFinite` usable**: without it the bridge computes
in the wrong direction.  It holds because `extend` is a supremum over the cap `m`,
and for `m` above the finitely many entries the capped truncation *is* `ofFin`. -/
theorem ofFin_le_extend (Φ : TruncationGauge) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (k : ℕ) :
    ((Φ (ofFin (fun i : Fin k => a i)) : ℝ≥0) : ℝ≥0∞)
      ≤ Φ.extend fun n => ENNReal.ofReal (a n) := by
  classical
  -- A cap above every one of the finitely many entries.
  obtain ⟨m, hm⟩ : ∃ m : ℝ≥0, ∀ i : Fin k, (a i).toNNReal ≤ m :=
    ⟨(Finset.univ.image fun i : Fin k => (a i).toNNReal).sup id,
      fun i => Finset.le_sup (f := id) (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
  have heq : ofFin (fun i : Fin k => a i) = truncate (fun n => ENNReal.ofReal (a n)) k m := by
    refine Finsupp.ext fun i => ?_
    simp only [truncate_apply, ofFin_apply]
    split
    · rename_i hi
      have hle : ENNReal.ofReal (a i) ≤ (m : ℝ≥0∞) := by
        rw [← ENNReal.ofNNReal_toNNReal, ENNReal.coe_le_coe]
        exact hm ⟨i, hi⟩
      rw [min_eq_left hle, ← ENNReal.ofNNReal_toNNReal, ENNReal.toNNReal_coe,
        Real.nnabs_of_nonneg (ha i)]
    · simp
  rw [heq]
  exact le_iSup_of_le k (le_iSup
    (fun m : ℝ≥0 => ((Φ (truncate (fun n => ENNReal.ofReal (a n)) k m) : ℝ≥0) : ℝ≥0∞)) m)

/-- **Hardy–Littlewood–Pólya for sequences**: a symmetric gauge is monotone under
weak majorization of antitone sequences.

This is the sequence form of Milestone B2.  The finite transfer
`FiniteSymmetricGauge.le_of_prefixSum_le` does the work at each truncation; the
bridge `toFinite` carries `Φ` down to `Fin k` and `ofFin_le_extend` carries the
answer back up.

**`b` may be infinite, and that split is the only content the finite case does not
already have.**  If some `b n = ∞` then `le_extend` makes `Φ∞ b = ∞`.  Otherwise
every `b n` is finite and so is every `a n` — **not pointwise from the hypothesis**,
which only compares prefix sums, but from the case `k = 1` together with `ha`. -/
theorem extend_le_extend_of_forall_sum_le (Φ : TruncationGauge) {a b : ℕ → ℝ≥0∞}
    (ha : Antitone a)
    (h : ∀ k, ∑ n ∈ Finset.range k, a n ≤ ∑ n ∈ Finset.range k, b n) :
    Φ.extend a ≤ Φ.extend b := by
  classical
  by_cases htop : ∃ n, b n = ⊤
  · obtain ⟨n, hn⟩ := htop
    have := Φ.le_extend b n
    rw [hn, top_le_iff] at this
    simp [this]
  push Not at htop
  -- Every `a n` is finite: the prefix inequality at `k = 1` bounds `a 0`, and `a`
  -- is antitone.
  have ha0 : a 0 ≠ ⊤ := by
    have h1 := h 1
    simp only [Finset.range_one, Finset.sum_singleton] at h1
    exact ne_top_of_le_ne_top (htop 0) h1
  have hafin : ∀ n, a n ≠ ⊤ := fun n => ne_top_of_le_ne_top ha0 (ha (Nat.zero_le n))
  refine iSup_le fun k => iSup_le fun m => ?_
  -- Reduce both sides to the `Fin k` gauge and apply the finite transfer.
  have hstep : (Φ.toFinite k) (fun i : Fin k => (a i).toReal)
      ≤ (Φ.toFinite k) (fun i : Fin k => (b i).toReal) := by
    refine FiniteSymmetricGauge.le_of_prefixSum_le (Φ := Φ.toFinite k)
      (fun i j hij => by
        simpa [ENNReal.toReal_le_toReal (hafin _) (hafin _)] using ha hij)
      (fun i => ENNReal.toReal_nonneg) (fun i => ENNReal.toReal_nonneg) ?_
    intro j
    have hj := h (min j k)
    have hre : ∀ f : ℕ → ℝ,
        (∑ i : Fin k, if (i : ℕ) < j then f (i : ℕ) else 0)
          = ∑ n ∈ Finset.range (min j k), f n := by
      intro f
      rw [Fin.sum_univ_eq_sum_range (fun n => if n < j then f n else 0) k,
        ← Finset.sum_filter]
      congr 1
      ext n
      simp [Finset.mem_filter, Finset.mem_range, and_comm]
    have hcast : ∑ n ∈ Finset.range (min j k), (a n).toReal
        ≤ ∑ n ∈ Finset.range (min j k), (b n).toReal := by
      rw [← ENNReal.toReal_sum (fun n _ => hafin n), ← ENNReal.toReal_sum (fun n _ => htop n)]
      exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun n _ => htop n) hj
    simp only [Finset.sum_filter,
      hre (fun n => (a n).toReal), hre (fun n => (b n).toReal)]
    exact hcast
  -- Both sequences are `ofReal` of their real parts, which is what lets the
  -- `Fin k` machinery apply.
  have harw : a = fun n => ENNReal.ofReal ((a n).toReal) :=
    funext fun n => (ENNReal.ofReal_toReal (hafin n)).symm
  have hbrw : b = fun n => ENNReal.ofReal ((b n).toReal) :=
    funext fun n => (ENNReal.ofReal_toReal (htop n)).symm
  calc ((Φ (truncate a k m) : ℝ≥0) : ℝ≥0∞)
      ≤ ((Φ (ofFin (fun i : Fin k => (a i).toReal)) : ℝ≥0) : ℝ≥0∞) := by
        have := Φ.mono (truncate_le_ofFin (a := fun n => (a n).toReal)
          (fun n => ENNReal.toReal_nonneg) k m)
        rw [← harw] at this
        exact_mod_cast this
    _ ≤ ((Φ (ofFin (fun i : Fin k => (b i).toReal)) : ℝ≥0) : ℝ≥0∞) := by
        exact_mod_cast hstep
    _ ≤ Φ.extend b := by
        have := Φ.ofFin_le_extend (a := fun n => (b n).toReal)
          (fun n => ENNReal.toReal_nonneg) k
        rwa [← hbrw] at this

/-- **On a nonnegative real sequence the cap in `extend` is inert.**

`extend` is a supremum over a length `k` *and* a value cap `m`, and the cap is
what stops it being compared with anything written as a `tsum`.  For a real
sequence every entry is finite, so the cap is never active and the double
supremum collapses to one index.

**This is the form any comparison against a `tsum` needs** — Milestone B3's
reconciliation of `symmetricGaugeENorm (schattenGauge p hp)` against
`schattenENorm p` among them. -/
theorem extend_eq_iSup_ofFin (Φ : TruncationGauge) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) :
    Φ.extend (fun n => ENNReal.ofReal (a n))
      = ⨆ k : ℕ, ((Φ (ofFin (fun i : Fin k => a i)) : ℝ≥0) : ℝ≥0∞) := by
  refine le_antisymm ?_ (iSup_le fun k => Φ.ofFin_le_extend ha k)
  refine iSup_le fun k => iSup_le fun m => ?_
  refine le_iSup_of_le k ?_
  exact_mod_cast Φ.mono (truncate_le_ofFin ha k m)

/-- The `ℓᵖ` gauge of a `Fin k` restriction, as a `Finset.range k` sum.

The bridge between `lpGaugeFinsupp`, which sums over a `Finsupp`'s support, and
the `range k` partial sums that a `tsum` decomposes into.  Needed by Milestone
B3's reconciliation in both directions. -/
theorem lpGaugeFinsupp_ofFin {p : ℝ} (hp : 0 < p) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (k : ℕ) :
    lpGaugeFinsupp p (ofFin (fun i : Fin k => a i))
      = (∑ n ∈ Finset.range k, (a n).toNNReal ^ p) ^ (1 / p) := by
  classical
  have hsupp : (ofFin (fun i : Fin k => a i)).support ⊆ Finset.range k := by
    intro n hn
    by_contra hk
    rw [Finsupp.mem_support_iff] at hn
    exact hn (by simp [ofFin_apply, Finset.mem_range.not.1 hk])
  rw [lpGaugeFinsupp_eq hp _ hsupp]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hk : n < k := Finset.mem_range.1 hn
  simp [ofFin_apply, hk, Real.nnabs_of_nonneg (ha n)]

/-- `rpow` with a positive exponent commutes with suprema on `ℝ≥0∞`.

Mathlib has `ENNReal.iSup_pow` for *natural* powers only, but
`ENNReal.orderIsoRpow` makes the real-exponent case immediate — an order
isomorphism preserves suprema. -/
theorem iSup_rpow {ι : Sort*} [Nonempty ι] (f : ι → ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    (⨆ i, f i) ^ r = ⨆ i, f i ^ r := by
  have h := (ENNReal.orderIsoRpow r hr).map_iSup f
  simpa only [ENNReal.orderIsoRpow_apply] using h

/-! ### The gauge a symmetric norming function induces on operators

`symmetricGaugeENorm Φ A = Φ∞ (a(A))`, the symmetric gauge read along the
approximation numbers.  This is `symmetricGaugeFamily`'s gauge, and the three
laws below are three of the five `OperatorIdealFamily` fields.

**`gauge_add_le` is not here**, and the structure is therefore not assembled: a
`SymmetricOperatorIdealFamily` with four of five fields is not a thing that can
exist, and an undischarged placeholder would fail `check_tauceti_readiness`.

**Its route is settled, and it is `Family/Schatten.lean`'s, generalised.**  That
module solves the identical problem for the `ℓᵖ` gauge in
`lpGauge_approximationNumber_add_le`, whose docstring states the argument: the
truncated sequences are *weakly majorized* — antitone and nonnegative because
approximation numbers are, prefix-comparable because that comparison **is**
`kyFanGauge_add_le_complex` — so a monotone-under-weak-majorization lemma applies.

Every ingredient for the general case now exists:

* `kyFanApproximationGauge_add_le_of_minMax` gives
  `∑_{i<k} aᵢ(S+T) ≤ ∑_{i<k} aᵢ(S) + ∑_{i<k} aᵢ(T)`, so `a(S+T)` is weakly
  majorized by the **pointwise sum** `a(S) + a(T)`;
* `FiniteSymmetricGauge.mono_weaklyMajorized` (`Analysis/Convex/Majorization.lean`)
  turns that into a gauge inequality, at `Φ.toFinite k` — which is what the
  bridge above was built for;
* `Φ.add_le'` then splits the right-hand side.

**Where Schatten needs finite Minkowski to split, a general symmetric gauge needs
only its own subadditivity** — which is the one place the general argument is
*simpler* than the `ℓᵖ` one, and worth knowing before anyone reaches for a
Minkowski analogue that does not exist here.

The remaining work is the `ℝ≥0∞` bookkeeping: `extend` caps at `m` before
converting, so the weak-majorization hypothesis has to be established for the
capped truncations rather than for `a` itself.

The `ENNReal.ofReal` convention is `schattenENorm`'s, deliberately, so that the
two gauges read the same way.
-/

section Operators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The gauge a symmetric norming function induces on operators: `Φ` read along
the approximation numbers, valued in `ℝ≥0∞` and so defined for every bounded
operator — it is `∞` exactly off the ideal. -/
noncomputable def symmetricGaugeENorm (Φ : TruncationGauge) (A : E →L[𝕜] F) : ℝ≥0∞ :=
  Φ.extend fun n => ENNReal.ofReal (A.approximationNumber n)

-- Completeness is not used: the bound is `a₀ A = ‖A‖` and one entry of a supremum.
omit [CompleteSpace E] [CompleteSpace F] in
/-- **Ideal law 1 of 5**: the induced gauge dominates the operator norm.

`a₀ A = ‖A‖`, and `le_extend` says every entry is below the gauge — which is
where `normalized'` and `symm'` are finally paying for themselves, through
`single_one`. -/
theorem enorm_le_symmetricGaugeENorm (Φ : TruncationGauge) (A : E →L[𝕜] F) :
    ‖A‖ₑ ≤ symmetricGaugeENorm Φ A := by
  have h := Φ.le_extend (fun n => ENNReal.ofReal (A.approximationNumber n)) 0
  rw [ContinuousLinearMap.approximationNumber_index_zero, ofReal_norm] at h
  exact h

-- Completeness is unused: `approximationNumber_smul` is an identity of reals.
omit [CompleteSpace E] [CompleteSpace F] in
/-- **Ideal law 2 of 5**: the induced gauge is absolutely homogeneous.

`approximationNumber_smul` scales every entry by `‖c‖`, and slice 2a's
`extend_smul` moves the scalar out of the gauge. -/
theorem symmetricGaugeENorm_smul (Φ : TruncationGauge) (c : 𝕜) (A : E →L[𝕜] F) :
    symmetricGaugeENorm Φ (c • A) = ‖c‖ₑ * symmetricGaugeENorm Φ A := by
  have hpt : ∀ n, ENNReal.ofReal ((c • A).approximationNumber n)
      = (‖c‖₊ : ℝ≥0∞) * ENNReal.ofReal (A.approximationNumber n) := by
    intro n
    rw [ContinuousLinearMap.approximationNumber_smul, ENNReal.ofReal_mul (norm_nonneg c)]
    congr 1
    rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg c)]
    rfl
  simp only [symmetricGaugeENorm, hpt]
  rw [Φ.extend_smul]
  rfl

-- Completeness is unused: both composition bounds are inequalities of reals.
omit [CompleteSpace E] [CompleteSpace F] in
/-- **Ideal law 3 of 5, one side**: pre-composition.

`aₙ (A ∘L R) ≤ aₙ A * ‖R‖` entrywise, then `extend_mono` and `extend_smul`. -/
theorem symmetricGaugeENorm_comp_right_le (Φ : TruncationGauge)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (A : E →L[𝕜] F) (R : H →L[𝕜] E) :
    symmetricGaugeENorm Φ (A ∘L R) ≤ symmetricGaugeENorm Φ A * ‖R‖ₑ := by
  have hpt : ∀ n, ENNReal.ofReal ((A ∘L R).approximationNumber n)
      ≤ (‖R‖₊ : ℝ≥0∞) * ENNReal.ofReal (A.approximationNumber n) := by
    intro n
    calc ENNReal.ofReal ((A ∘L R).approximationNumber n)
        ≤ ENNReal.ofReal (A.approximationNumber n * ‖R‖) :=
          ENNReal.ofReal_le_ofReal
            (ContinuousLinearMap.approximationNumber_comp_le_mul_norm A R n)
      _ = (‖R‖₊ : ℝ≥0∞) * ENNReal.ofReal (A.approximationNumber n) := by
          rw [ENNReal.ofReal_mul (ContinuousLinearMap.approximationNumber_nonneg A n),
            mul_comm]
          congr 1
          rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg R)]
          rfl
  calc symmetricGaugeENorm Φ (A ∘L R)
      ≤ Φ.extend (fun n => (‖R‖₊ : ℝ≥0∞) * ENNReal.ofReal (A.approximationNumber n)) :=
        Φ.extend_mono hpt
    _ = (‖R‖₊ : ℝ≥0∞) * symmetricGaugeENorm Φ A := Φ.extend_smul _ _
    _ = symmetricGaugeENorm Φ A * ‖R‖ₑ := by rw [mul_comm]; rfl

section Triangle

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Ideal law 4 of 5: subadditivity.**

This is Milestone B2, and it is the only law that is not a pointwise statement
about approximation numbers.  `aₙ(S+T) ≤ aₙ(S) + aₙ(T)` is **false** in general;
what is true is the prefix statement — the Ky Fan inequality — and getting from
prefix sums to a symmetric gauge is weak majorization.

The route is `Family/Schatten.lean`'s, at a general gauge instead of `ℓᵖ`: apply
the `Fin k` theory to the truncation at each `k`.  **Where Schatten needs finite
Minkowski to split the right-hand side, here `toFinite k` is a
`FiniteSymmetricGauge` and its own `add_le` does it.** -/
theorem symmetricGaugeENorm_add_le (Φ : TruncationGauge) (S T : E →L[𝕜] F) :
    symmetricGaugeENorm Φ (S + T)
      ≤ symmetricGaugeENorm Φ S + symmetricGaugeENorm Φ T := by
  have hnn : ∀ (A : E →L[𝕜] F) n, 0 ≤ A.approximationNumber n :=
    fun A n => ContinuousLinearMap.approximationNumber_nonneg A n
  refine iSup_le fun k => iSup_le fun m => ?_
  -- The capped truncation is below the uncapped `Fin k` vector.
  have hcap := Φ.mono (truncate_le_ofFin (hnn (S + T)) k m)
  -- The finite gauge inequality, from Ky Fan through `le_of_prefixSum_le`.
  have hfin : (Φ.toFinite k) (fun i : Fin k => (S + T).approximationNumber i)
      ≤ (Φ.toFinite k) (fun i : Fin k => S.approximationNumber i)
        + (Φ.toFinite k) (fun i : Fin k => T.approximationNumber i) := by
    refine le_trans (FiniteSymmetricGauge.le_of_prefixSum_le (Φ := Φ.toFinite k)
      (y := fun i : Fin k => S.approximationNumber i + T.approximationNumber i)
      (fun i j hij => ContinuousLinearMap.approximationNumber_antitone _ hij)
      (fun i => hnn _ _) (fun i => add_nonneg (hnn _ _) (hnn _ _)) ?_) ?_
    · intro j
      have hky := TauCeti.ApproximationNumber.kyFanApproximationGauge_add_le_of_minMax
        (ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.out (𝕜 := 𝕜) (E := E) (F := F))
        (min j k) S T
      -- Reindex: a filtered sum over `Fin k` is a `range (min j k)` sum.
      have hre : ∀ f : ℕ → ℝ,
          (∑ a : Fin k, if (a : ℕ) < j then f (a : ℕ) else 0)
            = ∑ n ∈ Finset.range (min j k), f n := by
        intro f
        rw [Fin.sum_univ_eq_sum_range (fun n => if n < j then f n else 0) k,
          ← Finset.sum_filter]
        congr 1
        ext n
        simp [Finset.mem_filter, Finset.mem_range, and_comm]
      simp only [TauCeti.ApproximationNumber.kyFanApproximationGauge,
        ContinuousLinearMap.kyFanGauge] at hky
      simpa [FiniteVector.prefixSum, Finset.sum_filter, hre,
        Finset.sum_add_distrib] using hky
    · exact (Φ.toFinite k).add_le _ _
  calc ((Φ (truncate (fun n => ENNReal.ofReal ((S + T).approximationNumber n)) k m) : ℝ≥0)
        : ℝ≥0∞)
      ≤ ((Φ (ofFin (fun i : Fin k => (S + T).approximationNumber i)) : ℝ≥0) : ℝ≥0∞) := by
        exact_mod_cast hcap
    _ ≤ ((Φ (ofFin (fun i : Fin k => S.approximationNumber i)) : ℝ≥0) : ℝ≥0∞)
        + ((Φ (ofFin (fun i : Fin k => T.approximationNumber i)) : ℝ≥0) : ℝ≥0∞) := by
        exact_mod_cast hfin
    _ ≤ symmetricGaugeENorm Φ S + symmetricGaugeENorm Φ T :=
        add_le_add (Φ.ofFin_le_extend (hnn S) k) (Φ.ofFin_le_extend (hnn T) k)

-- Neither the min-max hypothesis nor completeness is used: this is pointwise.
omit [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] in
/-- **Ideal law 5 of 5**: the gauge is unchanged by passing to the adjoint.

Pointwise, from `approximationNumber_adjoint`. -/
theorem symmetricGaugeENorm_adjoint (Φ : TruncationGauge) (A : E →L[𝕜] F) :
    symmetricGaugeENorm Φ (ContinuousLinearMap.adjoint A) = symmetricGaugeENorm Φ A := by
  simp only [symmetricGaugeENorm,
    ContinuousLinearMap.approximationNumber_adjoint]

-- The two-sided law is pointwise too: no min-max hypothesis, no completeness of
-- the outer spaces.  Only subadditivity needs the Ky Fan inequality.
omit [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
  [CompleteSpace E] [CompleteSpace F] in
/-- The two-sided ideal law, from the two one-sided bounds. -/
theorem symmetricGaugeENorm_comp_le (Φ : TruncationGauge)
    {G H : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : H →L[𝕜] E) :
    symmetricGaugeENorm Φ (L ∘L A ∘L R)
      ≤ ‖L‖ₑ * symmetricGaugeENorm Φ A * ‖R‖ₑ := by
  have hpt : ∀ n, ENNReal.ofReal ((L ∘L A ∘L R).approximationNumber n)
      ≤ ‖L‖ₑ * (‖R‖ₑ * ENNReal.ofReal (A.approximationNumber n)) := by
    intro n
    have h1 := ContinuousLinearMap.approximationNumber_comp_le_norm_mul L (A ∘L R) n
    have h2 := ContinuousLinearMap.approximationNumber_comp_le_mul_norm A R n
    have hchain : (L ∘L A ∘L R).approximationNumber n ≤ ‖L‖ * (A.approximationNumber n * ‖R‖) :=
      h1.trans (by
        refine mul_le_mul_of_nonneg_left h2 (norm_nonneg L))
    refine (ENNReal.ofReal_le_ofReal hchain).trans_eq ?_
    rw [ENNReal.ofReal_mul (norm_nonneg L), ENNReal.ofReal_mul
      (ContinuousLinearMap.approximationNumber_nonneg A n),
      ofReal_norm, ofReal_norm]
    ring
  calc symmetricGaugeENorm Φ (L ∘L A ∘L R)
      ≤ Φ.extend (fun n => ‖L‖ₑ *
          (‖R‖ₑ * ENNReal.ofReal (A.approximationNumber n))) := Φ.extend_mono hpt
    _ = ‖L‖ₑ * (‖R‖ₑ * symmetricGaugeENorm Φ A) := by
        rw [show (‖L‖ₑ : ℝ≥0∞) = ((‖L‖₊ : ℝ≥0) : ℝ≥0∞) from rfl,
          show (‖R‖ₑ : ℝ≥0∞) = ((‖R‖₊ : ℝ≥0) : ℝ≥0∞) from rfl,
          Φ.extend_smul, Φ.extend_smul]
        rfl
    _ = ‖L‖ₑ * symmetricGaugeENorm Φ A * ‖R‖ₑ := by ring

/-- **The operator ideal a symmetric norming function induces.**

Milestone B1, and the five fields are the five laws above. -/
@[expose]
noncomputable def symmetricGaugeFamily (𝕜 : Type u) [RCLike 𝕜]
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] (Φ : TruncationGauge) :
    TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  gauge A := symmetricGaugeENorm Φ A
  gauge_add_le A B := symmetricGaugeENorm_add_le Φ A B
  gauge_smul c A := symmetricGaugeENorm_smul Φ c A
  enorm_le_gauge A := enorm_le_symmetricGaugeENorm Φ A
  gauge_comp_le L A R := symmetricGaugeENorm_comp_le Φ L A R
  gauge_adjoint A := symmetricGaugeENorm_adjoint Φ A

end Triangle

/-! ### The `∞` endpoint gauge

`Φ_∞ a = ⨆ n, a n`, the sup norm of a finitely supported nonnegative sequence.  It sits at
the top of the Schatten scale and, unlike the finite exponents, needs no `ℓᵖ` machinery: four
of the five axioms follow from the two characterising bounds below, and only homogeneity
touches `Finset.sup` directly. -/

/-- The sup norm of a finitely supported nonnegative sequence. -/
noncomputable def supGaugeFinsupp (a : ℕ →₀ ℝ≥0) : ℝ≥0 := a.support.sup a

/-- Every term is bounded by the sup. -/
theorem le_supGaugeFinsupp (a : ℕ →₀ ℝ≥0) (n : ℕ) : a n ≤ supGaugeFinsupp a := by
  by_cases hn : n ∈ a.support
  · exact Finset.le_sup hn
  · simp only [Finsupp.notMem_support_iff] at hn
    simp [hn]

/-- The sup is the least such bound. -/
theorem supGaugeFinsupp_le {a : ℕ →₀ ℝ≥0} {c : ℝ≥0} (h : ∀ n, a n ≤ c) :
    supGaugeFinsupp a ≤ c :=
  Finset.sup_le fun n _ => h n

/-- `Φ_∞`, the symmetric gauge at the top of the Schatten scale. -/
noncomputable def supGauge : TruncationGauge where
  toFun := supGaugeFinsupp
  add_le' a b := supGaugeFinsupp_le fun n => by
    simpa using add_le_add (le_supGaugeFinsupp a n) (le_supGaugeFinsupp b n)
  smul' c a := by
    classical
    rcases eq_or_ne c 0 with rfl | hc
    · simp [supGaugeFinsupp]
    · have hsupp : (c • a).support = a.support := by
        ext n
        simp [Finsupp.mem_support_iff, hc]
      simp only [supGaugeFinsupp, hsupp, NNReal.mul_finset_sup]
      exact Finset.sup_congr rfl fun n _ => by simp
  symm' σ a := by
    refine le_antisymm (supGaugeFinsupp_le fun n => ?_) (supGaugeFinsupp_le fun n => ?_)
    · simpa [Finsupp.equivMapDomain_apply] using le_supGaugeFinsupp a (σ.symm n)
    · simpa [Finsupp.equivMapDomain_apply] using
        le_supGaugeFinsupp (Finsupp.equivMapDomain σ a) (σ n)
  mono' a b h := supGaugeFinsupp_le fun n => le_trans (h n) (le_supGaugeFinsupp b n)
  normalized' := by
    refine le_antisymm (supGaugeFinsupp_le fun n => ?_) ?_
    · by_cases hn : n = 0 <;> simp [hn]
    · simpa using le_supGaugeFinsupp (Finsupp.single (0 : ℕ) (1 : ℝ≥0)) 0

/-- **The `∞` gauge collapses to the leading term on an antitone sequence.**

Every capped truncation is bounded by `a 0`, and `le_extend` supplies the reverse, so the
supremum over lengths and caps recovers the first entry.  For approximation numbers this says
`Φ_∞ (a T) = a₀ T = ‖T‖`, which is the sense in which the `∞` endpoint of the Schatten scale
is the operator-norm gauge. -/
theorem supGauge_extend_of_antitone {a : ℕ → ℝ≥0∞} (ha : Antitone a) :
    supGauge.extend a = a 0 := by
  refine le_antisymm ?_ (supGauge.le_extend a 0)
  rcases eq_or_ne (a 0) ⊤ with h0 | h0
  · simp [h0]
  refine iSup_le fun k => iSup_le fun m => ?_
  have hle : supGaugeFinsupp (truncate a k m) ≤ (a 0).toNNReal := by
    refine supGaugeFinsupp_le fun n => ?_
    rw [truncate_apply]
    split
    · exact ENNReal.toNNReal_mono h0 (le_trans (min_le_left _ _) (ha (Nat.zero_le n)))
    · exact zero_le
  calc ((supGauge (truncate a k m) : ℝ≥0) : ℝ≥0∞) ≤ (((a 0).toNNReal : ℝ≥0) : ℝ≥0∞) := by
        exact_mod_cast hle
    _ = a 0 := ENNReal.coe_toNNReal h0

section Calkin

universe u

variable {𝕜 : Type u} [RCLike 𝕜]
  [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, u} 𝕜]

/-- **Milestone B1, the direction of the Calkin correspondence claimed here.**

Two symmetric gauges inducing the same operator ideal agree on antitone
sequences, so the ideal really is a function of the singular-value sequence
alone.

**The proof is a realisation argument, and it splits on boundedness — which the
roadmap's statement does not show.**  An unbounded antitone sequence is realised
by *no* bounded operator, so the realisation route simply does not apply to it.
It does not have to: `le_extend` makes both sides `∞`, and the equation holds
because neither gauge can see past the supremum.  A bounded sequence is realised
by `diagOpLp`, and `approximationNumber_diagOpLp` is what turns the operator
equality into the sequence equality.

Surjectivity — that every symmetric ideal arises this way — is *not* claimed; it
is the substantial half of Calkin's theorem and needs a separability hypothesis
nothing else here needs. -/
theorem symmetricGaugeFamily_injective {Φ Ψ : TruncationGauge}
    (h : symmetricGaugeFamily.{u, u} 𝕜 Φ = symmetricGaugeFamily.{u, u} 𝕜 Ψ)
    {a : ℕ → ℝ≥0∞} (ha : Antitone a) :
    Φ.extend a = Ψ.extend a := by
  classical
  by_cases hbdd : ∃ K : ℝ≥0, ∀ n, a n ≤ (K : ℝ≥0∞)
  · obtain ⟨K, hK⟩ := hbdd
    set c : ℕ → 𝕜 := fun n => (((a n).toReal : ℝ) : 𝕜) with hcdef
    have hafin : ∀ n, a n ≠ ⊤ := fun n =>
      ne_top_of_le_ne_top (by simp) (hK n)
    have hcnorm : ∀ n, ‖c n‖ = (a n).toReal := fun n => by
      simp [hcdef, abs_of_nonneg ENNReal.toReal_nonneg]
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    have hcK : ∀ i, ‖c i‖ ≤ (K : ℝ) := fun i => by
      rw [hcnorm i]
      exact (ENNReal.toReal_le_toReal (hafin i) (by simp)).2 (hK i)
    have hcanti : Antitone fun i => ‖c i‖ := fun i j hij => by
      simp only [hcnorm]
      exact (ENNReal.toReal_le_toReal (hafin j) (hafin i)).2 (ha hij)
    have hop := congrArg
      (fun N : TauCeti.SymmetricOperatorIdealFamily.{u, u} 𝕜 =>
        N.gauge (TauCeti.diagOpLp c hK0 hcK)) h
    simp only [symmetricGaugeFamily, symmetricGaugeENorm] at hop
    have hrw : (fun n => ENNReal.ofReal
        ((TauCeti.diagOpLp c hK0 hcK).approximationNumber n)) = a := by
      funext n
      rw [TauCeti.approximationNumber_diagOpLp c hK0 hcK hcanti n, hcnorm n,
        ENNReal.ofReal_toReal (hafin n)]
    rwa [hrw] at hop
  · push Not at hbdd
    -- Unbounded: the supremum is `⊤`, and every gauge dominates it.
    have hsup : (⨆ n, a n) = ⊤ := by
      refine iSup_eq_top.2 fun b hb => ?_
      lift b to ℝ≥0 using hb.ne
      obtain ⟨n, hn⟩ := hbdd b
      exact ⟨n, hn⟩
    have hinf : ∀ Θ : TruncationGauge, Θ.extend a = ⊤ := fun Θ =>
      top_le_iff.1 (hsup ▸ Θ.iSup_le_extend a)
    rw [hinf Φ, hinf Ψ]

/-- **Milestone B2 at the ideal-family API**: every family induced by a symmetric
gauge respects Ky Fan domination.

**The Hardy–Littlewood–Pólya transfer is not proved here** — it is
`extend_le_extend_of_forall_sum_le`, and this instance is the packaging that
exposes it.  `kyFanGauge T k` is by definition `∑_{n<k} aₙ(T)`, so the hypothesis
*is* that lemma's prefix comparison; all that happens below is moving it across
`ENNReal.ofReal`, which is monotone and additive on nonnegatives. -/
instance isKyFanDominant_symmetricGaugeFamily (Φ : TruncationGauge) :
    TauCeti.IsKyFanDominant (symmetricGaugeFamily.{u, u} 𝕜 Φ) where
  gauge_le_of_forall_kyFanGauge_le {E F} _ _ _ _ _ _ {A B} hAB := by
    refine Φ.extend_le_extend_of_forall_sum_le
      (fun i j hij => ENNReal.ofReal_le_ofReal
        (ContinuousLinearMap.approximationNumber_antitone _ hij)) fun k => ?_
    have hnn : ∀ (T : E →L[𝕜] F) n, 0 ≤ T.approximationNumber n :=
      fun T n => ContinuousLinearMap.approximationNumber_nonneg T n
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => hnn A n),
      ← ENNReal.ofReal_sum_of_nonneg (fun n _ => hnn B n)]
    exact ENNReal.ofReal_le_ofReal (hAB k)

/-- **The Schatten-`p` ideal, obtained rather than constructed.**

All five ideal laws are `symmetricGaugeFamily`'s, which is the roadmap's own
framing: *"the Schatten classes are obtained from Milestone B1 rather than
constructed, so their four laws are B1's and not new work."*

This is **not** asserted to agree with `TauCeti.schattenIdealFamily` in
`Family/Schatten.lean`, which is built from its own argument through the
`tsum`-based `schattenENorm`.  The two should agree and proving it is Milestone
B3's reconciliation obligation; nothing here claims it. -/
@[expose]
noncomputable def schattenFamily (p : ℝ) (hp : 1 ≤ p) :
    TauCeti.SymmetricOperatorIdealFamily.{u, u} 𝕜 :=
  symmetricGaugeFamily.{u, u} 𝕜 (schattenGauge p hp)

/-- **The Schatten scale is antitone in `p`**, hence the ideals nest.

`extend` is a supremum over truncations of the *same* sequence, so the pointwise
comparison of the two gauges on each truncation is all that is needed — the
finite content is `lpGaugeFinsupp_antitone`. -/
theorem gauge_schattenFamily_antitone {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : p ≤ q) {E F : Type u}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F) :
    (schattenFamily.{u} (𝕜 := 𝕜) q hq).gauge T
      ≤ (schattenFamily.{u} (𝕜 := 𝕜) p hp).gauge T := by
  simp only [schattenFamily, symmetricGaugeFamily, symmetricGaugeENorm, extend]
  refine iSup_mono fun k => iSup_mono fun m => ?_
  exact_mod_cast lpGaugeFinsupp_antitone (zero_lt_one.trans_le hp) hpq _

-- The min-max hypothesis is not used: this is an identity of two gauges, not an
-- ideal law.
omit [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, u} 𝕜] in
/-- **Milestone B3's reconciliation obligation, discharged.**

`symmetricGaugeENorm (schattenGauge p hp)` and `TauCeti.schattenENorm p` are the
same function, so the ideal `{lane:FTC-SCHATTENGAUGE}` *obtained* from Milestone
B1 is the ideal `Family/Schatten.lean` *constructs* from its own argument.

**The two are built along different routes and that is the point of proving it.**
This side is a supremum over capped truncations of a `Finsupp`-valued gauge; that
side is a `tsum`.  They meet once the cap is removed by `extend_eq_iSup_ofFin`
and the `tsum` is opened by `ENNReal.tsum_eq_iSup_nat`, leaving two suprema over
the same partial sums — and `iSup_rpow` carries the exponent across. -/
theorem symmetricGaugeENorm_schattenGauge {p : ℝ} (hp : 1 ≤ p)
    {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F) :
    symmetricGaugeENorm (schattenGauge p hp) T = ContinuousLinearMap.schattenENorm p T := by
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le hp
  have hinv : (0 : ℝ) < 1 / p := by positivity
  have hnn : ∀ n, 0 ≤ T.approximationNumber n := fun n =>
    ContinuousLinearMap.approximationNumber_nonneg T n
  rw [symmetricGaugeENorm, (schattenGauge p hp).extend_eq_iSup_ofFin hnn,
    ContinuousLinearMap.schattenENorm, ENNReal.tsum_eq_iSup_nat, ← one_div,
    iSup_rpow _ hinv]
  refine iSup_congr fun k => ?_
  rw [show (schattenGauge p hp) (ofFin (fun i : Fin k => T.approximationNumber i))
      = lpGaugeFinsupp p (ofFin (fun i : Fin k => T.approximationNumber i)) from rfl,
    lpGaugeFinsupp_ofFin hp0 hnn k]
  rw [ENNReal.coe_rpow_of_nonneg _ hinv.le, ENNReal.ofNNReal_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ENNReal.coe_rpow_of_nonneg _ hp0.le, ENNReal.ofNNReal_toNNReal]

end Calkin

end Operators

end TruncationGauge

/-! ### The `∞` endpoint of the Schatten scale -/

universe u₀ v₀ w₀

/-- **`S_∞`**, the top of the Schatten scale, defined as the operator-norm family.

The roadmap asks for a separately named endpoint whose gauge is `Φ_∞ = ‖·‖_∞`, and for the
identification with the operator-norm family.  Taking the operator-norm family as the
*definition* keeps this free of the `HasMinMaxLowerBoundEverywhere` hypothesis that
`symmetricGaugeFamily` carries — the roadmap's signature has no such hypothesis — and puts
the content in `gauge_schattenFamilyInf`, which is the `Φ_∞` description. -/
noncomputable def schattenFamilyInf (𝕜 : Type u₀) [RCLike 𝕜] :
    OperatorIdealFamily.{u₀, v₀, w₀} 𝕜 :=
  operatorNormIdealFamily 𝕜

/-- The `∞` endpoint's gauge is the sup gauge of the approximation-number sequence:
`supGauge_extend_of_antitone` collapses the supremum to `a₀`, which is the operator norm. -/
theorem gauge_schattenFamilyInf {𝕜 : Type u₀} [RCLike 𝕜] {E F : Type v₀}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F) :
    (schattenFamilyInf.{u₀, v₀, v₀} 𝕜).gauge T
      = TruncationGauge.supGauge.extend
          (fun n => ENNReal.ofReal (T.approximationNumber n)) := by
  have hanti : Antitone (fun n => ENNReal.ofReal (T.approximationNumber n)) :=
    fun m n hmn => ENNReal.ofReal_le_ofReal (T.approximationNumber_antitone hmn)
  rw [TruncationGauge.supGauge_extend_of_antitone hanti,
    ContinuousLinearMap.approximationNumber_index_zero]
  simp [schattenFamilyInf, operatorNormIdealFamily]

end TauCeti
