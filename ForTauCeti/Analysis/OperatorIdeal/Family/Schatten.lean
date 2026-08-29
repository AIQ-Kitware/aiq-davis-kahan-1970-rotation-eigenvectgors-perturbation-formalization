/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.Normed.FiniteLpGauge
public import ForTauCeti.Analysis.OperatorIdeal.Family.KyFan
public import ForTauCeti.Analysis.OperatorIdeal.Family.TraceClass
public import ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Energy
public import ForTauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.EnergyComparison

/-!
# The Schatten-`p` operator ideals

The **Schatten `p`-norm** of a bounded operator is the `ℓᵖ` norm of its approximation-number
sequence,

```
T.schattenENorm p = (∑' n, ‖aₙ(T)‖ₑ ^ p) ^ p⁻¹,
```

valued in `ℝ≥0∞` and therefore defined for every bounded operator, being `∞` exactly off the
ideal.  At `p = 1` it is the nuclear norm and at `p = 2` the Hilbert--Schmidt norm; those two
have their own modules, and this one is the family in between.

## Why the triangle inequality is the whole file

Every other ideal law is a pointwise statement about approximation numbers and transports
term by term.  Subadditivity is not: `aₙ(S + T) ≤ aₙ(S) + aₙ(T)` is **false** in general, and
what is true is the weaker *prefix* statement, the Ky Fan inequality
`∑_{n<k} aₙ(S+T) ≤ ∑_{n<k} aₙ(S) + ∑_{n<k} aₙ(T)`.  Getting from prefix sums to `ℓᵖ` norms is
exactly weak majorization.

`ForTauCeti/Analysis/Convex/Majorization.lean` has that theory, but for `Fin n`, and there is
no sequence version anywhere in the library.  **None is needed.**  The `Fin k` theory is
applied to the truncation at each `k`, which bounds every partial sum of the left side by the
*whole* right side; the supremum over `k` is then the left side's own `tsum`.  The finite
layer is the tool here, not the obstacle.

## Main definitions and results

* `ContinuousLinearMap.schattenENorm`: the Schatten `p`-norm, valued in `ℝ≥0∞`;
* `ContinuousLinearMap.schattenENorm_add_le`: the triangle inequality;
* `ContinuousLinearMap.schattenENorm_smul`, `_adjoint`, `_comp_le`: the remaining ideal laws;
* `ContinuousLinearMap.IsSchattenClass`: the membership predicate;
* `TauCeti.schattenIdealFamily`: the resulting symmetric operator ideal family;
* `ContinuousLinearMap.schattenENorm_one` and
  `TauCeti.schattenIdealFamily_one_eq_traceClassIdealFamily`: at `p = 1` this *is* the
  trace-class ideal;
* `ContinuousLinearMap.schattenENorm_two` and
  `TauCeti.schattenIdealFamily_two_eq_hilbertSchmidtIdealFamily`: at `p = 2` it is the
  Hilbert--Schmidt ideal.

## The `p = 2` bridge

`hilbertSchmidtENorm` is built from the Hilbert--Schmidt energy through a Hilbert basis and
never mentions approximation numbers, so unlike its `p = 1` twin the agreement with the
Schatten gauge is a theorem rather than arithmetic.  It is proved here, as
`tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy`.

**Neither of the two routes one expects is the one taken.**  Not the singular-value
decomposition of a compact operator: Mathlib's eigenvector basis is finite-dimensional only,
and pinned Mathlib has no orthonormal eigenbasis for a compact self-adjoint operator.  Not an
`ε`-argument either.  Instead both inequalities go through the *same* finite truncations of
the basis — forward by reading the finite case exactly, reverse by Fatou along
`Finset.atTop`.

The family-level consequences are here too:
`TauCeti.schattenIdealFamily_two_eq_hilbertSchmidtIdealFamily` and its `p = 1` twin
`TauCeti.schattenIdealFamily_one_eq_traceClassIdealFamily`.  **So the three named families
in this directory are three presentations of one scale**, not three unrelated
constructions.  Completeness
of the family is likewise open, as it is for the trace-class family.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: none.
-/

open scoped ENNReal NNReal InnerProductSpace

public section

namespace ContinuousLinearMap

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
-- Both spaces share a universe because `HasMinMaxLowerBoundEverywhere` quantifies over one:
-- an ideal family fixes a single universe for every pair it acts on.
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

section Truncation

/-- The prefix sums of a truncated sequence are the sequence's own partial sums, capped at the
truncation length.  This is the only bridge the file needs between
`TauCeti.FiniteVector.prefixSum` on `Fin k` and `Finset.range`. -/
theorem _root_.TauCeti.FiniteVector.prefixSum_comp_val {k : ℕ} (f : ℕ → ℝ) (j : ℕ) :
    TauCeti.FiniteVector.prefixSum j (fun i : Fin k => f i) =
      ∑ n ∈ Finset.range (min j k), f n := by
  classical
  rw [TauCeti.FiniteVector.prefixSum, Finset.sum_filter, Fin.sum_univ_eq_sum_range
    (fun m => if m < j then f m else 0) k, ← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_min]
  exact and_comm

end Truncation

section Finite

variable [HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]

/-- **The Schatten triangle inequality on a truncation.**  Every partial `ℓᵖ` sum of the
approximation numbers of `S + T` is bounded by the *full* partial sums of `S` and of `T` at
the same length.

The proof is the whole point of the module: the truncated sequences are weakly majorized —
antitone and nonnegative because approximation numbers are, and prefix-comparable because
that comparison *is* `kyFanGauge_add_le` — so `TauCeti.FiniteVector.lpGauge_mono_weaklyMajorized`
applies, and finite Minkowski splits the right-hand side. -/
theorem lpGauge_approximationNumber_add_le {p : ℝ} (hp : 1 ≤ p) (S T : E →L[𝕜] F) (k : ℕ) :
    TauCeti.FiniteVector.lpGauge p (fun i : Fin k => (S + T).approximationNumber i) ≤
      TauCeti.FiniteVector.lpGauge p (fun i : Fin k => S.approximationNumber i) +
        TauCeti.FiniteVector.lpGauge p (fun i : Fin k => T.approximationNumber i) := by
  classical
  have hmaj : TauCeti.FiniteVector.WeaklyMajorized
      (fun i : Fin k => (S + T).approximationNumber i)
      (fun i : Fin k => S.approximationNumber i + T.approximationNumber i) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact fun i j hij => (S + T).approximationNumber_antitone (by exact_mod_cast hij)
    · exact fun i j hij =>
        add_le_add (S.approximationNumber_antitone (by exact_mod_cast hij))
          (T.approximationNumber_antitone (by exact_mod_cast hij))
    · exact fun i => (S + T).approximationNumber_nonneg i
    · exact fun i =>
        add_nonneg (S.approximationNumber_nonneg i) (T.approximationNumber_nonneg i)
    · intro j
      rw [TauCeti.FiniteVector.prefixSum_comp_val (fun n => (S + T).approximationNumber n) j,
        show (fun i : Fin k => S.approximationNumber i + T.approximationNumber i)
          = (fun i : Fin k => (fun n => S.approximationNumber n + T.approximationNumber n) i)
          from rfl,
        TauCeti.FiniteVector.prefixSum_comp_val
          (fun n => S.approximationNumber n + T.approximationNumber n) j,
        Finset.sum_add_distrib]
      exact kyFanGauge_add_le_of_hasMinMaxLowerBound
        HasMinMaxLowerBoundEverywhere.out S T (min j k)
  calc TauCeti.FiniteVector.lpGauge p (fun i : Fin k => (S + T).approximationNumber i)
      ≤ TauCeti.FiniteVector.lpGauge p
          (fun i : Fin k => S.approximationNumber i + T.approximationNumber i) :=
        TauCeti.FiniteVector.lpGauge_mono_weaklyMajorized hp hmaj
    _ ≤ _ := TauCeti.FiniteVector.lpGauge_add_le hp _ _

end Finite


section Gauge

/-- The **Schatten `p`-norm**, valued in `ℝ≥0∞` and therefore defined for every bounded
operator: it is `∞` exactly when `T` is not Schatten-`p`. -/
@[expose]
noncomputable def schattenENorm (p : ℝ) (T : E →L[𝕜] F) : ℝ≥0∞ :=
  (∑' n : ℕ, ENNReal.ofReal (T.approximationNumber n) ^ p) ^ p⁻¹

-- Reading the finite gauge in `ℝ≥0∞` is arithmetic; neither space needs to be complete.
omit [CompleteSpace E] [CompleteSpace F] in
/-- The truncated `ℓᵖ` gauge, read in `ℝ≥0∞`.  This is the bridge between the real finite
theory, where the majorization argument lives, and the `ℝ≥0∞` gauge, where the ideal laws
are stated unconditionally. -/
theorem ofReal_lpGauge_approximationNumber {p : ℝ} (hp0 : 0 < p) (T : E →L[𝕜] F) (k : ℕ) :
    ENNReal.ofReal
        (TauCeti.FiniteVector.lpGauge p (fun i : Fin k => T.approximationNumber i)) =
      (∑ n ∈ Finset.range k, ENNReal.ofReal (T.approximationNumber n) ^ p) ^ p⁻¹ := by
  have hsum : ∀ i : Fin k, |T.approximationNumber i| ^ p = T.approximationNumber i ^ p :=
    fun i => by rw [abs_of_nonneg (T.approximationNumber_nonneg i)]
  rw [TauCeti.FiniteVector.lpGauge, one_div]
  rw [← ENNReal.ofReal_rpow_of_nonneg
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) (by positivity)]
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _,
    Fin.sum_univ_eq_sum_range
      (fun m => ENNReal.ofReal (|T.approximationNumber m| ^ p)) k]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [abs_of_nonneg (T.approximationNumber_nonneg m),
    ENNReal.ofReal_rpow_of_nonneg (T.approximationNumber_nonneg m) hp0.le]

-- A partial sum is at most its `tsum`; again no completeness is used.
omit [CompleteSpace E] [CompleteSpace F] in
/-- Every truncated `ℓᵖ` gauge is dominated by the whole Schatten norm. -/
theorem ofReal_lpGauge_le_schattenENorm {p : ℝ} (hp0 : 0 < p) (T : E →L[𝕜] F) (k : ℕ) :
    ENNReal.ofReal
        (TauCeti.FiniteVector.lpGauge p (fun i : Fin k => T.approximationNumber i)) ≤
      T.schattenENorm p := by
  rw [ofReal_lpGauge_approximationNumber hp0 T k, schattenENorm]
  exact ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum _) (by positivity)

section Triangle

variable [HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]

/-- **The Schatten triangle inequality.**

Each truncation is handled by `lpGauge_approximationNumber_add_le`, whose right-hand side is
already bounded by the two whole gauges; the `tsum` on the left is the supremum of those
truncations, so the bound passes to the limit with nothing further to prove. -/
theorem schattenENorm_add_le {p : ℝ} (hp : 1 ≤ p) (S T : E →L[𝕜] F) :
    (S + T).schattenENorm p ≤ S.schattenENorm p + T.schattenENorm p := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  set R := S.schattenENorm p + T.schattenENorm p with hR
  have hstep : ∀ k : ℕ,
      (∑ n ∈ Finset.range k, ENNReal.ofReal ((S + T).approximationNumber n) ^ p) ^ p⁻¹ ≤ R := by
    intro k
    rw [← ofReal_lpGauge_approximationNumber hp0 (S + T) k]
    calc ENNReal.ofReal
          (TauCeti.FiniteVector.lpGauge p (fun i : Fin k => (S + T).approximationNumber i))
        ≤ ENNReal.ofReal
            (TauCeti.FiniteVector.lpGauge p (fun i : Fin k => S.approximationNumber i) +
              TauCeti.FiniteVector.lpGauge p (fun i : Fin k => T.approximationNumber i)) :=
          ENNReal.ofReal_le_ofReal (lpGauge_approximationNumber_add_le hp S T k)
      _ = _ := ENNReal.ofReal_add (TauCeti.FiniteVector.lpGauge_nonneg _ _)
          (TauCeti.FiniteVector.lpGauge_nonneg _ _)
      _ ≤ R := add_le_add (ofReal_lpGauge_le_schattenENorm hp0 S k)
          (ofReal_lpGauge_le_schattenENorm hp0 T k)
  -- The partial sums are bounded by `R ^ p`, and `∑'` is their supremum.
  have hpow : ∀ k : ℕ,
      ∑ n ∈ Finset.range k, ENNReal.ofReal ((S + T).approximationNumber n) ^ p ≤ R ^ p := by
    intro k
    have h := ENNReal.rpow_le_rpow (hstep k) hp0.le
    rwa [← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one] at h
  have htsum : ∑' n : ℕ, ENNReal.ofReal ((S + T).approximationNumber n) ^ p ≤ R ^ p :=
    ENNReal.tsum_eq_iSup_nat.trans_le (iSup_le hpow)
  have := ENNReal.rpow_le_rpow htsum (by positivity : (0 : ℝ) ≤ p⁻¹)
  rwa [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one] at this

end Triangle

-- Scaling scales every approximation number, so it scales the whole sum; completeness is
-- not used.
omit [CompleteSpace E] [CompleteSpace F] in
/-- **Absolute homogeneity.** -/
theorem schattenENorm_smul {p : ℝ} (hp0 : 0 < p) (c : 𝕜) (T : E →L[𝕜] F) :
    (c • T).schattenENorm p = ‖c‖ₑ * T.schattenENorm p := by
  have hterm : ∀ n : ℕ, ENNReal.ofReal ((c • T).approximationNumber n) ^ p =
      ‖c‖ₑ ^ p * ENNReal.ofReal (T.approximationNumber n) ^ p := by
    intro n
    rw [approximationNumber_smul, ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  rw [schattenENorm, schattenENorm]
  simp only [hterm]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ p⁻¹),
    ← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]

-- The zeroth term alone gives the bound, so no completeness is needed.
omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Schatten norm dominates the operator norm**, being its zeroth term. -/
theorem enorm_le_schattenENorm {p : ℝ} (hp0 : 0 < p) (T : E →L[𝕜] F) :
    ‖T‖ₑ ≤ T.schattenENorm p := by
  have hz : ‖T‖ₑ ^ p ≤ ∑' n : ℕ, ENNReal.ofReal (T.approximationNumber n) ^ p := by
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum 0)
    rw [← ofReal_norm, ← T.approximationNumber_index_zero]
  have := ENNReal.rpow_le_rpow hz (by positivity : (0 : ℝ) ≤ p⁻¹)
  rwa [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one] at this

/-- **Adjoint invariance**, immediate from invariance of the approximation numbers.  This is
what makes the Schatten family *symmetric*. -/
theorem schattenENorm_adjoint (p : ℝ) (T : E →L[𝕜] F) :
    T.adjoint.schattenENorm p = T.schattenENorm p := by
  simp only [schattenENorm, approximationNumber_adjoint]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The two-sided ideal bound.** -/
theorem schattenENorm_comp_le {p : ℝ} (hp0 : 0 < p) {G H : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : F →L[𝕜] G) (T : E →L[𝕜] F) (R : H →L[𝕜] E) :
    (L ∘L T ∘L R).schattenENorm p ≤ ‖L‖ₑ * T.schattenENorm p * ‖R‖ₑ := by
  have hterm : ∀ n : ℕ, ENNReal.ofReal ((L ∘L T ∘L R).approximationNumber n) ^ p ≤
      (‖L‖ₑ * ‖R‖ₑ) ^ p * ENNReal.ofReal (T.approximationNumber n) ^ p := by
    intro n
    have h := ENNReal.ofReal_le_ofReal (approximationNumber_comp_comp_le L T R n)
    refine le_trans (ENNReal.rpow_le_rpow h hp0.le) (le_of_eq ?_)
    -- The `rw` chain this replaced repeated `ofReal_norm` twice and
    -- `mul_rpow_of_nonneg` three times, once per occurrence.
    simp only [ENNReal.ofReal_mul (mul_nonneg (norm_nonneg L) (T.approximationNumber_nonneg n)),
      ENNReal.ofReal_mul (norm_nonneg L), ofReal_norm,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    ring
  calc (L ∘L T ∘L R).schattenENorm p
      ≤ ((‖L‖ₑ * ‖R‖ₑ) ^ p * ∑' n : ℕ, ENNReal.ofReal (T.approximationNumber n) ^ p) ^ p⁻¹ := by
        refine ENNReal.rpow_le_rpow ?_ (by positivity)
        rw [← ENNReal.tsum_mul_left]
        exact ENNReal.tsum_le_tsum hterm
    _ = ‖L‖ₑ * T.schattenENorm p * ‖R‖ₑ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ p⁻¹),
          ← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one, schattenENorm]
        ring

-- Lower semicontinuity is about the approximation-number sequence; no completeness is used.
omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Schatten norm is lower semicontinuous along operator-norm convergence**, stated at
the `p`-th power.

Same shape as `nuclearENorm_le_liminf`: the summands are continuous images of the
approximation numbers and `ENNReal.tsum_le_liminf_tsum` handles the sum.

**Stated at the `p`-th power deliberately**, which is also why the Hilbert--Schmidt twin is
stated at the square.  Pulling `^ p⁻¹` out of a `liminf` needs that map to commute with
`liminf`, which is true but is a separate lemma about `ℝ≥0∞`; at the `p`-th power the sum is
literally the `liminf`'s subject and nothing has to commute.  Consumers undo it with
`ENNReal.rpow_le_rpow_iff`. -/
theorem schattenENorm_rpow_le_liminf {p : ℝ} (hp0 : 0 < p) {u : Filter ℕ} [u.NeBot]
    {T : ℕ → E →L[𝕜] F} {L : E →L[𝕜] F}
    (hop : Filter.Tendsto (fun n => ‖T n - L‖) u (nhds 0)) :
    L.schattenENorm p ^ p ≤ Filter.liminf (fun n => (T n).schattenENorm p ^ p) u := by
  have hpow : ∀ S : E →L[𝕜] F, S.schattenENorm p ^ p
      = ∑' i : ℕ, ENNReal.ofReal (S.approximationNumber i) ^ p := by
    intro S
    rw [schattenENorm, ← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  simp only [hpow]
  refine ENNReal.tsum_le_liminf_tsum fun i => ?_
  refine (ENNReal.continuous_rpow_const.tendsto _).comp ?_
  refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hop
  rw [Real.dist_eq]
  exact abs_approximationNumber_sub_approximationNumber_le (T n) L i

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Schatten norm is unchanged by negation, term by term. -/
@[simp] theorem schattenENorm_neg (p : ℝ) (T : E →L[𝕜] F) :
    (-T).schattenENorm p = T.schattenENorm p := by
  simp only [schattenENorm, approximationNumber_neg]

omit [CompleteSpace E] [CompleteSpace F] in
/-- `T` is **Schatten-`p`** when its Schatten norm is finite. -/
def IsSchattenClass (p : ℝ) (T : E →L[𝕜] F) : Prop := T.schattenENorm p ≠ ∞

section AgreementAtOne

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **At `p = 1` the Schatten norm is the nuclear norm.**  Both are `tsum`s of the same
sequence and the exponents are `1` and `1⁻¹`, so this is arithmetic in `ℝ≥0∞` rather than a
theorem about operators.

The `p = 2` counterpart is *not* arithmetic and is not proved here: `hilbertSchmidtENorm` is
built from the Hilbert--Schmidt energy through a basis and never mentions approximation
numbers, so relating the two needs Parseval together with the singular-value decomposition —
a statement this library does not contain. -/
theorem schattenENorm_one (T : E →L[𝕜] F) : T.schattenENorm 1 = T.nuclearENorm := by
  simp [schattenENorm, nuclearENorm]

end AgreementAtOne

section AgreementAtTwo

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **The Schatten-2 norm is the Hilbert--Schmidt norm.**  Both are the square root of the
same `ℝ≥0∞` quantity, by the identity above. -/
theorem schattenENorm_two (T : E →L[𝕜] F) :
    T.schattenENorm 2 = T.hilbertSchmidtENorm := by
  classical
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [schattenENorm, T.hilbertSchmidtENorm_eq b,
    ← tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy T b]
  norm_num


end AgreementAtTwo

end Gauge

end ContinuousLinearMap

namespace TauCeti

universe u v

open ContinuousLinearMap

/-- **The Schatten-`p` operator ideal**, for `1 ≤ p`.

At `p = 1` its gauge is the nuclear norm and at `p = 2` the Hilbert--Schmidt norm; those two
families are built separately in this directory from their own arguments, and agreeing with
them is not asserted here. -/
noncomputable def schattenIdealFamily (𝕜 : Type u) [RCLike 𝕜]
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] {p : ℝ} (hp : 1 ≤ p) :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  gauge A := A.schattenENorm p
  gauge_add_le A B := schattenENorm_add_le hp A B
  gauge_smul c A := schattenENorm_smul (lt_of_lt_of_le zero_lt_one hp) c A
  enorm_le_gauge A := enorm_le_schattenENorm (lt_of_lt_of_le zero_lt_one hp) A
  gauge_comp_le L A R := schattenENorm_comp_le (lt_of_lt_of_le zero_lt_one hp) L A R
  gauge_adjoint A := schattenENorm_adjoint p A

/-- **The Schatten ideal is complete**, for the same reason the trace-class ideal is: the
gauge dominates the operator norm, so a gauge-Cauchy sequence has an operator-norm limit,
and `schattenENorm_rpow_le_liminf` then puts that limit in the ideal and gives convergence
in the gauge. -/
instance isComplete_schattenIdealFamily {𝕜 : Type u} [RCLike 𝕜]
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] {p : ℝ} (hp : 1 ≤ p) :
    (schattenIdealFamily.{u, v} 𝕜 hp).toOperatorIdealFamily.IsComplete where
  completeSpace := by
    intro E F _ _ _ _ _ _
    have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
    refine Metric.complete_of_cauchySeq_tendsto fun a ha => ?_
    have hop : CauchySeq fun n => (a n).val :=
      TauCeti.OperatorIdealFamily.Elem.cauchySeq_val ha
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hop
    have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        (L - (a n).val).schattenENorm p ≤ ENNReal.ofReal ε := by
      intro ε hε
      rw [Metric.cauchySeq_iff] at ha
      obtain ⟨N, hN⟩ := ha ε hε
      refine ⟨N, fun n hn => ?_⟩
      have hfatou : (L - (a n).val).schattenENorm p ^ p ≤
          Filter.liminf (fun m => ((a m).val - (a n).val).schattenENorm p ^ p)
            Filter.atTop := by
        refine ContinuousLinearMap.schattenENorm_rpow_le_liminf hp0 ?_
        have hd : Filter.Tendsto (fun m => dist ((a m).val) L) Filter.atTop (nhds 0) :=
          tendsto_iff_dist_tendsto_zero.mp hL
        simpa [dist_eq_norm] using hd
      have hev : ∀ᶠ m in Filter.atTop,
          ((a m).val - (a n).val).schattenENorm p ^ p ≤ ENNReal.ofReal ε ^ p := by
        filter_upwards [Filter.eventually_ge_atTop N] with m hm
        have hd : ‖a m - a n‖ < ε := by simpa [dist_eq_norm] using hN m hm n hn
        have hgauge : ((a m).val - (a n).val).schattenENorm p ≤ ENNReal.ofReal ε := by
          have heq : (schattenIdealFamily.{u, v} 𝕜 hp).gauge (a m - a n).val
              = ((a m).val - (a n).val).schattenENorm p := rfl
          rw [← heq, ← TauCeti.OperatorIdealFamily.Elem.enorm_eq_gauge, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal hd.le
        exact ENNReal.rpow_le_rpow hgauge hp0.le
      have hle : Filter.liminf
          (fun m => ((a m).val - (a n).val).schattenENorm p ^ p) Filter.atTop
          ≤ ENNReal.ofReal ε ^ p := by
        calc Filter.liminf
              (fun m => ((a m).val - (a n).val).schattenENorm p ^ p) Filter.atTop
            ≤ Filter.liminf (fun _ : ℕ => ENNReal.ofReal ε ^ p) Filter.atTop :=
              Filter.liminf_le_liminf hev
          _ = ENNReal.ofReal ε ^ p := Filter.liminf_const _
      exact (ENNReal.rpow_le_rpow_iff hp0).mp (hfatou.trans hle)
    obtain ⟨N₁, hN₁⟩ := hcauchy 1 one_pos
    have hmemL : L ∈ (schattenIdealFamily.{u, v} 𝕜 hp).toOperatorIdealFamily.carrier := by
      have hsplit : L = (L - (a N₁).val) + (a N₁).val := by abel
      rw [TauCeti.OperatorIdealFamily.mem_carrier_iff, hsplit]
      refine ne_top_of_le_ne_top ?_
        ((schattenIdealFamily.{u, v} 𝕜 hp).toOperatorIdealFamily.gauge_add_le _ _)
      refine ENNReal.add_ne_top.mpr ⟨?_, (a N₁).gauge_val_ne_top⟩
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hN₁ N₁ le_rfl)
    refine ⟨TauCeti.OperatorIdealFamily.Elem.mk hmemL, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have hgauge : ((a n).val - L).schattenENorm p ≤ ENNReal.ofReal (ε / 2) := by
      have hneg : ((a n).val - L) = -(L - (a n).val) := by abel
      rw [hneg, ContinuousLinearMap.schattenENorm_neg]
      exact hN n hn
    have hle : ‖a n - TauCeti.OperatorIdealFamily.Elem.mk hmemL‖ ≤ ε / 2 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgauge
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    calc dist (a n) (TauCeti.OperatorIdealFamily.Elem.mk hmemL)
        = ‖a n - TauCeti.OperatorIdealFamily.Elem.mk hmemL‖ := dist_eq_norm _ _
      _ ≤ ε / 2 := hle
      _ < ε := by linarith

variable {𝕜 : Type u} [RCLike 𝕜]
  [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The gauge of the Schatten family *is* the Schatten norm, definitionally. -/
@[simp] theorem gauge_schattenIdealFamily {p : ℝ} (hp : 1 ≤ p) (A : E →L[𝕜] F) :
    (schattenIdealFamily.{u, v} 𝕜 hp).gauge A = A.schattenENorm p := (rfl)

/-- Membership in the Schatten ideal is exactly `IsSchattenClass`. -/
theorem mem_schattenIdealFamily_carrier_iff {p : ℝ} (hp : 1 ≤ p) (A : E →L[𝕜] F) :
    A ∈ (schattenIdealFamily.{u, v} 𝕜 hp).toOperatorIdealFamily.carrier ↔
      A.IsSchattenClass p := (Iff.rfl)

/-- **The Schatten ideal at `p = 1` is the trace-class ideal**, as families and not merely as
gauges.  `OperatorIdealFamily.ext` is what makes the upgrade available: a family in this
presentation is determined by its gauge, including off the ideal, so the two structures agree
once their gauges do. -/
theorem schattenIdealFamily_one_eq_traceClassIdealFamily (𝕜 : Type u) [RCLike 𝕜]
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] :
    schattenIdealFamily.{u, v} 𝕜 (le_refl (1 : ℝ)) = traceClassIdealFamily.{u, v} 𝕜 := by
  exact SymmetricOperatorIdealFamily.ext fun {_E _F} _ _ _ _ _ _ A => A.schattenENorm_one

/-- **The Schatten ideal at `p = 2` is the Hilbert--Schmidt ideal**, as families.

Together with `schattenIdealFamily_one_eq_traceClassIdealFamily` this places the two named
families of this directory inside the Schatten scale, so the three constructions in
`Analysis/OperatorIdeal/Family/` are three presentations of one object rather than three
objects. -/
theorem schattenIdealFamily_two_eq_hilbertSchmidtIdealFamily (𝕜 : Type u) [RCLike 𝕜]
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] :
    schattenIdealFamily.{u, v} 𝕜 (one_le_two (α := ℝ))
      = hilbertSchmidtIdealFamily.{u, v} 𝕜 :=
  SymmetricOperatorIdealFamily.ext fun {_E _F} _ _ _ _ _ _ A =>
    ContinuousLinearMap.schattenENorm_two A


end TauCeti
