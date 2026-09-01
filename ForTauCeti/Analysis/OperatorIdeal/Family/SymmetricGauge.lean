/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
module

public import ForTauCeti.Analysis.Normed.SymmetricGauge
public import ForTauCeti.Analysis.Normed.SchattenGauge
public import ForTauCeti.Analysis.OperatorIdeal.Family.Basic
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint
public import ForTauCeti.Analysis.OperatorIdeal.Family.KyFanDominance
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.DiagonalSequence
public import ForTauCeti.Analysis.OperatorIdeal.Family.Schatten

/-!
# The operator ideal family induced by a symmetric gauge

Calkin's correspondence in the direction this development needs: a symmetric
gauge on sequences induces an operator ideal family, by applying the gauge to the
sequence of approximation numbers.

* `TauCeti.symmetricGaugeFamily` — the family, `gauge A = Φ∞ (a(A))`.

## The four laws, and where each comes from

Each structure field is one approximation-number fact composed with one law of
`SymmetricGauge.extend`; no new analysis happens here.

* `gauge_add_le` — `ContinuousLinearMap.kyFanGauge_add_le_complex` says the prefix sums
  of `a(A + B)` are dominated by those of `a(A) + a(B)`, which
  `SymmetricGauge.extend_le_extend_of_forall_sum_le` converts into a statement
  about the gauge, and `SymmetricGauge.extend_add_le` then splits the right-hand
  side.  **This is the only field needing two gauge laws**, and it is why
  `extend_add_le` had to exist before this file could;
* `gauge_smul` — `approximationNumber_smul` then `SymmetricGauge.extend_smul`;
* `enorm_le_gauge` — `approximationNumber_index_zero` (`a₀ T = ‖T‖`) then
  `SymmetricGauge.le_extend` at index `0`;
* `gauge_comp_le` — `approximationNumber_comp_le_mul_norm` and its companion,
  then `SymmetricGauge.extend_mono` and `SymmetricGauge.extend_smul`.

## Why `ℂ`

`ContinuousLinearMap.kyFanGauge_add_le_complex` is unconditional over `ℂ`.  Its
`RCLike`-generic counterpart carries a `HasMinMaxLowerBoundEverywhere` typeclass,
so a general-field version of this construction would have to carry it too.  The
roadmap states the family over `ℂ`, and this is the reason.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **new**.  Written against the target signature in
  `TauCetiRoadmap/OperatorTheory/OperatorIdeals/Suggested.lean`.
* Roadmap topic: `OperatorIdeals`.
* Original authors / copyright: Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
-/

public section

open scoped NNReal ENNReal

namespace TauCeti

universe u v

open _root_.ContinuousLinearMap

variable (Φ : SymmetricGauge)

/-- The approximation-number sequence of an operator, in `ℝ≥0∞`. -/
noncomputable def approxSeq {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (A.approximationNumber n)

/-- The approximation-number sequence is antitone. -/
theorem approxSeq_antitone {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) : Antitone (approxSeq A) := by
  intro m n hmn
  exact ENNReal.ofReal_le_ofReal (A.approximationNumber_antitone hmn)

/-- Every approximation number is finite, so `approxSeq` never takes the value
`⊤`.  This is what lets the `ℝ≥0∞` reductions in `SymmetricGauge` fire. -/
theorem approxSeq_ne_top {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) (n : ℕ) : approxSeq A n ≠ ⊤ :=
  ENNReal.ofReal_ne_top

section Laws

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Prefix sums of `approxSeq (A + B)` are dominated by those of the sum
sequence.  This is `kyFanGauge_add_le_complex` pushed into `ℝ≥0∞`. -/
theorem approxSeq_prefix_add_le (A B : E →L[ℂ] F) (k : ℕ) :
    ∑ n ∈ Finset.range k, approxSeq (A + B) n
      ≤ ∑ n ∈ Finset.range k, (approxSeq A n + approxSeq B n) := by
  have hky := ContinuousLinearMap.kyFanGauge_add_le_complex A B k
  simp only [ContinuousLinearMap.kyFanGauge] at hky
  -- Both sides are `ofReal` of a finite sum of nonnegative reals.
  have hL : ∑ n ∈ Finset.range k, approxSeq (A + B) n
      = ENNReal.ofReal (∑ n ∈ Finset.range k, (A + B).approximationNumber n) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · rfl
    · exact fun i _ => (A + B).approximationNumber_nonneg i
  have hR : ∑ n ∈ Finset.range k, (approxSeq A n + approxSeq B n)
      = ENNReal.ofReal ((∑ n ∈ Finset.range k, A.approximationNumber n)
          + ∑ n ∈ Finset.range k, B.approximationNumber n) := by
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => A.approximationNumber_nonneg i)
      (Finset.sum_nonneg fun i _ => B.approximationNumber_nonneg i),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => A.approximationNumber_nonneg i),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => B.approximationNumber_nonneg i),
      ← Finset.sum_add_distrib]
    rfl
  rw [hL, hR]
  exact ENNReal.ofReal_le_ofReal hky

/-- **Subadditivity of the induced gauge.**  The only law needing two `extend`
lemmas: majorization first, then splitting. -/
theorem extend_approxSeq_add_le (A B : E →L[ℂ] F) :
    Φ.extend (approxSeq (A + B)) ≤ Φ.extend (approxSeq A) + Φ.extend (approxSeq B) := by
  have hmaj : Φ.extend (approxSeq (A + B))
      ≤ Φ.extend (fun n => approxSeq A n + approxSeq B n) :=
    Φ.extend_le_extend_of_forall_sum_le (approxSeq_antitone (A + B))
      (fun m n hmn => add_le_add (approxSeq_antitone A hmn) (approxSeq_antitone B hmn))
      (approxSeq_prefix_add_le A B)
  exact hmaj.trans (Φ.extend_add_le _ _)

/-- **Homogeneity of the induced gauge.** -/
theorem extend_approxSeq_smul (c : ℂ) (A : E →L[ℂ] F) :
    Φ.extend (approxSeq (c • A)) = ‖c‖ₑ * Φ.extend (approxSeq A) := by
  have hseq : approxSeq (c • A) = fun n => ((‖c‖₊ : ℝ≥0) : ℝ≥0∞) * approxSeq A n := by
    funext n
    simp only [approxSeq, ContinuousLinearMap.approximationNumber_smul]
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
    rfl
  rw [hseq, Φ.extend_smul]
  rfl

/-- **The gauge dominates the operator norm**, via `a₀ T = ‖T‖`. -/
theorem enorm_le_extend_approxSeq (A : E →L[ℂ] F) :
    ‖A‖ₑ ≤ Φ.extend (approxSeq A) := by
  have h0 : approxSeq A 0 = ‖A‖ₑ := by
    simp only [approxSeq, ContinuousLinearMap.approximationNumber_index_zero]
    rw [← ofReal_norm]
  calc ‖A‖ₑ = approxSeq A 0 := h0.symm
    _ ≤ Φ.extend (approxSeq A) := Φ.le_extend _ 0

/-- **The composition bound.**  `approxSeq` of `L ∘L A ∘L R` is dominated
termwise by `‖L‖ * ‖R‖` times `approxSeq A`, and `extend_mono` plus
`extend_smul` turn that into the gauge statement. -/
theorem extend_approxSeq_comp_le {G H : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : F →L[ℂ] G) (A : E →L[ℂ] F) (R : H →L[ℂ] E) :
    Φ.extend (approxSeq (L ∘L A ∘L R)) ≤ ‖L‖ₑ * Φ.extend (approxSeq A) * ‖R‖ₑ := by
  have hterm : ∀ n, approxSeq (L ∘L A ∘L R) n
      ≤ ((‖L‖₊ * ‖R‖₊ : ℝ≥0) : ℝ≥0∞) * approxSeq A n := by
    intro n
    have h1 : (L ∘L A ∘L R).approximationNumber n ≤ ‖L‖ * ((A ∘L R).approximationNumber n) :=
      ContinuousLinearMap.approximationNumber_comp_le_norm_mul L (A ∘L R) n
    have h2 : (A ∘L R).approximationNumber n ≤ A.approximationNumber n * ‖R‖ :=
      ContinuousLinearMap.approximationNumber_comp_le_mul_norm A R n
    have hchain : (L ∘L A ∘L R).approximationNumber n
        ≤ (‖L‖ * ‖R‖) * A.approximationNumber n := by
      calc (L ∘L A ∘L R).approximationNumber n
          ≤ ‖L‖ * ((A ∘L R).approximationNumber n) := h1
        _ ≤ ‖L‖ * (A.approximationNumber n * ‖R‖) := by gcongr
        _ = (‖L‖ * ‖R‖) * A.approximationNumber n := by ring
    simp only [approxSeq]
    calc ENNReal.ofReal ((L ∘L A ∘L R).approximationNumber n)
        ≤ ENNReal.ofReal ((‖L‖ * ‖R‖) * A.approximationNumber n) :=
          ENNReal.ofReal_le_ofReal hchain
      _ = ((‖L‖₊ * ‖R‖₊ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (A.approximationNumber n) := by
          rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal]
          congr 1
  calc Φ.extend (approxSeq (L ∘L A ∘L R))
      ≤ Φ.extend (fun n => ((‖L‖₊ * ‖R‖₊ : ℝ≥0) : ℝ≥0∞) * approxSeq A n) :=
        Φ.extend_mono hterm
    _ = ((‖L‖₊ * ‖R‖₊ : ℝ≥0) : ℝ≥0∞) * Φ.extend (approxSeq A) :=
        Φ.extend_smul (‖L‖₊ * ‖R‖₊) (approxSeq A)
    _ = ‖L‖ₑ * Φ.extend (approxSeq A) * ‖R‖ₑ := by
        simp only [enorm_eq_nnnorm, ENNReal.coe_mul]
        ring

end Laws

/-- **The operator ideal family induced by a symmetric gauge.**

`gauge A = Φ∞ (a(A))`: the extended gauge applied to the approximation-number
sequence.  The four laws are the four theorems above, each of which is one
approximation-number fact composed with one law of `SymmetricGauge.extend`. -/
@[expose]
noncomputable def symmetricGaugeFamily : OperatorIdealFamily ℂ where
  gauge A := Φ.extend (approxSeq A)
  gauge_add_le A B := extend_approxSeq_add_le Φ A B
  gauge_smul c A := extend_approxSeq_smul Φ c A
  enorm_le_gauge A := enorm_le_extend_approxSeq Φ A
  gauge_comp_le L A R := extend_approxSeq_comp_le Φ L A R

/-- The induced family's gauge unfolds to the extended gauge of the
approximation-number sequence. -/
@[simp]
theorem symmetricGaugeFamily_gauge {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) :
    (symmetricGaugeFamily Φ).gauge A = Φ.extend (approxSeq A) := rfl

/-- **Milestone B1, the direction of the Calkin correspondence claimed here.**

Two symmetric gauges inducing the same operator ideal agree on antitone sequences, so the
ideal really is a function of the singular-value sequence alone.

**The proof splits on boundedness, which the roadmap's statement does not show.**  An
unbounded antitone sequence is realised by *no* bounded operator, so the realisation route
does not apply to it — and does not have to: `le_extend` makes both sides `∞`, and the
equation holds because neither gauge can see past the supremum.  A bounded sequence is
realised by `diagOpLp`, and `approximationNumber_diagOpLp` turns the operator equality into
the sequence equality.

Surjectivity — that every symmetric ideal arises this way — is **not** claimed; it is the
substantial half of Calkin's theorem and needs a separability hypothesis nothing else here
needs. -/
theorem symmetricGaugeFamily_injective {Φ Ψ : SymmetricGauge}
    (h : symmetricGaugeFamily.{0, 0} Φ = symmetricGaugeFamily.{0, 0} Ψ)
    {a : ℕ → ℝ≥0∞} (ha : Antitone a) :
    Φ.extend a = Ψ.extend a := by
  classical
  by_cases hbdd : ∃ K : ℝ≥0, ∀ n, a n ≤ (K : ℝ≥0∞)
  · obtain ⟨K, hK⟩ := hbdd
    set c : ℕ → ℂ := fun n => (((a n).toReal : ℝ) : ℂ) with hcdef
    have hafin : ∀ n, a n ≠ ⊤ := fun n => ne_top_of_le_ne_top (by simp) (hK n)
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
      (fun N : OperatorIdealFamily.{0, 0, 0} ℂ =>
        N.gauge (TauCeti.diagOpLp c hK0 hcK)) h
    simp only [symmetricGaugeFamily_gauge] at hop
    have hrw : approxSeq (TauCeti.diagOpLp c hK0 hcK) = a := by
      funext n
      rw [approxSeq, TauCeti.approximationNumber_diagOpLp c hK0 hcK hcanti n, hcnorm n,
        ENNReal.ofReal_toReal (hafin n)]
    rwa [hrw] at hop
  · push Not at hbdd
    have hsup : (⨆ n, a n) = ⊤ := by
      refine iSup_eq_top.2 fun b hb => ?_
      lift b to ℝ≥0 using hb.ne
      obtain ⟨n, hn⟩ := hbdd b
      exact ⟨n, hn⟩
    have hinf : ∀ Θ : SymmetricGauge, Θ.extend a = ⊤ := fun Θ =>
      top_le_iff.1 (hsup ▸ Θ.iSup_le_extend a)
    rw [hinf Φ, hinf Ψ]

/-- **Milestone B3's reconciliation.**  The Schatten ideal *obtained* from a symmetric
gauge is the one `Family/Schatten.lean` *constructs*.

The two routes are genuinely different: this side is a supremum over truncations of a
`Finsupp`-valued gauge, the other a `tsum`.  Three facts make them meet —
`extend_eq_iSup_ofFin` removes the cap, `ENNReal.tsum_eq_iSup_nat` opens the `tsum` into
the same partial sums, and `iSup_rpow` carries the exponent across. -/
theorem extend_approxSeq_schattenGauge {p : ℝ} (hp : 1 ≤ p) {E F : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) :
    (schattenGauge p hp).extend (approxSeq T)
      = ContinuousLinearMap.schattenENorm p T := by
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le hp
  have hinv : (0 : ℝ) < 1 / p := by positivity
  have hnn : ∀ n, 0 ≤ T.approximationNumber n := fun n =>
    ContinuousLinearMap.approximationNumber_nonneg T n
  rw [show approxSeq T = fun n => ENNReal.ofReal (T.approximationNumber n) from rfl,
    (schattenGauge p hp).extend_eq_iSup_ofFin hnn,
    ContinuousLinearMap.schattenENorm, ENNReal.tsum_eq_iSup_nat, ← one_div,
    iSup_rpow _ hinv]
  refine iSup_congr fun k => ?_
  rw [show (schattenGauge p hp)
        (SymmetricGauge.ofFin (fun i : Fin k => T.approximationNumber i))
      = schattenGaugeFun p
        (SymmetricGauge.ofFin (fun i : Fin k => T.approximationNumber i)) from rfl,
    schattenGaugeFun_ofFin hp0 hnn k]
  rw [ENNReal.coe_rpow_of_nonneg _ hinv.le, ENNReal.ofNNReal_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ENNReal.coe_rpow_of_nonneg _ hp0.le, ENNReal.ofNNReal_toNNReal]

/-! ## The adjoint-closed form, and Ky Fan dominance

`IsKyFanDominant` is a class on `SymmetricOperatorIdealFamily`, not on
`OperatorIdealFamily`, so the dominance statement needs the adjoint-closed form
of the construction.  That form differs in exactly one field, `gauge_adjoint`,
which `ContinuousLinearMap.approximationNumber_adjoint` supplies outright: `T`
and `T⋆` have the same approximation numbers, hence the same gauge.

The universes collapse here — `SymmetricOperatorIdealFamily.{u, v}` uses one
universe for source and target — because the adjoint exchanges them.  So this is
the *square* companion of `symmetricGaugeFamily` rather than a replacement.
-/

section Symmetric

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The gauge is unchanged by passing to the adjoint. -/
theorem extend_approxSeq_adjoint (A : E →L[ℂ] F) :
    Φ.extend (approxSeq (ContinuousLinearMap.adjoint A)) = Φ.extend (approxSeq A) := by
  congr 1
  funext n
  simp only [approxSeq, ContinuousLinearMap.approximationNumber_adjoint]

end Symmetric

/-- **The adjoint-closed operator ideal family induced by a symmetric gauge.**

The square companion of `symmetricGaugeFamily`: same gauge, plus the adjoint
invariance that `SymmetricOperatorIdealFamily` requires. -/
noncomputable def symmetricGaugeSymmetricFamily :
    SymmetricOperatorIdealFamily.{0, v} ℂ where
  toOperatorIdealFamily := symmetricGaugeFamily.{v, v} Φ
  gauge_adjoint A := extend_approxSeq_adjoint Φ A

/-- **Milestone B2.**  A family induced by a symmetric gauge is Ky Fan dominant.

The hypothesis `∀ k, A.kyFanGauge k ≤ B.kyFanGauge k` *is* prefix-sum domination
of the approximation-number sequences, which is exactly what
`SymmetricGauge.extend_le_extend_of_forall_sum_le` consumes.  Antitonicity of
both sequences is `approximationNumber_antitone`.

So no part of the Hardy--Littlewood--Pólya argument appears here: it was done
once, at the level of sequences, and this instance is its transport. -/
instance isKyFanDominant_symmetricGaugeSymmetricFamily :
    IsKyFanDominant (symmetricGaugeSymmetricFamily.{v} Φ) where
  gauge_le_of_forall_kyFanGauge_le {E F _ _ _ _ _ _} {A B} h := by
    have hpre : ∀ k, ∑ n ∈ Finset.range k, approxSeq A n
        ≤ ∑ n ∈ Finset.range k, approxSeq B n := by
      intro k
      have hk := h k
      simp only [ContinuousLinearMap.kyFanGauge] at hk
      rw [show (∑ n ∈ Finset.range k, approxSeq A n)
            = ENNReal.ofReal (∑ n ∈ Finset.range k, A.approximationNumber n) by
          rw [ENNReal.ofReal_sum_of_nonneg
            (fun i _ => A.approximationNumber_nonneg i)]; rfl,
        show (∑ n ∈ Finset.range k, approxSeq B n)
            = ENNReal.ofReal (∑ n ∈ Finset.range k, B.approximationNumber n) by
          rw [ENNReal.ofReal_sum_of_nonneg
            (fun i _ => B.approximationNumber_nonneg i)]; rfl]
      exact ENNReal.ofReal_le_ofReal hk
    exact Φ.extend_le_extend_of_forall_sum_le (approxSeq_antitone A)
      (approxSeq_antitone B) hpre

/-! ## The Schatten scale

The Schatten classes are *obtained* from the symmetric-gauge construction rather
than built separately, which is the roadmap's point: their four laws are the
family's and not new work.
-/

/-- **The Schatten-`p` operator ideal family**, `symmetricGaugeFamily` at the
`ℓᵖ` gauge.

Distinct from `ForTauCeti.Analysis.OperatorIdeal.Family.Schatten.schattenIdealFamily`,
which is the *square*, adjoint-closed, general-`RCLike` family gauged directly by
`schattenENorm`.  This one is the rectangular `ℂ` family obtained through the
gauge construction — the two are different objects with the same name in the
literature, and an audit on 2026-07-31 found them being conflated by name. -/
@[expose]
noncomputable def schattenFamily (p : ℝ) (hp : 1 ≤ p) : OperatorIdealFamily ℂ :=
  symmetricGaugeFamily (schattenGauge p hp)

/-- The Schatten family's gauge is the `ℓᵖ` gauge of the approximation-number
sequence. -/
@[simp]
theorem schattenFamily_gauge {p : ℝ} (hp : 1 ≤ p) {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) :
    (schattenFamily p hp).gauge A = (schattenGauge p hp).extend (approxSeq A) := rfl

/-- **The Schatten scale is antitone**, hence the ideals nest: `S_p ⊆ S_q` for
`p ≤ q`.

Entirely a transport: `schattenGaugeFun_antitone` is the `ℓ`-scale nesting at
the level of finitely supported sequences, and `extend_le_extend_of_le` carries
it to the extension, which is the family's gauge by definition. -/
theorem gauge_schattenFamily_antitone {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : p ≤ q) {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) :
    (schattenFamily q hq).gauge T ≤ (schattenFamily p hp).gauge T :=
  SymmetricGauge.extend_le_extend_of_le
    (fun c => schattenGaugeFun_antitone hp hq hpq c) (approxSeq T)

end TauCeti
