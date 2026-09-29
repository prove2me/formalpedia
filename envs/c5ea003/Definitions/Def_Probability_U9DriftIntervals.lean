-- Prove2me | Definitions.Def_Probability_U9DriftIntervals
-- name    : Probability_U9DriftIntervals
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:11.318275+00:00
-- url     : https://prove2.me/theorems/63afa98b-ed17-49d6-b6fb-11bc94891fc7
-- title:
--   Aether Catalog definitions — Probability_U9DriftIntervals
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.U9DriftIntervals`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/U9DriftIntervals.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Confidence intervals for the band-9 smoothness ratio: coverage, deliverables, and the
  round-to-four display defect

Context (experiment 569, paper 216; replication of the paper-214 pilot).  A run measures
the ratio

`r = (rate of B-smooth values among the candidates x^2 - N) / (rate among size-matched controls)`

at band 9 (bit length 96 balanced semiprimes) and reports a cluster-bootstrap percentile
interval for `r`.  The *decision rule* is: the null "candidates behave like size-matched
random values" is retained exactly when the interval covers `1`; the *deliverable* that is
compared between runs is the worst-case CI edge distance `max (|lo - 1|) (|hi - 1|)`.

This file gives the exact theory of that reporting scheme, and the numerical facts the
round-74 ledger rests on.

Main results:

* `U9Drift.CI.covers_iff_abs_le` — coverage is the symmetric statement `|x - c| ≤ h`
  around the interval centre.
* `U9Drift.CI.edge_eq_halfWidth_add` — for an interval that covers `1`, the reported
  deliverable splits exactly as `halfWidth + |centre - 1|`: a run can improve the
  deliverable either by getting tighter or by drifting back towards `1`.
* `U9Drift.replication_tightens_deliverable` — the fresh-seed replication interval
  `[0.919, 1.0101]` has deliverable `0.081`, strictly tightening the pilot's `0.137`;
  `U9Drift.replication_is_more_precise` and `U9Drift.replication_is_less_drifted` show
  that *both* summands improve, so the tightening is not an artifact of re-centering.
* `U9Drift.all_intervals_cover_one` — every reported interval (pilot `1e6`, replication
  `1e5` primary, replication `1e6` secondary) covers `1`: the `H0` branch is the one the
  pre-registration selects.
* `U9Drift.store4_eq_zero_of_small` / `U9Drift.store4_not_injective` — the pre-patch writer
  stored `round(·, 4)`, which is *constant zero* on the whole range `[0, 5·10⁻⁵)` in which
  the candidate rate lives; the stored `0.0` therefore carries no information beyond that
  range membership.
* `U9Drift.candidate_rate_pinned` / `U9Drift.candidate_rate_pos` — the CI-implied recovery:
  the true candidate rate lies in `[2.65701·10⁻⁵, 3.56128·10⁻⁵]`, in particular it is
  positive, so the stored value is provably not the measured one.
* `U9Drift.ledger_bracket_is_not_an_enclosure` — an adversarial catch: the bracket
  `[2.66·10⁻⁵, 3.56·10⁻⁵]` quoted in the ledger has its endpoints rounded *inwards*, so it
  is not a valid enclosure of the CI-implied range; the outward-rounded
  `[2.65·10⁻⁵, 3.57·10⁻⁵]` (`U9Drift.candidate_rate_safe_bracket`) is.
-/

namespace U9Drift

open Real

/-! ## Elementary square comparison helpers -/




/-! ## Reported intervals -/

/-- A reported (percentile bootstrap) confidence interval. -/
structure CI where
  lo : ℝ
  hi : ℝ
  le : lo ≤ hi

namespace CI

variable (I : CI)

/-- The centre of the reported interval. -/
noncomputable def center : ℝ := (I.lo + I.hi) / 2

/-- Half the width of the reported interval; the natural precision measure. -/
noncomputable def halfWidth : ℝ := (I.hi - I.lo) / 2

/-- Coverage: the interval contains the value `x`.  The retained-null decision rule is
`I.Covers 1`. -/
def Covers (x : ℝ) : Prop := I.lo ≤ x ∧ x ≤ I.hi

/-- The reported deliverable: the worst-case CI-edge distance from the null value `1`. -/
noncomputable def edge : ℝ := max |I.lo - 1| |I.hi - 1|







end CI

/-! ## The three reported intervals of the round-74 ledger -/

/-- Paper 214's pilot interval at the `1e6` low-prime-factor cut. -/
def pilot1e6 : CI := ⟨0.8630, 1.0389, by norm_num⟩

/-- Experiment 569's fresh-seed replication at the pre-registered primary `1e5` cut. -/
def rep1e5 : CI := ⟨0.8571, 1.1488, by norm_num⟩

/-- Experiment 569's fresh-seed replication at the better-powered secondary `1e6` cut. -/
def rep1e6 : CI := ⟨0.919, 1.0101, by norm_num⟩







/-! ## The round-to-four display defect -/

/-- The pre-patch writer: store `round(x, 4)` (half-up). -/
noncomputable def store4 (x : ℝ) : ℝ := (⌊x * 10 ^ 4 + 1 / 2⌋ : ℤ) / 10 ^ 4



/-! ## CI-implied recovery of the candidate rate -/

/-- The measured control rate at the primary `1e5` cut. -/
noncomputable def rateCtrl : ℝ := 3.1 / 10 ^ 5






end U9Drift


