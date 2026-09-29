-- Prove2me | solution 1 for U9Drift.le_of_sq_le_sq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:34:57.464256+00:00
-- url     : https://prove2.me/submissions/f23b6bee-a291-47cd-8c82-5cef9f55b21e

-- Sol generated from Probability/U9DriftIntervals.lean
import Mathlib
import Definitions.Def_Probability_U9DriftIntervals
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

open U9Drift

open Real

/-! ## Elementary square comparison helpers -/




/-! ## Reported intervals -/


open CI

variable (I : CI)












/-! ## The three reported intervals of the round-74 ledger -/










/-! ## The round-to-four display defect -/




/-! ## CI-implied recovery of the candidate rate -/








open U9Drift in
theorem solution{x y : ℝ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  nlinarith
