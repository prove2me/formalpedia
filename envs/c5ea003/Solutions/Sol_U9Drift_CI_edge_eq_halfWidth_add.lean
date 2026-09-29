-- Prove2me | solution 1 for U9Drift.CI.edge_eq_halfWidth_add
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:36:48.898895+00:00
-- url     : https://prove2.me/submissions/289bb2a3-3874-43ab-872e-560b273b2126

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





theorem halfWidth_nonneg : 0 ≤ I.halfWidth := by
  have := I.le; simp only [halfWidth]; linarith

theorem lo_eq : I.lo = I.center - I.halfWidth := by
  simp only [center, halfWidth]; ring

theorem hi_eq : I.hi = I.center + I.halfWidth := by
  simp only [center, halfWidth]; ring





/-! ## The three reported intervals of the round-74 ledger -/










/-! ## The round-to-four display defect -/




/-! ## CI-implied recovery of the candidate rate -/








open U9Drift in
theorem solution(h : I.Covers 1) :
    I.edge = I.halfWidth + |I.center - 1| := by
  obtain ⟨h1, h2⟩ := h
  have hlo : |I.lo - 1| = 1 - I.lo := by rw [abs_of_nonpos (by linarith)]; ring
  have hhi : |I.hi - 1| = I.hi - 1 := by rw [abs_of_nonneg (by linarith)]
  have hL := lo_eq I
  have hH := hi_eq I
  have hw := halfWidth_nonneg I
  rw [edge, hlo, hhi]
  rcases le_total I.center 1 with hc | hc
  · rw [abs_of_nonpos (by linarith), max_eq_left (by rw [hL, hH] at *; linarith)]
    rw [hL]; ring
  · rw [abs_of_nonneg (by linarith), max_eq_right (by rw [hL, hH] at *; linarith)]
    rw [hH]; ring
