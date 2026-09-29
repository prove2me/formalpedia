-- Prove2me | solution 1 for AscentCostLaw.breakeven_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:40:07.891622+00:00
-- url     : https://prove2.me/submissions/f7f38b38-3123-451b-bf17-d587196eee12

-- Sol generated from Novelty/AscentCostExponent.lean
import Mathlib
import Definitions.Def_Novelty_AscentCostExponent
import Definitions.Def_Novelty_AscentCostLaw
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# The ascent exponent law: `rate(α) = min(3, 1/α)`, with a kink at `α = 1/3`

Cycle 1 (`Novelty.AscentCostLaw`) priced the two schedules exactly.  This second cycle extracts
the *exponent* of the optimal schedule and shows the phase structure of the branch-oracle
economy.

Main results.

* `ascent_exponent_law` : the per-depth logarithmic cost of the best of the two schedules
  converges to `log (min 3 (1/α))`.  Since the cheaper schedule is the one with the smaller
  base, the exponential rate of an ascent guided by an accuracy-`α` ternary branch oracle is
  exactly `min(3, 1/α)`.
* `ascent_rate_eq_three_of_le_third` / `ascent_rate_lt_three_of_gt_third` : the kink.  Below
  `α = 1/3` accuracy buys *nothing* at the level of the exponent (the rate is pinned at `3`,
  the effective-branching refutation of cycle 1 in its sharpest form); above `1/3` the rate is
  `1/α`, strictly decreasing.
* `breakeven_iff` : the breakeven accuracy of cycle 1 is not merely sufficient — it is an exact
  threshold, `win ↔ α > ((1+c)h/F) ^ (1/h)`, with `criticalAccuracy_strictMono_cost` showing
  that a costlier per-step feature strictly raises the accuracy the oracle must reach.
* `sequential_beats_class_hint` : a one-shot class hint keeping a fraction `θ ≥ 1/3` of a
  ternary tree is capped at speedup `1/θ ≤ 3`, while sequential branch hints pass any cap.
* `dfsCost_strictAnti` : within a schedule, accuracy is always worth something (strict monotone
  price), even though — by the exponent law — it is worth nothing to the exponent below `1/3`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer, cycle 2): the two exact laws of cycle 1 are two branches of one
exponent law with a nonsmooth crossover, and the crossover is at the reciprocal of the branching
factor.

Experiment (Experimenter): `log E / h` evaluated on the closed laws (see
`ComputationalEvidence.md`).  At `α = 0.5`: restart gives `log(10 · 2^10)/10 = 0.92341` at
`h = 10` and `0.78537` at `h = 40`, descending towards `log 2 = 0.69315`, while DFS gives
`1.04109` at `h = 10` and `1.08423` at `h = 40`, ascending towards `log 3 = 1.09861` — the min
tracks `log(1/α) = log 2 < log 3`.  At `α = 0.25 < 1/3` the same computation gives restart rate
`1.61655` at `h = 10` (towards `log 4 = 1.38629`) and DFS rate `1.09704` (towards `log 3`); the
min is `log 3`, i.e. pinned at the branching factor.  The crossover is at `α = 1/3` exactly,
where the two rates coincide at `log 3`.

Analysis (Analyst): the kink is a genuine non-analyticity in `α` of the optimal exponent, and it
sits exactly at the reciprocal branching factor `1/b` with `b = 3`.  Nothing in the argument uses
`b = 3`, so the same statement should hold verbatim with `min (b) (1/α)`; that generalisation is
recorded in `FUTURE_DIRECTIONS.md`.

Critique (Critic): the exponent law needs both costs positive, hence `h ≥ 1` Filter.eventually filters
and `0 < α < 1`.  At `α = 1` the restart law is polynomial and its `log`-rate is `0`, consistent
with `min 3 1 = 1` only in the degenerate reading `log 1 = 0`; the theorem is therefore stated
for `α < 1` and the `α = 1` case is covered separately by `restartCost_one` of cycle 1.
-/

open AscentCostLaw

open Filter Topology

/-! ### Logarithmic rates -/




/-! ### The optimal schedule and its exponent -/







/-! ### Accuracy always has a price, even where it has no exponent -/



/-! ### Breakeven is an exact threshold -/


theorem criticalAccuracy_pow {c F : ℝ} {h : ℕ} (hh : 1 ≤ h) (ht : 0 ≤ (1 + c) * h / F) :
    (criticalAccuracy c F h) ^ h = (1 + c) * h / F := by
  have hh0 : ((h : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold criticalAccuracy
  rw [← Real.rpow_natCast (((1 + c) * h / F) ^ ((h : ℝ)⁻¹)) h, ← Real.rpow_mul ht,
    inv_mul_cancel₀ hh0, Real.rpow_one]



/-! ### Sequential hints leave the class-hint cap behind -/





open AscentCostLaw in
theorem solution{c F : ℝ} (hc : 0 ≤ c) {h : ℕ} (hh : 1 ≤ h) (hF : 0 < F) {α : ℝ}
    (hα : 0 < α) :
    (1 + c) * restartCost α h < F ↔ criticalAccuracy c F h < α := by
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hαh : (0 : ℝ) < α ^ h := pow_pos hα h
  have hnum : (0 : ℝ) ≤ (1 + c) * h / F := by positivity
  have hcrit : (0 : ℝ) ≤ criticalAccuracy c F h := Real.rpow_nonneg hnum _
  have hkey : (1 + c) * restartCost α h < F ↔ (1 + c) * h / F < α ^ h := by
    unfold restartCost
    rw [mul_div_assoc', div_lt_iff₀ hαh, div_lt_iff₀ hF]
    constructor
    · intro hlt; nlinarith
    · intro hlt; nlinarith
  rw [hkey, ← criticalAccuracy_pow hh hnum,
    pow_lt_pow_iff_left₀ hcrit hα.le (by omega)]
