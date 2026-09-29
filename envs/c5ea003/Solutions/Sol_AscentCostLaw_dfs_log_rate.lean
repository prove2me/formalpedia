-- Prove2me | solution 1 for AscentCostLaw.dfs_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:46:07.545279+00:00
-- url     : https://prove2.me/submissions/bf65ed59-767f-4480-8b01-855fdf4c4d74

-- Sol generated from Novelty/AscentCostExponent.lean
import Mathlib
import Definitions.Def_Novelty_AscentCostExponent
import Definitions.Def_Novelty_AscentCostLaw
import Theorems.Thm_AscentCostLaw_dfsCost_div_pow_tendsto
import Theorems.Thm_AscentCostLaw_dfsCost_ge
import Theorems.Thm_AscentCostLaw_failWeight_pos
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





/-! ### Sequential hints leave the class-hint cap behind -/





open AscentCostLaw in
theorem solution{α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    Filter.Tendsto (fun h : ℕ => Real.log (dfsCost α h) / h) Filter.atTop (𝓝 (Real.log 3)) := by
  have hK : 0 < failWeight α := failWeight_pos h1
  have hL : (0 : ℝ) < 3 * failWeight α / 4 := by positivity
  have hg : Filter.Tendsto (fun h : ℕ => dfsCost α h / (3 : ℝ) ^ h) Filter.atTop
      (𝓝 (3 * failWeight α / 4)) := dfsCost_div_pow_tendsto α
  have hlog : Filter.Tendsto (fun h : ℕ => Real.log (dfsCost α h / (3 : ℝ) ^ h)) Filter.atTop
      (𝓝 (Real.log (3 * failWeight α / 4))) :=
    (Real.continuousAt_log (ne_of_gt hL)).tendsto.comp hg
  have hquot : Filter.Tendsto (fun h : ℕ => Real.log (dfsCost α h / (3 : ℝ) ^ h) / h) Filter.atTop (𝓝 0) :=
    hlog.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Filter.Tendsto (fun h : ℕ => Real.log 3 + Real.log (dfsCost α h / (3 : ℝ) ^ h) / h)
      Filter.atTop (𝓝 (Real.log 3)) := by
    simpa using hquot.const_add (Real.log 3)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with h hh
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have h3 : (0 : ℝ) < (3 : ℝ) ^ h := by positivity
  have hd : 0 < dfsCost α h := lt_of_lt_of_le (by positivity) (dfsCost_ge h0 h1.le hh)
  have hsplit : dfsCost α h = (3 : ℝ) ^ h * (dfsCost α h / (3 : ℝ) ^ h) := by
    field_simp
  rw [hsplit, Real.log_mul (ne_of_gt h3) (ne_of_gt (div_pos hd h3)), Real.log_pow, ← hsplit]
  field_simp
