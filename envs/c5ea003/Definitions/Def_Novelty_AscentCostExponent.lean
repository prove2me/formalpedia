-- Prove2me | Definitions.Def_Novelty_AscentCostExponent
-- name    : Novelty_AscentCostExponent
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:04:03.146229+00:00
-- url     : https://prove2.me/theorems/bbe55811-e0e1-42f5-9c4b-9e3e9cad490d
-- title:
--   Aether Catalog definitions — Novelty_AscentCostExponent
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AscentCostExponent`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AscentCostExponent.lean by skeleton subtraction
import Mathlib
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

namespace AscentCostLaw

open Filter Topology

/-! ### Logarithmic rates -/




/-! ### The optimal schedule and its exponent -/

/-- The cost of the better of the two exact schedules. -/
noncomputable def minCost (α : ℝ) (h : ℕ) : ℝ := min (dfsCost α h) (restartCost α h)






/-! ### Accuracy always has a price, even where it has no exponent -/



/-! ### Breakeven is an exact threshold -/

/-- The critical accuracy `α* = ((1+c) h / F) ^ (1/h)`. -/
noncomputable def criticalAccuracy (c F : ℝ) (h : ℕ) : ℝ := ((1 + c) * h / F) ^ ((h : ℝ)⁻¹)




/-! ### Sequential hints leave the class-hint cap behind -/

/-- Speedup of a one-shot class hint that keeps a fraction `θ` of the search space. -/
noncomputable def classHintSpeedup (θ : ℝ) : ℝ := 1 / θ



end AscentCostLaw


