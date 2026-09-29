-- Prove2me | Theorems.Thm_Probability_PortfolioRegret_leastArgmin_not_monotone_without_dd
-- name    : Probability.PortfolioRegret.leastArgmin_not_monotone_without_dd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:58:59.977898+00:00
-- url     : https://prove2.me/theorems/3cdef4fd-803d-43ad-98bc-b9066798edb0
-- title:
--   Necessity of single crossing.
-- statement:
--   **Necessity of single crossing.**  This cost matrix violates decreasing
--   differences, and its fiberwise-optimal schedule is not monotone — hence not a
--   threshold rule in the observed quantile.  Ordered observations alone do not make
--   schedules ordered.
--
--   ```lean
--   theorem Probability.PortfolioRegret.leastArgmin_not_monotone_without_dd:
--       ¬ DecreasingDifferences crossCost ∧
--         ¬ Monotone (fun o => leastArgmin (crossCost o)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PortfolioThresholdSchedule.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PortfolioThresholdSchedule.lean#L156

-- Thm stub generated from Probability/PortfolioThresholdSchedule.lean
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioRegretCore
import Definitions.Def_Probability_PortfolioThresholdSchedule
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Threshold schedules: monotone comparative statics for portfolio scheduling

Seventh cycle of the portfolio programme, closing direction 2 of
`FUTURE_DIRECTIONS.md` ("smoothness-quantile scheduling law").

The measured cell of experiment 560 is organised by a *single hidden scalar* — the
powersmoothness of `p - 1` — and the named next experiment buys a noisy view of
that scalar with a short-capped `p - 1` probe.  If the probe's output is ordered
(a smoothness quantile), one wants to know whether the optimal schedule is a
*threshold rule* in that one number rather than an unstructured policy.  This file
proves that it is, under the exact structural hypothesis that makes it true.

* `DecreasingDifferences` — the single-crossing hypothesis: raising the observed
  quantile never raises the *relative* cost of a later portfolio member.
* `leastArgmin_monotone` — **discrete Topkis theorem**: under decreasing
  differences the least fiberwise-optimal member is a monotone function of the
  observation.
* `exists_monotone_optimal_dial` — hence some *monotone* rule attains the optimal
  dial value `dialValue`: the optimal schedule is order-structured, and searching
  monotone rules loses nothing.
* `dial_fibers_ordConnected` — the instance set on which a given member is played
  is an interval of quantiles; `monotone_two_member_upward_closed` states the
  two-member case as a genuine threshold: the second member is played exactly on
  an upward-closed set of quantiles.
* `leastArgmin_not_monotone_without_dd` — the hypothesis is not decorative: an
  explicit `2 x 2` cost matrix without decreasing differences has a
  non-monotone (hence non-threshold) optimal schedule.

The results are stated for an arbitrary finite linearly ordered observation space
and finite linearly ordered portfolio, and then specialised to the fiber values
`fiberVal` of `Probability.PortfolioDialEdge`.
-/

open Probability.PortfolioRegret

open Finset

variable {Ω O S : Type*}

/-! ## Least minimisers -/








/-! ## Discrete Topkis: monotone comparative statics -/



/-! ## Monotone (threshold) schedules are optimal -/






/-! ## The hypothesis is necessary -/

theorem Probability.PortfolioRegret.leastArgmin_not_monotone_without_dd:
    ¬ DecreasingDifferences crossCost ∧
      ¬ Monotone (fun o => leastArgmin (crossCost o)) := by sorry
