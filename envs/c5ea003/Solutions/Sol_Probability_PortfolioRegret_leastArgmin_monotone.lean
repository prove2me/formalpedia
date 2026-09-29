-- Prove2me | solution 1 for Probability.PortfolioRegret.leastArgmin_monotone
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:01:10.571979+00:00
-- url     : https://prove2.me/submissions/c89ded4a-054c-45e2-a0a2-5935ef7b64f7

-- Sol generated from Probability/PortfolioThresholdSchedule.lean
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





theorem leastArgmin_le [Fintype S] [LinearOrder S] [Nonempty S] (f : S → ℚ) (t : S) :
    f (leastArgmin f) ≤ f t :=
  mem_argminSet.mp ((argminSet f).min'_mem (argminSet_nonempty f)) t

theorem leastArgmin_min [Fintype S] [LinearOrder S] [Nonempty S] {f : S → ℚ} {s : S}
    (hs : ∀ t, f s ≤ f t) : leastArgmin f ≤ s :=
  (argminSet f).min'_le s (mem_argminSet.mpr hs)


/-! ## Discrete Topkis: monotone comparative statics -/



/-! ## Monotone (threshold) schedules are optimal -/






/-! ## The hypothesis is necessary -/




open Probability.PortfolioRegret in
theorem solution[Fintype S] [LinearOrder S] [Nonempty S] [Preorder O]
    {f : O → S → ℚ} (hdd : DecreasingDifferences f) :
    Monotone (fun o => leastArgmin (f o)) := by
  intro o o' hoo
  by_contra hcon
  push_neg at hcon
  set s := leastArgmin (f o) with hs
  set t := leastArgmin (f o') with ht
  have hts : t ≤ s := le_of_lt hcon
  have hkey : f o' s - f o' t ≤ f o s - f o t := hdd hoo hts
  have h1 : f o s ≤ f o t := leastArgmin_le (f o) t
  have h2 : f o' t ≤ f o' s := leastArgmin_le (f o') s
  have h3 : f o s = f o t := le_antisymm h1 (by linarith)
  have hmin : ∀ u, f o t ≤ f o u := fun u => h3 ▸ leastArgmin_le (f o) u
  exact absurd (leastArgmin_min hmin) (not_le.mpr hcon)
