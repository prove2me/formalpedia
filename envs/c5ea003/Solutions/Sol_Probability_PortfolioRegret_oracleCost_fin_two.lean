-- Prove2me | solution 1 for Probability.PortfolioRegret.oracleCost_fin_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:01:11.667984+00:00
-- url     : https://prove2.me/submissions/6b452480-83d6-4a34-8ad2-cba6b7f10c86

-- Sol generated from Probability/PortfolioRegretTail.lean
import Mathlib
import Definitions.Def_Probability_PortfolioRegretCore
import Definitions.Def_Probability_PortfolioRegretTail
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The regret tail: median blindness and the failure of mean-based elimination

Companion to `Probability.PortfolioRegretCore`.  Two phenomena observed in
experiment 560 are isolated and proved here.

* **Median blindness.**  Every scheduling strategy in the experiment had median
  regret ratio exactly `1.000`, while the *mean* regret was large: the loss lives
  entirely in a thin tail.  `median_one_mean_unbounded` shows this is not an
  artifact — for every prescribed level `M` there is a portfolio whose *optimal
  static* strategy has median regret ratio `1` and mean regret ratio `> M`.
  Hence the median is a provably uninformative statistic for portfolio
  selection.

* **Failure of mean-based elimination (the "H3" ledger entry).**  Eliminating a
  portfolio member because its *mean* cost is larger is not a
  dominance-in-distribution argument.  `ev_le_of_stochDom` proves the valid
  direction (stochastic dominance implies a mean inequality, via an exact finite
  layer-cake identity `ev_nat_layercake`), while `mean_lt_not_stochDom` exhibits
  a variance-tail counterexample to the converse.
-/

open Probability.PortfolioRegret

open Finset

variable {Ω S : Type*}

/-! ## Probabilities, ratios and medians -/











/-! ## Layer cake and stochastic dominance -/







open Probability.PortfolioRegret in
theorem solution(cost : Ω → Fin 2 → ℚ) (ω : Ω) :
    oracleCost cost ω = min (cost ω 0) (cost ω 1) := by
  refine le_antisymm ?_ (Finset.le_inf' _ _ ?_)
  · exact le_min (Finset.inf'_le _ (mem_univ 0)) (Finset.inf'_le _ (mem_univ 1))
  · intro i _
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
