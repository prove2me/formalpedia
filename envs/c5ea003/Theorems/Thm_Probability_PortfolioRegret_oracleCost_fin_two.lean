-- Prove2me | Theorems.Thm_Probability_PortfolioRegret_oracleCost_fin_two
-- name    : Probability.PortfolioRegret.oracleCost_fin_two
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:59:14.998136+00:00
-- url     : https://prove2.me/theorems/ac80c2c8-2527-4984-830b-628191469158
-- title:
--   On a two-member portfolio the oracle is the pointwise minimum.
-- statement:
--   On a two-member portfolio the oracle is the pointwise minimum.
--
--   ```lean
--   theorem Probability.PortfolioRegret.oracleCost_fin_two(cost : Ω → Fin 2 → ℚ) (ω : Ω) :
--       oracleCost cost ω = min (cost ω 0) (cost ω 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PortfolioRegretTail.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PortfolioRegretTail.lean#L43

-- Thm stub generated from Probability/PortfolioRegretTail.lean
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

theorem Probability.PortfolioRegret.oracleCost_fin_two(cost : Ω → Fin 2 → ℚ) (ω : Ω) :
    oracleCost cost ω = min (cost ω 0) (cost ω 1) := by sorry
