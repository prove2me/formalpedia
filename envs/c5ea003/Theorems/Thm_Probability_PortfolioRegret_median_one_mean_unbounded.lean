-- Prove2me | Theorems.Thm_Probability_PortfolioRegret_median_one_mean_unbounded
-- name    : Probability.PortfolioRegret.median_one_mean_unbounded
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:59:10.988972+00:00
-- url     : https://prove2.me/theorems/ac50f318-5654-421a-ac76-a1b9bdcb676b
-- title:
--   Median blindness of regret.
-- statement:
--   **Median blindness of regret.**  For every level `M` there is a two-instance,
--   two-member portfolio whose *optimal static* strategy ties the oracle on more than
--   half of the mass (median regret ratio `1`) and yet has mean regret ratio above
--   `M`.  No median-based diagnostic can see the tail.
--
--   ```lean
--   theorem Probability.PortfolioRegret.median_one_mean_unbounded(M : ℚ) (hM : 0 ≤ M) :
--       (∀ ω, 0 ≤ tailW ω) ∧ (∑ ω, tailW ω = 1) ∧
--       (∀ ω, 0 < oracleCost (tailCost M) ω) ∧
--       bestConstant tailW (tailCost M) = EV tailW (fun ω => tailCost M ω 0) ∧
--       1 / 2 ≤ Pr tailW (fun ω => tailCost M ω 0 = oracleCost (tailCost M) ω) ∧
--       M < EV tailW (regretRatio (tailCost M) 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PortfolioRegretTail.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PortfolioRegretTail.lean#L84

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

theorem Probability.PortfolioRegret.median_one_mean_unbounded(M : ℚ) (hM : 0 ≤ M) :
    (∀ ω, 0 ≤ tailW ω) ∧ (∑ ω, tailW ω = 1) ∧
    (∀ ω, 0 < oracleCost (tailCost M) ω) ∧
    bestConstant tailW (tailCost M) = EV tailW (fun ω => tailCost M ω 0) ∧
    1 / 2 ≤ Pr tailW (fun ω => tailCost M ω 0 = oracleCost (tailCost M) ω) ∧
    M < EV tailW (regretRatio (tailCost M) 0) := by sorry
