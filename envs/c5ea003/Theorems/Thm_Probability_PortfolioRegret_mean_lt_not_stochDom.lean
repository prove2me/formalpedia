-- Prove2me | Theorems.Thm_Probability_PortfolioRegret_mean_lt_not_stochDom
-- name    : Probability.PortfolioRegret.mean_lt_not_stochDom
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:59:10.474116+00:00
-- url     : https://prove2.me/theorems/bc523cca-e9f8-406e-9ae7-8d11d3c942fb
-- title:
--   The invalid direction (the H3 refutation).
-- statement:
--   **The invalid direction (the H3 refutation).**  A strictly smaller mean does
--   *not* imply dominance in distribution: a two-valued cost with a heavy upper tail
--   has a smaller mean than a constant cost yet exceeds it with positive probability.
--   Eliminating a portfolio member on a mean comparison is therefore not a
--   dominance argument.
--
--   ```lean
--   theorem Probability.PortfolioRegret.mean_lt_not_stochDom:
--       ∃ (w : Fin 2 → ℚ) (X Y : Fin 2 → ℕ),
--         (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
--         (∑ i, w i * (X i : ℚ)) < (∑ i, w i * (Y i : ℚ)) ∧
--         ¬ StochDom w X Y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PortfolioRegretTail.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PortfolioRegretTail.lean#L165

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











/-! ## Layer cake and stochastic dominance -/

theorem Probability.PortfolioRegret.mean_lt_not_stochDom:
    ∃ (w : Fin 2 → ℚ) (X Y : Fin 2 → ℕ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i * (X i : ℚ)) < (∑ i, w i * (Y i : ℚ)) ∧
      ¬ StochDom w X Y := by sorry
