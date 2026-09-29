-- Prove2me | Theorems.Thm_Probability_PortfolioRegret_sum_fiberMass
-- name    : Probability.PortfolioRegret.sum_fiberMass
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:55:13.617967+00:00
-- url     : https://prove2.me/theorems/438d885e-91c8-4ad7-8412-b59f92cf5f7e
-- title:
--   Sum fiberMass
-- statement:
--   Formal statement of `Probability.PortfolioRegret.sum_fiberMass` from the Aether Catalog (Probability). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Probability.PortfolioRegret.sum_fiberMass[Fintype Ω] [Fintype O] [DecidableEq O]
--       (w : Ω → ℚ) (obs : Ω → O) : ∑ o, fiberMass w obs o = ∑ ω, w ω := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PortfolioRegretCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PortfolioRegretCore.lean#L82

-- Thm stub generated from Probability/PortfolioRegretCore.lean
import Mathlib
import Definitions.Def_Probability_PortfolioRegretCore
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Portfolio scheduling over an invisible channel — core theory

This file formalises the probabilistic skeleton behind the empirical finding of
experiment 560 ("no universal winner, no dial edge; the regret tail is
`N`-invisible"): a finite portfolio of algorithms is run on instances drawn from
a finite probability space; each instance carries an *observable* feature
(bit length, balance, ... — anything computable from `N`) and a *hidden* feature
(the powersmoothness of `p - 1`), and the running cost of every member of the
portfolio depends only on the hidden feature.

The main results are:

* `PortfolioRegret.ev_policy_eq_sum_fiber` — a fiberwise decomposition of the
  expected cost of a *dial rule* (a policy that reads the observable only);
* `PortfolioRegret.bestConstant_eq_inf_mean` — under invisibility the value of
  the best constant strategy is exactly `min_s m s`;
* `PortfolioRegret.no_dial_edge` — **no dial rule beats the best constant
  strategy**: the "tuned dial" of the experiment provably tunes itself to
  do-nothing;
* `PortfolioRegret.ml_rule_strictly_worse` — a *strict* converse: any rule that
  deviates towards a suboptimal strategy on a positive-mass fiber is strictly
  worse than doing nothing (the formal shadow of "the ML rule is significantly
  worse than static");
* `PortfolioRegret.exists_policy_eq_oracle` and
  `PortfolioRegret.paid_probe_beneficial_iff` — a probe that reveals the hidden
  channel attains the oracle, and is worth its price exactly when the price
  undercuts the static regret.

Everything is stated over `ℚ` on finite spaces, so the accompanying concrete
portfolios are exactly computable.
-/

open Probability.PortfolioRegret

open Finset

variable {Ω O S : Type*}

/-! ## Basic objects -/








/-! ## Fiberwise decomposition -/

theorem Probability.PortfolioRegret.sum_fiberMass[Fintype Ω] [Fintype O] [DecidableEq O]
    (w : Ω → ℚ) (obs : Ω → O) : ∑ o, fiberMass w obs o = ∑ ω, w ω := by sorry
