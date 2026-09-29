-- Prove2me | Definitions.Def_Probability_PortfolioRegretCore
-- name    : Probability_PortfolioRegretCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:29:59.366775+00:00
-- url     : https://prove2.me/theorems/91ee1bc2-36a9-4e25-bd31-bfc2f7902971
-- title:
--   Aether Catalog definitions — Probability_PortfolioRegretCore
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PortfolioRegretCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PortfolioRegretCore.lean by skeleton subtraction
import Mathlib
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

namespace Probability.PortfolioRegret

open Finset

variable {Ω O S : Type*}

/-! ## Basic objects -/

/-- Expectation of `f : Ω → ℚ` under the weights `w`. -/
def EV [Fintype Ω] (w f : Ω → ℚ) : ℚ := ∑ ω, w ω * f ω

/-- Total mass of the fiber of the observation map `obs` over `o`. -/
def fiberMass [Fintype Ω] [DecidableEq O] (w : Ω → ℚ) (obs : Ω → O) (o : O) : ℚ :=
  ∑ ω ∈ univ.filter (fun ω => obs ω = o), w ω

/-- Cost incurred by the *dial rule* `π`, which picks a portfolio member from the
observable feature alone. -/
def policyCost (cost : Ω → S → ℚ) (obs : Ω → O) (π : O → S) (ω : Ω) : ℚ :=
  cost ω (π (obs ω))

/-- The oracle cost: the best member of the portfolio, chosen with hindsight. -/
noncomputable def oracleCost [Fintype S] [Nonempty S] (cost : Ω → S → ℚ) (ω : Ω) : ℚ :=
  univ.inf' univ_nonempty (cost ω)

/-- Expected cost of the best *constant* strategy (the "static" schedule). -/
noncomputable def bestConstant [Fintype Ω] [Fintype S] [Nonempty S]
    (w : Ω → ℚ) (cost : Ω → S → ℚ) : ℚ :=
  univ.inf' univ_nonempty (fun s => EV w (fun ω => cost ω s))

/-- Static regret: how much the best fixed strategy loses against the oracle. -/
noncomputable def staticRegret [Fintype Ω] [Fintype S] [Nonempty S]
    (w : Ω → ℚ) (cost : Ω → S → ℚ) : ℚ :=
  bestConstant w cost - EV w (oracleCost cost)

/-- **Invisibility of the organising channel.**  Relative to the observation map
`obs`, the conditional mean cost of every portfolio member is the same number
`m s` on every fiber: the observation carries no information about which member
will win. -/
def Invisible [Fintype Ω] [DecidableEq O] (w : Ω → ℚ) (cost : Ω → S → ℚ)
    (obs : Ω → O) (m : S → ℚ) : Prop :=
  ∀ (o : O) (s : S),
    ∑ ω ∈ univ.filter (fun ω => obs ω = o), w ω * cost ω s = fiberMass w obs o * m s

/-! ## Fiberwise decomposition -/





/-! ## No dial edge -/




/-! ## Paid probes: buying the hidden channel -/





end Probability.PortfolioRegret


