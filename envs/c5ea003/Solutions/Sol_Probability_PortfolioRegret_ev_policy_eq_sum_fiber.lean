-- Prove2me | solution 1 for Probability.PortfolioRegret.ev_policy_eq_sum_fiber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:47:05.608391+00:00
-- url     : https://prove2.me/submissions/e74e9387-1f21-4a41-9cba-ceeb3b5eea67

-- Sol generated from Probability/PortfolioRegretCore.lean
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





/-! ## No dial edge -/




/-! ## Paid probes: buying the hidden channel -/






open Probability.PortfolioRegret in
theorem solution[Fintype Ω] [Fintype O] [DecidableEq O]
    {w : Ω → ℚ} {cost : Ω → S → ℚ} {obs : Ω → O} {m : S → ℚ}
    (hinv : Invisible w cost obs m) (π : O → S) :
    EV w (policyCost cost obs π) = ∑ o, fiberMass w obs o * m (π o) := by
  have h : ∑ o, ∑ ω ∈ univ.filter (fun ω => obs ω = o), w ω * cost ω (π (obs ω))
      = ∑ ω, w ω * cost ω (π (obs ω)) :=
    Finset.sum_fiberwise (univ : Finset Ω) obs (fun ω => w ω * cost ω (π (obs ω)))
  simp only [EV, policyCost]
  rw [← h]
  refine Finset.sum_congr rfl fun o _ => ?_
  have : ∑ ω ∈ univ.filter (fun ω => obs ω = o), w ω * cost ω (π (obs ω))
      = ∑ ω ∈ univ.filter (fun ω => obs ω = o), w ω * cost ω (π o) := by
    refine Finset.sum_congr rfl fun ω hω => ?_
    rw [(Finset.mem_filter.mp hω).2]
  rw [this, hinv o (π o)]
