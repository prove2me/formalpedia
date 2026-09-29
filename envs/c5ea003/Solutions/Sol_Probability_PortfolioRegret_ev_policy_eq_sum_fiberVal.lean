-- Prove2me | solution 1 for Probability.PortfolioRegret.ev_policy_eq_sum_fiberVal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:40:23.437858+00:00
-- url     : https://prove2.me/submissions/e4fbadc0-4928-4745-a77e-6fb6f78bdf28

-- Sol generated from Probability/PortfolioDialEdge.lean
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioRegretCore
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# When does a dial help?  An exact characterisation, and the information ladder

Second cycle of the portfolio programme.  `Probability.PortfolioRegretCore`
shows that an *invisible* observation gives no scheduling edge.  Here we drop the
invisibility hypothesis entirely and compute the exact optimum over all
observation-measurable rules.

For an observation map `obs` write `fiberVal o s` for the unnormalised
conditional cost of member `s` on the fiber over `o`.  Then

* `ev_policy_eq_sum_fiberVal` — every rule costs `∑ o, fiberVal o (π o)`;
* `dialValue` `= ∑ o, min_s fiberVal o s` is attained (`exists_optimal_dial`)
  and is a lower bound for every rule (`dialValue_le_ev_policy`);
* `dialValue_le_bestConstant` — a dial never hurts if it is *optimised*;
* `dial_edge_iff` — **exact characterisation**: an optimised dial strictly beats
  the best static member if and only if every member is beaten on some fiber;
* `dialValue_mono_of_refines` — a finer observation is worth (weakly) more:
  monotonicity of the value of information;
* `ev_oracle_le_dialValue` — the whole ladder
  `E[oracle] ≤ dialValue ≤ bestConstant`.

Combined with the `N`-invisibility of the `p - 1` powersmoothness channel
(`Probability.PortfolioSmoothnessChannel`), `dial_edge_iff` explains the measured
`Δ = 0.000`: the tuned dial found nothing because on each fiber the same member
minimises the conditional cost.
-/

open Probability.PortfolioRegret

open Finset

variable {Ω O O' S : Type*}














open Probability.PortfolioRegret in
theorem solution[Fintype Ω] [Fintype O] [DecidableEq O]
    (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) (π : O → S) :
    EV w (policyCost cost obs π) = ∑ o, fiberVal w cost obs o (π o) := by
  have h : ∑ o, ∑ ω ∈ univ.filter (fun ω => obs ω = o), w ω * cost ω (π (obs ω))
      = ∑ ω, w ω * cost ω (π (obs ω)) :=
    Finset.sum_fiberwise (univ : Finset Ω) obs (fun ω => w ω * cost ω (π (obs ω)))
  simp only [EV, policyCost]
  rw [← h]
  refine Finset.sum_congr rfl fun o _ => ?_
  refine Finset.sum_congr rfl fun ω hω => ?_
  rw [(Finset.mem_filter.mp hω).2]
