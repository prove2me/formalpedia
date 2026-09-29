-- Prove2me | solution 1 for Probability.PortfolioRegret.dial_edge_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:47:04.440235+00:00
-- url     : https://prove2.me/submissions/88e29bf9-75bb-45bc-b2b6-a71cd45a24bd

-- Sol generated from Probability/PortfolioDialEdge.lean
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioRegretCore
import Theorems.Thm_Probability_PortfolioRegret_ev_const_eq_sum_fiberVal
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
theorem solution[Fintype Ω] [Fintype O] [DecidableEq O] [Fintype S] [Nonempty S]
    (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) :
    dialValue w cost obs < bestConstant w cost ↔
      ∀ s : S, ∃ o : O, univ.inf' univ_nonempty (fiberVal w cost obs o) < fiberVal w cost obs o s := by
  constructor
  · intro hlt s
    have hb : bestConstant w cost ≤ EV w (fun ω => cost ω s) := Finset.inf'_le _ (mem_univ s)
    have hsum : ∑ o, univ.inf' univ_nonempty (fiberVal w cost obs o)
        < ∑ o, fiberVal w cost obs o s := by
      rw [← dialValue, ← ev_const_eq_sum_fiberVal w cost obs s]
      exact lt_of_lt_of_le hlt hb
    by_contra hcon
    push_neg at hcon
    exact absurd hsum (not_lt.mpr (Finset.sum_le_sum fun o _ => hcon o))
  · intro hall
    obtain ⟨s, -, hs⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := S))
      (fun s => EV w (fun ω => cost ω s))
    have hb : bestConstant w cost = EV w (fun ω => cost ω s) := hs
    obtain ⟨o₀, ho₀⟩ := hall s
    rw [hb, ev_const_eq_sum_fiberVal w cost obs s, dialValue]
    exact Finset.sum_lt_sum (fun o _ => Finset.inf'_le _ (mem_univ s)) ⟨o₀, mem_univ _, ho₀⟩
