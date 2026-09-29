-- Prove2me | solution 1 for Probability.PortfolioRegret.gap_le_sum_pair_swaps
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:58:55.102662+00:00
-- url     : https://prove2.me/submissions/05744ab7-bb1c-4892-8767-9600e57119e9

-- Sol generated from Probability/PortfolioIrredundant.lean
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioEpsInvisible
import Definitions.Def_Probability_PortfolioIrredundant
import Definitions.Def_Probability_PortfolioNullDial
import Definitions.Def_Probability_PortfolioRegretCore
import Theorems.Thm_Probability_PortfolioRegret_ev_const_eq_sum_fiberVal
import Theorems.Thm_Probability_PortfolioRegret_fiberRegret_eq
import Theorems.Thm_Probability_PortfolioRegret_fiberRegret_le_sum_swapMass
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Irredundancy does not rescue the pairwise certificate

Eighth cycle of the portfolio programme.  `Probability.PortfolioNullDial` shows
that the portfolio-level dial gain can be `0` while two members swap places with
positive mass, the swap being hidden by a third member that is optimal on every
fiber.  The natural repair — and the first conjecture recorded in the previous
cycle's `FUTURE_DIRECTIONS.md` — is to delete such dominating structure first: on
an **irredundant** portfolio (no member weakly beats another on *every* fiber, so
nothing can be eliminated by the proved fiberwise rule) one might hope that the
measured gain controls all pairwise swap masses, up to a constant depending only
on the number of members.

This file **refutes** that hope, for every constant and already with three
members:

* `IrredundantPortfolio` — no member fiberwise dominates another;
* `irred_portfolio_irredundant` — the explicit family `irredCost e` (three
  instances, each its own fiber, uniform weights) is irredundant for `0 < e`;
* `irred_gap`, `irred_swapMass` — its dial gain is exactly `2e/3` while the swap
  masses of its first two members are exactly `10/3` in both directions;
* `swap_unbounded_on_irredundant` — hence for **every** ratio `M` there is an
  irredundant three-member portfolio whose pairwise swap mass exceeds `M` times
  its dial gain.  No constant, and no function of the number of members, can
  bound pairwise swaps by the measured gain.

The moral for the measured cell: a small scheduling gain is compatible with
arbitrarily large pairwise trade-offs even after every eliminable member has been
removed, so pairwise structure must be measured pair by pair
(`two_member_gap`), never inferred from the portfolio-level dial.
-/

open Probability.PortfolioRegret

open Finset

variable {Ω O S : Type*}














/-! ## The inequality that *is* true: the gap is covered by pairwise swaps

The refutation above is one-sided.  In the opposite direction the portfolio gain
is always dominated by the pairwise swap masses against a best static member, and
the bound is exactly the anti-diagonal ratio `|S| - 1`. -/

/-- The two swap masses of a pair differ by the difference of the static costs. -/
theorem swapMassFun_sub [Fintype Ω] [Fintype O] [DecidableEq O]
    (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) (s t : S) :
    swapMassFun (fun o => fiberVal w cost obs o s) (fun o => fiberVal w cost obs o t)
        - swapMassFun (fun o => fiberVal w cost obs o t) (fun o => fiberVal w cost obs o s)
      = EV w (fun ω => cost ω s) - EV w (fun ω => cost ω t) := by
  rw [ev_const_eq_sum_fiberVal w cost obs s, ev_const_eq_sum_fiberVal w cost obs t,
    swapMassFun, swapMassFun, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  rcases le_total (fiberVal w cost obs o s) (fiberVal w cost obs o t) with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring





open Probability.PortfolioRegret in
theorem solution[Fintype Ω] [Fintype O] [DecidableEq O]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) {s₀ : S}
    (hs₀ : EV w (fun ω => cost ω s₀) = bestConstant w cost) :
    bestConstant w cost - dialValue w cost obs
      ≤ ∑ t ∈ univ.erase s₀,
          min (swapMassFun (fun o => fiberVal w cost obs o s₀)
                (fun o => fiberVal w cost obs o t))
              (swapMassFun (fun o => fiberVal w cost obs o t)
                (fun o => fiberVal w cost obs o s₀)) := by
  have hmin : ∀ t ∈ univ.erase s₀,
      min (swapMassFun (fun o => fiberVal w cost obs o s₀) (fun o => fiberVal w cost obs o t))
          (swapMassFun (fun o => fiberVal w cost obs o t) (fun o => fiberVal w cost obs o s₀))
        = swapMassFun (fun o => fiberVal w cost obs o s₀)
            (fun o => fiberVal w cost obs o t) := by
    intro t _
    have hdiff := swapMassFun_sub w cost obs s₀ t
    have hEV : bestConstant w cost ≤ EV w (fun ω => cost ω t) := Finset.inf'_le _ (mem_univ t)
    exact min_eq_left (by rw [hs₀] at hdiff; linarith)
  rw [Finset.sum_congr rfl hmin]
  have hfr : fiberRegret w cost obs s₀ = bestConstant w cost - dialValue w cost obs := by
    rw [fiberRegret_eq, hs₀]
  rw [← hfr]
  exact fiberRegret_le_sum_swapMass w cost obs s₀
