-- Prove2me | Theorems.Thm_Probability_PortfolioRegret_gap_le_sum_pair_swaps
-- name    : Probability.PortfolioRegret.gap_le_sum_pair_swaps
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:58:19.719069+00:00
-- url     : https://prove2.me/theorems/851d9618-4778-4c8c-aac2-f2b89fb8b89e
-- title:
--   The gap is covered by pairwise swaps.
-- statement:
--   **The gap is covered by pairwise swaps.**  Against a best static member `s₀`,
--   each pairwise swap mass in the direction of `s₀` is the *smaller* of the two, and
--   their sum dominates the whole portfolio's dial gain.  Together with
--   `swap_unbounded_on_irredundant` this pins the relationship between the two
--   functionals exactly: the gap is bounded by the pairwise swaps, never the reverse.
--
--   ```lean
--   theorem Probability.PortfolioRegret.gap_le_sum_pair_swaps[Fintype Ω] [Fintype O] [DecidableEq O]
--       [Fintype S] [DecidableEq S] [Nonempty S]
--       (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) {s₀ : S}
--       (hs₀ : EV w (fun ω => cost ω s₀) = bestConstant w cost) :
--       bestConstant w cost - dialValue w cost obs
--         ≤ ∑ t ∈ univ.erase s₀,
--             min (swapMassFun (fun o => fiberVal w cost obs o s₀)
--                   (fun o => fiberVal w cost obs o t))
--                 (swapMassFun (fun o => fiberVal w cost obs o t)
--                   (fun o => fiberVal w cost obs o s₀)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PortfolioIrredundant.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PortfolioIrredundant.lean#L235

-- Thm stub generated from Probability/PortfolioIrredundant.lean
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioEpsInvisible
import Definitions.Def_Probability_PortfolioIrredundant
import Definitions.Def_Probability_PortfolioNullDial
import Definitions.Def_Probability_PortfolioRegretCore
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

theorem Probability.PortfolioRegret.gap_le_sum_pair_swaps[Fintype Ω] [Fintype O] [DecidableEq O]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) {s₀ : S}
    (hs₀ : EV w (fun ω => cost ω s₀) = bestConstant w cost) :
    bestConstant w cost - dialValue w cost obs
      ≤ ∑ t ∈ univ.erase s₀,
          min (swapMassFun (fun o => fiberVal w cost obs o s₀)
                (fun o => fiberVal w cost obs o t))
              (swapMassFun (fun o => fiberVal w cost obs o t)
                (fun o => fiberVal w cost obs o s₀)) := by sorry
