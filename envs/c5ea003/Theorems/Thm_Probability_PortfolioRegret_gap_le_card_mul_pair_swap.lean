-- Prove2me | Theorems.Thm_Probability_PortfolioRegret_gap_le_card_mul_pair_swap
-- name    : Probability.PortfolioRegret.gap_le_card_mul_pair_swap
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:58:30.293538+00:00
-- url     : https://prove2.me/theorems/6d955d6b-6b71-466c-b90d-cafd308090fd
-- title:
--   Corollary in the anti-diagonal form: if every pairwise swap against a best
-- statement:
--   Corollary in the anti-diagonal form: if every pairwise swap against a best
--   static member is at most `c`, the dial gain is at most `(|S| - 1) * c`.  The
--   constant is attained by the anti-diagonal portfolios of
--   `Probability.PortfolioEpsInvisible`.
--
--   ```lean
--   theorem Probability.PortfolioRegret.gap_le_card_mul_pair_swap[Fintype Ω] [Fintype O] [DecidableEq O]
--       [Fintype S] [DecidableEq S] [Nonempty S]
--       (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) {s₀ : S} {c : ℚ}
--       (hs₀ : EV w (fun ω => cost ω s₀) = bestConstant w cost)
--       (hc : ∀ t ∈ univ.erase s₀,
--         min (swapMassFun (fun o => fiberVal w cost obs o s₀) (fun o => fiberVal w cost obs o t))
--             (swapMassFun (fun o => fiberVal w cost obs o t)
--               (fun o => fiberVal w cost obs o s₀)) ≤ c) :
--       bestConstant w cost - dialValue w cost obs ≤ ((Fintype.card S : ℚ) - 1) * c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PortfolioIrredundant.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PortfolioIrredundant.lean#L265

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

theorem Probability.PortfolioRegret.gap_le_card_mul_pair_swap[Fintype Ω] [Fintype O] [DecidableEq O]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) {s₀ : S} {c : ℚ}
    (hs₀ : EV w (fun ω => cost ω s₀) = bestConstant w cost)
    (hc : ∀ t ∈ univ.erase s₀,
      min (swapMassFun (fun o => fiberVal w cost obs o s₀) (fun o => fiberVal w cost obs o t))
          (swapMassFun (fun o => fiberVal w cost obs o t)
            (fun o => fiberVal w cost obs o s₀)) ≤ c) :
    bestConstant w cost - dialValue w cost obs ≤ ((Fintype.card S : ℚ) - 1) * c := by sorry
