-- Prove2me | Theorems.Thm_Probability_PortfolioRegret_swap_unbounded_on_irredundant
-- name    : Probability.PortfolioRegret.swap_unbounded_on_irredundant
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:00:03.249161+00:00
-- url     : https://prove2.me/theorems/e406342c-fdb1-4934-846f-a52a1481f65d
-- title:
--   Refutation of the pairwise-swap conjecture.
-- statement:
--   **Refutation of the pairwise-swap conjecture.**  For every ratio `M` there is an
--   *irredundant* three-member portfolio — uniform weights, each instance its own
--   fiber — whose two first members swap with mass `10/3` in both directions while the
--   whole portfolio's dial gain is smaller than `(10/3)/M`.  So no constant, and no
--   function of the number of members, bounds pairwise swap masses by the measured
--   dial gain, even after every fiberwise-eliminable member has been deleted.
--
--   ```lean
--   theorem Probability.PortfolioRegret.swap_unbounded_on_irredundant(M : ℚ) :
--       ∃ e : ℚ, 0 < e ∧ e ≤ 1 ∧
--         (∀ o, 0 ≤ irredW o) ∧ (∑ o, irredW o = 1) ∧
--         IrredundantPortfolio irredW (irredCost e) id ∧
--         M * (bestConstant irredW (irredCost e) - dialValue irredW (irredCost e) id) <
--           min (swapMassFun (fun o => fiberVal irredW (irredCost e) id o 0)
--                 (fun o => fiberVal irredW (irredCost e) id o 1))
--               (swapMassFun (fun o => fiberVal irredW (irredCost e) id o 1)
--                 (fun o => fiberVal irredW (irredCost e) id o 0)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PortfolioIrredundant.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PortfolioIrredundant.lean#L148

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

theorem Probability.PortfolioRegret.swap_unbounded_on_irredundant(M : ℚ) :
    ∃ e : ℚ, 0 < e ∧ e ≤ 1 ∧
      (∀ o, 0 ≤ irredW o) ∧ (∑ o, irredW o = 1) ∧
      IrredundantPortfolio irredW (irredCost e) id ∧
      M * (bestConstant irredW (irredCost e) - dialValue irredW (irredCost e) id) <
        min (swapMassFun (fun o => fiberVal irredW (irredCost e) id o 0)
              (fun o => fiberVal irredW (irredCost e) id o 1))
            (swapMassFun (fun o => fiberVal irredW (irredCost e) id o 1)
              (fun o => fiberVal irredW (irredCost e) id o 0)) := by sorry
