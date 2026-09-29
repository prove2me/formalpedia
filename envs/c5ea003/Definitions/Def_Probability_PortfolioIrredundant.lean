-- Prove2me | Definitions.Def_Probability_PortfolioIrredundant
-- name    : Probability_PortfolioIrredundant
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:34:37.66321+00:00
-- url     : https://prove2.me/theorems/a8ae4076-f16d-4c82-aa72-b379aefa110d
-- title:
--   Aether Catalog definitions — Probability_PortfolioIrredundant
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PortfolioIrredundant`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PortfolioIrredundant.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioEpsInvisible
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

namespace Probability.PortfolioRegret

open Finset

variable {Ω O S : Type*}

/-- A portfolio is **irredundant** for the observation `obs` when no member is
weakly beaten by another on every fiber — i.e. when the fiberwise elimination rule
`dialValueOn_erase_of_fiberwise_dominates` applies to no pair. -/
def IrredundantPortfolio [Fintype Ω] [DecidableEq O] (w : Ω → ℚ) (cost : Ω → S → ℚ)
    (obs : Ω → O) : Prop :=
  ∀ s t : S, s ≠ t → ∃ o : O, fiberVal w cost obs o t < fiberVal w cost obs o s

/-- Uniform weights on three instances. -/
def irredW : Fin 3 → ℚ := fun _ => 1/3

/-- Three instances (each its own fiber) and three members.  Members `0` and `1`
trade places on the first two fibers and are both bad on the third; member `2` is
cheap (`e`) on the first two fibers and free on the third, but never *dominates*,
because `e > 0` while members `0`, `1` are free on their own fiber. -/
def irredCost (e : ℚ) : Fin 3 → Fin 3 → ℚ := fun o s =>
  if (s : ℕ) = 2 then (if (o : ℕ) = 2 then 0 else e)
  else if (o : ℕ) = 2 then 10
  else if (s : ℕ) = (o : ℕ) then 0 else 10











/-! ## The inequality that *is* true: the gap is covered by pairwise swaps

The refutation above is one-sided.  In the opposite direction the portfolio gain
is always dominated by the pairwise swap masses against a best static member, and
the bound is exactly the anti-diagonal ratio `|S| - 1`. -/





end Probability.PortfolioRegret


