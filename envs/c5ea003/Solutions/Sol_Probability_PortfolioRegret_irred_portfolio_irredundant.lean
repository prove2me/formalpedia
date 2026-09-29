-- Prove2me | solution 1 for Probability.PortfolioRegret.irred_portfolio_irredundant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:01:10.088325+00:00
-- url     : https://prove2.me/submissions/6a05b538-88fb-4f5c-b251-62cc8af1b295

-- Sol generated from Probability/PortfolioIrredundant.lean
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioEpsInvisible
import Definitions.Def_Probability_PortfolioIrredundant
import Definitions.Def_Probability_PortfolioNullDial
import Definitions.Def_Probability_PortfolioRegretCore
import Theorems.Thm_Probability_PortfolioRegret_fiberVal_id
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




theorem fiberVal_irred (e : ℚ) (o s : Fin 3) :
    fiberVal irredW (irredCost e) id o s = irredW o * irredCost e o s :=
  fiberVal_id irredW (irredCost e) o s










/-! ## The inequality that *is* true: the gap is covered by pairwise swaps

The refutation above is one-sided.  In the opposite direction the portfolio gain
is always dominated by the pairwise swap masses against a best static member, and
the bound is exactly the anti-diagonal ratio `|S| - 1`. -/






open Probability.PortfolioRegret in
theorem solution{e : ℚ} (he : 0 < e) :
    IrredundantPortfolio irredW (irredCost e) id := by
  have hv : ∀ o s, fiberVal irredW (irredCost e) id o s = irredW o * irredCost e o s :=
    fiberVal_irred e
  intro s t hst
  fin_cases s <;> fin_cases t
  · exact absurd rfl hst
  · exact ⟨1, by rw [hv, hv]; norm_num [irredW, irredCost, Fin.ext_iff]⟩
  · exact ⟨2, by rw [hv, hv]; norm_num [irredW, irredCost, Fin.ext_iff]⟩
  · exact ⟨0, by rw [hv, hv]; norm_num [irredW, irredCost, Fin.ext_iff]⟩
  · exact absurd rfl hst
  · exact ⟨2, by rw [hv, hv]; norm_num [irredW, irredCost, Fin.ext_iff]⟩
  · exact ⟨0, by rw [hv, hv]; norm_num [irredW, irredCost, Fin.ext_iff]; linarith⟩
  · exact ⟨1, by rw [hv, hv]; norm_num [irredW, irredCost, Fin.ext_iff]; linarith⟩
  · exact absurd rfl hst
