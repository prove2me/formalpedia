-- Prove2me | solution 1 for Probability.PortfolioRegret.fiberRegret_le_sum_swapMass
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:56:05.951786+00:00
-- url     : https://prove2.me/submissions/e4a156d6-f994-4539-89fb-5cd88a256a21

-- Sol generated from Probability/PortfolioIrredundant.lean
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






open Probability.PortfolioRegret in
theorem solution[Fintype Ω] [Fintype O] [DecidableEq O]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) (s₀ : S) :
    fiberRegret w cost obs s₀
      ≤ ∑ t ∈ univ.erase s₀,
          swapMassFun (fun o => fiberVal w cost obs o s₀) (fun o => fiberVal w cost obs o t) := by
  have hpt : ∀ o : O,
      fiberVal w cost obs o s₀ - univ.inf' univ_nonempty (fiberVal w cost obs o)
        ≤ ∑ t ∈ univ.erase s₀, max (fiberVal w cost obs o s₀ - fiberVal w cost obs o t) 0 := by
    intro o
    obtain ⟨t₀, -, ht₀⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := S)) (fiberVal w cost obs o)
    have hnn : ∀ t ∈ univ.erase s₀,
        0 ≤ max (fiberVal w cost obs o s₀ - fiberVal w cost obs o t) 0 :=
      fun t _ => le_max_right _ _
    by_cases h : t₀ = s₀
    · have : fiberVal w cost obs o s₀ - univ.inf' univ_nonempty (fiberVal w cost obs o) = 0 := by
        rw [ht₀, h]; ring
      rw [this]
      exact Finset.sum_nonneg hnn
    · have hmem : t₀ ∈ univ.erase s₀ := Finset.mem_erase.mpr ⟨h, mem_univ t₀⟩
      have hle : fiberVal w cost obs o s₀ - univ.inf' univ_nonempty (fiberVal w cost obs o)
          ≤ max (fiberVal w cost obs o s₀ - fiberVal w cost obs o t₀) 0 := by
        rw [ht₀]; exact le_max_left _ _
      exact hle.trans (Finset.single_le_sum hnn hmem)
  calc fiberRegret w cost obs s₀
      ≤ ∑ o, ∑ t ∈ univ.erase s₀,
          max (fiberVal w cost obs o s₀ - fiberVal w cost obs o t) 0 :=
        Finset.sum_le_sum fun o _ => hpt o
    _ = ∑ t ∈ univ.erase s₀, ∑ o : O,
          max (fiberVal w cost obs o s₀ - fiberVal w cost obs o t) 0 := Finset.sum_comm
    _ = ∑ t ∈ univ.erase s₀,
          swapMassFun (fun o => fiberVal w cost obs o s₀) (fun o => fiberVal w cost obs o t) := rfl
