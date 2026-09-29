-- Prove2me | solution 1 for Probability.PortfolioRegret.gap_eq_inf_fiberRegret
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:58:54.420572+00:00
-- url     : https://prove2.me/submissions/4ca1888f-b317-4949-a31e-32e19e0fe937

-- Sol generated from Probability/PortfolioNullDial.lean
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioEpsInvisible
import Definitions.Def_Probability_PortfolioNullDial
import Definitions.Def_Probability_PortfolioRegretCore
import Theorems.Thm_Probability_PortfolioRegret_fiberRegret_eq
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# What a null dial measurement actually certifies

Sixth cycle of the portfolio programme.  `Probability.PortfolioRegretCore` proves
that an *invisible* observation gives no scheduling edge (`no_dial_edge`), and
`Probability.PortfolioEpsInvisible` makes that quantitative and shows that the
naive converse fails: a measured dial gain of `0` does **not** imply that the
observation is `ε`-invisible.  The obvious question left open by that cycle is
what a null measurement *does* certify.  This file answers it exactly.

Main results.

* `fiberRegret_eq`, `gap_eq_inf_fiberRegret` — the dial gain
  `bestConstant - dialValue` equals the *smallest fiberwise regret* of a member,
  `min_s ∑_o (fiberVal o s - min_t fiberVal o t)`.  The scheduling gap is thus an
  exact optimisation over members, not merely bounded by one.
* `gap_zero_iff_exists_fiberwise_optimal` — **the correct converse.**  The dial
  gain vanishes **iff** some single member minimises the conditional cost on
  *every* fiber.  So the measured `Δ = 0.000` certifies exactly a fiberwise
  champion; it certifies neither invisibility of the observation nor absence of
  member-discriminating information.  (Direction 1 of `FUTURE_DIRECTIONS.md`,
  answered in the corrected — centred, i.e. difference-based — form.)
* `min_sum_sub_sum_min`, `two_member_gap` — for a two-member portfolio the gain
  is *exactly* `min` of the two **swap masses** `∑_o (fiberVal o s - fiberVal o t)^+`:
  a dial earns precisely the smaller of the two directions in which the members
  trade places, and `two_member_dial_edge_iff` turns this into a decidable test.
* `swap_hidden_by_third_member` — the pair certificate is *not* visible at the
  portfolio level: an explicit three-member portfolio has gain exactly `0` while
  two of its members swap with positive mass on the fibers.  A null dial hides
  arbitrarily much pairwise structure behind a dominating third member.
* `dialValueOn_erase_of_fiberwise_dominates`,
  `bestConstantOn_erase_of_fiberwise_dominates` — **fiberwise dominance is an
  elimination certificate**: deleting a member that is beaten on every fiber
  changes neither the optimal dial value nor the best static value.  This is the
  safe middle rung between the pointwise test of
  `Probability.PortfolioElimination` and the unsafe mean comparison refuted there.

Everything is finite and rational.
-/

open Probability.PortfolioRegret

open Finset

variable {Ω O S : Type*}

/-! ## The dial gain as an optimisation over members -/






/-! ## Two members: the gain is the smaller swap mass -/









/-! ## A null dial hides pairwise structure -/





/-! ## Fiberwise dominance is an elimination certificate -/








open Probability.PortfolioRegret in
theorem solution[Fintype Ω] [Fintype O] [DecidableEq O] [Fintype S] [Nonempty S]
    (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) :
    bestConstant w cost - dialValue w cost obs
      = univ.inf' univ_nonempty (fiberRegret w cost obs) := by
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := S))
    (fun s => EV w (fun ω => cost ω s))
  obtain ⟨s₁, -, hs₁⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := S))
    (fiberRegret w cost obs)
  have hb : bestConstant w cost = EV w (fun ω => cost ω s₀) := hs₀
  refine le_antisymm ?_ ?_
  · rw [hs₁, fiberRegret_eq]
    have : bestConstant w cost ≤ EV w (fun ω => cost ω s₁) := Finset.inf'_le _ (mem_univ s₁)
    linarith
  · have h1 : univ.inf' univ_nonempty (fiberRegret w cost obs) ≤ fiberRegret w cost obs s₀ :=
      Finset.inf'_le _ (mem_univ s₀)
    rw [fiberRegret_eq] at h1
    linarith [hb]
