-- Prove2me | solution 1 for Probability.PortfolioRegret.inf_p_fin_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T00:28:26.930161+00:00
-- url     : https://prove2.me/submissions/18411cbf-bd5e-4059-b1f7-9bb98d2897b4

-- Sol generated from Probability/PortfolioNullDial.lean
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioEpsInvisible
import Definitions.Def_Probability_PortfolioNullDial
import Definitions.Def_Probability_PortfolioRegretCore
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
theorem solution(f : Fin 3 → ℚ) :
    (univ : Finset (Fin 3)).inf' univ_nonempty f = min (f 0) (min (f 1) (f 2)) := by
  refine le_antisymm (le_min (Finset.inf'_le _ (mem_univ 0))
    (le_min (Finset.inf'_le _ (mem_univ 1)) (Finset.inf'_le _ (mem_univ 2)))) ?_
  refine Finset.le_inf' _ _ fun s _ => ?_
  fin_cases s
  · exact min_le_left _ _
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · exact le_trans (min_le_right _ _) (min_le_right _ _)
