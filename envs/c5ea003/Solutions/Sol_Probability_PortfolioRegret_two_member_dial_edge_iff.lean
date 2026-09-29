-- Prove2me | solution 1 for Probability.PortfolioRegret.two_member_dial_edge_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:50:17.360093+00:00
-- url     : https://prove2.me/submissions/e59dd553-8b32-4f5d-ad69-98424b6a20dc

-- Sol generated from Probability/PortfolioNullDial.lean
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioEpsInvisible
import Definitions.Def_Probability_PortfolioNullDial
import Definitions.Def_Probability_PortfolioRegretCore
import Theorems.Thm_Probability_PortfolioRegret_ev_const_eq_sum_fiberVal
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



theorem sum_sub_sum_min [Fintype O] (f g : O → ℚ) :
    (∑ o, f o) - ∑ o, min (f o) (g o) = swapMassFun f g := by
  rw [swapMassFun, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  rcases le_total (f o) (g o) with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]

/-- **Exact two-member gain.**  For two cost profiles on the fibers, the gain of the
fiberwise minimum over the better of the two totals is exactly the smaller of the
two swap masses. -/
theorem min_sum_sub_sum_min [Fintype O] (f g : O → ℚ) :
    min (∑ o, f o) (∑ o, g o) - ∑ o, min (f o) (g o)
      = min (swapMassFun f g) (swapMassFun g f) := by
  have hf := sum_sub_sum_min f g
  have hg := sum_sub_sum_min g f
  have hmin : ∀ o, min (g o) (f o) = min (f o) (g o) := fun o => min_comm _ _
  rw [Finset.sum_congr rfl (fun o _ => hmin o)] at hg
  rcases le_total (∑ o, f o) (∑ o, g o) with h | h
  · rw [min_eq_left h, min_eq_left (by linarith)]
    linarith
  · rw [min_eq_right h, min_eq_right (by linarith)]
    linarith

theorem inf'_fin_two (f : Fin 2 → ℚ) :
    (univ : Finset (Fin 2)).inf' univ_nonempty f = min (f 0) (f 1) := by
  refine le_antisymm (le_min (Finset.inf'_le _ (mem_univ 0)) (Finset.inf'_le _ (mem_univ 1))) ?_
  refine Finset.le_inf' _ _ fun s _ => ?_
  fin_cases s
  · exact min_le_left _ _
  · exact min_le_right _ _


/-- **The two-member scheduling gain, exactly.**  For a portfolio of two members
the dial gain equals the smaller of the two swap masses of their conditional
costs. -/
theorem two_member_gap [Fintype Ω] [Fintype O] [DecidableEq O]
    (w : Ω → ℚ) (cost : Ω → Fin 2 → ℚ) (obs : Ω → O) :
    bestConstant w cost - dialValue w cost obs
      = min (swapMassFun (fun o => fiberVal w cost obs o 0) (fun o => fiberVal w cost obs o 1))
            (swapMassFun (fun o => fiberVal w cost obs o 1) (fun o => fiberVal w cost obs o 0)) := by
  have hb : bestConstant w cost
      = min (∑ o, fiberVal w cost obs o 0) (∑ o, fiberVal w cost obs o 1) := by
    rw [bestConstant, inf'_fin_two, ev_const_eq_sum_fiberVal w cost obs 0,
      ev_const_eq_sum_fiberVal w cost obs 1]
  have hd : dialValue w cost obs
      = ∑ o, min (fiberVal w cost obs o 0) (fiberVal w cost obs o 1) := by
    rw [dialValue]
    exact Finset.sum_congr rfl fun o _ => inf'_fin_two _
  rw [hb, hd]
  exact min_sum_sub_sum_min _ _


/-! ## A null dial hides pairwise structure -/





/-! ## Fiberwise dominance is an elimination certificate -/








open Probability.PortfolioRegret in
theorem solution[Fintype Ω] [Fintype O] [DecidableEq O]
    (w : Ω → ℚ) (cost : Ω → Fin 2 → ℚ) (obs : Ω → O) :
    dialValue w cost obs < bestConstant w cost ↔
      0 < swapMassFun (fun o => fiberVal w cost obs o 0) (fun o => fiberVal w cost obs o 1) ∧
        0 < swapMassFun (fun o => fiberVal w cost obs o 1) (fun o => fiberVal w cost obs o 0) := by
  have h := two_member_gap w cost obs
  constructor
  · intro hlt
    have : 0 < min
        (swapMassFun (fun o => fiberVal w cost obs o 0) (fun o => fiberVal w cost obs o 1))
        (swapMassFun (fun o => fiberVal w cost obs o 1) (fun o => fiberVal w cost obs o 0)) := by
      linarith
    exact lt_min_iff.mp this
  · rintro ⟨h0, h1⟩
    have : 0 < min
        (swapMassFun (fun o => fiberVal w cost obs o 0) (fun o => fiberVal w cost obs o 1))
        (swapMassFun (fun o => fiberVal w cost obs o 1) (fun o => fiberVal w cost obs o 0)) :=
      lt_min_iff.mpr ⟨h0, h1⟩
    linarith
