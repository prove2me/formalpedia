-- Prove2me | Definitions.Def_Probability_PortfolioNullDial
-- name    : Probability_PortfolioNullDial
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:34:01.994523+00:00
-- url     : https://prove2.me/theorems/6a1c8377-4021-45ce-9da4-534a2496b154
-- title:
--   Aether Catalog definitions — Probability_PortfolioNullDial
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PortfolioNullDial`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PortfolioNullDial.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioEpsInvisible
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

namespace Probability.PortfolioRegret

open Finset

variable {Ω O S : Type*}

/-! ## The dial gain as an optimisation over members -/

/-- The **fiberwise regret** of member `s`: the total amount by which `s` is beaten
by the fiberwise best member, summed over the fibers of the observation. -/
noncomputable def fiberRegret [Fintype Ω] [Fintype O] [DecidableEq O] [Fintype S] [Nonempty S]
    (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) (s : S) : ℚ :=
  ∑ o, (fiberVal w cost obs o s - univ.inf' univ_nonempty (fiberVal w cost obs o))





/-! ## Two members: the gain is the smaller swap mass -/

/-- The **swap mass** of `f` over `g`: the total excess of `f` on the fibers where
`f` loses. -/
def swapMassFun [Fintype O] (f g : O → ℚ) : ℚ := ∑ o, max (f o - g o) 0








/-! ## A null dial hides pairwise structure -/

/-- Uniform weights on two instances. -/
def swapW : Fin 2 → ℚ := fun _ => 1/2

/-- Three members on two instances: members `0` and `1` trade places (each costing
`1` on its own instance and `3` on the other), while member `2` costs `0` on both
and hence dominates them. -/
def swapCost : Fin 2 → Fin 3 → ℚ :=
  fun o s => if s = 2 then 0 else if (s : ℕ) = (o : ℕ) then 1 else 3



/-! ## Fiberwise dominance is an elimination certificate -/

/-- Optimal dial value of the sub-portfolio `T`. -/
noncomputable def dialValueOn [Fintype Ω] [Fintype O] [DecidableEq O]
    (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) (T : Finset S) (hT : T.Nonempty) : ℚ :=
  ∑ o, T.inf' hT (fiberVal w cost obs o)

/-- Best static value of the sub-portfolio `T`. -/
noncomputable def bestConstantOn [Fintype Ω] (w : Ω → ℚ) (cost : Ω → S → ℚ)
    (T : Finset S) (hT : T.Nonempty) : ℚ :=
  T.inf' hT (fun s => EV w (fun ω => cost ω s))





end Probability.PortfolioRegret


