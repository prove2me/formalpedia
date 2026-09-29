-- Prove2me | Definitions.Def_NumberTheory_RLHFScheduleCollapse
-- name    : NumberTheory_RLHFScheduleCollapse
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:16:41.701022+00:00
-- url     : https://prove2.me/theorems/646a3f35-ada5-4117-9fd5-bf72f39bdac5
-- title:
--   Aether Catalog definitions — NumberTheory_RLHFScheduleCollapse
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.RLHFScheduleCollapse`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/RLHFScheduleCollapse.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFRewardIdentifiability

/-!
# Temperature schedules collapse: iterated RLHF is single-step RLHF

This file settles Conjecture 4 of `FUTURE_DIRECTIONS.md`.  `RLHF.gibbs_compose` shows that
two alignment steps *at the same temperature* add their reward models.  A real training
pipeline, however, runs a **schedule**: step `i` uses its own KL coefficient `β i` and its
own reward `r i`.  We show that the whole schedule collapses:

* `RLHF.gibbsPolicy_rescale` — only the ratio `r / β` matters, so a step at temperature `β'`
  is a step at temperature `β` with the rescaled reward `(β/β') r`.
* `RLHF.gibbs_schedule_two` — a two-step schedule equals one step with reward
  `(β/β₁) r₁ + (β/β₂) r₂`.
* `RLHF.runSchedule` and `RLHF.schedule_collapse` — an arbitrary finite schedule, folded left
  over a list of (temperature, reward) pairs, equals a single RLHF step at any chosen
  temperature `β` with reward `∑ᵢ (β/βᵢ) rᵢ`.
* `RLHF.schedule_reachable_in_one_step` — consequently no multi-step schedule can reach a
  policy that is unreachable in one step: the reachable set is exactly the orbit of the
  one-step map, so iterated RLHF adds no expressive power (only optimization dynamics).
* `RLHF.zeta_schedule_collapse` — arithmetic payoff: for Dirichlet rewards on a smooth-number
  response space, a schedule with sharpnesses `s₁, s₂` at *arbitrary* temperatures produces
  the truncated zeta policy of exponent `s₁ + s₂`, independently of the schedule.  The
  alignment schedule acts on Dirichlet exponents by addition, i.e. by multiplication of the
  associated Dirichlet series.
-/

namespace RLHF

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## 1. Only the ratio reward/temperature matters -/




/-! ## 2. Arbitrary finite schedules -/

/-- Run a finite RLHF schedule: a list of (KL coefficient, reward model) pairs applied in
order, starting from the SFT reference `p`. -/
noncomputable def runSchedule (p : Ω → ℝ) : List (ℝ × (Ω → ℝ)) → (Ω → ℝ) :=
  List.foldl (fun q br => gibbsPolicy br.1 br.2 q) p





/-! ## 3. Arithmetic corollary: Dirichlet exponents add along any schedule -/

variable {A B : ℕ}



end RLHF


