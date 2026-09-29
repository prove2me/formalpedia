-- Prove2me | Theorems.Thm_RLHF_schedule_collapse
-- name    : RLHF.schedule_collapse
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:47:32.357095+00:00
-- url     : https://prove2.me/theorems/83643075-132f-4e09-97aa-d2909f1aa40e
-- title:
--   Schedule collapse.
-- statement:
--   **Schedule collapse.**  Any finite temperature schedule is equivalent to a single RLHF
--   step, at an arbitrary temperature `β`, with the reward model `∑ᵢ (β/βᵢ) rᵢ`.
--
--   ```lean
--   theorem RLHF.schedule_collapse{β : ℝ} (hβ : β ≠ 0) :
--       ∀ (L : List (ℝ × (Ω → ℝ))) (p : Ω → ℝ), IsPosDist p → (∀ br ∈ L, br.1 ≠ 0) →
--         runSchedule p L
--           = gibbsPolicy β (fun y => (L.map (fun br => (β / br.1) * br.2 y)).sum) p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFScheduleCollapse.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFScheduleCollapse.lean#L81

-- Thm stub generated from NumberTheory/RLHFScheduleCollapse.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFRewardIdentifiability
import Definitions.Def_NumberTheory_RLHFScheduleCollapse

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

open RLHF

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## 1. Only the ratio reward/temperature matters -/




/-! ## 2. Arbitrary finite schedules -/

theorem RLHF.schedule_collapse{β : ℝ} (hβ : β ≠ 0) :
    ∀ (L : List (ℝ × (Ω → ℝ))) (p : Ω → ℝ), IsPosDist p → (∀ br ∈ L, br.1 ≠ 0) →
      runSchedule p L
        = gibbsPolicy β (fun y => (L.map (fun br => (β / br.1) * br.2 y)).sum) p := by sorry
