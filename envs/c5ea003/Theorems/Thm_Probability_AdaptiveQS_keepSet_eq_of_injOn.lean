-- Prove2me | Theorems.Thm_Probability_AdaptiveQS_keepSet_eq_of_injOn
-- name    : Probability.AdaptiveQS.keepSet_eq_of_injOn
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:53:54.327585+00:00
-- url     : https://prove2.me/theorems/506fe7df-db0f-4f7e-b934-8abcb2ff6d9c
-- title:
--   No ties, no slack.
-- statement:
--   **No ties, no slack.**  If the rate dial is injective on the targets, the threshold
--   policy retains exactly the minimal separated schedule.
--
--   ```lean
--   theorem Probability.AdaptiveQS.keepSet_eq_of_injOn{s T : Finset ι} {r : ι → ℝ} (hTs : T ⊆ s)
--       (hT : T.Nonempty) (hsep : Separated s T r) (hinj : Set.InjOn r s) :
--       keepSet s r (T.inf' hT r) = T := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AdaptiveQSTieSlack.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AdaptiveQSTieSlack.lean#L80

-- Thm stub generated from Probability/AdaptiveQSTieSlack.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSPrefixOptimality
import Definitions.Def_Probability_AdaptiveQSResidueRate
import Definitions.Def_Probability_AdaptiveQSSkipFlip
import Definitions.Def_Probability_AdaptiveQSTieSlack
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Tie-multiplicity slack of threshold deferral, and its arithmetic vanishing

`AdaptiveQSPrefixOptimality.lean` collapsed the deployment policy space: the minimum-work
quota-feasible schedule can always be taken *separated*, and a separated schedule sits
inside the dial threshold set `keepSet s r θ` at `θ = ` its own minimal rate.  That left
exactly one gap, recorded as the open direction "Tie-Multiplicity Slack of Threshold
Deferral": the threshold set retains *every* target whose rate equals `θ`, so it can be
strictly larger than the minimal schedule.

This file closes that gap.

* `tieClass` — the targets sitting exactly on the threshold.
* `keepSet_sdiff_eq_tieClass_sdiff` — the excess of the threshold set over a separated
  schedule is *exactly* the tie class outside it (an equality of sets, not a bound).
* `keepSet_card_eq_add_tie_slack` — hence the cardinality identity
  `|keepSet| = |T| + |tieClass \ T|`: the extra work done by the threshold policy is the
  tie multiplicity, nothing more.
* `keepSet_eq_of_injOn` — if the rate dial is injective on the targets there are no ties,
  and the threshold policy reproduces the minimal schedule *on the nose*.
* `periodRate_injOn_admissible` — the arithmetic input: on a factor base of admissible odd
  primes the exact rate `2/p` is injective, because `p ↦ 2/p` is.
* `factorBase_threshold_exactly_minimal` — the capstone: on such a factor base, whenever a
  relation quota is attainable there is a threshold whose retained set meets the quota, has
  the *minimum possible* cardinality among all quota-feasible schedules, and has throughput
  at least that of sieving the whole factor base.
* Lab note `labnote_tie_slack_is_one`: a three-target instance with a genuine tie, where the
  threshold policy does one unit of work more than the optimum — showing the slack term is
  not vacuous and that injectivity is doing real work.
-/

open Probability.AdaptiveQS

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ## The tie class of a threshold -/

theorem Probability.AdaptiveQS.keepSet_eq_of_injOn{s T : Finset ι} {r : ι → ℝ} (hTs : T ⊆ s)
    (hT : T.Nonempty) (hsep : Separated s T r) (hinj : Set.InjOn r s) :
    keepSet s r (T.inf' hT r) = T := by sorry
