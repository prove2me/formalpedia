-- Prove2me | Theorems.Thm_Probability_AdaptiveQS_periodRate_injOn_admissible
-- name    : Probability.AdaptiveQS.periodRate_injOn_admissible
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:54:03.353985+00:00
-- url     : https://prove2.me/theorems/b7d5cef6-cca4-4d66-8a16-4aa70e602a93
-- title:
--   The exact rates of a factor base are pairwise distinct.
-- statement:
--   **The exact rates of a factor base are pairwise distinct.**  Since an admissible odd
--   prime has rate exactly `2/p`, and `p ↦ 2/p` is injective on positive integers, no two
--   factor-base primes tie.
--
--   ```lean
--   theorem Probability.AdaptiveQS.periodRate_injOn_admissible{N : ℤ} {FB : Finset ℕ} (hFB : AdmissibleFB N FB) :
--       Set.InjOn (periodRate N) FB := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AdaptiveQSTieSlack.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AdaptiveQSTieSlack.lean#L105

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





/-! ## The arithmetic case: rates `2/p` are pairwise distinct -/

theorem Probability.AdaptiveQS.periodRate_injOn_admissible{N : ℤ} {FB : Finset ℕ} (hFB : AdmissibleFB N FB) :
    Set.InjOn (periodRate N) FB := by sorry
