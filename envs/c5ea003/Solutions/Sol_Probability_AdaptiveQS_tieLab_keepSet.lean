-- Prove2me | solution 1 for Probability.AdaptiveQS.tieLab_keepSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:40:21.918564+00:00
-- url     : https://prove2.me/submissions/5cf2133f-590a-4740-a484-d11cc9c61fe7

-- Sol generated from Probability/AdaptiveQSTieSlack.lean
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




/-! ## Lab note — the slack is real when rates tie

Rates `(3, 3, 1)` on the three targets `{0, 1, 2}` and quota `Q = 3`.  The minimum-work
schedule is a single target, but the threshold at `θ = 3` must retain both targets of rate
`3`: the tie multiplicity is `1`, and the threshold policy does one unit of work more than
the optimum.  This is exactly the term that `keepSet_card_eq_add_tie_slack` isolates, and
that `periodRate_injOn_admissible` rules out arithmetically. -/





open Probability.AdaptiveQS in
theorem solution: keepSet ({0, 1, 2} : Finset ℕ) tieLabRate 3 = {0, 1} := by
  ext i
  simp only [keepSet, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, hri⟩
    rcases hi with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [tieLabRate] at hri
      norm_num at hri
  · rintro (rfl | rfl)
    · exact ⟨by norm_num, by norm_num [tieLabRate]⟩
    · exact ⟨by norm_num, by norm_num [tieLabRate]⟩
