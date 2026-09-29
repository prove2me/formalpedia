-- Prove2me | solution 1 for Probability.AdaptiveQS.separated_subset_keepSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:28:12.435705+00:00
-- url     : https://prove2.me/submissions/abf57f97-2c5b-42a3-ac12-59eb4c19a79c

-- Sol generated from Probability/AdaptiveQSPrefixOptimality.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSPrefixOptimality
import Definitions.Def_Probability_AdaptiveQSSkipFlip
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Prefix optimality of deferral under a relation quota

Experiment 559 (round-73 #2, `ADAPT-NULL-EQUALIZER / SKIP-FLIP-WINS`) ended with the
deployment recommendation *defer, don't sieve deeper*: a dial threshold `θ = q20` skipped
`28.3%` of the work while retaining `89.5%` of the relations.  `AdaptiveQSSkipFlip.lean`
proved the sign of that flip (throughput never falls, and strictly rises once a genuinely
worse target is deferred), and `AdaptiveQSThresholdTradeoff.lean` proved the honest
boundary (total retained yield falls with the threshold).

What was left open — and is what a deployment actually has to decide — is the *policy
space*: the sieve must collect a quota `Q` of relations, and one may in principle pick any
subset `K ⊆ s` of targets to work on.  This file closes that question:

* `exists_max_sum_card_subset` — a maximal-yield subset of each fixed cardinality exists;
* `separated_of_max_sum` — **every** such maximiser is *separated*: each retained target
  beats every deferred one.  This is an exchange argument, and it is the reason a sort is
  enough: no maximiser can be "interleaved" with the deferred set.
* `exists_separated_of_quota` — any quota-feasible schedule is dominated, at the same cost,
  by a separated one;
* `exists_separated_minimal_feasible` — the **minimum-work** quota-feasible schedule can
  always be taken separated;
* `separated_subset_keepSet`, `keepSet_sum_ge_of_separated` — a separated set is contained
  in a dial threshold set `keepSet s r θ` at `θ = min` of its own rates, and that threshold
  set is again quota-feasible;
* `quota_threshold_policy` — the capstone: whenever the quota is attainable at all, it is
  attained by a *single threshold* on the rate dial, and that threshold policy has
  throughput at least that of sieving everything.

So the deployment's policy space collapses from `2^|s|` subsets to one real number: the
skip-flip's `θ` is not just a good heuristic, it is the shape of the optimum.  The
hypotheses are exactly "rates are nonnegative" — no calibration, no independence.
-/

open Probability.AdaptiveQS

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ## Separated schedules -/




/-! ## Quota feasibility -/



/-! ## A separated schedule is a dial threshold -/





/-! ## Lab notes — a machine-checked three-target instance

Rates `r = (3, 1, 0)` on `s = {0, 1, 2} ⊆ ℕ` with quota `Q = 3`.  The minimum-work feasible
schedule is the single top target `{0}`: one target instead of three, i.e. `66.7%` of the
work deferred at `100%` of the quota, and the throughput rises from `4/3` to `3`.  Every
number below is proved, not asserted. -/





open Probability.AdaptiveQS in
omit [DecidableEq ι] in
theorem solution{s T : Finset ι} {r : ι → ℝ} (hTs : T ⊆ s)
    (hT : T.Nonempty) :
    T ⊆ keepSet s r (T.inf' hT r) := by
  intro i hi
  rw [keepSet, Finset.mem_filter]
  exact ⟨hTs hi, Finset.inf'_le r hi⟩
