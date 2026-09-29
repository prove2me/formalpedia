-- Prove2me | Theorems.Thm_Probability_AdaptiveQS_exists_separated_minimal_feasible
-- name    : Probability.AdaptiveQS.exists_separated_minimal_feasible
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:53:27.465582+00:00
-- url     : https://prove2.me/theorems/c2a5599e-db0e-4d5f-adaa-0d0c19bec6da
-- title:
--   The minimum-work quota schedule is a sorted prefix.
-- statement:
--   **The minimum-work quota schedule is a sorted prefix.**  If the quota is attainable at
--   all, then it is attained by a set `T` that (i) is of minimal cardinality among all
--   quota-feasible sets and (ii) is separated — every target it works on beats every target it
--   defers.  The deployment therefore never has to search the subset lattice.
--
--   ```lean
--   theorem Probability.AdaptiveQS.exists_separated_minimal_feasible{s : Finset ι} {r : ι → ℝ} {Q : ℝ}
--       (hfeas : ∃ K ⊆ s, Q ≤ ∑ i ∈ K, r i) :
--       ∃ T ⊆ s, Q ≤ ∑ i ∈ T, r i ∧ Separated s T r ∧
--         ∀ K ⊆ s, Q ≤ ∑ i ∈ K, r i → T.card ≤ K.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AdaptiveQSPrefixOptimality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AdaptiveQSPrefixOptimality.lean#L107

-- Thm stub generated from Probability/AdaptiveQSPrefixOptimality.lean
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


omit [DecidableEq ι] in

theorem Probability.AdaptiveQS.exists_separated_minimal_feasible{s : Finset ι} {r : ι → ℝ} {Q : ℝ}
    (hfeas : ∃ K ⊆ s, Q ≤ ∑ i ∈ K, r i) :
    ∃ T ⊆ s, Q ≤ ∑ i ∈ T, r i ∧ Separated s T r ∧
      ∀ K ⊆ s, Q ≤ ∑ i ∈ K, r i → T.card ≤ K.card := by sorry
