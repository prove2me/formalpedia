-- Prove2me | Theorems.Thm_KnownUnresolvedCards_sum_orbit_kary
-- name    : KnownUnresolvedCards.sum_orbit_kary
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:40:43.713076+00:00
-- url     : https://prove2.me/theorems/5b9f4e74-8b83-411c-8d75-e438cc2325bd
-- title:
--   Along a single orbit of the cyclic shift the fair-odds score cancels
-- statement:
--   Along a single orbit of the cyclic shift the fair-odds score cancels
--   exactly: one of the `k` shifts is a hit worth `k - 1`, the other `k - 1` are
--   misses worth `-1`.
--
--   ```lean
--   theorem KnownUnresolvedCards.sum_orbit_kary(b c : ZMod k) :
--       ∑ t : ZMod k, (if b = c + t then ((k : ℚ) - 1) else -1) = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/KnownUnresolvedCards/NoFreeLunch.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/KnownUnresolvedCards/NoFreeLunch.lean#L197

-- Thm stub generated from MachineLearning/KnownUnresolvedCards/NoFreeLunch.lean
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
import Definitions.Def_MachineLearning_KnownUnresolvedCards_NoFreeLunch
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Known versus unresolved cards — V. The learning-theoretic incarnation

The deck of `d` known and `u` unresolved cards has an exact analogue in learning
theory.  Fix a finite domain `X` and let the *target* `f : X → Bool` be uniformly
random.  A learner sees the labels on a training set `T` and outputs a hypothesis
`L f`.  Then:

* the points of `T` are the **known cards** — a consistent learner reproduces
  their labels with certainty;
* the points outside `T` are the **unresolved cards** — and, scored at fair odds,
  each of them has *exactly* zero expected value.

The second statement is Wolpert's No-Free-Lunch phenomenon, and the proof here is
the sharpest possible one: the label-flip at an off-training point is a
fixed-point-free involution of the space of targets which preserves the
hypothesis and negates the score.  The `k`-ary version replaces the involution by
the free action of the cyclic group `ZMod k`.

## Main results

* `sum_offTraining_score_eq_zero` — the involution argument (binary labels).
* `no_free_lunch_expected_score` — **`E[total ±1 score] = |T|` exactly**: the
  learning-theoretic form of "expected payoff is exactly `d`".
* `expected_correct_count` — equivalently, expected accuracy is
  `|T| + (|X| - |T|)/2`: chance level off the training set.
* `training_dependence_is_necessary` — sharpness: a learner allowed to peek at
  off-training labels achieves the maximal score, so the hypothesis that `L`
  depends only on the training labels cannot be dropped.
* `sum_offTraining_kary_score_eq_zero`, `no_free_lunch_kary_expected_score` —
  the `ZMod k` generalisation, with fair odds `(k-1) : 1`.

All of these are instances of the splitting theorem
`expected_total_eq_certain_sum` of `Basic.lean`.
-/


open KnownUnresolvedCards

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Binary labels: the flip involution -/










/-! ## `k`-ary labels: the cyclic action -/

variable {k : ℕ} [NeZero k]

theorem KnownUnresolvedCards.sum_orbit_kary(b c : ZMod k) :
    ∑ t : ZMod k, (if b = c + t then ((k : ℚ) - 1) else -1) = 0 := by sorry
