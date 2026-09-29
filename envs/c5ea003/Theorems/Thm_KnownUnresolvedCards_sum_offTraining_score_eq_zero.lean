-- Prove2me | Theorems.Thm_KnownUnresolvedCards_sum_offTraining_score_eq_zero
-- name    : KnownUnresolvedCards.sum_offTraining_score_eq_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:40:16.210539+00:00
-- url     : https://prove2.me/theorems/892d4812-ec0e-4e92-b571-50220215297f
-- title:
--   The No-Free-Lunch involution.
-- statement:
--   **The No-Free-Lunch involution.**  If the learner `L` depends on the target
--   only through its labels on `T`, then at any point `x ∉ T` the `±1` score sums to
--   zero over all targets: flipping the label at `x` leaves the hypothesis unchanged
--   and negates the score.
--
--   ```lean
--   theorem KnownUnresolvedCards.sum_offTraining_score_eq_zero(T : Finset X) (x : X) (hx : x ∉ T)
--       (L : (X → Bool) → (X → Bool))
--       (hL : ∀ f g : X → Bool, (∀ y ∈ T, f y = g y) → L f = L g) :
--       ∑ f : X → Bool, (if L f x = f x then (1 : ℚ) else -1) = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/KnownUnresolvedCards/NoFreeLunch.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/KnownUnresolvedCards/NoFreeLunch.lean#L68

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

theorem KnownUnresolvedCards.sum_offTraining_score_eq_zero(T : Finset X) (x : X) (hx : x ∉ T)
    (L : (X → Bool) → (X → Bool))
    (hL : ∀ f g : X → Bool, (∀ y ∈ T, f y = g y) → L f = L g) :
    ∑ f : X → Bool, (if L f x = f x then (1 : ℚ) else -1) = 0 := by sorry
