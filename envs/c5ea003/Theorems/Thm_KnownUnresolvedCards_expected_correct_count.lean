-- Prove2me | Theorems.Thm_KnownUnresolvedCards_expected_correct_count
-- name    : KnownUnresolvedCards.expected_correct_count
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:40:57.99681+00:00
-- url     : https://prove2.me/theorems/6f0bf863-a40b-497f-bb4b-df26a413361e
-- title:
--   Expected accuracy is chance level off the training set.
-- statement:
--   **Expected accuracy is chance level off the training set.**  The expected
--   number of correctly predicted points is `(|T| + |X|)/2`, i.e. all of `T` plus
--   exactly half of the rest.
--
--   ```lean
--   theorem KnownUnresolvedCards.expected_correct_count(T : Finset X) (L : (X → Bool) → (X → Bool))
--       (hL : ∀ f g : X → Bool, (∀ y ∈ T, f y = g y) → L f = L g)
--       (hT : ∀ f : X → Bool, ∀ y ∈ T, L f y = f y) :
--       E (fun f : X → Bool => ∑ y : X, (if L f y = f y then (1 : ℚ) else 0))
--         = ((T.card : ℚ) + (Fintype.card X : ℚ)) / 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/KnownUnresolvedCards/NoFreeLunch.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/KnownUnresolvedCards/NoFreeLunch.lean#L119

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

theorem KnownUnresolvedCards.expected_correct_count(T : Finset X) (L : (X → Bool) → (X → Bool))
    (hL : ∀ f g : X → Bool, (∀ y ∈ T, f y = g y) → L f = L g)
    (hT : ∀ f : X → Bool, ∀ y ∈ T, L f y = f y) :
    E (fun f : X → Bool => ∑ y : X, (if L f y = f y then (1 : ℚ) else 0))
      = ((T.card : ℚ) + (Fintype.card X : ℚ)) / 2 := by sorry
