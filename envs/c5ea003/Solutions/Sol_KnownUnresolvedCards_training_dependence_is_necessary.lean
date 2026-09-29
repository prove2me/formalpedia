-- Prove2me | solution 1 for KnownUnresolvedCards.training_dependence_is_necessary
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:03:41.097+00:00
-- url     : https://prove2.me/submissions/61292059-c24b-4eb5-a3fc-b03b1d907574

-- Sol generated from MachineLearning/KnownUnresolvedCards/NoFreeLunch.lean
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
import Definitions.Def_MachineLearning_KnownUnresolvedCards_NoFreeLunch
import Theorems.Thm_KnownUnresolvedCards_E_const
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









open KnownUnresolvedCards in
theorem solution[Nonempty X] :
    ∃ L : (X → Bool) → (X → Bool),
      (∀ f : X → Bool, ∀ y ∈ (∅ : Finset X), L f y = f y)
      ∧ E (fun f : X → Bool => ∑ y : X, (if L f y = f y then (1 : ℚ) else -1))
          = (Fintype.card X : ℚ)
      ∧ ((∅ : Finset X).card : ℚ) ≠ (Fintype.card X : ℚ) := by
  refine ⟨id, by simp, ?_, ?_⟩
  · have : (fun f : X → Bool => ∑ _y : X, (1 : ℚ)) =
        fun _ : X → Bool => (Fintype.card X : ℚ) := by
      funext f; rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    simp only [id_eq, if_pos]
    rw [this, E_const]
  · have : 0 < Fintype.card X := Fintype.card_pos
    simp only [Finset.card_empty, Nat.cast_zero]
    exact fun h => by
      have : (Fintype.card X : ℚ) = 0 := h.symm
      exact absurd (by exact_mod_cast this) (by omega)
