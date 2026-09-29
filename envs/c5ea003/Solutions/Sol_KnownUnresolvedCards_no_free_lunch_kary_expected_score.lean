-- Prove2me | solution 1 for KnownUnresolvedCards.no_free_lunch_kary_expected_score
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:03:39.743053+00:00
-- url     : https://prove2.me/submissions/7c624124-3e42-4073-a76c-5996d444d0ea

-- Sol generated from MachineLearning/KnownUnresolvedCards/NoFreeLunch.lean
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
import Definitions.Def_MachineLearning_KnownUnresolvedCards_NoFreeLunch
import Theorems.Thm_KnownUnresolvedCards_E_def
import Theorems.Thm_KnownUnresolvedCards_expected_total_eq_certain_sum
import Theorems.Thm_KnownUnresolvedCards_sum_offTraining_kary_score_eq_zero
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
theorem solution(T : Finset X) (L : (X → ZMod k) → (X → ZMod k))
    (hL : ∀ f g : X → ZMod k, (∀ y ∈ T, f y = g y) → L f = L g)
    (hT : ∀ f : X → ZMod k, ∀ y ∈ T, L f y = f y) :
    E (fun f : X → ZMod k => ∑ y : X, (if L f y = f y then ((k : ℚ) - 1) else -1))
      = ((k : ℚ) - 1) * (T.card : ℚ) := by
  have hres : ∀ y ∈ T,
      Resolved (fun f : X → ZMod k => if L f y = f y then ((k : ℚ) - 1) else -1) ((k : ℚ) - 1) := by
    intro y hy f
    exact if_pos (hT f y hy)
  have hfair : ∀ y ∉ T,
      Fair (fun f : X → ZMod k => if L f y = f y then ((k : ℚ) - 1) else -1) := by
    intro y hy
    rw [Fair, E_def, sum_offTraining_kary_score_eq_zero T y hy L hL, zero_div]
  have := expected_total_eq_certain_sum (Ω := X → ZMod k)
    (fun y f => if L f y = f y then ((k : ℚ) - 1) else -1) T (fun _ => (k : ℚ) - 1) hres hfair
  rw [this, Finset.sum_const, nsmul_eq_mul]
  ring
