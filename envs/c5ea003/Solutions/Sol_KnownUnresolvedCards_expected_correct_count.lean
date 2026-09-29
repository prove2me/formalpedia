-- Prove2me | solution 1 for KnownUnresolvedCards.expected_correct_count
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:46:22.306808+00:00
-- url     : https://prove2.me/submissions/6a4bc166-175f-47f3-b5f9-2259e511e2cd

-- Sol generated from MachineLearning/KnownUnresolvedCards/NoFreeLunch.lean
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
import Definitions.Def_MachineLearning_KnownUnresolvedCards_NoFreeLunch
import Theorems.Thm_KnownUnresolvedCards_E_add
import Theorems.Thm_KnownUnresolvedCards_E_const
import Theorems.Thm_KnownUnresolvedCards_E_def
import Theorems.Thm_KnownUnresolvedCards_E_smul
import Theorems.Thm_KnownUnresolvedCards_expected_total_eq_certain_sum
import Theorems.Thm_KnownUnresolvedCards_sum_offTraining_score_eq_zero
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






/-- Off the training set, the `±1` score is a *fair* card. -/
theorem offTraining_fair (T : Finset X) (x : X) (hx : x ∉ T)
    (L : (X → Bool) → (X → Bool))
    (hL : ∀ f g : X → Bool, (∀ y ∈ T, f y = g y) → L f = L g) :
    Fair (fun f : X → Bool => if L f x = f x then (1 : ℚ) else -1) := by
  rw [Fair, E_def, sum_offTraining_score_eq_zero T x hx L hL, zero_div]

/-- **No Free Lunch, deck form.**  A learner that is consistent on the training
set `T` and that depends on the target only through the training labels has
expected total `±1` score exactly `|T|`, whatever the algorithm: the `|T|`
resolved points pay one unit each and the unresolved points pay nothing on
average. -/
theorem no_free_lunch_expected_score (T : Finset X) (L : (X → Bool) → (X → Bool))
    (hL : ∀ f g : X → Bool, (∀ y ∈ T, f y = g y) → L f = L g)
    (hT : ∀ f : X → Bool, ∀ y ∈ T, L f y = f y) :
    E (fun f : X → Bool => ∑ y : X, (if L f y = f y then (1 : ℚ) else -1)) = (T.card : ℚ) := by
  have hres : ∀ y ∈ T, Resolved (fun f : X → Bool => if L f y = f y then (1 : ℚ) else -1) 1 := by
    intro y hy f
    exact if_pos (hT f y hy)
  have hfair : ∀ y ∉ T, Fair (fun f : X → Bool => if L f y = f y then (1 : ℚ) else -1) :=
    fun y hy => offTraining_fair T y hy L hL
  have := expected_total_eq_certain_sum (Ω := X → Bool)
    (fun y f => if L f y = f y then (1 : ℚ) else -1) T (fun _ => 1) hres hfair
  simpa using this



/-! ## `k`-ary labels: the cyclic action -/

variable {k : ℕ} [NeZero k]









open KnownUnresolvedCards in
theorem solution(T : Finset X) (L : (X → Bool) → (X → Bool))
    (hL : ∀ f g : X → Bool, (∀ y ∈ T, f y = g y) → L f = L g)
    (hT : ∀ f : X → Bool, ∀ y ∈ T, L f y = f y) :
    E (fun f : X → Bool => ∑ y : X, (if L f y = f y then (1 : ℚ) else 0))
      = ((T.card : ℚ) + (Fintype.card X : ℚ)) / 2 := by
  have hpt : ∀ f : X → Bool,
      ∑ y : X, (if L f y = f y then (1 : ℚ) else 0)
        = (∑ y : X, (if L f y = f y then (1 : ℚ) else -1) + (Fintype.card X : ℚ)) / 2 := by
    intro f
    have : ∀ y : X, (if L f y = f y then (1 : ℚ) else 0)
        = ((if L f y = f y then (1 : ℚ) else -1) + 1) / 2 := by
      intro y; by_cases h : L f y = f y <;> simp [h]
    rw [Finset.sum_congr rfl (fun y _ => this y)]
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  have hfun : (fun f : X → Bool => ∑ y : X, (if L f y = f y then (1 : ℚ) else 0))
      = fun f : X → Bool =>
          (1 / 2 : ℚ) * (∑ y : X, (if L f y = f y then (1 : ℚ) else -1))
            + (1 / 2 : ℚ) * (Fintype.card X : ℚ) := by
    funext f; rw [hpt f]; ring
  rw [hfun, E_add, E_smul, E_const, no_free_lunch_expected_score T L hL hT]
  ring
