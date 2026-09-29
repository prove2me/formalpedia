-- Prove2me | solution 1 for KnownUnresolvedCards.sum_offTraining_score_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:41:26.717746+00:00
-- url     : https://prove2.me/submissions/a6dfc04d-27cc-449f-8a31-71195f3a811f

-- Sol generated from MachineLearning/KnownUnresolvedCards/NoFreeLunch.lean
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


omit [Fintype X] in
lemma flipAt_involutive (x : X) : Function.Involutive (flipAt (X := X) x) := by
  intro f
  funext y
  by_cases h : y = x
  · subst h; simp [flipAt]
  · simp [flipAt, Function.update_of_ne h]

omit [Fintype X] in
@[simp] lemma flipAt_apply_self (x : X) (f : X → Bool) : flipAt x f x = !(f x) := by
  simp [flipAt]

omit [Fintype X] in
lemma flipAt_apply_ne {x y : X} (h : y ≠ x) (f : X → Bool) : flipAt x f y = f y := by
  simp [flipAt, Function.update_of_ne h]






/-! ## `k`-ary labels: the cyclic action -/

variable {k : ℕ} [NeZero k]









open KnownUnresolvedCards in
theorem solution(T : Finset X) (x : X) (hx : x ∉ T)
    (L : (X → Bool) → (X → Bool))
    (hL : ∀ f g : X → Bool, (∀ y ∈ T, f y = g y) → L f = L g) :
    ∑ f : X → Bool, (if L f x = f x then (1 : ℚ) else -1) = 0 := by
  set p : (X → Bool) → ℚ := fun f => if L f x = f x then (1 : ℚ) else -1 with hp
  have key : ∀ f : X → Bool, p (flipAt x f) = -p f := by
    intro f
    have hLe : L (flipAt x f) = L f := by
      refine hL _ _ ?_
      intro y hy
      refine flipAt_apply_ne ?_ f
      intro h; subst h; exact hx hy
    simp only [hp, hLe, flipAt_apply_self]
    cases hb : L f x <;> cases hb2 : f x <;> simp
  have h1 : ∑ f : X → Bool, p (flipAt x f) = ∑ f : X → Bool, p f :=
    Fintype.sum_bijective (flipAt x) (flipAt_involutive x).bijective _ _ (fun _ => rfl)
  have h2 : ∑ f : X → Bool, p (flipAt x f) = -∑ f : X → Bool, p f := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun f _ => key f
  have h3 := h1.symm.trans h2
  linarith
