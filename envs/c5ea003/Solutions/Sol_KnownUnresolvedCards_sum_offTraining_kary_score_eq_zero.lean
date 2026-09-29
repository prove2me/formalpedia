-- Prove2me | solution 1 for KnownUnresolvedCards.sum_offTraining_kary_score_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:57:32.242859+00:00
-- url     : https://prove2.me/submissions/55448fd7-b179-443e-af98-c4b3af687fb8

-- Sol generated from MachineLearning/KnownUnresolvedCards/NoFreeLunch.lean
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
import Definitions.Def_MachineLearning_KnownUnresolvedCards_NoFreeLunch
import Theorems.Thm_KnownUnresolvedCards_shiftBy_bijective
import Theorems.Thm_KnownUnresolvedCards_sum_orbit_kary
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


omit [Fintype X] [NeZero k] in
@[simp] lemma shiftBy_apply_self (x : X) (t : ZMod k) (f : X → ZMod k) :
    shiftBy x t f x = f x + t := by simp [shiftBy]

omit [Fintype X] [NeZero k] in
lemma shiftBy_apply_ne {x y : X} (h : y ≠ x) (t : ZMod k) (f : X → ZMod k) :
    shiftBy x t f y = f y := by simp [shiftBy, Function.update_of_ne h]






open KnownUnresolvedCards in
theorem solution(T : Finset X) (x : X) (hx : x ∉ T)
    (L : (X → ZMod k) → (X → ZMod k))
    (hL : ∀ f g : X → ZMod k, (∀ y ∈ T, f y = g y) → L f = L g) :
    ∑ f : X → ZMod k, (if L f x = f x then ((k : ℚ) - 1) else -1) = 0 := by
  classical
  set p : (X → ZMod k) → ℚ := fun f => if L f x = f x then ((k : ℚ) - 1) else -1 with hp
  have hshift : ∀ (t : ZMod k) (f : X → ZMod k),
      p (shiftBy x t f) = (if L f x = f x + t then ((k : ℚ) - 1) else -1) := by
    intro t f
    have hLe : L (shiftBy x t f) = L f := by
      refine hL _ _ ?_
      intro y hy
      refine shiftBy_apply_ne ?_ t f
      intro h; subst h; exact hx hy
    rw [hp]
    simp only [hLe, shiftBy_apply_self]
  have hcol : ∀ t : ZMod k, ∑ f : X → ZMod k, p (shiftBy x t f) = ∑ f : X → ZMod k, p f :=
    fun t => Fintype.sum_bijective (shiftBy x t) (shiftBy_bijective x t) _ _ (fun _ => rfl)
  have hk : ((k : ℚ)) ≠ 0 := by
    have : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
    positivity
  have hmain : (k : ℚ) * (∑ f : X → ZMod k, p f) = 0 := by
    have h1 : ∑ _t : ZMod k, (∑ f : X → ZMod k, p f) = (k : ℚ) * ∑ f : X → ZMod k, p f := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card k]
    rw [← h1]
    rw [Finset.sum_congr rfl (fun t (_ : t ∈ (univ : Finset (ZMod k))) => (hcol t).symm)]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun f _ => ?_
    rw [Finset.sum_congr rfl (fun t (_ : t ∈ (univ : Finset (ZMod k))) => hshift t f)]
    exact sum_orbit_kary (L f x) (f x)
  rcases mul_eq_zero.mp hmain with h | h
  · exact absurd h hk
  · exact h
