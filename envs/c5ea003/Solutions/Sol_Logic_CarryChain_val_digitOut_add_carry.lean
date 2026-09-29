-- Prove2me | solution 1 for Logic.CarryChain.val_digitOut_add_carry
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:23:47.459268+00:00
-- url     : https://prove2.me/submissions/f2e1b5ab-28ac-42f8-83ef-885009994dbf

import Mathlib
import Definitions.Def_Logic_DenseFinalStepCarryChain
open Logic.CarryChain in
theorem solution (base : ℕ) (a b : ℕ → ℕ) (n : ℕ) :
    val base (digitOut base a b) n + carry base a b n * base ^ n
      = val base a n + val base b n := by
  induction n with
  | zero => simp [val, carry]
  | succ n ih =>
    have hval : ∀ f : ℕ → ℕ, val base f (n + 1) = val base f n + f n * base ^ n := by
      intro f
      simp [val, Finset.sum_range_succ]
    have expand : (a n + b n + carry base a b n) % base * base ^ n
        + (a n + b n + carry base a b n) / base * base ^ (n + 1)
        = (a n + b n + carry base a b n) * base ^ n := by
      rw [pow_succ]
      calc (a n + b n + carry base a b n) % base * base ^ n
            + (a n + b n + carry base a b n) / base * (base ^ n * base)
          = ((a n + b n + carry base a b n) % base
              + (a n + b n + carry base a b n) / base * base) * base ^ n := by ring
        _ = (a n + b n + carry base a b n) * base ^ n := by
              rw [Nat.mod_add_div' (a n + b n + carry base a b n) base]
    show val base (digitOut base a b) (n + 1)
        + (a n + b n + carry base a b n) / base * base ^ (n + 1) = _
    rw [hval, hval, hval]
    show val base (digitOut base a b) n
        + (a n + b n + carry base a b n) % base * base ^ n
        + (a n + b n + carry base a b n) / base * base ^ (n + 1) = _
    calc val base (digitOut base a b) n
          + (a n + b n + carry base a b n) % base * base ^ n
          + (a n + b n + carry base a b n) / base * base ^ (n + 1)
        = val base (digitOut base a b) n
            + ((a n + b n + carry base a b n) % base * base ^ n
              + (a n + b n + carry base a b n) / base * base ^ (n + 1)) := by ring
      _ = val base (digitOut base a b) n + (a n + b n + carry base a b n) * base ^ n := by
            rw [expand]
      _ = (val base (digitOut base a b) n + carry base a b n * base ^ n)
            + (a n + b n) * base ^ n := by ring
      _ = (val base a n + val base b n) + (a n + b n) * base ^ n := by rw [ih]
      _ = (val base a n + a n * base ^ n) + (val base b n + b n * base ^ n) := by ring
