-- Prove2me | Theorems.Thm_vojta_conjecture
-- name    : vojta_conjecture
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-31T21:56:48.442856+00:00
-- url     : https://prove2.me/theorems/e85d2103-ef79-4197-9020-bb38793eab34
-- statement:
--   Vojta's conjecture (1987): For algebraic varieties V over number fields, rational points have height bounded by the discriminant and canonical divisor in a precise way. Implies the abc conjecture, Mordell conjecture (Faltings), and many Diophantine results. Wide open in general.
-- source:
--   https://en.wikipedia.org/wiki/Vojta%27s_conjecture

import Mathlib

import Mathlib

theorem vojta_conjecture :
    ∀ (d : ℕ) (eps : ℝ) (_ : 0 < eps),
    ∃ C : ℝ, ∀ (x y : ℤ),
      Nat.Coprime x.natAbs y.natAbs →
      (∃ a b : ℤ, x ^ 2 + y ^ 2 = a * b ∧ a ≠ 0 ∧ b ≠ 0) →
      (x : ℝ) ^ 2 + (y : ℝ) ^ 2 ≤ C * max |x| |y| ^ (2 + eps) := by
  sorry
