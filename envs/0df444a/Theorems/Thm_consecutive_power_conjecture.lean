-- Prove2me | Theorems.Thm_consecutive_power_conjecture
-- name    : consecutive_power_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:39:05.999954+00:00
-- url     : https://prove2.me/theorems/aa81ecc5-02a0-4ab8-8293-9ddb2f0662c2
-- statement:
--   Catalan's conjecture (proved by Mihailescu 2002): The only solution to x^p - y^q = 1 with x,y,p,q > 1 is 3² - 2³ = 1. This is now a theorem. The statement here is the precise version. Generalizations to x^m - y^n = k remain open.
-- source:
--   https://en.wikipedia.org/wiki/Mih%C4%83ilescu%27s_theorem

import Mathlib

import Mathlib

theorem consecutive_power_conjecture :
    ∀ (a b m n : ℕ), 2 ≤ m → 2 ≤ n → 1 < a → 1 < b →
      a ^ m = b ^ n + 1 →
      (a = 3 ∧ m = 2 ∧ b = 2 ∧ n = 3) := by
  sorry
