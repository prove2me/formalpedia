-- Prove2me | Theorems.Thm_odd_perfect_number
-- name    : odd_perfect_number
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:29:28.01048+00:00
-- url     : https://prove2.me/theorems/4a9d9515-7e99-49f4-aa5a-7578ec0cd5d2
-- statement:
--   Odd perfect number problem: Does there exist an odd perfect number (an odd positive integer equal to the sum of its proper divisors)? No odd perfect number has ever been found. Known constraints: if one exists, it must be > 10^{1500} (Ochem–Rao 2012), have at least 101 prime factors, and satisfy many other conditions.
-- source:
--   https://en.wikipedia.org/wiki/Perfect_number

import Mathlib

import Mathlib

theorem odd_perfect_number :
    ¬ ∃ n : ℕ, ¬ 2 ∣ n ∧ n.divisors.sum id = 2 * n := by
  sorry
