-- Prove2me | Theorems.Thm_erdos_straus_2n
-- name    : erdos_straus_2n
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:25:11.326953+00:00
-- url     : https://prove2.me/theorems/45242661-cc18-4da5-9741-4e39343294be
-- statement:
--   Erdős-Straus for 2/n: Every fraction 2/n (n ≥ 2) can be written as 1/a + 1/b (unit fractions). Proved easily. The harder conjecture 4/n = 1/a+1/b+1/c (Erdős-Straus) is open.
-- source:
--   https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Straus_conjecture

import Mathlib

import Mathlib

theorem erdos_straus_2n :
    ∀ n : ℕ, 2 ≤ n →
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
      2 * a * b = n * (b + a) := by
  sorry
