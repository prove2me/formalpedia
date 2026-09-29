-- Prove2me | Theorems.Thm_automatic_sequence_irrationality
-- name    : automatic_sequence_irrationality
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:17:37.69418+00:00
-- url     : https://prove2.me/theorems/c8128efe-cb0e-4d6c-aa4b-8b365827f763
-- statement:
--   Automatic sequence irrationality: The generating function of any non-eventually-periodic automatic sequence over a finite alphabet, when evaluated at a rational number, is irrational (Adamczewski-Bugeaud conjecture). Partly proved; general case relates to transcendence of p-adic numbers.
-- source:
--   https://en.wikipedia.org/wiki/Automatic_sequence

import Mathlib

import Mathlib

theorem automatic_sequence_irrationality :
    Irrational (∑' n : ℕ, (if ∀ k : ℕ, k ≤ Nat.log 2 (n+1) →
        (n / 2^k) % 4 ≠ 2 then (1 : ℝ) else 0) / 2^(n+1)) := by
  sorry
