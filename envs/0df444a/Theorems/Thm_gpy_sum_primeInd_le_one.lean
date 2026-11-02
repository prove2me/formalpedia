-- Prove2me | Theorems.Thm_gpy_sum_primeInd_le_one
-- name    : gpy_sum_primeInd_le_one
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T08:11:33.336794+00:00
-- url     : https://prove2.me/theorems/11cffbd7-d121-43e5-8e7d-3cc6a26c011e
-- title:
--   Prime-indicator sum bound for a translate with at most one prime coordinate
-- statement:
--   If at most one coordinate of a translate is prime, the sum of prime indicators over the tuple is at most 1. Pure Mathlib statement: the prime indicator is written out as an if-then-else.
-- source:
--   GPY ratio analysis: threshold, main-term approximations, and BV level cap

import Mathlib
open Classical

theorem gpy_sum_primeInd_le_one {k : ℕ} (h : Fin k → ℕ) (n : ℕ) (hat : ∀ i j : Fin k, i ≠ j → ¬ Nat.Prime (n + h i) ∨ ¬ Nat.Prime (n + h j)) : (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) ≤ 1 := by sorry
