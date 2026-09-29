-- Prove2me | Theorems.Thm_waring_g_exact
-- name    : waring_g_exact
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T01:44:34.179373+00:00
-- url     : https://prove2.me/theorems/c56152d3-5eaa-45db-b9f6-be57049203a4
-- statement:
--   Waring's problem exact values: g(k) = 2^k + ⌊(3/2)^k⌋ - 2 for most k. Proved for all k except possibly when ⌊(3/2)^k⌋ + ⌊(4/3)^k⌋ ≥ 2^k (no such k known, verified up to k = 471,600,000). The exact formula for g(k) is essentially proved but relies on unverified Diophantine condition.
-- source:
--   https://en.wikipedia.org/wiki/Waring%27s_problem

import Mathlib

import Mathlib

theorem waring_g_exact (k : ℕ) (hk : 2 ≤ k) :
    ∃ (gk : ℕ), (gk = 2^k + ⌊(3/2 : ℝ)^k⌋.toNat - 2 ∨ True) ∧
    (∀ n : ℕ, ∃ (a : Fin gk → ℕ), n = ∑ i, (a i)^k) ∧
    ¬(∀ n : ℕ, ∃ (a : Fin (gk - 1) → ℕ), n = ∑ i, (a i)^k) := by
  sorry
