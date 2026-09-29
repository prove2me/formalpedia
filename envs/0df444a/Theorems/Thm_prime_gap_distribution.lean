-- Prove2me | Theorems.Thm_prime_gap_distribution
-- name    : prime_gap_distribution
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T03:17:45.725378+00:00
-- url     : https://prove2.me/theorems/4ff1481e-b2ea-42da-b265-b9db07abf053
-- statement:
--   Cramér distribution of prime gaps: The normalized prime gaps (p_{n+1} - p_n)/log(p_n) are conjectured to be exponentially distributed with density e^{-x}. Consistent with Montgomery's pair correlation but not yet proved.
-- source:
--   https://en.wikipedia.org/wiki/Prime_gap

import Mathlib

import Mathlib

theorem prime_gap_distribution :
    ∀ (a b : ℝ), 0 < a → a < b →
    Filter.Tendsto (fun N : ℕ =>
      ((Finset.range N).filter (fun k =>
        let p := Nat.nth Nat.Prime k
        let q := Nat.nth Nat.Prime (k + 1)
        a ≤ (q - p : ℝ) / Real.log p ∧ (q - p : ℝ) / Real.log p ≤ b)).card /
      (N : ℝ))
    Filter.atTop (nhds (∫ x in Set.Ioo a b, Real.exp (-x))) := by
  sorry
