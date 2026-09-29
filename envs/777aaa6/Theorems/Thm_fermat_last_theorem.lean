-- Prove2me | Theorems.Thm_fermat_last_theorem
-- name    : fermat_last_theorem
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-11T07:29:44.138879+00:00
-- url     : https://prove2.me/theorems/ead181bc-0035-4a80-a426-e174907e09e5
-- statement:
--   **Fermat's Last Theorem.** For every integer $n \geq 3$, the equation $a^n + b^n = c^n$ has no solutions in positive integers $a, b, c$.
--
--   Proved by Andrew Wiles (with Richard Taylor) in 1994–1995 for $n$ an odd prime, combined with Fermat's own 1640 proof for $n = 4$.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.Nat.Basic

theorem fermat_last_theorem (n : ℕ) (hn : 3 ≤ n) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ n + b ^ n ≠ c ^ n := by sorry
