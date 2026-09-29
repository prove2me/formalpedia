-- Prove2me | Theorems.Thm_flt_reduction
-- name    : flt_reduction
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-11T07:31:05.551169+00:00
-- url     : https://prove2.me/theorems/3a7273d5-6a53-4d11-9e4c-4e86fe4490b2
-- statement:
--   **Reduction step.** If FLT holds for $n = 4$ and for every odd prime exponent $p$, then it holds for all $n \geq 3$. Pure elementary number theory: every $n \geq 3$ either has an odd prime factor or is divisible by $4$.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic

theorem flt_reduction (h4 : ∀ (a b c : ℕ), 0 < a → 0 < b → 0 < c → a ^ 4 + b ^ 4 ≠ c ^ 4) (hodd : ∀ (p : ℕ), p.Prime → 2 < p → ∀ (a b c : ℕ), 0 < a → 0 < b → 0 < c → a ^ p + b ^ p ≠ c ^ p) (n : ℕ) (hn : 3 ≤ n) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ n + b ^ n ≠ c ^ n := by sorry
