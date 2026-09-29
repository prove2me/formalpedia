-- Prove2me | Theorems.Thm_flt_odd_prime_gt_5
-- name    : flt_odd_prime_gt_5
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-15T06:31:30.486111+00:00
-- url     : https://prove2.me/theorems/d2ddf54f-5946-4962-9eb5-03d5ee116936
-- statement:
--   FLT for odd prime exponents p≥7. The deep case requiring Kummer's theorem for regular primes and Wiles-Taylor modularity for irregular primes.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic

theorem flt_odd_prime_gt_5 (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ p + b ^ p ≠ c ^ p := by sorry
