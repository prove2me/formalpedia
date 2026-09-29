-- Prove2me | Theorems.Thm_flt_odd_prime_gt_5
-- name    : flt_odd_prime_gt_5
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T06:31:30.486111+00:00
-- url     : https://prove2.me/theorems/5bceca98-096a-4a88-9cfd-bdb9110dfea2
-- statement:
--   FLT for odd prime exponents p≥7. The deep case requiring Kummer's theorem for regular primes and Wiles-Taylor modularity for irregular primes.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic

theorem flt_odd_prime_gt_5 (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ p + b ^ p ≠ c ^ p := by sorry
