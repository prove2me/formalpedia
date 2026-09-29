-- Prove2me | Theorems.Thm_flt_odd_prime_ge_5
-- name    : flt_odd_prime_ge_5
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-11T08:21:10.33994+00:00
-- url     : https://prove2.me/theorems/41f7c2ee-ac36-4a76-918d-412c9c720508
-- statement:
--   **FLT for prime exponents $p \geq 5$.** No positive integers $a, b, c$ satisfy $a^p + b^p = c^p$ for any prime $p \geq 5$. This is the core of Wiles's 1995 proof, which handles primes not covered by Euler's $n=3$ case.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic

theorem flt_odd_prime_ge_5 (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ p + b ^ p ≠ c ^ p := by sorry
