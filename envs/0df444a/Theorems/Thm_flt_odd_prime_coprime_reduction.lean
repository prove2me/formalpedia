-- Prove2me | Theorems.Thm_flt_odd_prime_coprime_reduction
-- name    : flt_odd_prime_coprime_reduction
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-11T08:33:39.021272+00:00
-- url     : https://prove2.me/theorems/19f9803d-e2a3-4b6d-87e0-7c0d3ba08d64
-- statement:
--   **Coprime reduction for odd prime FLT.** To prove FLT for an odd prime $p \geq 5$, it suffices to prove it for pairwise coprime triples $(a, b, c)$. If $a^p + b^p = c^p$ for arbitrary positive integers, dividing by $\gcd(a,b,c)^p$ yields a coprime counterexample.

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem flt_odd_prime_coprime_reduction (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hcoprime : ∀ (a' b' c' : ℕ), 0 < a' → 0 < b' → 0 < c' → Nat.Coprime a' b' → Nat.Coprime b' c' → Nat.Coprime a' c' → a' ^ p + b' ^ p ≠ c' ^ p) : a ^ p + b ^ p ≠ c ^ p := by sorry
