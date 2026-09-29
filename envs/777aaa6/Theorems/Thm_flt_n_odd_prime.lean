-- Prove2me | Theorems.Thm_flt_n_odd_prime
-- name    : flt_n_odd_prime
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-11T07:31:00.607772+00:00
-- url     : https://prove2.me/theorems/becab797-74f3-4645-994e-ec5e344f7d36
-- statement:
--   **FLT for odd prime exponents.** For every prime $p > 2$, no positive integers $a, b, c$ satisfy $a^p + b^p = c^p$. The deep case, completed by Wiles and Taylor (1995) via modularity of semistable elliptic curves.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic

theorem flt_n_odd_prime (p : ℕ) (hp : p.Prime) (hodd : 2 < p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ p + b ^ p ≠ c ^ p := by sorry
