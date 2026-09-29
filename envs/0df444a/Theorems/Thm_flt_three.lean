-- Prove2me | Theorems.Thm_flt_three
-- name    : flt_three
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-11T08:21:06.240212+00:00
-- url     : https://prove2.me/theorems/0b6ae900-2ca5-4185-8bc1-5ded4e002e54
-- statement:
--   **FLT for $n = 3$.** No positive integers $a, b, c$ satisfy $a^3 + b^3 = c^3$. First proved by Euler (1770) using infinite descent in $\mathbb{Z}[\omega]$ where $\omega$ is a primitive cube root of unity.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.Nat.Basic

theorem flt_three (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ 3 + b ^ 3 ≠ c ^ 3 := by sorry
