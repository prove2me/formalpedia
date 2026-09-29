-- Prove2me | Theorems.Thm_flt_five
-- name    : flt_five
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-11T08:33:34.6407+00:00
-- url     : https://prove2.me/theorems/4fc34c3c-e8b3-408b-9e48-c5445d602846
-- statement:
--   **FLT for $n=5$.** No positive integers $a, b, c$ satisfy $a^5 + b^5 = c^5$. First proved by Dirichlet (1825) and Legendre (1830) independently, using descent in $\mathbb{Z}[\zeta_5]$ where $\zeta_5$ is a primitive 5th root of unity.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.Nat.Basic

theorem flt_five (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ 5 + b ^ 5 ≠ c ^ 5 := by sorry
