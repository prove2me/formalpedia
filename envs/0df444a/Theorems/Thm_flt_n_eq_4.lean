-- Prove2me | Theorems.Thm_flt_n_eq_4
-- name    : flt_n_eq_4
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-11T07:30:55.973222+00:00
-- url     : https://prove2.me/theorems/8123b251-6881-49d6-9408-130b52c96117
-- statement:
--   **FLT for $n=4$.** No positive integers $a, b, c$ satisfy $a^4 + b^4 = c^4$. Proved by Fermat via infinite descent — the only case Fermat actually proved himself.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.Nat.Basic

theorem flt_n_eq_4 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ 4 + b ^ 4 ≠ c ^ 4 := by sorry
