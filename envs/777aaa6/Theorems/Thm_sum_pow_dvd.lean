-- Prove2me | Theorems.Thm_sum_pow_dvd
-- name    : sum_pow_dvd
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T05:40:37.267076+00:00
-- url     : https://prove2.me/theorems/5f67b9e3-c46d-47af-a029-e10cf99cdbd6
-- statement:
--   **Divisibility: (a+b) divides a^5+b^5.** For any integers a, b, the sum (a+b) divides a^5+b^5. This follows immediately from the cyclotomic factoring a^5+b^5 = (a+b)*Φ₅(a,b). More generally, for any odd n, (a+b) divides a^n+b^n.

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem sum_pow_dvd (a b : ℤ) : (a + b) ∣ a ^ 5 + b ^ 5 := by sorry
