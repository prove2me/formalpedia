-- Prove2me | Theorems.Thm_cyclotomic5_factored
-- name    : cyclotomic5_factored
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T07:04:48.55295+00:00
-- url     : https://prove2.me/theorems/533cab45-5dc7-4fbd-81a0-7457a331068b
-- statement:
--   Ring identity: (a+b)*Phi5(a,b) = a^5+b^5.

import Mathlib.Tactic.Ring

theorem cyclotomic5_factored (a b : ℤ) : (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) = a ^ 5 + b ^ 5 := by sorry
