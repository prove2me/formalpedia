-- Prove2me | Theorems.Thm_cyclotomic5_mod5
-- name    : cyclotomic5_mod5
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-05-12T07:04:52.565914+00:00
-- url     : https://prove2.me/theorems/b2436336-9191-4a0f-86f6-ab6fc0b26806
-- statement:
--   Phi5(a,b) congruent to (a-b)^4 mod 5.

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem cyclotomic5_mod5 (a b : ℤ) : (5 : ℤ) ∣ (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) - (a - b) ^ 4 := by sorry
