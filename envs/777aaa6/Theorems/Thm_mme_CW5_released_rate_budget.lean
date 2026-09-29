-- Prove2me | Theorems.Thm_mme_CW5_released_rate_budget
-- name    : mme_CW5_released_rate_budget
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:12:45.458098+00:00
-- url     : https://prove2.me/theorems/110c1157-3297-4074-8a21-4af6847220ad
-- title:
--   The target extraction totals retain surplus after a fixed loss allowance
-- statement:
--   Assuming lower bounds for the actual outer, parent, and child contributions and a total loss at most one twenty-thousandth, their net rate is strictly above 144 log seven. The logarithm upper bound is certified; matching the actual extraction rates to these totals remains a separate obligation. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_CW5_base_log_bounds

theorem mme_CW5_released_rate_budget
    (outer parent child loss : ℝ)
    (ho : (6707994429 / 125000000 : ℝ) ≤ outer)
    (hp : (6627490041 / 250000000 : ℝ) ≤ parent)
    (hc : (200037213610 / 1000000000 : ℝ) ≤ child)
    (hl : loss ≤ (1 / 20000 : ℝ)) :
    144 * Real.log 7 < outer + parent + child - loss := by sorry
