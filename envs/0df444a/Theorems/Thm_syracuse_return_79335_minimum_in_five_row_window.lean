-- Prove2me | Theorems.Thm_syracuse_return_79335_minimum_in_five_row_window
-- name    : syracuse_return_79335_minimum_in_five_row_window
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:59:00.491744+00:00
-- url     : https://prove2.me/theorems/6a833ccb-bd6f-4058-aa0a-1b8e84a31611
-- title:
--   A nontrivial 79,335-step Syracuse return has a minimum below 5,710,000,000
-- statement:
--   A positive nontrivial Syracuse orbit returning after 79,335 steps has an orbit minimum in [1,241,513,984, 5,710,000,000). The minimum is 7 or 11 modulo 12 and occurs before the return.
-- source:
--   Five-entry reciprocal bound from an exact check of 81 short valuation words and a direct bound on larger valuations, summed over the cycle.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_return_79335_minimum_in_five_row_window (m : ℕ) (hm : 0 < m)
    (hcycle : syracuseStep^[79335] m = m) (hne : m ≠ 1) :
    ∃ j < 79335, 1241513984 ≤ syracuseStep^[j] m ∧ syracuseStep^[j] m < 5710000000 ∧
      (syracuseStep^[j] m % 12 = 7 ∨ syracuseStep^[j] m % 12 = 11) ∧
      ∀ i : ℕ, syracuseStep^[j] m ≤ syracuseStep^[i] m := by sorry
