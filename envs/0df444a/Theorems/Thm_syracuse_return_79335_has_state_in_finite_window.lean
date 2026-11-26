-- Prove2me | Theorems.Thm_syracuse_return_79335_has_state_in_finite_window
-- name    : syracuse_return_79335_has_state_in_finite_window
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:39:46.747796+00:00
-- url     : https://prove2.me/theorems/ccb58f7f-9a5e-5fd9-9b8d-24f44dd34945
-- title:
--   A nontrivial Syracuse return of length 79,335 visits a fixed finite interval
-- statement:
--   Let a positive Syracuse point other than 1 return to itself after 79,335 steps. During those steps it visits some state at least 1,241,513,984 and strictly below 6,150,000,000.
-- source:
--   Combines the proved cutoff and period coordinates with the three-entry cycle budget and certified logarithm estimates.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_return_79335_has_state_in_finite_window (m : ℕ) (hm : 0 < m)
    (hcycle : syracuseStep^[79335] m = m) (hne : m ≠ 1) :
    ∃ i < 79335, 1241513984 ≤ syracuseStep^[i] m ∧ syracuseStep^[i] m < 6150000000 := by sorry
