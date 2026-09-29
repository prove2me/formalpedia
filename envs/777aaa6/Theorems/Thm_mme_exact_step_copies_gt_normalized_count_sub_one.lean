-- Prove2me | Theorems.Thm_mme_exact_step_copies_gt_normalized_count_sub_one
-- name    : mme_exact_step_copies_gt_normalized_count_sub_one
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:54:47.678897+00:00
-- url     : https://prove2.me/theorems/5796c40f-ca5d-4609-9864-79ee3c2ca2b7
-- title:
--   Explicit repair and rounding loss for exact extraction copies
-- statement:
--   If B is a real lower bound for the selected count of an exact extraction step, its integer number of repaired copies is strictly greater than B divided by the power-of-eight repair budget minus one.
-- source:
--   Released regional integer profiles, quantitative exact extraction, and explicit repair losses.

import Theorems.Thm_mme_recursive_profiled_CW_exact_step
import Definitions.Def_mme_recursive_profiled_CW_data
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
open MME MME.ProfiledCW
set_option autoImplicit false
universe u

theorem mme_exact_step_copies_gt_normalized_count_sub_one
    {ell N : ℕ} {P : Predicate N} (E : ExactStep ell N P) {B : ℝ}
    (hB : B ≤ E.count) :
    B / (8 : ℝ) ^ E.stage.repairExponent - 1 < E.copies := by sorry
