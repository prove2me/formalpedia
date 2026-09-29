-- Prove2me | Theorems.Thm_lean_workbook_plus_33494
-- name    : lean_workbook_plus_33494
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/9ebe747e-8d28-475f-8491-d2c57b1867c6
-- statement:
--   Hence the result : $ \boxed{ - \frac {13}8\le m\le\frac 32}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33494 (m : ℝ) (hm : 2 * m + 3 ≤ m + 8) (hn : m + 8 ≤ 4 * m - 13) : - 13 / 8 ≤ m ∧ m ≤ 3 / 2   :=  by sorry
