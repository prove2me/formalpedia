-- Prove2me | Theorems.Thm_lean_workbook_plus_21017
-- name    : lean_workbook_plus_21017
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/bc348800-b864-4bbb-895a-996b991bfb75
-- statement:
--   Find the value of $\displaystyle\sum_{n = 1}^{40}{39n(41 - n)^2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21017 (n : ℕ) : ∑ n in Finset.Icc 1 40, 39 * n * (41 - n) ^ 2 = 9178260   :=  by sorry
