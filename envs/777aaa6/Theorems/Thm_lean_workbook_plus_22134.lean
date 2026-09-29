-- Prove2me | Theorems.Thm_lean_workbook_plus_22134
-- name    : lean_workbook_plus_22134
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/e02f2086-7b77-4cd4-8859-f1b9cf7010b2
-- statement:
--   Let $\log 2 = A, \log 3 = B$ in base $10$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22134 (A B : ℝ) (hA : A = Real.log 2 / Real.log 10) (hB : B = Real.log 3 / Real.log 10) : A + B = Real.log 6 / Real.log 10   :=  by sorry
