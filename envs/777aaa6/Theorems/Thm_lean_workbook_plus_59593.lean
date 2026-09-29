-- Prove2me | Theorems.Thm_lean_workbook_plus_59593
-- name    : lean_workbook_plus_59593
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e8d6f638-cde6-4ba5-accd-fd7562dfbeff
-- statement:
--   Find the value of 5log(subscript 3)2 + 2log(subscript 9)10, simplified to $6\log_3 2 + \log_3 5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59593 (x : ℝ) : (5 * Real.logb 3 2 + 2 * Real.logb 9 10) = (6 * Real.logb 3 2 + Real.logb 3 5)   :=  by sorry
