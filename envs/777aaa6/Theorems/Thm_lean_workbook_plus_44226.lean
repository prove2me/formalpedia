-- Prove2me | Theorems.Thm_lean_workbook_plus_44226
-- name    : lean_workbook_plus_44226
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/50e28e65-5a65-483a-bb02-e213d006e204
-- statement:
--   Find the value of 5log(subscript 3)2 + 2log(subscript 9)10, simplified to $log_3(2^6 5)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44226 (x : ℝ) : (5 * Real.logb 3 2) + (2 * Real.logb 9 10) = Real.logb 3 (2^6 * 5)   :=  by sorry
