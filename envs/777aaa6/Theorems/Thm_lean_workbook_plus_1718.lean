-- Prove2me | Theorems.Thm_lean_workbook_plus_1718
-- name    : lean_workbook_plus_1718
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/7ceaf9e8-1700-4eee-8c29-91ab692de589
-- statement:
--   Now, $(r+m+o)^2\geq3(rm+mo+or)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1718 (r m o : ℝ) : (r + m + o) ^ 2 ≥ 3 * (r * m + m * o + o * r)   :=  by sorry
