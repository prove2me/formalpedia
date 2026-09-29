-- Prove2me | Theorems.Thm_lean_workbook_plus_30818
-- name    : lean_workbook_plus_30818
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/2665a23a-b2e1-4bd2-bb43-4d2b9c2b91c9
-- statement:
--   Prove that $(y+1)^7 - 2(y+1)^5 + 10(y+1)^2 - 1 > 0$ when $ y > 0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30818 (y : ℝ) (h : y > 0) : (y + 1) ^ 7 - 2 * (y + 1) ^ 5 + 10 * (y + 1) ^ 2 - 1 > 0   :=  by sorry
