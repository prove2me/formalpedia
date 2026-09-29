-- Prove2me | Theorems.Thm_lean_workbook_plus_26183
-- name    : lean_workbook_plus_26183
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/8511ec80-1791-45ea-9ad4-0c46f409ae54
-- statement:
--   For $ x > 1$, show that $ 2x^2 + 8x + 6 > (x+3)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26183 (x : ℝ) (h : x > 1) : 2 * x ^ 2 + 8 * x + 6 > (x + 3) ^ 2   :=  by sorry
