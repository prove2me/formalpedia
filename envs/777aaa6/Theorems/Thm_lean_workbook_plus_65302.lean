-- Prove2me | Theorems.Thm_lean_workbook_plus_65302
-- name    : lean_workbook_plus_65302
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/4192dace-7552-478b-bef3-7b544c1ca4bc
-- statement:
--   If $xy+yx+x=1$, show that $2xy+x=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65302 (x y : ℝ) (h : x * y + y * x + x = 1) : 2 * x * y + x = 1   :=  by sorry
