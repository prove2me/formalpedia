-- Prove2me | Theorems.Thm_lean_workbook_plus_69182
-- name    : lean_workbook_plus_69182
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/e2dc40f5-c468-4786-a297-af4b50871f1a
-- statement:
--   Subtract the first equation from the second to get\n\n$x^2+y^2-2xy+4x-4y=5\iff (x-y)^2+4(x-y)-5=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69182 (x y : ℝ) : x^2 + y^2 - 2 * x * y + 4 * x - 4 * y = 5 ↔ (x - y)^2 + 4 * (x - y) - 5 = 0   :=  by sorry
