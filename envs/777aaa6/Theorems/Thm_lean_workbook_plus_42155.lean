-- Prove2me | Theorems.Thm_lean_workbook_plus_42155
-- name    : lean_workbook_plus_42155
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/c06bad19-c838-4437-9b7a-e6f611fffca6
-- statement:
--   $ x^{2} + 2xy + 3y^{2} - 6x - 2y+11 = (x+y-3)^2+2(y+1)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42155 (x y : ℝ) : x^2 + 2*x*y + 3*y^2 - 6*x - 2*y + 11 = (x + y - 3)^2 + 2*(y + 1)^2   :=  by sorry
