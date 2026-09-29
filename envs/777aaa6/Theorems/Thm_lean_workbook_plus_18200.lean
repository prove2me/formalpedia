-- Prove2me | Theorems.Thm_lean_workbook_plus_18200
-- name    : lean_workbook_plus_18200
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/8b7ee4be-6bad-43f2-8b3b-fa317658ceb9
-- statement:
--   Prove $13b^{3}-5b^{2}-8b+4\geq 0$ for $b \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18200 (b : ℝ) (h : b >= 0) : 13*b^3 - 5*b^2 - 8*b + 4 >= 0   :=  by sorry
