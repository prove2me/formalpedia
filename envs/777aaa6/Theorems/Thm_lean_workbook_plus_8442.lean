-- Prove2me | Theorems.Thm_lean_workbook_plus_8442
-- name    : lean_workbook_plus_8442
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/4283cfcd-b893-447c-a4eb-842efd971320
-- statement:
--   Prove $3(x^2+y^2+1^2+yx+x+y) \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8442 (x y : ℝ) : 3 * (x ^ 2 + y ^ 2 + 1 ^ 2 + y * x + x + y) ≥ 0   :=  by sorry
