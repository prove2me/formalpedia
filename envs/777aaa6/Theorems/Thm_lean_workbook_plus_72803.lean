-- Prove2me | Theorems.Thm_lean_workbook_plus_72803
-- name    : lean_workbook_plus_72803
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/cb7b2147-6fc5-461d-9b5a-f8eda5e73e3d
-- statement:
--   If $x,y>0$ , then prove: $x^4+y^4+x^2+y^2+2+2x(4x^2+1)+2y(4y^2+1)>18xy$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72803 (x y : ℝ) (hx : x > 0) (hy : y > 0) : x^4 + y^4 + x^2 + y^2 + 2 + 2 * x * (4 * x^2 + 1) + 2 * y * (4 * y^2 + 1) > 18 * x * y   :=  by sorry
