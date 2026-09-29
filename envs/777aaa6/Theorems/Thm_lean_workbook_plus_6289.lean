-- Prove2me | Theorems.Thm_lean_workbook_plus_6289
-- name    : lean_workbook_plus_6289
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/b0c02489-7da3-49fc-b642-31b66aaa8826
-- statement:
--   We need to show that $26x^2+39y^2+52z^2\ge12(x+y+z)^2$ , or: $14x^2+27y^2+40z^2\ge24xy+24yz+24zx\Leftrightarrow2(3y-2x)^2+6(x-2z)^2+(3y-4z)^2\ge0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6289 (x y z : ℝ) :
  26 * x ^ 2 + 39 * y ^ 2 + 52 * z ^ 2 ≥ 12 * (x + y + z) ^ 2   :=  by sorry
