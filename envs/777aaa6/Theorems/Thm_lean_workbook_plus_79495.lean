-- Prove2me | Theorems.Thm_lean_workbook_plus_79495
-- name    : lean_workbook_plus_79495
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/8cf00ee2-fc8b-43ac-bc30-02c157da0048
-- statement:
--   Prove that $x^3+y^3+z^3-3xyz=\frac {1}{2}(x+y+z)\left (\sum_{cyc}(x-y)^2\right)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79495 (x y z : ℝ) :
  x^3 + y^3 + z^3 - 3 * x * y * z =
    1 / 2 * (x + y + z) * ((x - y)^2 + (y - z)^2 + (z - x)^2)   :=  by sorry
