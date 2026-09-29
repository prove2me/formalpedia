-- Prove2me | Theorems.Thm_lean_workbook_plus_80913
-- name    : lean_workbook_plus_80913
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e1940169-0582-409c-836f-d8306d5e4046
-- statement:
--   Suppose $a>0,\ |x-1|<\frac {a}{3},\ |y-2|<\frac {a}{3}.$ Prove that $|2x+y-4|<a.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80913 (a : ℝ) (x y : ℝ) (ha : a > 0) (hx : |x - 1| < a / 3) (hy : |y - 2| < a / 3) : |2 * x + y - 4| < a   :=  by sorry
