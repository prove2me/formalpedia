-- Prove2me | Theorems.Thm_lean_workbook_plus_12721
-- name    : lean_workbook_plus_12721
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/6889a052-1cfa-4a0a-acbf-a9ec799dbe69
-- statement:
--   Prove that $(x-y)^4+(y-z)^4+(z-x)^4=2(x^2+y^2+z^2-xy-yz-zx)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12721 (x y z : ℝ) :
  (x - y) ^ 4 + (y - z) ^ 4 + (z - x) ^ 4 =
    2 * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) ^ 2   :=  by sorry
