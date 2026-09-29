-- Prove2me | Theorems.Thm_lean_workbook_plus_78005
-- name    : lean_workbook_plus_78005
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/0ed5cccb-5c57-420f-a681-fb80e25f1bd3
-- statement:
--   prove that : $\frac{x^4-y^4}{4x^3}>x-y$, given $x>y>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78005 (x y : ℝ) (hxy : x > y) (hy : y > 0) : (x^4 - y^4) / (4 * x^3) > x - y   :=  by sorry
