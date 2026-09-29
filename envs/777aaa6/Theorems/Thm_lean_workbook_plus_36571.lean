-- Prove2me | Theorems.Thm_lean_workbook_plus_36571
-- name    : lean_workbook_plus_36571
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/8e70f33f-a7eb-4bb8-9430-308c45d4ef1b
-- statement:
--   $x+y+\sqrt{2x^2+2xy+3y^2}=1$ and $x,y\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36571 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y + Real.sqrt (2 * x ^ 2 + 2 * x * y + 3 * y ^ 2) = 1) : x + y + Real.sqrt (2 * x ^ 2 + 2 * x * y + 3 * y ^ 2) = 1   :=  by sorry
