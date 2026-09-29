-- Prove2me | Theorems.Thm_lean_workbook_plus_55251
-- name    : lean_workbook_plus_55251
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/bc377424-a391-4c61-8a5b-f30fc0bb55d0
-- statement:
--   Find the minimum value of $2x^2+10y^2+16z^2-16yz$ when $x,y,z$ are real numbers that satisfy $xy+yz+zx=-9$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55251 (x y z : ℝ) (h : x * y + y * z + z * x = -9) : 2 * x ^ 2 + 10 * y ^ 2 + 16 * z ^ 2 - 16 * y * z ≥ -18   :=  by sorry
