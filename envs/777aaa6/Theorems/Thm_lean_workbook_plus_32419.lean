-- Prove2me | Theorems.Thm_lean_workbook_plus_32419
-- name    : lean_workbook_plus_32419
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/60484616-06e7-4532-88ef-6e6b35f020b8
-- statement:
--   If $x,\,y$ are non-negattive numbers, then \n $xy(x^2+y^2) \leqslant 2+2xy(x+y)(x+y-2).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32419 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : x * y * (x ^ 2 + y ^ 2) ≤ 2 + 2 * x * y * (x + y) * (x + y - 2)   :=  by sorry
