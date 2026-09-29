-- Prove2me | Theorems.Thm_lean_workbook_plus_22922
-- name    : lean_workbook_plus_22922
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/37649119-fcb4-434a-a690-77600b71d9d1
-- statement:
--   The incidence matrix of the simple 3-cycle is $ \begin{bmatrix}1 & 0 & 1 \ 1 & 1 & 0 \ 0 & 1 & 1\end{bmatrix}$ which has determinant 2 itself.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22922 Matrix.det (![![(1 : ℤ), 0, 1],![1, 1, 0],![0, 1, 1]]) = 2   :=  by sorry
