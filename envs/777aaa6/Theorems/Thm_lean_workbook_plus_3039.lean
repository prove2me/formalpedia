-- Prove2me | Theorems.Thm_lean_workbook_plus_3039
-- name    : lean_workbook_plus_3039
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/c035a7b3-bd9a-4a63-b47c-694dcf3f96bb
-- statement:
--   Prove that the determinant of the matrix \(\begin{vmatrix} y & x & x+y \\ x+y & y & x \\ x & x+y& y \end{vmatrix}\) is equal to \(2(x^3+y^3)\) without expanding the determinant.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3039 (x y : ℝ) : Matrix.det (![![y, x, x+y],![x+y, y, x],![x, x+y, y]]) = 2 * (x^3 + y^3)   :=  by sorry
