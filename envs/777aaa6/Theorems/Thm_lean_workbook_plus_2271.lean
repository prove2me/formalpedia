-- Prove2me | Theorems.Thm_lean_workbook_plus_2271
-- name    : lean_workbook_plus_2271
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/1cd95833-479e-4707-b429-79b1d0f6409c
-- statement:
--   Prove that the determinant of the matrix \(\begin{vmatrix} y & x & x+y \\ x+y & y & x \\ x & x+y& y \end{vmatrix}\) is equal to \(2(x^3+y^3)\) without expanding the determinant.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2271 (x y : ℂ) : Matrix.det (![![y, x, x+y],![x+y, y, x],![x, x+y, y]]) = 2 * (x^3 + y^3)   :=  by sorry
