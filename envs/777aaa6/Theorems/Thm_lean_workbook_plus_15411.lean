-- Prove2me | Theorems.Thm_lean_workbook_plus_15411
-- name    : lean_workbook_plus_15411
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/38957f25-5b28-4e75-be65-d7459034c281
-- statement:
--   Find the determinant of the matrix $ \begin{vmatrix} a+b & b+c & c+a \ a^2+b^2 & b^2+c^2 & c^2+a^2 \ a^3+b^3& b^3+c^3 & c^3+a^3 \end{vmatrix}$ using row operations.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15411 (a b c : ℝ) : Matrix.det (![![a+b, b+c, c+a],![a^2+b^2, b^2+c^2, c^2+a^2],![a^3+b^3, b^3+c^3, c^3+a^3]]) = 2*a*b*c*(a-b)*(b-c)*(c-a)   :=  by sorry
