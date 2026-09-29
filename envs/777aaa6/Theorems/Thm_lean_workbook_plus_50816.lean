-- Prove2me | Theorems.Thm_lean_workbook_plus_50816
-- name    : lean_workbook_plus_50816
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/51c4ccc2-929a-40e8-bae8-617d1a685430
-- statement:
--   Prove that determinant\n\n$ \det\left( \begin{array}{ccc} a & b & c \\\n c & a & b \\\n b & c & a \end{array} \right) = a^3 + b^3 + c^3 - 3abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50816 (a b c : ℝ) :
  Matrix.det (![![a, b, c],![c, a, b],![b, c, a]]) = a^3 + b^3 + c^3 - 3*a*b*c   :=  by sorry
