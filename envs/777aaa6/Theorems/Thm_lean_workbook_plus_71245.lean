-- Prove2me | Theorems.Thm_lean_workbook_plus_71245
-- name    : lean_workbook_plus_71245
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/1fe124c5-71d7-40ff-af7c-ed6c0fffa763
-- statement:
--   The row reduced echelon form matrix is \n $$\begin{bmatrix}1 & 0 & 0 & x/w \\0 & 1 & 0 & y/w \\0 & 0 & 1 & z/w\end{bmatrix},$$ where $x = -46 - a - 6q + 3aq$ , $y = -5a + 6q - 2aq$ , $z = 46 - 17a$ , $w = q - 23$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71245 (a q x y z w : ℝ) : (x = -46 - a - 6*q + 3*a*q ∧ y = -5*a + 6*q - 2*a*q ∧ z = 46 - 17*a ∧ w = q - 23 → x/w = (-46 - a - 6*q + 3*a*q)/(q - 23) ∧ y/w = (-5*a + 6*q - 2*a*q)/(q - 23) ∧ z/w = (46 - 17*a)/(q - 23))   :=  by sorry
