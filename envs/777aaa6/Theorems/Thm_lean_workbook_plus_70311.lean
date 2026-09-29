-- Prove2me | Theorems.Thm_lean_workbook_plus_70311
-- name    : lean_workbook_plus_70311
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/b022af68-9716-4beb-88ad-7414bccf86a0
-- statement:
--   Find $x$ if $A=\begin{bmatrix} 0 & 2 & 1 \ 3 & -1 & 2 \ x & x-4 & x-3 \end{bmatrix}$ and $det(A)=14$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70311 (x : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A =!![0, 2, 1; 3, -1, 2; x, x-4, x-3]) (h_det : Matrix.det A = 14) : x = 29/7   :=  by sorry
