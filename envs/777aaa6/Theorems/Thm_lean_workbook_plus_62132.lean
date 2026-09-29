-- Prove2me | Theorems.Thm_lean_workbook_plus_62132
-- name    : lean_workbook_plus_62132
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ecb8870c-b968-4eef-9420-309991e2c8b4
-- statement:
--   Use row reduction to find the inverse of the matrix: $\begin{bmatrix} 9/2 & 7/2 \\ -7/2 & -5/2 \end{bmatrix}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62132 (A : Matrix (Fin 2) (Fin 2) ℚ) (hA : A =!![9 / 2, 7 / 2; -7 / 2, -5 / 2]) : A *!![-5 / 2, -7 / 2; 7 / 2, 9 / 2] = 1   :=  by sorry
