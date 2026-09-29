-- Prove2me | Theorems.Thm_lean_workbook_plus_43897
-- name    : lean_workbook_plus_43897
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/59584e55-cd33-48f9-a5d5-adf40f42c2c2
-- statement:
--   Let $A=\begin{pmatrix}-89&77\\66&-80\end{pmatrix}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43897 (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A =!![-89, 77; 66, -80]) : A * (Matrix.adjugate A) = Matrix.det A • (1 : Matrix (Fin 2) (Fin 2) ℤ)   :=  by sorry
