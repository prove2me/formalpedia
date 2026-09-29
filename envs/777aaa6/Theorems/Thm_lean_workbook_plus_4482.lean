-- Prove2me | Theorems.Thm_lean_workbook_plus_4482
-- name    : lean_workbook_plus_4482
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e9553293-609d-4399-ac7b-3b09fb6694a3
-- statement:
--   Let $A=B=\begin{bmatrix}1&1\\0&0\end{bmatrix}.$ Clearly $AB=BA=A^2=A.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4482 (A B : Matrix (Fin 2) (Fin 2) ℚ) (hA : A =![![1, 1],![0, 0]]) (hB : B =![![1, 1],![0, 0]]) : A * B = B * A ∧ A * B = A^2 ∧ A * B = A   :=  by sorry
