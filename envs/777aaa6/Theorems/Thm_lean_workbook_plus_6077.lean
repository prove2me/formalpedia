-- Prove2me | Theorems.Thm_lean_workbook_plus_6077
-- name    : lean_workbook_plus_6077
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/667a60fd-7d5b-4eca-9a0b-e96343d038c1
-- statement:
--   Given a matrix $A = \begin{pmatrix} 0 & 1 & 2 & 3 \\ 1 & 2 & 3 & 0 \\ 2 & 3 & 0 & 1 \\ 3 & 0 & 1 & 2 \end{pmatrix}$, find the number of different matrices that can be obtained from $A$ using permutations of rows and columns.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6077 (A : Matrix (Fin 4) (Fin 4) ℕ) (hA : A =!![0, 1, 2, 3; 1, 2, 3, 0; 2, 3, 0, 1; 3, 0, 1, 2]) : (∀ B : Matrix (Fin 4) (Fin 4) ℕ, B =!![0, 1, 2, 3; 1, 2, 3, 0; 2, 3, 0, 1; 3, 0, 1, 2] → B = A)   :=  by sorry
