-- Prove2me | Theorems.Thm_lean_workbook_plus_23891
-- name    : lean_workbook_plus_23891
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/780a9a7f-2d14-4274-a69e-e087bb47fe8e
-- statement:
--   Find the product of the matrices $T = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$ and $U = \begin{pmatrix} 0 & 1 \\ 0 & 1 \end{pmatrix}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23891 (T U : Matrix (Fin 2) (Fin 2) ℚ) (hT : T =![![1, 0],![0, 0]]) (hU : U =![![0, 1],![0, 1]]) : T * U =![![0, 1],![0, 0]]   :=  by sorry
