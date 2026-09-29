-- Prove2me | Theorems.Thm_WorkbookRestored_plus_34790
-- name    : WorkbookRestored.plus_34790
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:34:26.39345+00:00
-- url     : https://prove2.me/theorems/417dae5c-d6f5-4807-a7e7-1a0d76e51de2
-- title:
--   Lean-Workbook Plus 34790: Trigonometric identity
-- statement:
--   **Lean-Workbook Plus 34790: Integer matrix with nonzero determinant**
--
--   There exists a $2\times2$ matrix with integer entries and nonzero determinant.
--
--   Source: Lean-Workbook row `lean_workbook_plus_34790` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/590b737f-5ed2-49c1-8fbc-98b6d2b6f0fd); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_34790; immutable original Prove2Me node 590b737f-5ed2-49c1-8fbc-98b6d2b6f0fd

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

theorem WorkbookRestored.plus_34790 : ∃ A : Matrix (Fin 2) (Fin 2) ℤ, A.det ≠ 0   :=  by sorry
