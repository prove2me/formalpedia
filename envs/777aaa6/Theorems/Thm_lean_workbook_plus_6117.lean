-- Prove2me | Theorems.Thm_lean_workbook_plus_6117
-- name    : lean_workbook_plus_6117
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/0fef901a-75ea-4e0c-a69d-7eb7023215c5
-- statement:
--   Find matrices $A$ and $B$ of order $2 \times 2$ over $\mathbb{Z}/2\mathbb{Z}$ that satisfy $AB - BA = I$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6117 : ∃ A B : Matrix (Fin 2) (Fin 2) (ZMod 2), A * B - B * A = 1   :=  by sorry
