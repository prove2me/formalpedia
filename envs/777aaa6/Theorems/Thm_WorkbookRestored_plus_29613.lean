-- Prove2me | Theorems.Thm_WorkbookRestored_plus_29613
-- name    : WorkbookRestored.plus_29613
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:16.669049+00:00
-- url     : https://prove2.me/theorems/780ea030-a407-4ad3-ae39-bffa01b9010e
-- title:
--   Lean-Workbook Plus 29613: Exponential identity
-- statement:
--   For real $L$, $L(1-e^{-L^2/4})=0$ if and only if $L=0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_29613` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/6e43f6ef-2a96-400a-a50c-6ba665e1cccb); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_29613; immutable original Prove2Me node 6e43f6ef-2a96-400a-a50c-6ba665e1cccb

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_29613 (L : ℝ) : L * (1 - exp (-L^2 / 4)) = 0 ↔ L = 0   :=  by sorry
