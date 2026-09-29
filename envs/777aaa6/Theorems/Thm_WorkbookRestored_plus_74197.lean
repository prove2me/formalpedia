-- Prove2me | Theorems.Thm_WorkbookRestored_plus_74197
-- name    : WorkbookRestored.plus_74197
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:59.585301+00:00
-- url     : https://prove2.me/theorems/9602e214-c3f5-4c26-81c1-3ec3fc22542f
-- title:
--   Lean-Workbook Plus 74197: Trigonometric identity
-- statement:
--   For real $a,b$, $\sin(a-b)=\sin a\cos b-\sin b\cos a$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_74197` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/fceb4e5c-7376-4c15-8b23-381b61cd1d6f); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_74197; immutable original Prove2Me node fceb4e5c-7376-4c15-8b23-381b61cd1d6f

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_74197 (a b : ℝ) : sin (a - b) = sin a * cos b - sin b * cos a   :=  by sorry
