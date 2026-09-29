-- Prove2me | Theorems.Thm_WorkbookRestored_plus_5722
-- name    : WorkbookRestored.plus_5722
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:29:49.530739+00:00
-- url     : https://prove2.me/theorems/5ee00453-7e69-4f49-9215-1e1214454721
-- title:
--   Lean-Workbook Plus 5722: Trigonometric identity
-- statement:
--   For all real $a,b$, $2\cos a\cos b=\cos(a+b)+\cos(a-b)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_5722` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/a00d7137-fd6b-4df6-8f10-ca24bebe6d2d); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_5722; immutable original Prove2Me node a00d7137-fd6b-4df6-8f10-ca24bebe6d2d

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_5722 (a b : ℝ) : 2 * cos a * cos b = cos (a + b) + cos (a - b)   :=  by sorry
