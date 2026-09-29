-- Prove2me | Theorems.Thm_WorkbookRestored_plus_71970
-- name    : WorkbookRestored.plus_71970
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:53.24817+00:00
-- url     : https://prove2.me/theorems/5e872bcd-3e18-4fce-a483-92295adbf5b2
-- title:
--   Lean-Workbook Plus 71970: Trigonometric identity
-- statement:
--   For real $a,b,u,v$, $a\sin u+b\sin(u+v)=(a+b\cos v)\sin u+(b\sin v)\cos u$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_71970` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/9e87e1a0-8c8a-4ac9-9976-ce2f9fbad5ee); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_71970; immutable original Prove2Me node 9e87e1a0-8c8a-4ac9-9976-ce2f9fbad5ee

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_71970 (a b : ℝ) (u v : ℝ) : a * sin u + b * sin (u + v) = (a + b * cos v) * sin u + (b * sin v) * cos u   :=  by sorry
