-- Prove2me | Theorems.Thm_WorkbookRestored_plus_33814
-- name    : WorkbookRestored.plus_33814
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:48.820987+00:00
-- url     : https://prove2.me/theorems/72c43103-51e6-40d1-9ed0-53d2b3c066c9
-- title:
--   Lean-Workbook Plus 33814: Trigonometric identity
-- statement:
--   For real $A,B$, $\cos(A-B)=\cos A\cos B+\sin A\sin B$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_33814` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/7faa8836-5fde-49b5-94f6-ff8c3bedb9e9); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_33814; immutable original Prove2Me node 7faa8836-5fde-49b5-94f6-ff8c3bedb9e9

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_33814 (A B : ℝ) : Real.cos (A - B) = Real.cos A * Real.cos B + Real.sin A * Real.sin B   :=  by sorry
