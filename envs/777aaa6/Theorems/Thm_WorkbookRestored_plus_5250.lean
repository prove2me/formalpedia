-- Prove2me | Theorems.Thm_WorkbookRestored_plus_5250
-- name    : WorkbookRestored.plus_5250
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:29:44.568787+00:00
-- url     : https://prove2.me/theorems/372ac588-ea56-4ca1-9d3c-f02d043d1f6b
-- title:
--   Lean-Workbook Plus 5250: Trigonometric identity
-- statement:
--   Demonstrate the identity: \(\sin(a+x)-\sin(a-x)=2\cos(a)\sin(x)\)
--
--   Source: Lean-Workbook row `lean_workbook_plus_5250` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/a56376b9-4548-4465-9638-fd38782aeccd); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_5250; immutable original Prove2Me node a56376b9-4548-4465-9638-fd38782aeccd

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_5250 (a x : ℝ) : Real.sin (a + x) - Real.sin (a - x) = 2 * Real.cos a * Real.sin x   :=  by sorry
