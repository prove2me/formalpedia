-- Prove2me | Theorems.Thm_WorkbookRestored_plus_60336
-- name    : WorkbookRestored.plus_60336
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:15.905673+00:00
-- url     : https://prove2.me/theorems/42f8c78c-7f62-4caf-967d-f12a4f3c91c2
-- title:
--   Lean-Workbook Plus 60336: Trigonometric identity
-- statement:
--   $\cos 36^\circ-\cos 72^\circ=\sin 54^\circ-\sin 18^\circ$
--
--   Source: Lean-Workbook row `lean_workbook_plus_60336` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/a5050888-6cac-4b7c-921a-6347d8a2e160); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_60336; immutable original Prove2Me node a5050888-6cac-4b7c-921a-6347d8a2e160

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_60336 : Real.cos (36 * Real.pi / 180) - Real.cos (72 * Real.pi / 180) = Real.sin (54 * Real.pi / 180) - Real.sin (18 * Real.pi / 180)   :=  by sorry
